import path from 'path';
import debug from 'debug';
import pify from 'pify';
import BufferCursor from 'buffercursor';
import sortby from 'lodash.sortby';
import shasum from 'shasum';
import crc32 from 'crc/lib/crc32.js';
import applyDelta from 'git-apply-delta';
import listpack from 'git-list-pack';
import { mark, stop } from 'marky';
import pako from 'pako';
import { PassThrough } from 'stream';
import pad from 'pad';
import streamSource from 'stream-source/index.node.js';
import ignore from 'ignore';
import AsyncLock from 'async-lock';
import concat from 'simple-concat';
import simpleGet from 'simple-get';
import { clean } from 'clean-git-ref';
import split2 from 'split2';
import through2 from 'through2';
import createHash from 'sha.js';

/**
 * Use with push and fetch to set Basic Authentication headers.
 *
 * @link https://isomorphic-git.github.io/docs/utils_auth.html
 */
function auth (username, password) {
  // Allow specifying it as one argument (mostly for CLI inputability)
  if (password === undefined) {
    let i = username.indexOf(':');
    if (i > -1) {
      password = username.slice(i + 1);
      username = username.slice(0, i);
    } else {
      password = ''; // Enables the .auth(GITHUB_TOKEN) no-username shorthand
    }
  }
  return { username, password }
}

/*::
type Node = {
  type: string,
  fullpath: string,
  basename: string,
  metadata: Object, // mode, oid
  parent?: Node,
  children: Array<Node>
}
*/

function flatFileListToDirectoryStructure (
  files
) {
  const inodes = new Map();
  const mkdir = function (name) {
    if (!inodes.has(name)) {
      let dir = {
        type: 'tree',
        fullpath: name,
        basename: path.basename(name),
        metadata: {},
        children: []
      };
      inodes.set(name, dir);
      // This recursively generates any missing parent folders.
      // We do it after we've added the inode to the set so that
      // we don't recurse infinitely trying to create the root '.' dirname.
      dir.parent = mkdir(path.dirname(name));
      if (dir.parent && dir.parent !== dir) dir.parent.children.push(dir);
    }
    return inodes.get(name)
  };

  const mkfile = function (name, metadata) {
    if (!inodes.has(name)) {
      let file = {
        type: 'blob',
        fullpath: name,
        basename: path.basename(name),
        metadata: metadata,
        // This recursively generates any missing parent folders.
        parent: mkdir(path.dirname(name)),
        children: []
      };
      if (file.parent) file.parent.children.push(file);
      inodes.set(name, file);
    }
    return inodes.get(name)
  };

  mkdir('.');
  for (let file of files) {
    mkfile(file.path, file);
  }
  return inodes.get('.')
}

const log = debug('isomorphic-git');

log.log = console.log.bind(console);

/**
 * Use with push and fetch to set Basic Authentication headers.
 *
 * @link https://isomorphic-git.github.io/docs/utils_oauth2.html
 */
function oauth2 (company, token) {
  switch (company) {
    case 'github':
      return {
        username: token,
        password: 'x-oauth-basic'
      }
    case 'bitbucket':
      return {
        username: 'x-token-auth',
        password: token
      }
    case 'gitlab':
      return {
        username: 'oauth2',
        password: token
      }
    default:
      throw new Error(
        `I don't know how ${company} expects its Basic Auth headers to be formatted for OAuth2 usage. If you do, you can use the regular '.auth(username, password)' to set the basic auth header yourself.`
      )
  }
}

const pkg = {
  name: 'isomorphic-git',
  version: '0.0.0-development'
};

async function sleep (ms) {
  return new Promise((resolve, reject) => setTimeout(resolve, ms))
}

const delayedReleases = new Map();
/**
 * This is just a collection of helper functions really. At least that's how it started.
 */
class FileSystem {
  constructor (fs) {
    if (typeof fs._readFile !== 'undefined') return fs
    this._readFile = pify(fs.readFile.bind(fs));
    this._writeFile = pify(fs.writeFile.bind(fs));
    this._mkdir = pify(fs.mkdir.bind(fs));
    this._rmdir = pify(fs.rmdir.bind(fs));
    this._unlink = pify(fs.unlink.bind(fs));
    this._stat = pify(fs.stat.bind(fs));
    this._lstat = pify(fs.lstat.bind(fs));
    this._readdir = pify(fs.readdir.bind(fs));
  }
  /**
   * Return true if a file exists, false if it doesn't exist.
   * Rethrows errors that aren't related to file existance.
   */
  async exists (filepath, options = {}) {
    try {
      await this._stat(filepath);
      return true
    } catch (err) {
      if (err.code === 'ENOENT' || err.code === 'ENOTDIR') {
        return false
      } else {
        console.log('Unhandled error in "FileSystem.exists()" function', err);
        throw err
      }
    }
  }
  /**
   * Return the contents of a file if it exists, otherwise returns null.
   */
  async read (filepath, options = {}) {
    try {
      let buffer = await this._readFile(filepath, options);
      return buffer
    } catch (err) {
      return null
    }
  }
  /**
   * Write a file (creating missing directories if need be) without throwing errors.
   */
  async write (
    filepath,
    contents,
    options = {}
  ) {
    try {
      await this._writeFile(filepath, contents, options);
      return
    } catch (err) {
      // Hmm. Let's try mkdirp and try again.
      await this.mkdir(path.dirname(filepath));
      await this._writeFile(filepath, contents, options);
    }
  }
  /**
   * Make a directory (or series of nested directories) without throwing an error if it already exists.
   */
  async mkdir (filepath) {
    try {
      await this._mkdir(filepath);
      return
    } catch (err) {
      // If err is null then operation succeeded!
      if (err === null) return
      // If the directory already exists, that's OK!
      if (err.code === 'EEXIST') return
      // If we got a "no such file or directory error" backup and try again.
      if (err.code === 'ENOENT') {
        let parent = path.dirname(filepath);
        // Check to see if we've gone too far
        if (parent === '.' || parent === '/' || parent === filepath) throw err
        // Infinite recursion, what could go wrong?
        await this.mkdir(parent);
        await this._mkdir(filepath);
      }
    }
  }
  /**
   * Delete a file without throwing an error if it is already deleted.
   */
  async rm (filepath) {
    try {
      await this._unlink(filepath);
    } catch (err) {
      if (err.code !== 'ENOENT') throw err
    }
  }
  /**
   * Read a directory without throwing an error is the directory doesn't exist
   */
  async readdir (filepath) {
    try {
      return await this._readdir(filepath)
    } catch (err) {
      return []
    }
  }
  /**
   * Return a flast list of all the files nested inside a directory
   *
   * Based on an elegant concurrent recursive solution from SO
   * https://stackoverflow.com/a/45130990/2168416
   */
  async readdirDeep (dir) {
    const subdirs = await this._readdir(dir);
    const files = await Promise.all(
      subdirs.map(async subdir => {
        const res = dir + '/' + subdir;
        return (await this._stat(res)).isDirectory()
          ? this.readdirDeep(res)
          : res
      })
    );
    return files.reduce((a, f) => a.concat(f), [])
  }

  async lock (filename, triesLeft = 3) {
    // check to see if we still have it
    if (delayedReleases.has(filename)) {
      clearTimeout(delayedReleases.get(filename));
      delayedReleases.delete(filename);
      return
    }
    if (triesLeft === 0) {
      throw new Error(
        `Unable to acquire lockfile '${filename}'. Exhausted tries.`
      )
    }
    try {
      await this._mkdir(`${filename}.lock`);
    } catch (err) {
      if (err.code === 'EEXIST') {
        await sleep(100);
        await this.lock(filename, triesLeft - 1);
      }
    }
  }

  async unlock (filename, delayRelease = 50) {
    if (delayedReleases.has(filename)) {
      throw new Error('Cannot double-release lockfile')
    }
    // Basically, we lie and say it was deleted ASAP.
    // But really we wait a bit to see if you want to acquire it again.
    delayedReleases.set(
      filename,
      setTimeout(async () => {
        delayedReleases.delete(filename);
        await this._rmdir(`${filename}.lock`);
      }, delayRelease)
    );
  }
}

function formatTimezoneOffset (minutes) {
  let sign = Math.sign(minutes) || 1;
  minutes = Math.abs(minutes);
  let hours = Math.floor(minutes / 60);
  minutes -= hours * 60;
  let strHours = String(hours);
  let strMinutes = String(minutes);
  if (strHours.length < 2) strHours = '0' + strHours;
  if (strMinutes.length < 2) strMinutes = '0' + strMinutes;
  return (sign === 1 ? '-' : '+') + strHours + strMinutes
}

function parseTimezoneOffset (offset) {
  let [, sign, hours, minutes] = offset.match(/(\+|-)(\d\d)(\d\d)/);
  minutes = (sign === '-' ? 1 : -1) * Number(hours) * 60 + Number(minutes);
  return minutes
}

function parseAuthor (author) {
  let [, name, email, timestamp, offset] = author.match(
    /^(.*) <(.*)> (.*) (.*)$/
  );
  return {
    name: name,
    email: email,
    timestamp: Number(timestamp),
    timezoneOffset: parseTimezoneOffset(offset)
  }
}

function normalize (str) {
  // remove all <CR>
  str = str.replace(/\r/g, '');
  // no extra newlines up front
  str = str.replace(/^\n+/, '');
  // and a single newline at the end
  str = str.replace(/\n+$/, '') + '\n';
  return str
}

function indent (str) {
  return (
    str
      .trim()
      .split('\n')
      .map(x => ' ' + x)
      .join('\n') + '\n'
  )
}

function outdent (str) {
  return str
    .split('\n')
    .map(x => x.replace(/^ /, ''))
    .join('\n')
}

// TODO: Make all functions have static async signature?

class GitCommit {
  constructor (commit) {
    if (typeof commit === 'string') {
      this._commit = commit;
    } else if (Buffer.isBuffer(commit)) {
      this._commit = commit.toString('utf8');
    } else if (typeof commit === 'object') {
      this._commit = GitCommit.render(commit);
    } else {
      throw new Error('invalid type passed to GitCommit constructor')
    }
  }

  static fromPayloadSignature ({ payload, signature }) {
    let headers = GitCommit.justHeaders(payload);
    let message = GitCommit.justMessage(payload);
    let commit = normalize(
      headers + '\ngpgsig' + indent(signature) + '\n' + message
    );
    return new GitCommit(commit)
  }

  static from (commit) {
    return new GitCommit(commit)
  }

  toObject () {
    return Buffer.from(this._commit, 'utf8')
  }

  // Todo: allow setting the headers and message
  headers () {
    return this.parseHeaders()
  }

  // Todo: allow setting the headers and message
  message () {
    return GitCommit.justMessage(this._commit)
  }

  parse () {
    return Object.assign({ message: this.message() }, this.headers())
  }

  static justMessage (commit) {
    return normalize(commit.slice(commit.indexOf('\n\n') + 2))
  }

  static justHeaders (commit) {
    return commit.slice(0, commit.indexOf('\n\n'))
  }

  parseHeaders () {
    let headers = GitCommit.justHeaders(this._commit).split('\n');
    let hs = [];
    for (let h of headers) {
      if (h[0] === ' ') {
        // combine with previous header (without space indent)
        hs[hs.length - 1] += '\n' + h.slice(1);
      } else {
        hs.push(h);
      }
    }
    let obj = {};
    for (let h of hs) {
      let key = h.slice(0, h.indexOf(' '));
      let value = h.slice(h.indexOf(' ') + 1);
      obj[key] = value;
    }
    obj.parent = obj.parent ? obj.parent.split(' ') : [];
    if (obj.author) {
      obj.author = parseAuthor(obj.author);
    }
    if (obj.committer) {
      obj.committer = parseAuthor(obj.committer);
    }
    return obj
  }

  static renderHeaders (obj) {
    let headers = '';
    if (obj.tree) {
      headers += `tree ${obj.tree}\n`;
    } else {
      headers += `tree 4b825dc642cb6eb9a060e54bf8d69288fbee4904\n`; // the null tree
    }
    if (obj.parent && obj.parent.length) {
      headers += 'parent';
      for (let p of obj.parent) {
        headers += ' ' + p;
      }
      headers += '\n';
    }
    let author = obj.author;
    headers += `author ${author.name} <${author.email}> ${
      author.timestamp
    } ${formatTimezoneOffset(author.timezoneOffset)}\n`;
    let committer = obj.committer || obj.author;
    headers += `committer ${committer.name} <${committer.email}> ${
      committer.timestamp
    } ${formatTimezoneOffset(committer.timezoneOffset)}\n`;
    if (obj.gpgsig) {
      headers += 'gpgsig' + indent(obj.gpgsig);
    }
    return headers
  }

  static render (obj) {
    return GitCommit.renderHeaders(obj) + '\n' + normalize(obj.message)
  }

  render () {
    return this._commit
  }

  withoutSignature () {
    let commit = normalize(this._commit);
    if (commit.indexOf('\ngpgsig') === -1) return commit
    let headers = commit.slice(0, commit.indexOf('\ngpgsig'));
    let message = commit.slice(
      commit.indexOf('-----END PGP SIGNATURE-----\n') +
        '-----END PGP SIGNATURE-----\n'.length
    );
    return normalize(headers + '\n' + message)
  }

  isolateSignature () {
    let signature = this._commit.slice(
      this._commit.indexOf('-----BEGIN PGP SIGNATURE-----'),
      this._commit.indexOf('-----END PGP SIGNATURE-----') +
        '-----END PGP SIGNATURE-----'.length
    );
    return outdent(signature)
  }
}

// This is straight from parse_unit_factor in config.c of canonical git
const num = val => {
  val = val.toLowerCase();
  let n = parseInt(val);
  if (val.endsWith('k')) n *= 1024;
  if (val.endsWith('m')) n *= 1024 * 1024;
  if (val.endsWith('g')) n *= 1024 * 1024 * 1024;
  return n
};

// This is straight from git_parse_maybe_bool_text in config.c of canonical git
const bool = val => {
  val = val.trim().toLowerCase();
  if (val === 'true' || val === 'yes' || val === 'on') return true
  if (val === 'false' || val === 'no' || val === 'off') return false
  throw Error(
    `Expected 'true', 'false', 'yes', 'no', 'on', or 'off', but got ${val}`
  )
};

const schema = {
  core: {
    _named: false,
    repositoryformatversion: String,
    filemode: bool,
    bare: bool,
    logallrefupdates: bool,
    symlinks: bool,
    ignorecase: bool,
    bigFileThreshold: num
  },
  remote: {
    _named: true,
    url: String,
    fetch: String
  },
  branch: {
    _named: true,
    remote: String,
    merge: String
  }
};

const isSection = line => line.trim().startsWith('[');

const extractSection = line => {
  const indices = [line.indexOf(']'), line.indexOf(' ')].filter(i => i > -1);
  return line.slice(line.indexOf('[') + 1, Math.min(...indices)).trim()
};

const isNamedSection = section => schema[section] && schema[section]._named;

const isKeyValuePair = line => line.includes('=');

const extractSectionName = line =>
  line.slice(line.indexOf('"') + 1, line.lastIndexOf('"'));

// Note: there are a LOT of edge cases that aren't covered (e.g. keys in sections that also
// have subsections, [include] directives, etc.
class GitConfig {
  constructor (text) {
    this.lines = text.split('\n');
  }
  static from (text) {
    return new GitConfig(text)
  }
  async get (path$$1, getall = false) {
    const parts = path$$1.split('.');
    const section = parts.shift();
    const sectionName = isNamedSection(section) ? parts.shift() : null;
    const key = parts.shift();

    let currentSection = '';
    let currentSectionName = null;
    let allValues = [];
    for (const line of this.lines) {
      // zero in on section
      if (isSection(line)) {
        currentSection = extractSection(line);
        if (isNamedSection(currentSection)) {
          currentSectionName = extractSectionName(line);
        }
      } else if (
        currentSection === section &&
        (sectionName === null || currentSectionName === sectionName)
      ) {
        if (isKeyValuePair(line)) {
          let [_key, _value] = line.split('=', 2);
          if (_key.trim() === key) {
            allValues.push(_value.trim());
          }
        }
      }
    }
    // Cast value to correct type
    let fn = schema[section] && schema[section][key];
    if (fn) {
      allValues = allValues.map(fn);
    }
    return getall ? allValues : allValues.pop()
  }
  async getall (path$$1) {
    return this.get(path$$1, true)
  }
  async append (path$$1, value) {
    return this.set(path$$1, value, true)
  }
  async set (path$$1, value, append = false) {
    const parts = path$$1.split('.');
    const section = parts.shift();
    const sectionName = isNamedSection(section) ? parts.shift() : null;
    const key = parts.shift();

    let currentSection = '';
    let currentSectionName = null;
    let lastSectionMatch = null;
    let lastMatch = null;
    for (let i = 0; i < this.lines.length; i++) {
      const line = this.lines[i];
      if (isSection(line)) {
        currentSection = extractSection(line);
        if (currentSection === section) {
          if (sectionName) {
            currentSectionName = extractSectionName(line);
          }
          if (currentSectionName === sectionName) {
            lastSectionMatch = i;
          }
        } else {
          currentSectionName = null;
        }
      } else if (
        currentSection === section &&
        (sectionName === null || currentSectionName === sectionName)
      ) {
        if (isKeyValuePair(line)) {
          let [_key] = line.split('=', 1);
          if (_key.trim() === key) {
            lastMatch = i;
          }
        }
      }
    }
    if (lastMatch !== null) {
      if (value === undefined) {
        this.lines.splice(lastMatch, 1);
      } else if (append) {
        this.lines.splice(lastMatch + 1, 0, [`\t${key} = ${value}`]);
      } else {
        this.lines[lastMatch] = `\t${key} = ${value}`;
      }
    } else if (lastSectionMatch !== null) {
      if (value !== undefined) {
        this.lines.splice(lastSectionMatch + 1, 0, [`\t${key} = ${value}`]);
      }
    } else if (value !== undefined) {
      if (sectionName) {
        this.lines.push(`[${section} "${sectionName}"]`);
      } else {
        this.lines.push(`[${section}]`);
      }
      this.lines.push([`\t${key} = ${value}`]);
    }
  }
  toString () {
    return this.lines.join('\n') + '\n'
  }
}

const MAX_UINT32 = 2 ** 32;
/*::
import type {Stats} from 'fs'

type CacheEntryFlags = {
  assumeValid: boolean,
  extended: boolean,
  stage: number,
  nameLength: number
}

type CacheEntry = {
  ctime: Date,
  ctimeNanoseconds?: number,
  mtime: Date,
  mtimeNanoseconds?: number,
  dev: number,
  ino: number,
  mode: number,
  uid: number,
  gid: number,
  size: number,
  oid: string,
  flags: CacheEntryFlags,
  path: string
}
*/

// Extract 1-bit assume-valid, 1-bit extended flag, 2-bit merge state flag, 12-bit path length flag
function parseCacheEntryFlags (bits) {
  return {
    assumeValid: Boolean(bits & 0b1000000000000000),
    extended: Boolean(bits & 0b0100000000000000),
    stage: (bits & 0b0011000000000000) >> 12,
    nameLength: bits & 0b0000111111111111
  }
}

function renderCacheEntryFlags (flags) {
  return (
    (flags.assumeValid ? 0b1000000000000000 : 0) +
    (flags.extended ? 0b0100000000000000 : 0) +
    ((flags.stage & 0b11) << 12) +
    (flags.nameLength & 0b111111111111)
  )
}

function parseBuffer (buffer) {
  // Verify shasum
  let shaComputed = shasum(buffer.slice(0, -20));
  let shaClaimed = buffer.slice(-20).toString('hex');
  if (shaClaimed !== shaComputed) {
    throw new Error(
      `Invalid checksum in GitIndex buffer: expected ${shaClaimed} but saw ${shaComputed}`
    )
  }
  let reader = new BufferCursor(buffer);
  let _entries = new Map();
  let magic = reader.toString('utf8', 4);
  if (magic !== 'DIRC') {
    throw new Error(`Inavlid dircache magic file number: ${magic}`)
  }
  let version = reader.readUInt32BE();
  if (version !== 2) throw new Error(`Unsupported dircache version: ${version}`)
  let numEntries = reader.readUInt32BE();
  let i = 0;
  while (!reader.eof() && i < numEntries) {
    let entry = {};
    let ctimeSeconds = reader.readUInt32BE();
    let ctimeNanoseconds = reader.readUInt32BE();
    entry.ctime = new Date(ctimeSeconds * 1000 + ctimeNanoseconds / 1000000);
    entry.ctimeNanoseconds = ctimeNanoseconds;
    let mtimeSeconds = reader.readUInt32BE();
    let mtimeNanoseconds = reader.readUInt32BE();
    entry.mtime = new Date(mtimeSeconds * 1000 + mtimeNanoseconds / 1000000);
    entry.mtimeNanoseconds = mtimeNanoseconds;
    entry.dev = reader.readUInt32BE();
    entry.ino = reader.readUInt32BE();
    entry.mode = reader.readUInt32BE();
    entry.uid = reader.readUInt32BE();
    entry.gid = reader.readUInt32BE();
    entry.size = reader.readUInt32BE();
    entry.oid = reader.slice(20).toString('hex');
    let flags = reader.readUInt16BE();
    entry.flags = parseCacheEntryFlags(flags);
    // TODO: handle if (version === 3 && entry.flags.extended)
    let pathlength = buffer.indexOf(0, reader.tell() + 1) - reader.tell();
    if (pathlength < 1) throw new Error(`Got a path length of: ${pathlength}`)
    entry.path = reader.toString('utf8', pathlength);
    // The next bit is awkward. We expect 1 to 8 null characters
    let tmp = reader.readUInt8();
    if (tmp !== 0) {
      throw new Error(`Expected 1-8 null characters but got '${tmp}'`)
    }
    let numnull = 1;
    while (!reader.eof() && reader.readUInt8() === 0 && numnull < 9) numnull++;
    reader.seek(reader.tell() - 1);
    // end of awkward part
    _entries.set(entry.path, entry);
    i++;
  }
  return _entries
}

class GitIndex {
  /*::
   _entries: Map<string, CacheEntry>
   _dirty: boolean // Used to determine if index needs to be saved to filesystem
   */
  constructor (index) {
    this._dirty = false;
    if (Buffer.isBuffer(index)) {
      this._entries = parseBuffer(index);
    } else if (index === null) {
      this._entries = new Map();
    } else {
      throw new Error('invalid type passed to GitIndex constructor')
    }
  }
  static from (buffer) {
    return new GitIndex(buffer)
  }
  get entries () {
    return sortby([...this._entries.values()], 'path')
  }
  * [Symbol.iterator] () {
    for (let entry of this.entries) {
      yield entry;
    }
  }
  insert ({
    filepath,
    stats,
    oid
  }) {
    let entry = {
      ctime: stats.ctime,
      mtime: stats.mtime,
      dev: stats.dev % MAX_UINT32,
      ino: stats.ino % MAX_UINT32,
      mode: stats.mode % MAX_UINT32,
      uid: stats.uid % MAX_UINT32,
      gid: stats.gid % MAX_UINT32,
      size: stats.size % MAX_UINT32,
      path: filepath,
      oid: oid,
      flags: {
        assumeValid: false,
        extended: false,
        stage: 0,
        nameLength: filepath.length < 0xfff ? filepath.length : 0xfff
      }
    };
    this._entries.set(entry.path, entry);
    this._dirty = true;
  }
  delete ({ filepath }) {
    if (this._entries.has(filepath)) {
      this._entries.delete(filepath);
    } else {
      for (let key of this._entries.keys()) {
        if (key.startsWith(filepath + '/')) {
          this._entries.delete(key);
        }
      }
    }
    this._dirty = true;
  }
  clear () {
    this._entries.clear();
    this._dirty = true;
  }
  render () {
    return this.entries
      .map(entry => `${entry.mode.toString(8)} ${entry.oid}    ${entry.path}`)
      .join('\n')
  }
  toObject () {
    let header = Buffer.alloc(12);
    let writer = new BufferCursor(header);
    writer.write('DIRC', 4, 'utf8');
    writer.writeUInt32BE(2);
    writer.writeUInt32BE(this.entries.length);
    let body = Buffer.concat(
      this.entries.map(entry => {
        // the fixed length + the filename + at least one null char => align by 8
        let length = Math.ceil((62 + entry.path.length + 1) / 8) * 8;
        let written = Buffer.alloc(length);
        let writer = new BufferCursor(written);
        let ctimeMilliseconds = entry.ctime.valueOf();
        let ctimeSeconds = Math.floor(ctimeMilliseconds / 1000);
        let ctimeNanoseconds =
          entry.ctimeNanoseconds ||
          ctimeMilliseconds * 1000000 - ctimeSeconds * 1000000 * 1000;
        let mtimeMilliseconds = entry.mtime.valueOf();
        let mtimeSeconds = Math.floor(mtimeMilliseconds / 1000);
        let mtimeNanoseconds =
          entry.mtimeNanoseconds ||
          mtimeMilliseconds * 1000000 - mtimeSeconds * 1000000 * 1000;
        writer.writeUInt32BE(ctimeSeconds % MAX_UINT32);
        writer.writeUInt32BE(ctimeNanoseconds % MAX_UINT32);
        writer.writeUInt32BE(mtimeSeconds % MAX_UINT32);
        writer.writeUInt32BE(mtimeNanoseconds % MAX_UINT32);
        writer.writeUInt32BE(entry.dev % MAX_UINT32);
        writer.writeUInt32BE(entry.ino % MAX_UINT32);
        writer.writeUInt32BE(entry.mode % MAX_UINT32);
        writer.writeUInt32BE(entry.uid % MAX_UINT32);
        writer.writeUInt32BE(entry.gid % MAX_UINT32);
        writer.writeUInt32BE(entry.size % MAX_UINT32);
        writer.write(entry.oid, 20, 'hex');
        writer.writeUInt16BE(renderCacheEntryFlags(entry.flags));
        writer.write(entry.path, entry.path.length, 'utf8');
        return written
      })
    );
    let main = Buffer.concat([header, body]);
    let sum = shasum(main);
    return Buffer.concat([main, Buffer.from(sum, 'hex')])
  }
}

class GitObject {
  static hash ({ type, object }) {
    let buffer = Buffer.concat([
      Buffer.from(`${type} ${object.byteLength.toString()}\0`),
      Buffer.from(object)
    ]);
    let oid = shasum(buffer);
    return oid
  }
  static wrap ({ type, object }) {
    let buffer = Buffer.concat([
      Buffer.from(`${type} ${object.byteLength.toString()}\0`),
      object
    ]);
    let oid = shasum(buffer);
    return {
      oid,
      buffer
    }
  }
  static unwrap ({ oid, buffer }) {
    if (oid) {
      let sha = shasum(buffer);
      if (sha !== oid) {
        throw new Error(`SHA check failed! Expected ${oid}, computed ${sha}`)
      }
    }
    let s = buffer.indexOf(32); // first space
    let i = buffer.indexOf(0); // first null value
    let type = buffer.slice(0, s).toString('utf8'); // get type of object
    let length = buffer.slice(s + 1, i).toString('utf8'); // get type of object
    let actualLength = buffer.length - (i + 1);
    // verify length
    if (parseInt(length) !== actualLength) {
      throw new Error(
        `Length mismatch: expected ${length} bytes but got ${actualLength} instead.`
      )
    }
    return {
      type,
      object: Buffer.from(buffer.slice(i + 1))
    }
  }
}

function buffer2stream (buffer) {
  let stream = new PassThrough();
  stream.end(buffer);
  return stream
}

function decodeVarInt (reader) {
  let bytes = [];
  let byte = 0;
  let multibyte = 0;
  do {
    byte = reader.readUInt8();
    // We keep bits 6543210
    const lastSeven = byte & 0b01111111;
    bytes.push(lastSeven);
    // Whether the next byte is part of the variable-length encoded number
    // is encoded in bit 7
    multibyte = byte & 0b10000000;
  } while (multibyte)
  // Now that all the bytes are in big-endian order,
  // alternate shifting the bits left by 7 and OR-ing the next byte.
  // And... do a weird increment-by-one thing that I don't quite understand.
  return bytes.reduce((a, b) => ((a + 1) << 7) | b, -1)
}

// I'm pretty much copying this one from the git C source code,
// because it makes no sense.
function otherVarIntDecode (reader, startWith) {
  let result = startWith;
  let shift = 4;
  let byte = null;
  do {
    byte = reader.readUInt8();
    result |= (byte & 0b01111111) << shift;
    shift += 7;
  } while (byte & 0b10000000)
  return result
}

class GitPackIndex {
  constructor (stuff) {
    Object.assign(this, stuff);
    this.offsetCache = {};
  }
  static async fromIdx ({ idx, getExternalRefDelta }) {
    let reader = new BufferCursor(idx);
    let magic = reader.slice(4).toString('hex');
    // Check for IDX v2 magic number
    if (magic !== 'ff744f63') {
      return // undefined
    }
    let version = reader.readUInt32BE();
    if (version !== 2) {
      throw new Error(
        `Unable to read version ${version} packfile IDX. (Only version 2 supported)`
      )
    }
    // Verify checksums
    let shaComputed = shasum(idx.slice(0, -20));
    let shaClaimed = idx.slice(-20).toString('hex');
    if (shaClaimed !== shaComputed) {
      throw new Error(
        `Invalid checksum in IDX buffer: expected ${shaClaimed} but saw ${shaComputed}`
      )
    }
    if (idx.byteLength > 2048 * 1024 * 1024) {
      throw new Error(
        `To keep implementation simple, I haven't implemented the layer 5 feature needed to support packfiles > 2GB in size.`
      )
    }
    let fanout = [];
    for (let i = 0; i < 256; i++) {
      fanout.push(reader.readUInt32BE());
    }
    let size = fanout[255];
    // For now we'll parse the whole thing. We can optimize later if we need to.
    let hashes = [];
    for (let i = 0; i < size; i++) {
      hashes.push(reader.slice(20).toString('hex'));
    }
    let crcs = {};
    for (let i = 0; i < size; i++) {
      crcs[hashes[i]] = reader.readUInt32BE();
    }
    let offsets = {};
    for (let i = 0; i < size; i++) {
      offsets[hashes[i]] = reader.readUInt32BE();
    }
    let packfileSha = reader.slice(20).toString('hex');
    return new GitPackIndex({
      hashes,
      crcs,
      offsets,
      packfileSha,
      getExternalRefDelta
    })
  }
  static async fromPack ({ pack, getExternalRefDelta }) {
    const listpackTypes = {
      1: 'commit',
      2: 'tree',
      3: 'blob',
      4: 'tag',
      6: 'ofs-delta',
      7: 'ref-delta'
    };
    let offsetToObject = {};

    // Older packfiles do NOT use the shasum of the pack itself,
    // so it is recommended to just use whatever bytes are in the trailer.
    // Source: https://github.com/git/git/commit/1190a1acf800acdcfd7569f87ac1560e2d077414
    // let packfileSha = shasum(pack.slice(0, -20))
    let packfileSha = pack.slice(-20).toString('hex');

    let hashes = [];
    let crcs = {};
    let offsets = {};
    let totalObjectCount = null;
    let lastPercent = null;
    let times = {
      hash: 0,
      readSlice: 0,
      offsets: 0,
      crcs: 0,
      sort: 0
    };
    let histogram = {
      commit: 0,
      tree: 0,
      blob: 0,
      tag: 0,
      'ofs-delta': 0,
      'ref-delta': 0
    };
    let bytesProcessed = 0;

    log('Indexing objects');
    log(
      `percent\tmilliseconds\tbytesProcessed\tcommits\ttrees\tblobs\ttags\tofs-deltas\tref-deltas`
    );
    mark('total');
    mark('offsets');
    mark('percent');
    await new Promise((resolve, reject) => {
      buffer2stream(pack)
        .pipe(listpack())
        .on('data', async ({ data, type, reference, offset, num }) => {
          if (totalObjectCount === null) totalObjectCount = num;
          let percent = Math.floor(
            (totalObjectCount - num) * 100 / totalObjectCount
          );
          if (percent !== lastPercent) {
            log(
              `${percent}%\t${Math.floor(
                stop('percent').duration
              )}\t${bytesProcessed}\t${histogram.commit}\t${histogram.tree}\t${
                histogram.blob
              }\t${histogram.tag}\t${histogram['ofs-delta']}\t${
                histogram['ref-delta']
              }`
            );

            histogram = {
              commit: 0,
              tree: 0,
              blob: 0,
              tag: 0,
              'ofs-delta': 0,
              'ref-delta': 0
            };
            bytesProcessed = 0;
            mark('percent');
          }
          lastPercent = percent;
          // Change type from a number to a meaningful string
          type = listpackTypes[type];

          histogram[type]++;
          bytesProcessed += data.byteLength;

          if (['commit', 'tree', 'blob', 'tag'].includes(type)) {
            offsetToObject[offset] = {
              type,
              offset
            };
          } else if (type === 'ofs-delta') {
            offsetToObject[offset] = {
              type,
              offset
            };
          } else if (type === 'ref-delta') {
            offsetToObject[offset] = {
              type,
              offset
            };
          }
          if (num === 0) resolve();
        });
    });
    times['offsets'] = Math.floor(stop('offsets').duration);

    log('Computing CRCs');
    mark('crcs');
    // We need to know the lengths of the slices to compute the CRCs.
    let offsetArray = Object.keys(offsetToObject).map(Number);
    for (let [i, start] of offsetArray.entries()) {
      let end =
        i + 1 === offsetArray.length ? pack.byteLength - 20 : offsetArray[i + 1];
      let o = offsetToObject[start];
      let crc = crc32(pack.slice(start, end));
      o.end = end;
      o.crc = crc;
    }
    times['crcs'] = Math.floor(stop('crcs').duration);

    // We don't have the hashes yet. But we can generate them using the .readSlice function!
    const p = new GitPackIndex({
      pack,
      packfileSha,
      crcs,
      hashes,
      offsets,
      getExternalRefDelta
    });

    // Resolve deltas and compute the oids
    log('Resolving deltas');
    log(`percent2\tmilliseconds2\tcallsToReadSlice\tcallsToGetExternal`);
    mark('percent');
    lastPercent = null;
    let count = 0;
    let callsToReadSlice = 0;
    let callsToGetExternal = 0;
    let timeByDepth = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    let objectsByDepth = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    for (let offset in offsetToObject) {
      offset = Number(offset);
      let percent = Math.floor(count++ * 100 / totalObjectCount);
      if (percent !== lastPercent) {
        log(
          `${percent}%\t${Math.floor(
            stop('percent').duration
          )}\t${callsToReadSlice}\t${callsToGetExternal}`
        );
        mark('percent');
        callsToReadSlice = 0;
        callsToGetExternal = 0;
      }
      lastPercent = percent;

      let o = offsetToObject[offset];
      if (o.oid) continue
      try {
        p.readDepth = 0;
        p.externalReadDepth = 0;
        mark('readSlice');
        let { type, object } = await p.readSlice({ start: offset });
        let time = stop('readSlice').duration;
        times.readSlice += time;
        callsToReadSlice += p.readDepth;
        callsToGetExternal += p.externalReadDepth;
        timeByDepth[p.readDepth] += time;
        objectsByDepth[p.readDepth] += 1;
        mark('hash');
        let oid = GitObject.hash({ type, object });
        times.hash += stop('hash').duration;
        o.oid = oid;
        hashes.push(oid);
        offsets[oid] = offset;
        crcs[oid] = o.crc;
      } catch (err) {
        log('ERROR', err);
        continue
      }
    }

    mark('sort');
    hashes.sort();
    times['sort'] = Math.floor(stop('sort').duration);
    let totalElapsedTime = stop('total').duration;
    times.hash = Math.floor(times.hash);
    times.readSlice = Math.floor(times.readSlice);
    times.misc = Math.floor(
      Object.values(times).reduce((a, b) => a - b, totalElapsedTime)
    );
    log(Object.keys(times).join('\t'));
    log(Object.values(times).join('\t'));
    log('by depth:');
    log([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11].join('\t'));
    log(objectsByDepth.slice(0, 12).join('\t'));
    log(
      timeByDepth
        .map(Math.floor)
        .slice(0, 12)
        .join('\t')
    );
    return p
  }
  toBuffer () {
    let buffers = [];
    let write = (str, encoding) => {
      buffers.push(Buffer.from(str, encoding));
    };
    // Write out IDX v2 magic number
    write('ff744f63', 'hex');
    // Write out version number 2
    write('00000002', 'hex');
    // Write fanout table
    let fanoutBuffer = new BufferCursor(Buffer.alloc(256 * 4));
    for (let i = 0; i < 256; i++) {
      let count = 0;
      for (let hash of this.hashes) {
        if (parseInt(hash.slice(0, 2), 16) <= i) count++;
      }
      fanoutBuffer.writeUInt32BE(count);
    }
    buffers.push(fanoutBuffer.buffer);
    // Write out hashes
    for (let hash of this.hashes) {
      write(hash, 'hex');
    }
    // Write out crcs
    let crcsBuffer = new BufferCursor(Buffer.alloc(this.hashes.length * 4));
    for (let hash of this.hashes) {
      crcsBuffer.writeUInt32BE(this.crcs[hash]);
    }
    buffers.push(crcsBuffer.buffer);
    // Write out offsets
    let offsetsBuffer = new BufferCursor(Buffer.alloc(this.hashes.length * 4));
    for (let hash of this.hashes) {
      offsetsBuffer.writeUInt32BE(this.offsets[hash]);
    }
    buffers.push(offsetsBuffer.buffer);
    // Write out packfile checksum
    write(this.packfileSha, 'hex');
    // Write out shasum
    let totalBuffer = Buffer.concat(buffers);
    let sha = shasum(totalBuffer);
    let shaBuffer = Buffer.alloc(20);
    shaBuffer.write(sha, 'hex');
    return Buffer.concat([totalBuffer, shaBuffer])
  }
  async load ({ pack }) {
    this.pack = pack;
  }
  async unload () {
    this.pack = null;
  }
  async read ({ oid }) {
    if (!this.offsets[oid]) {
      if (this.getExternalRefDelta) {
        this.externalReadDepth++;
        return this.getExternalRefDelta(oid)
      } else {
        throw new Error(`Could not read object ${oid} from packfile`)
      }
    }
    let start = this.offsets[oid];
    return this.readSlice({ start })
  }
  async readSlice ({ start }) {
    if (this.offsetCache[start]) return this.offsetCache[start]
    this.readDepth++;
    const types = {
      0b0010000: 'commit',
      0b0100000: 'tree',
      0b0110000: 'blob',
      0b1000000: 'tag',
      0b1100000: 'ofs_delta',
      0b1110000: 'ref_delta'
    };
    if (!this.pack) {
      throw new Error(
        'Tried to read from a GitPackIndex with no packfile loaded into memory'
      )
    }
    let raw = this.pack.slice(start);
    let reader = new BufferCursor(raw);
    let byte = reader.readUInt8();
    // Object type is encoded in bits 654
    let btype = byte & 0b1110000;
    let type = types[btype];
    if (type === undefined) {
      throw new Error('Unrecognized type: 0b' + btype.toString(2))
    }
    // The length encoding get complicated.
    // Last four bits of length is encoded in bits 3210
    let lastFour = byte & 0b1111;
    let length = lastFour;
    // Whether the next byte is part of the variable-length encoded number
    // is encoded in bit 7
    let multibyte = byte & 0b10000000;
    if (multibyte) {
      length = otherVarIntDecode(reader, lastFour);
    }
    let base = null;
    let object = null;
    // Handle deltified objects
    if (type === 'ofs_delta') {
      let offset = decodeVarInt(reader);
      let baseOffset = start - offset
      ;({ object: base, type } = await this.readSlice({ start: baseOffset }));
    }
    if (type === 'ref_delta') {
      let oid = reader.slice(20).toString('hex')
      ;({ object: base, type } = await this.read({ oid }));
    }
    // Handle undeltified objects
    let buffer = raw.slice(reader.tell());
    object = Buffer.from(pako.inflate(buffer));
    // Assert that the object length is as expected.
    if (object.byteLength !== length) {
      throw new Error(
        `Packfile told us object would have length ${length} but it had length ${
          object.byteLength
        }`
      )
    }
    if (base) {
      object = Buffer.from(applyDelta(object, base));
    }
    // Cache the result based on depth.
    if (this.readDepth > 3) {
      // hand tuned for speed / memory usage tradeoff
      this.offsetCache[start] = { type, object };
    }
    return { type, format: 'content', object }
  }
}

/**
pkt-line Format
---------------

Much (but not all) of the payload is described around pkt-lines.

A pkt-line is a variable length binary string.  The first four bytes
of the line, the pkt-len, indicates the total length of the line,
in hexadecimal.  The pkt-len includes the 4 bytes used to contain
the length's hexadecimal representation.

A pkt-line MAY contain binary data, so implementors MUST ensure
pkt-line parsing/formatting routines are 8-bit clean.

A non-binary line SHOULD BE terminated by an LF, which if present
MUST be included in the total length. Receivers MUST treat pkt-lines
with non-binary data the same whether or not they contain the trailing
LF (stripping the LF if present, and not complaining when it is
missing).

The maximum length of a pkt-line's data component is 65516 bytes.
Implementations MUST NOT send pkt-line whose length exceeds 65520
(65516 bytes of payload + 4 bytes of length data).

Implementations SHOULD NOT send an empty pkt-line ("0004").

A pkt-line with a length field of 0 ("0000"), called a flush-pkt,
is a special case and MUST be handled differently than an empty
pkt-line ("0004").

----
  pkt-line     =  data-pkt / flush-pkt

  data-pkt     =  pkt-len pkt-payload
  pkt-len      =  4*(HEXDIG)
  pkt-payload  =  (pkt-len - 4)*(OCTET)

  flush-pkt    = "0000"
----

Examples (as C-style strings):

----
  pkt-line          actual value
  ---------------------------------
  "0006a\n"         "a\n"
  "0005a"           "a"
  "000bfoobar\n"    "foobar\n"
  "0004"            ""
----
*/

// I'm really using this more as a namespace.
// There's not a lot of "state" in a pkt-line

class GitPktLine {
  static flush () {
    return Buffer.from('0000', 'utf8')
  }

  static encode (line) {
    if (typeof line === 'string') {
      line = Buffer.from(line);
    }
    let length = line.length + 4;
    let hexlength = pad(4, length.toString(16), '0');
    return Buffer.concat([Buffer.from(hexlength, 'utf8'), line])
  }

  static reader (buffer) {
    let buffercursor = new BufferCursor(buffer);
    return async function read () {
      if (buffercursor.eof()) return true
      let length = parseInt(buffercursor.slice(4).toString('utf8'), 16);
      if (length === 0) return null
      return buffercursor.slice(length - 4).buffer
    }
  }

  static streamReader (stream) {
    const bufferstream = streamSource(stream);
    return async function read () {
      try {
        let length = await bufferstream.slice(4);
        if (length === null) return true
        length = parseInt(length.toString('utf8'), 16);
        if (length === 0) return null
        let buffer = await bufferstream.slice(length - 4);
        if (buffer === null) return true
        return buffer
      } catch (err) {
        console.log('error', err);
        return true
      }
    }
  }
}

class GitRefSpec {
  constructor ({ remotePath, localPath, force, matchPrefix }) {
    Object.assign(this, {
      remotePath,
      localPath,
      force,
      matchPrefix
    });
  }
  static from (refspec) {
    const [
      forceMatch,
      remotePath,
      remoteGlobMatch,
      localPath,
      localGlobMatch
    ] = refspec.match(/^(\+?)(.*?)(\*?):(.*?)(\*?)$/).slice(1);
    const force = forceMatch === '+';
    const remoteIsGlob = remoteGlobMatch === '*';
    const localIsGlob = localGlobMatch === '*';
    // validate
    // TODO: Make this check more nuanced, and depend on whether this is a fetch refspec or a push refspec
    if (remoteIsGlob !== localIsGlob) throw new Error('Invalid refspec')
    return new GitRefSpec({
      remotePath,
      localPath,
      force,
      matchPrefix: remoteIsGlob
    })
    // TODO: We need to run resolveRef on both paths to expand them to their full name.
  }
  translate (remoteBranch) {
    if (this.matchPrefix) {
      if (remoteBranch.startsWith(this.remotePath)) {
        return this.localPath + remoteBranch.replace(this.remotePath, '')
      }
    } else {
      if (remoteBranch === this.remotePath) return this.localPath
    }
    return null
  }
}

class GitRefSpecSet {
  constructor (rules = []) {
    this.rules = rules;
  }
  static from (refspecs) {
    const rules = [];
    for (const refspec of refspecs) {
      rules.push(GitRefSpec.from(refspec)); // might throw
    }
    return new GitRefSpecSet(rules)
  }
  add (refspec) {
    const rule = GitRefSpec.from(refspec); // might throw
    this.rules.push(rule);
  }
  translate (remoteRefs) {
    const result = [];
    for (const rule of this.rules) {
      for (const remoteRef of remoteRefs) {
        const localRef = rule.translate(remoteRef);
        if (localRef) {
          result.push([remoteRef, localRef]);
        }
      }
    }
    return result
  }
  translateOne (remoteRef) {
    let result = null;
    for (const rule of this.rules) {
      const localRef = rule.translate(remoteRef);
      if (localRef) {
        result = localRef;
      }
    }
    return result
  }
}

/*::
type TreeEntry = {
  mode: string,
  path: string,
  oid: string,
  type?: string
}
*/

function parseBuffer$1 (buffer) {
  let _entries = [];
  let cursor = 0;
  while (cursor < buffer.length) {
    let space = buffer.indexOf(32, cursor);
    if (space === -1) {
      throw new Error(
        `GitTree: Error parsing buffer at byte location ${cursor}: Could not find the next space character.`
      )
    }
    let nullchar = buffer.indexOf(0, cursor);
    if (nullchar === -1) {
      throw new Error(
        `GitTree: Error parsing buffer at byte location ${cursor}: Could not find the next null character.`
      )
    }
    let mode = buffer.slice(cursor, space).toString('utf8');
    if (mode === '40000') mode = '040000'; // makes it line up neater in printed output
    let type = mode === '040000' ? 'tree' : 'blob';
    let path$$1 = buffer.slice(space + 1, nullchar).toString('utf8');
    let oid = buffer.slice(nullchar + 1, nullchar + 21).toString('hex');
    cursor = nullchar + 21;
    _entries.push({ mode, path: path$$1, oid, type });
  }
  return _entries
}

function limitModeToAllowed (mode) {
  if (typeof mode === 'number') {
    mode = mode.toString(8);
  }
  // tree
  if (mode.match(/^0?4.*/)) return '40000' // Directory
  if (mode.match(/^1006.*/)) return '100644' // Regular non-executable file
  if (mode.match(/^1007.*/)) return '100755' // Regular executable file
  if (mode.match(/^120.*/)) return '120000' // Symbolic link
  if (mode.match(/^160.*/)) return '160000' // Commit (git submodule reference)
  throw new Error(`Could not understand file mode: ${mode}`)
}

function nudgeIntoShape (entry) {
  if (!entry.oid && entry.sha) {
    entry.oid = entry.sha; // Github
  }
  entry.mode = limitModeToAllowed(entry.mode); // index
  if (!entry.type) {
    entry.type = 'blob'; // index
  }
  return entry
}

class GitTree {
  /*::
  _entries: Array<TreeEntry>
  */
  constructor (entries) {
    if (Buffer.isBuffer(entries)) {
      this._entries = parseBuffer$1(entries);
    } else if (Array.isArray(entries)) {
      this._entries = entries.map(nudgeIntoShape);
    } else {
      throw new Error('invalid type passed to GitTree constructor')
    }
  }
  static from (tree) {
    return new GitTree(tree)
  }
  render () {
    return this._entries
      .map(entry => `${entry.mode} ${entry.type} ${entry.oid}    ${entry.path}`)
      .join('\n')
  }
  toObject () {
    return Buffer.concat(
      this._entries.map(entry => {
        let mode = Buffer.from(entry.mode.replace(/^0/, ''));
        let space = Buffer.from(' ');
        let path$$1 = Buffer.from(entry.path, { encoding: 'utf8' });
        let nullchar = Buffer.from([0]);
        let oid = Buffer.from(entry.oid.match(/../g).map(n => parseInt(n, 16)));
        return Buffer.concat([mode, space, path$$1, nullchar, oid])
      })
    )
  }
  entries () {
    return this._entries
  }
  * [Symbol.iterator] () {
    for (let entry of this._entries) {
      yield entry;
    }
  }
}

function normalize$1 (str) {
  // remove all <CR>
  str = str.replace(/\r/g, '');
  // no extra newlines up front
  str = str.replace(/^\n+/, '');
  // and a single newline at the end
  str = str.replace(/\n+$/, '') + '\n';
  return str
}

function indent$1 (str) {
  return (
    str
      .trim()
      .split('\n')
      .map(x => ' ' + x)
      .join('\n') + '\n'
  )
}

class SignedGitCommit extends GitCommit {
  static from (commit) {
    return new SignedGitCommit(commit)
  }
  async sign (openpgp, privateKeys) {
    let commit = this.withoutSignature();
    let headers = GitCommit.justHeaders(this._commit);
    let message = GitCommit.justMessage(this._commit);
    let privKeyObj = openpgp.key.readArmored(privateKeys).keys;
    let { signature } = await openpgp.sign({
      data: openpgp.util.str2Uint8Array(commit),
      privateKeys: privKeyObj,
      detached: true,
      armor: true
    });
    // renormalize the line endings to the one true line-ending
    signature = normalize$1(signature);
    let signedCommit =
      headers + '\n' + 'gpgsig' + indent$1(signature) + '\n' + message;
    // return a new commit object
    return GitCommit.from(signedCommit)
  }

  async listSigningKeys (openpgp) {
    let msg = openpgp.message.readSignedContent(
      this.withoutSignature(),
      this.isolateSignature()
    );
    return msg.getSigningKeyIds().map(keyid => keyid.toHex())
  }

  async verify (openpgp, publicKeys) {
    let pubKeyObj = openpgp.key.readArmored(publicKeys).keys;
    let msg = openpgp.message.readSignedContent(
      this.withoutSignature(),
      this.isolateSignature()
    );
    let results = msg.verify(pubKeyObj);
    let validity = results.reduce((a, b) => a.valid && b.valid, { valid: true });
    return validity
  }
}

class GitConfigManager {
  static async get ({ fs: _fs, gitdir }) {
    const fs = new FileSystem(_fs);
    // We can improve efficiency later if needed.
    // TODO: read from full list of git config files
    let text = await fs.read(`${gitdir}/config`, { encoding: 'utf8' });
    return GitConfig.from(text)
  }
  static async save ({ fs: _fs, gitdir, config }) {
    const fs = new FileSystem(_fs);
    // We can improve efficiency later if needed.
    // TODO: handle saving to the correct global/user/repo location
    await fs.write(`${gitdir}/config`, config.toString(), {
      encoding: 'utf8'
    });
  }
}

// I'm putting this in a Manager because I reckon it could benefit
// from a LOT of cacheing.

// TODO: Implement .git/info/exclude

class GitIgnoreManager {
  static async isIgnored ({
    fs: _fs,
    dir,
    gitdir = path.join(dir, '.git'),
    filepath
  }) {
    const fs = new FileSystem(_fs);
    let pairs = [
      {
        gitignore: path.join(dir, '.gitignore'),
        filepath
      }
    ];
    let pieces = filepath.split('/');
    for (let i = 1; i < pieces.length; i++) {
      let folder = pieces.slice(0, i).join('/');
      let file = pieces.slice(i).join('/');
      pairs.push({
        gitignore: path.join(dir, folder, '.gitignore'),
        filepath: file
      });
    }
    let ignoredStatus = false;
    for (let p of pairs) {
      let file;
      try {
        file = await fs.read(p.gitignore, 'utf8');
      } catch (err) {
        if (err.code === 'NOENT') continue
      }
      let ign = ignore().add(file);
      let unign = ignore().add(`**\n${file}`);
      // If the parent directory is excluded, we are done.
      // "It is not possible to re-include a file if a parent directory of that file is excluded. Git doesn’t list excluded directories for performance reasons, so any patterns on contained files have no effect, no matter where they are defined."
      // source: https://git-scm.com/docs/gitignore
      let parentdir = path.dirname(p.filepath);
      if (ign.ignores(parentdir)) return true
      // If the file is currently ignored, test for UNignoring.
      if (ignoredStatus) {
        ignoredStatus = unign.ignores(p.filepath);
      } else {
        ignoredStatus = ign.ignores(p.filepath);
      }
    }
    return ignoredStatus
  }
}

// import LockManager from 'travix-lock-manager'

// import Lock from '../utils'

// TODO: replace with an LRU cache?
const map = new Map();
// const lm = new LockManager()
const lock = new AsyncLock();

class GitIndexManager {
  static async acquire ({ fs: _fs, filepath }, closure) {
    const fs = new FileSystem(_fs);
    await lock.acquire(filepath, async function () {
      let index = map.get(filepath);
      if (index === undefined) {
        // Acquire a file lock while we're reading the index
        // to make sure other processes aren't writing to it
        // simultaneously, which could result in a corrupted index.
        // const fileLock = await Lock(filepath)
        const rawIndexFile = await fs.read(filepath);
        index = GitIndex.from(rawIndexFile);
        // cache the GitIndex object so we don't need to re-read it
        // every time.
        // TODO: save the stat data for the index so we know whether
        // the cached file is stale (modified by an outside process).
        map.set(filepath, index);
        // await fileLock.cancel()
      }
      await closure(index);
      if (index._dirty) {
        // Acquire a file lock while we're writing the index file
        // let fileLock = await Lock(filepath)
        const buffer = index.toObject();
        await fs.write(filepath, buffer);
        index._dirty = false;
      }
      // For now, discard our cached object so that external index
      // manipulation is picked up. TODO: use lstat and compare
      // file times to determine if our cached object should be
      // discarded.
      map.delete(filepath);
    });
  }
}

const PackfileCache = new Map();

class GitObjectManager {
  static async read ({ fs: _fs, gitdir, oid, format = 'content' }) {
    const fs = new FileSystem(_fs);
    // Look for it in the loose object directory.
    let file = await fs.read(
      `${gitdir}/objects/${oid.slice(0, 2)}/${oid.slice(2)}`
    );
    let source = `./objects/${oid.slice(0, 2)}/${oid.slice(2)}`;
    // Check to see if it's in a packfile.
    if (!file) {
      // Curry the current read method so that the packfile un-deltification
      // process can acquire external ref-deltas.
      const getExternalRefDelta = oid =>
        GitObjectManager.read({ fs: _fs, gitdir, oid });
      // Iterate through all the .pack files
      let list = await fs.readdir(path.join(gitdir, '/objects/pack'));
      list = list.filter(x => x.endsWith('.pack'));
      for (let filename of list) {
        // Try to get the packfile from the in-memory cache
        let p = PackfileCache.get(filename);
        if (!p) {
          // If not there, load it from a .idx file
          const idxName = filename.replace(/pack$/, 'idx');
          if (await fs.exists(`${gitdir}/objects/pack/${idxName}`)) {
            const idx = await fs.read(`${gitdir}/objects/pack/${idxName}`);
            p = await GitPackIndex.fromIdx({ idx, getExternalRefDelta });
          } else {
            // If the .idx file isn't available, generate one.
            const pack = await fs.read(`${gitdir}/objects/pack/${filename}`);
            p = await GitPackIndex.fromPack({ pack, getExternalRefDelta });
            // Save .idx file
            await fs.write(`${gitdir}/objects/pack/${idxName}`, p.toBuffer());
          }
          PackfileCache.set(filename, p);
        }
        // console.log(p)
        // If the packfile DOES have the oid we're looking for...
        if (p.hashes.includes(oid)) {
          // Make sure the packfile is loaded in memory
          if (!p.pack) {
            const pack = await fs.read(`${gitdir}/objects/pack/${filename}`);
            await p.load({ pack });
          }
          // Get the resolved git object from the packfile
          let result = await p.read({ oid, getExternalRefDelta });
          result.source = `./objects/pack/${filename}`;
          return result
        }
      }
    }
    // Check to see if it's in shallow commits.
    if (!file) {
      let text = await fs.read(`${gitdir}/shallow`, { encoding: 'utf8' });
      if (text !== null && text.includes(oid)) {
        throw new Error(
          `Failed to read git object with oid ${oid} because it is a shallow commit`
        )
      }
    }
    // Finally
    if (!file) {
      throw new Error(`Failed to read git object with oid ${oid}`)
    }
    if (format === 'deflated') {
      return { format: 'deflated', object: file, source }
    }
    let buffer = Buffer.from(pako.inflate(file));
    if (format === 'wrapped') {
      return { format: 'wrapped', object: buffer, source }
    }
    let { type, object } = GitObject.unwrap({ oid, buffer });
    if (format === 'content') return { type, format: 'content', object, source }
  }

  static async hash ({ gitdir, type, object }) {
    let buffer = Buffer.concat([
      Buffer.from(type + ' '),
      Buffer.from(object.byteLength.toString()),
      Buffer.from([0]),
      Buffer.from(object)
    ]);
    let oid = shasum(buffer);
    return oid
  }

  static async write ({ fs: _fs, gitdir, type, object }) {
    const fs = new FileSystem(_fs);
    let { buffer, oid } = GitObject.wrap({ type, object });
    let file = Buffer.from(pako.deflate(buffer));
    let filepath = `${gitdir}/objects/${oid.slice(0, 2)}/${oid.slice(2)}`;
    // Don't overwrite existing git objects - this helps avoid EPERM errors.
    // Although I don't know how we'd fix corrupted objects then. Perhaps delete them
    // on read?
    if (!await fs.exists(filepath)) await fs.write(filepath, file);
    return oid
  }
}

// This is a convenience wrapper for reading and writing files in the 'refs' directory.

// @see https://git-scm.com/docs/git-rev-parse.html#_specifying_revisions
const refpaths = ref => [
  `${ref}`,
  `refs/${ref}`,
  `refs/tags/${ref}`,
  `refs/heads/${ref}`,
  `refs/remotes/${ref}`,
  `refs/remotes/${ref}/HEAD`
];

class GitRefManager {
  static async updateRemoteRefs ({
    fs: _fs,
    gitdir,
    remote,
    refs,
    symrefs,
    tags,
    refspecs
  }) {
    const fs = new FileSystem(_fs);
    // Validate input
    for (let value of refs.values()) {
      if (!value.match(/[0-9a-f]{40}/)) {
        throw new Error(`Unexpected ref contents: '${value}'`)
      }
    }
    const config = await GitConfigManager.get({ fs, gitdir });
    if (!refspecs) {
      refspecs = await config.getall(`remote.${remote}.fetch`);
      if (refspecs.length === 0) {
        throw new Error(
          `Could not find a fetch refspec fot remote '${remote}'.
Make sure the config file has an entry like the following:
[remote "${remote}"]
fetch = +refs/heads/*:refs/remotes/origin/*`
        )
      }
    }
    const refspec = GitRefSpecSet.from(refspecs);
    let actualRefsToWrite = new Map();
    // Add all tags if the fetch tags argument is true.
    if (tags) {
      for (const serverRef of refs.keys()) {
        if (serverRef.startsWith('refs/tags') && !serverRef.endsWith('^{}')) {
          const filename = path.join(gitdir, serverRef);
          // Git's behavior is to only fetch tags that do not conflict with tags already present.
          if (!await fs.exists(filename)) {
            // If there is a dereferenced an annotated tag value available, prefer that.
            const oid = refs.get(serverRef + '^{}') || refs.get(serverRef);
            actualRefsToWrite.set(serverRef, oid);
          }
        }
      }
    }
    // Combine refs and symrefs giving symrefs priority
    let refTranslations = refspec.translate([...refs.keys()]);
    for (let [serverRef, translatedRef] of refTranslations) {
      let value = refs.get(serverRef);
      actualRefsToWrite.set(translatedRef, value);
    }
    let symrefTranslations = refspec.translate([...symrefs.keys()]);
    for (let [serverRef, translatedRef] of symrefTranslations) {
      let value = symrefs.get(serverRef);
      let symtarget = refspec.translateOne(value);
      if (symtarget) {
        actualRefsToWrite.set(translatedRef, `ref: ${symtarget}`);
      }
    }
    // Update files
    // TODO: For large repos with a history of thousands of pull requests
    // (i.e. gitlab-ce) it would be vastly more efficient to write them
    // to .git/packed-refs.
    // The trick is to make sure we a) don't write a packed ref that is
    // already shadowed by a loose ref and b) don't loose any refs already
    // in packed-refs. Doing this efficiently may be difficult. A
    // solution that might work is
    // a) load the current packed-refs file
    // b) add actualRefsToWrite, overriding the existing values if present
    // c) enumerate all the loose refs currently in .git/refs/remotes/${remote}
    // d) overwrite their value with the new value.
    // Examples of refs we need to avoid writing in loose format for efficieny's sake
    // are .git/refs/remotes/origin/refs/remotes/remote_mirror_3059
    // and .git/refs/remotes/origin/refs/merge-requests
    const normalizeValue = value => value.trim() + '\n';
    for (let [key, value] of actualRefsToWrite) {
      await fs.write(path.join(gitdir, key), normalizeValue(value), 'utf8');
    }
  }
  // TODO: make this less crude?
  static async writeRef ({ fs: _fs, gitdir, ref, value }) {
    const fs = new FileSystem(_fs);
    // Validate input
    if (!value.match(/[0-9a-f]{40}/)) {
      throw new Error(`Unexpected ref contents: '${value}'`)
    }
    const normalizeValue = value => value.trim() + '\n';
    await fs.write(path.join(gitdir, ref), normalizeValue(value), 'utf8');
  }
  static async resolve ({ fs: _fs, gitdir, ref, depth }) {
    const fs = new FileSystem(_fs);
    if (depth !== undefined) {
      depth--;
      if (depth === -1) {
        return ref
      }
    }
    let sha;
    // Is it a ref pointer?
    if (ref.startsWith('ref: ')) {
      ref = ref.slice('ref: '.length);
      return GitRefManager.resolve({ fs, gitdir, ref, depth })
    }
    // Is it a complete and valid SHA?
    if (ref.length === 40 && /[0-9a-f]{40}/.test(ref)) {
      return ref
    }
    // We need to alternate between the file system and the packed-refs
    let packedMap = await GitRefManager.packedRefs({ fs, gitdir });
    // Look in all the proper paths, in this order
    const allpaths = refpaths(ref);
    for (let ref of allpaths) {
      sha =
        (await fs.read(`${gitdir}/${ref}`, { encoding: 'utf8' })) ||
        packedMap.get(ref);
      if (sha) {
        return GitRefManager.resolve({ fs, gitdir, ref: sha.trim(), depth })
      }
    }
    // Do we give up?
    throw new Error(`Could not resolve reference ${ref}`)
  }
  static async expand ({ fs: _fs, gitdir, ref }) {
    const fs = new FileSystem(_fs);
    // Is it a complete and valid SHA?
    if (ref.length === 40 && /[0-9a-f]{40}/.test(ref)) {
      return ref
    }
    // We need to alternate between the file system and the packed-refs
    let packedMap = await GitRefManager.packedRefs({ fs, gitdir });
    // Look in all the proper paths, in this order
    const allpaths = refpaths(ref);
    for (let ref of allpaths) {
      if (await fs.exists(`${gitdir}/${ref}`)) return ref
      if (packedMap.has(ref)) return ref
    }
    // Do we give up?
    throw new Error(`Could not expand ref ${ref}`)
  }
  static resolveAgainstMap ({ ref, depth, map }) {
    if (depth !== undefined) {
      depth--;
      if (depth === -1) {
        return ref
      }
    }
    // Is it a ref pointer?
    if (ref.startsWith('ref: ')) {
      ref = ref.slice('ref: '.length);
      return GitRefManager.resolveAgainstMap({ ref, depth, map })
    }
    // Is it a complete and valid SHA?
    if (ref.length === 40 && /[0-9a-f]{40}/.test(ref)) {
      return ref
    }
    // Look in all the proper paths, in this order
    const allpaths = refpaths(ref);
    for (let ref of allpaths) {
      let sha = map.get(ref);
      if (sha) {
        return GitRefManager.resolveAgainstMap({ ref: sha.trim(), depth, map })
      }
    }
    // Do we give up?
    throw new Error(`Could not resolve reference ${ref}`)
  }
  static async packedRefs ({ fs: _fs, gitdir }) {
    const refs = new Map();
    const fs = new FileSystem(_fs);
    const text = await fs.read(`${gitdir}/packed-refs`, { encoding: 'utf8' });
    if (!text) return refs
    const lines = text
      .trim()
      .split('\n')
      .filter(line => !/^\s*#/.test(line));
    let key = null;
    for (let line of lines) {
      const i = line.indexOf(' ');
      if (line.startsWith('^')) {
        // This is a oid for the commit associated with the annotated tag immediately preceding this line.
        // Trim off the '^'
        const value = line.slice(1, i);
        // The tagname^{} syntax is based on the output of `git show-ref --tags -d`
        refs.set(key + '^{}', value);
      } else {
        // This is an oid followed by the ref name
        const value = line.slice(0, i);
        key = line.slice(i + 1);
        refs.set(key, value);
      }
    }
    return refs
  }
  // List all the refs that match the `filepath` prefix
  static async listRefs ({ fs: _fs, gitdir, filepath }) {
    const fs = new FileSystem(_fs);
    let packedMap = GitRefManager.packedRefs({ fs, gitdir });
    let files = null;
    try {
      files = await fs.readdirDeep(`${gitdir}/${filepath}`);
      files = files.map(x => x.replace(`${gitdir}/${filepath}/`, ''));
    } catch (err) {
      files = [];
    }

    for (let key of (await packedMap).keys()) {
      // filter by prefix
      if (key.startsWith(filepath)) {
        // remove prefix
        key = key.replace(filepath + '/', '');
        // Don't include duplicates; the loose files have precedence anyway
        if (!files.includes(key)) {
          files.push(key);
        }
      }
    }
    return files
  }
  static async listBranches ({ fs: _fs, gitdir, remote }) {
    const fs = new FileSystem(_fs);
    if (remote) {
      return GitRefManager.listRefs({
        fs,
        gitdir,
        filepath: `refs/remotes/${remote}`
      })
    } else {
      return GitRefManager.listRefs({ fs, gitdir, filepath: `refs/heads` })
    }
  }
  static async listTags ({ fs: _fs, gitdir }) {
    const fs = new FileSystem(_fs);
    let tags = await GitRefManager.listRefs({
      fs,
      gitdir,
      filepath: `refs/tags`
    });
    tags = tags.filter(x => !x.endsWith('^{}'));
    return tags
  }
}

class GitRemoteConnection {
  static async discover (service, res) {
    const capabilities = new Set();
    const refs = new Map();
    const symrefs = new Map();

    let data = await pify(concat)(res);
    // There is probably a better way to do this, but for now
    // let's just throw the result parser inline here.
    let read = GitPktLine.reader(data);
    let lineOne = await read();
    // skip past any flushes
    while (lineOne === null) lineOne = await read();
    if (lineOne === true) throw new Error('Bad response from git server.')
    if (lineOne.toString('utf8') !== `# service=${service}\n`) {
      throw new Error(
        `Expected '# service=${service}\\n' but got '${lineOne.toString(
          'utf8'
        )}'`
      )
    }
    let lineTwo = await read();
    // skip past any flushes
    while (lineTwo === null) lineTwo = await read();
    // In the edge case of a brand new repo, zero refs (and zero capabilities)
    // are returned.
    if (lineTwo === true) return { capabilities, refs, symrefs }
    let [firstRef, capabilitiesLine] = lineTwo
      .toString('utf8')
      .trim()
      .split('\0');
    capabilitiesLine.split(' ').map(x => capabilities.add(x));
    let [ref, name] = firstRef.split(' ');
    refs.set(name, ref);
    while (true) {
      let line = await read();
      if (line === true) break
      if (line !== null) {
        let [ref, name] = line
          .toString('utf8')
          .trim()
          .split(' ');
        refs.set(name, ref);
      }
    }
    // Symrefs are thrown into the "capabilities" unfortunately.
    for (let cap of capabilities) {
      if (cap.startsWith('symref=')) {
        let m = cap.match(/symref=([^:]+):(.*)/);
        if (m.length === 3) {
          symrefs.set(m[1], m[2]);
        }
      }
    }
    return { capabilities, refs, symrefs }
  }
  static async stream ({ res }) {
    // Parse the response!
    let read = GitPktLine.streamReader(res);
    // And now for the ridiculous side-band-64k protocol
    let packetlines = new PassThrough();
    let packfile = new PassThrough();
    let progress = new PassThrough();
    // TODO: Use a proper through stream?
    const nextBit = async function () {
      let line = await read();
      // Skip over flush packets
      if (line === null) return nextBit()
      // A made up convention to signal there's no more to read.
      if (line === true) {
        packetlines.end();
        progress.end();
        packfile.end();
        return
      }
      // Examine first byte to determine which output "stream" to use
      switch (line[0]) {
        case 1: // pack data
          packfile.write(line.slice(1));
          break
        case 2: // progress message
          progress.write(line.slice(1));
          break
        case 3: // fatal error message just before stream aborts
          let error = line.slice(1);
          progress.write(error);
          packfile.destroy(new Error(error.toString('utf8')));
          return
        default:
          // Not part of the side-band-64k protocol
          packetlines.write(line.slice(0));
      }
      // Careful not to blow up the stack.
      // I think Promises in a tail-call position should be OK.
      nextBit();
    };
    nextBit();
    return {
      packetlines,
      packfile,
      progress
    }
  }
}

function basicAuth (auth$$1) {
  return `Basic ${Buffer.from(auth$$1.username + ':' + auth$$1.password).toString(
    'base64'
  )}`
}

class GitRemoteHTTP {
  static async capabilities () {
    return ['discover', 'connect']
  }
  static async discover ({ service, url, auth: auth$$1 }) {
    // Auto-append the (necessary) .git if it's missing.
    if (!url.endsWith('.git')) url = url += '.git';
    let headers = {};
    // headers['Accept'] = `application/x-${service}-advertisement`
    if (auth$$1) {
      headers['Authorization'] = basicAuth(auth$$1);
    }
    let res = await pify(simpleGet)({
      method: 'GET',
      url: `${url}/info/refs?service=${service}`,
      headers
    });
    if (res.statusCode !== 200) {
      throw new Error(`HTTP Error: ${res.statusCode} ${res.statusMessage}`)
    }
    return GitRemoteConnection.discover(service, res)
  }
  static async connect ({ service, url, auth: auth$$1, stream }) {
    // Auto-append the (necessary) .git if it's missing.
    if (!url.endsWith('.git')) url = url += '.git';
    let headers = {};
    headers['content-type'] = `application/x-${service}-request`;
    headers['accept'] = `application/x-${service}-result`;
    headers['user-agent'] = `git/${pkg.name}@${pkg.version}`;
    if (auth$$1) {
      headers['authorization'] = basicAuth(auth$$1);
    }
    let res = await pify(simpleGet)({
      method: 'POST',
      url: `${url}/${service}`,
      body: stream,
      headers
    });
    if (res.statusCode !== 200) {
      throw new Error(`HTTP Error: ${res.statusCode} ${res.statusMessage}`)
    }
    return GitRemoteConnection.stream({ res })
  }
}

// For now, to remain API compatible, we'll pre-register the GitRemoteHTTP helper

const remoteHelpers = new Map();
remoteHelpers.set('http', GitRemoteHTTP);
remoteHelpers.set('https', GitRemoteHTTP);

function parseRemoteUrl ({ url }) {
  let matches = url.match(/(\w+)(:\/\/|::)(.*)/);
  if (matches === null) return
  /*
   * When git encounters a URL of the form <transport>://<address>, where <transport> is
   * a protocol that it cannot handle natively, it automatically invokes git remote-<transport>
   * with the full URL as the second argument.
   *
   * @see https://git-scm.com/docs/git-remote-helpers
   */
  if (matches[2] === '://') {
    return {
      transport: matches[1],
      address: matches[0]
    }
  }
  /*
   * A URL of the form <transport>::<address> explicitly instructs git to invoke
   * git remote-<transport> with <address> as the second argument.
   *
   * @see https://git-scm.com/docs/git-remote-helpers
   */
  if (matches[2] === '::') {
    return {
      transport: matches[1],
      address: matches[3]
    }
  }
}

class GitRemoteManager {
  static getRemoteHelperFor ({ url }) {
    let parts = parseRemoteUrl({ url });
    if (!parts) {
      throw new Error(`Cannot determine protocol of remote URL: "${url}"`)
    }
    if (remoteHelpers.has(parts.transport)) {
      return remoteHelpers.get(parts.transport)
    }
    throw new Error(
      `Git remote "${url}" uses an unrecognized transport protocol: "${
        parts.transport
      }"`
    )
  }
}

const lock$1 = new AsyncLock();

class GitShallowManager {
  static async read ({ fs: _fs, gitdir }) {
    const fs = new FileSystem(_fs);
    const filepath = path.join(gitdir, 'shallow');
    let oids = new Set();
    await lock$1.acquire(filepath, async function () {
      let text = await fs.read(filepath, { encoding: 'utf8' });
      if (text === null) return
      text
        .trim()
        .split('\n')
        .map(oid => oids.add(oid));
    });
    return oids
  }
  static async write ({ fs: _fs, gitdir, oids }) {
    const fs = new FileSystem(_fs);
    const filepath = path.join(gitdir, 'shallow');
    let text = [...oids].join('\n') + '\n';
    await lock$1.acquire(filepath, async function () {
      await fs.write(filepath, text, {
        encoding: 'utf8'
      });
    });
  }
}

/**
 * Add a file to the git index (aka staging area)
 *
 * @link https://isomorphic-git.github.io/docs/add.html
 */
async function add ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs,
  filepath
}) {
  const fs = new FileSystem(_fs);
  const type = 'blob';
  const object = await fs.read(path.join(dir, filepath));
  if (object === null) throw new Error(`Could not read file '${filepath}'`)
  const oid = await GitObjectManager.write({ fs, gitdir, type, object });
  await GitIndexManager.acquire(
    { fs, filepath: `${gitdir}/index` },
    async function (index) {
      let stats = await fs._lstat(path.join(dir, filepath));
      index.insert({ filepath, stats, oid });
    }
  );
  // TODO: return oid?
}

/**
 * Create a branch
 *
 * @link https://isomorphic-git.github.io/docs/branch.html
 */
async function branch ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs,
  ref
}) {
  const fs = new FileSystem(_fs);
  if (ref === undefined) {
    throw new Error('Cannot create branch "undefined"')
  }

  if (ref !== clean(ref)) {
    throw new Error(`Failed to create branch '${ref}' because that name would not be a valid git reference. A valid alternative would be '${clean(ref)}'.`)
  }

  const exist = await fs.exists(`${gitdir}/refs/heads/${ref}`);
  if (exist) {
    throw new Error(`Failed to create branch '${ref}' because branch '${ref}' already exists.`)
  }
  // Get tree oid
  let oid;
  try {
    oid = await GitRefManager.resolve({ fs, gitdir, ref: 'HEAD' });
  } catch (e) {
    throw new Error(`Failed to create branch '${ref}' because there are no commits in this project.`)
  }
  // Create a new branch that points at that same commit
  await fs.write(`${gitdir}/refs/heads/${ref}`, oid + '\n');
}

/**
 * Read and/or write to the git config files.
 *
 * @link https://isomorphic-git.github.io/docs/config.html
 */
async function config (args) {
  // These arguments are not in the function signature but destructured separately
  // as a result of a bit of a design flaw that requires the un-destructured argument object
  // in order to call args.hasOwnProperty('value') later on.
  let {
    dir,
    gitdir = path.join(dir, '.git'),
    fs: _fs,
    all = false,
    append = false,
    path: path$$1,
    value
  } = args;
  const fs = new FileSystem(_fs);
  const config = await GitConfigManager.get({ fs, gitdir });
  // This carefully distinguishes between
  // 1) there is no 'value' argument (do a "get")
  // 2) there is a 'value' argument with a value of undefined (do a "set")
  // Because setting a key to undefined is how we delete entries from the ini.
  if (value === undefined && !args.hasOwnProperty('value')) {
    if (all) {
      return config.getall(path$$1)
    } else {
      return config.get(path$$1)
    }
  } else {
    if (append) {
      await config.append(path$$1, value);
    } else {
      await config.set(path$$1, value);
    }
    await GitConfigManager.save({ fs, gitdir, config });
  }
}

/**
 * Checkout a branch
 *
 * @link https://isomorphic-git.github.io/docs/checkout.html
 */
async function checkout ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs,
  remote = 'origin',
  ref
}) {
  const fs = new FileSystem(_fs);
  if (ref === undefined) {
    throw new Error('Cannot checkout ref "undefined"')
  }
  // Get tree oid
  let oid;
  try {
    oid = await GitRefManager.resolve({ fs, gitdir, ref });
    // TODO: Figure out what to do if both 'ref' and 'remote' are specified, ref already exists,
    // and is configured to track a different remote.
  } catch (err) {
    // If `ref` doesn't exist, create a new remote tracking branch
    // Figure out the commit to checkout
    let remoteRef = `${remote}/${ref}`;
    oid = await GitRefManager.resolve({
      fs,
      gitdir,
      ref: remoteRef
    });
    // Set up remote tracking branch
    await config({
      gitdir,
      fs,
      path: `branch.${ref}.remote`,
      value: `${remote}`
    });
    await config({
      gitdir,
      fs,
      path: `branch.${ref}.merge`,
      value: `refs/heads/${ref}`
    });
    // Create a new branch that points at that same commit
    await fs.write(`${gitdir}/refs/heads/${ref}`, oid + '\n');
  }
  let commit = {};
  try {
    commit = await GitObjectManager.read({ fs, gitdir, oid });
  } catch (err) {
    throw new Error(
      `Failed to checkout ref '${ref}' because commit ${oid} is not available locally. Do a git fetch to make the branch available locally.`
    )
  }
  if (commit.type !== 'commit') {
    throw new Error(`Unexpected type: ${commit.type}`)
  }
  let comm = GitCommit.from(commit.object.toString('utf8'));
  let sha = comm.headers().tree;
  // Get top-level tree
  let { type, object } = await GitObjectManager.read({ fs, gitdir, oid: sha });
  if (type !== 'tree') throw new Error(`Unexpected type: ${type}`)
  let tree = GitTree.from(object);
  // Acquire a lock on the index
  await GitIndexManager.acquire(
    { fs, filepath: `${gitdir}/index` },
    async function (index) {
      // TODO: Big optimization possible here.
      // Instead of deleting and rewriting everything, only delete files
      // that are not present in the new branch, and only write files that
      // are not in the index or are in the index but have the wrong SHA.
      for (let entry of index) {
        try {
          await fs.rm(path.join(dir, entry.path));
        } catch (err) {}
      }
      index.clear();
      // Write files. TODO: Write them atomically
      await writeTreeToDisk({ fs, gitdir, dir, index, prefix: '', tree });
      // Update HEAD TODO: Handle non-branch cases
      await fs.write(`${gitdir}/HEAD`, `ref: refs/heads/${ref}`);
    }
  );
}

async function writeTreeToDisk ({ fs: _fs, dir, gitdir, index, prefix, tree }) {
  const fs = new FileSystem(_fs);
  for (let entry of tree) {
    let { type, object } = await GitObjectManager.read({
      fs,
      gitdir,
      oid: entry.oid
    });
    let entrypath = prefix === '' ? entry.path : `${prefix}/${entry.path}`;
    let filepath = path.join(dir, prefix, entry.path);
    switch (type) {
      case 'blob':
        await fs.write(filepath, object);
        let stats = await fs._lstat(filepath);
        index.insert({
          filepath: entrypath,
          stats,
          oid: entry.oid
        });
        break
      case 'tree':
        let tree = GitTree.from(object);
        await writeTreeToDisk({
          fs,
          dir,
          gitdir,
          index,
          prefix: entrypath,
          tree
        });
        break
      default:
        throw new Error(
          `Unexpected object type ${type} found in tree for '${entrypath}'`
        )
    }
  }
}

/**
 * Fetch commits from a remote repository
 *
 * @link https://isomorphic-git.github.io/docs/fetch.html
 */
async function fetch ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs,
  emitter,
  ref = 'HEAD',
  refs,
  remote,
  url,
  authUsername,
  authPassword,
  depth,
  since,
  exclude,
  relative,
  tags,
  singleBranch,
  onprogress // deprecated
}) {
  if (onprogress !== undefined) {
    console.warn(
      'The `onprogress` callback has been deprecated. Please use the more generic `emitter` EventEmitter argument instead.'
    );
  }
  const fs = new FileSystem(_fs);
  let response = await fetchPackfile({
    gitdir,
    fs,
    ref,
    refs,
    remote,
    url,
    authUsername,
    authPassword,
    depth,
    since,
    exclude,
    relative,
    tags,
    singleBranch
  });
  // Note: progress messages are designed to be written directly to the terminal,
  // so they are often sent with just a carriage return to overwrite the last line of output.
  // But there are also messages delimited with newlines.
  // I also include CRLF just in case.
  response.progress.pipe(split2(/(\r\n)|\r|\n/)).on('data', line => {
    if (emitter) {
      emitter.emit('message', line.trim());
    }
    let matches = line.match(/\((\d+?)\/(\d+?)\)/);
    if (matches && emitter) {
      emitter.emit('progress', {
        loaded: parseInt(matches[1], 10),
        total: parseInt(matches[2], 10),
        lengthComputable: true
      });
    }
  });
  let packfile = await pify(concat)(response.packfile);
  let packfileSha = packfile.slice(-20).toString('hex');
  await fs.write(
    path.join(gitdir, `objects/pack/pack-${packfileSha}.pack`),
    packfile
  );
  // TODO: Return more metadata?
  return {
    defaultBranch: response.HEAD,
    fetchHead: response.FETCH_HEAD
  }
}

async function fetchPackfile ({
  gitdir,
  fs: _fs,
  ref,
  refs = [ref],
  remote,
  url,
  authUsername,
  authPassword,
  depth = null,
  since = null,
  exclude = [],
  relative = false,
  tags = false,
  singleBranch = false
}) {
  const fs = new FileSystem(_fs);
  if (depth !== null) {
    if (Number.isNaN(parseInt(depth))) {
      throw new Error(`Invalid value for depth argument: ${depth}`)
    }
    depth = parseInt(depth);
  }
  remote = remote || 'origin';
  if (url === undefined) {
    url = await config({
      fs,
      gitdir,
      path: `remote.${remote}.url`
    });
  }
  let auth$$1;
  if (authUsername !== undefined && authPassword !== undefined) {
    auth$$1 = {
      username: authUsername,
      password: authPassword
    };
  }
  let GitRemoteHTTP$$1 = GitRemoteManager.getRemoteHelperFor({ url });
  let remoteHTTP = await GitRemoteHTTP$$1.discover({
    service: 'git-upload-pack',
    url,
    auth: auth$$1
  });
  // Check server supports shallow cloning
  if (depth !== null && !remoteHTTP.capabilities.has('shallow')) {
    throw new Error(`Remote does not support shallow fetches`)
  }
  if (since !== null && !remoteHTTP.capabilities.has('deepen-since')) {
    throw new Error(`Remote does not support shallow fetches by date`)
  }
  if (exclude.length > 0 && !remoteHTTP.capabilities.has('deepen-not')) {
    throw new Error(
      `Remote does not support shallow fetches excluding commits reachable by refs`
    )
  }
  if (relative === true && !remoteHTTP.capabilities.has('deepen-relative')) {
    throw new Error(
      `Remote does not support shallow fetches relative to the current shallow depth`
    )
  }
  // TODO: Don't add other refs if singleBranch is specified.
  await GitRefManager.updateRemoteRefs({
    fs,
    gitdir,
    remote,
    refs: remoteHTTP.refs,
    symrefs: remoteHTTP.symrefs,
    tags
  });
  const capabilities = `multi_ack_detailed no-done side-band-64k thin-pack ofs-delta agent=git/${
    pkg.name
  }@${pkg.version}${relative ? ' deepen-relative' : ''}`;
  let packstream = new PassThrough();
  // Figure out the SHA for the requested ref
  let oid = GitRefManager.resolveAgainstMap({
    ref,
    map: remoteHTTP.refs
  });
  // Start requesting oids from the remote by their SHAs
  let wants = singleBranch ? [oid] : remoteHTTP.refs.values();
  wants = [...new Set(wants)]; // remove duplicates
  let firstLineCapabilities = ` ${capabilities}`;
  for (const want of wants) {
    packstream.write(
      GitPktLine.encode(`want ${want}${firstLineCapabilities}\n`)
    );
    firstLineCapabilities = '';
  }
  let oids = await GitShallowManager.read({ fs, gitdir });
  if (oids.size > 0 && remoteHTTP.capabilities.has('shallow')) {
    for (let oid of oids) {
      packstream.write(GitPktLine.encode(`shallow ${oid}\n`));
    }
  }
  if (depth !== null) {
    packstream.write(GitPktLine.encode(`deepen ${depth}\n`));
  }
  if (since !== null) {
    packstream.write(
      GitPktLine.encode(`deepen-since ${Math.floor(since.valueOf() / 1000)}\n`)
    );
  }
  for (let x of exclude) {
    packstream.write(GitPktLine.encode(`deepen-not ${x}\n`));
  }
  let haves = [];
  for (let ref of refs) {
    try {
      ref = await GitRefManager.expand({ fs, gitdir, ref });
      // TODO: Actually, should we test whether we have the object using readObject?
      if (!ref.startsWith('refs/tags')) {
        let have = await GitRefManager.resolve({ fs, gitdir, ref });
        haves.push(have);
      }
    } catch (err) {}
  }
  for (const have of haves) {
    packstream.write(GitPktLine.encode(`have ${have}\n`));
  }
  packstream.write(GitPktLine.flush());
  packstream.end(GitPktLine.encode(`done\n`));
  let response = await GitRemoteHTTP$$1.connect({
    service: 'git-upload-pack',
    url,
    auth: auth$$1,
    stream: packstream
  });
  // Apply all the 'shallow' and 'unshallow' commands
  response.packetlines.pipe(
    through2(async (data, enc, next) => {
      let line = data.toString('utf8');
      if (line.startsWith('shallow')) {
        let oid = line.slice(-41).trim();
        if (oid.length !== 40) {
          throw new Error(`non-40 character 'shallow' oid: ${oid}`)
        }
        oids.add(oid);
        await GitShallowManager.write({ fs, gitdir, oids });
      } else if (line.startsWith('unshallow')) {
        let oid = line.slice(-41).trim();
        if (oid.length !== 40) {
          throw new Error(`non-40 character 'shallow' oid: ${oid}`)
        }
        oids.delete(oid);
        await GitShallowManager.write({ fs, gitdir, oids });
      }
      next(null, data);
    })
  );
  // We need this value later for the `clone` command.
  response.HEAD = remoteHTTP.symrefs.get('HEAD');
  response.FETCH_HEAD = oid;
  return response
}

/**
 * Initialize a new repository
 *
 * @link https://isomorphic-git.github.io/docs/init.html
 */
async function init ({ dir, gitdir = path.join(dir, '.git'), fs: _fs }) {
  const fs = new FileSystem(_fs);
  let folders = [
    'hooks',
    'info',
    'objects/info',
    'objects/pack',
    'refs/heads',
    'refs/tags'
  ];
  folders = folders.map(dir => gitdir + '/' + dir);
  for (let folder of folders) {
    await fs.mkdir(folder);
  }
  await fs.write(
    gitdir + '/config',
    '[core]\n' +
      '\trepositoryformatversion = 0\n' +
      '\tfilemode = false\n' +
      '\tbare = false\n' +
      '\tlogallrefupdates = true\n' +
      '\tsymlinks = false\n' +
      '\tignorecase = true\n'
  );
  await fs.write(gitdir + '/HEAD', 'ref: refs/heads/master\n');
}

/**
 * Clone a repository
 *
 * @link https://isomorphic-git.github.io/docs/clone.html
 */
async function clone ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs,
  emitter,
  url,
  ref,
  remote,
  authUsername,
  authPassword,
  depth,
  since,
  exclude,
  relative,
  singleBranch,
  onprogress
}) {
  if (onprogress !== undefined) {
    console.warn(
      'The `onprogress` callback has been deprecated. Please use the more generic `emitter` EventEmitter argument instead.'
    );
  }
  const fs = new FileSystem(_fs);
  remote = remote || 'origin';
  await init({ gitdir, fs });
  // Add remote
  await config({
    gitdir,
    fs,
    path: `remote.${remote}.url`,
    value: url
  });
  await config({
    gitdir,
    fs,
    path: `remote.${remote}.fetch`,
    value: `+refs/heads/*:refs/remotes/${remote}/*`
  });
  // Fetch commits
  let { defaultBranch } = await fetch({
    gitdir,
    fs,
    emitter,
    ref,
    remote,
    authUsername,
    authPassword,
    depth,
    since,
    exclude,
    relative,
    singleBranch,
    tags: true
  });
  ref = ref || defaultBranch;
  ref = ref.replace('refs/heads/', '');
  // Checkout that branch
  await checkout({
    dir,
    gitdir,
    fs,
    ref,
    remote
  });
}

/**
 * Create a new commit
 *
 * @link https://isomorphic-git.github.io/docs/commit.html
 */
async function commit ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs,
  message,
  author,
  committer
}) {
  const fs = new FileSystem(_fs);
  // Fill in missing arguments with default values
  if (author === undefined) author = {};
  if (author.name === undefined) {
    author.name = await config({ fs, gitdir, path: 'user.name' });
  }
  if (author.email === undefined) {
    author.email = await config({ fs, gitdir, path: 'user.email' });
  }
  if (author.name === undefined || author.email === undefined) {
    throw new Error(
      'Author name and email must be specified as an argument or in the .git/config file'
    )
  }
  committer = committer || author;
  let authorDateTime = author.date || new Date();
  let committerDateTime = committer.date || authorDateTime;
  let oid;
  await GitIndexManager.acquire(
    { fs, filepath: `${gitdir}/index` },
    async function (index) {
      const inode = flatFileListToDirectoryStructure(index.entries);
      const treeRef = await constructTree({ fs, gitdir, inode });
      let parents;
      try {
        let parent = await GitRefManager.resolve({ fs, gitdir, ref: 'HEAD' });
        parents = [parent];
      } catch (err) {
        // Probably an initial commit
        parents = [];
      }
      let comm = GitCommit.from({
        tree: treeRef,
        parent: parents,
        author: {
          name: author.name,
          email: author.email,
          timestamp:
            author.timestamp || Math.floor(authorDateTime.valueOf() / 1000),
          timezoneOffset: author.timezoneOffset || 0
        },
        committer: {
          name: committer.name,
          email: committer.email,
          timestamp:
            committer.timestamp ||
            Math.floor(committerDateTime.valueOf() / 1000),
          timezoneOffset: committer.timezoneOffset || 0
        },
        message
      });
      oid = await GitObjectManager.write({
        fs,
        gitdir,
        type: 'commit',
        object: comm.toObject()
      });
      // Update branch pointer
      const branch = await GitRefManager.resolve({
        fs,
        gitdir,
        ref: 'HEAD',
        depth: 2
      });
      await fs.write(path.join(gitdir, branch), oid + '\n');
    }
  );
  return oid
}

async function constructTree ({ fs, gitdir, inode }) {
  // use depth first traversal
  let children = inode.children;
  for (let inode of children) {
    if (inode.type === 'tree') {
      inode.metadata.mode = '040000';
      inode.metadata.oid = await constructTree({ fs, gitdir, inode });
    }
  }
  let entries = children.map(inode => ({
    mode: inode.metadata.mode,
    path: inode.basename,
    oid: inode.metadata.oid,
    type: inode.type
  }));
  const tree = GitTree.from(entries);
  let oid = await GitObjectManager.write({
    fs,
    gitdir,
    type: 'tree',
    object: tree.toObject()
  });
  return oid
}

/**
 * Find the root git directory
 *
 * @link https://isomorphic-git.github.io/docs/findRoot.html
 */
async function findRoot ({ fs: _fs, filepath }) {
  const fs = new FileSystem(_fs);
  return _findRoot(fs, filepath)
}

async function _findRoot (fs, filepath) {
  if (await fs.exists(path.join(filepath, '.git'))) {
    return filepath
  } else {
    let parent = path.dirname(filepath);
    if (parent === filepath) throw new Error('Unable to find git root')
    return _findRoot(fs, parent)
  }
}

/**
 * List a remote servers branches, tags, and capabilities.
 *
 * @link https://isomorphic-git.github.io/docs/getRemoteInfo.html
 */
async function getRemoteInfo ({ url, authUsername, authPassword }) {
  let auth;
  if (authUsername !== undefined && authPassword !== undefined) {
    auth = {
      username: authUsername,
      password: authPassword
    };
  }

  const remote = await GitRemoteHTTP.discover({
    service: 'git-upload-pack',
    url,
    auth
  });
  const result = {};
  // Note: remote.capabilities, remote.refs, and remote.symrefs are Set and Map objects,
  // but one of the objectives of the public API is to always return JSON-compatible objects
  // so we must JSONify them.
  result.capabilities = [...remote.capabilities];
  // Convert the flat list into an object tree, because I figure 99% of the time
  // that will be easier to use.
  for (const [ref, oid] of remote.refs) {
    let parts = ref.split('/');
    let last = parts.pop();
    let o = result;
    for (let part of parts) {
      o[part] = o[part] || {};
      o = o[part];
    }
    o[last] = oid;
  }
  // Merge symrefs on top of refs to more closely match actual git repo layouts
  for (const [symref, ref] of remote.symrefs) {
    let parts = symref.split('/');
    let last = parts.pop();
    let o = result;
    for (let part of parts) {
      o[part] = o[part] || {};
      o = o[part];
    }
    o[last] = ref;
  }
  return result
}

/**
 * Create the .idx file for a given .pack file
 *
 * @link https://isomorphic-git.github.io/docs/indexPack.html
 */
async function indexPack ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs,
  filepath
}) {
  const fs = new FileSystem(_fs);
  const pack = await fs.read(path.join(dir, filepath));
  const idx = await GitPackIndex.fromPack({ pack });
  await fs.write(filepath.replace(/\.pack$/, '.idx'), idx.toBuffer());
}

/**
 * List branches
 *
 * @link https://isomorphic-git.github.io/docs/listBranches.html
 */
async function listBranches ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs,
  remote = undefined
}) {
  const fs = new FileSystem(_fs);
  return GitRefManager.listBranches({ fs, gitdir, remote })
}

/**
 * List all the files in the git index
 *
 * @link https://isomorphic-git.github.io/docs/listFiles.html
 */
async function listFiles ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs
}) {
  const fs = new FileSystem(_fs);
  let filenames;
  await GitIndexManager.acquire(
    { fs, filepath: `${gitdir}/index` },
    async function (index) {
      filenames = index.entries.map(x => x.path);
    }
  );
  return filenames
}

/**
 * List tags
 *
 * @link https://isomorphic-git.github.io/docs/listTags.html
 */
async function listTags ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs
}) {
  const fs = new FileSystem(_fs);
  return GitRefManager.listTags({ fs, gitdir })
}

/**
 * Get commit descriptions from the git history
 *
 * @link https://isomorphic-git.github.io/docs/log.html
 */
async function log$1 ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs,
  ref = 'HEAD',
  depth,
  since, // Date
  signing = false
}) {
  const fs = new FileSystem(_fs);
  let sinceTimestamp =
    since === undefined ? undefined : Math.floor(since.valueOf() / 1000);
  // TODO: In the future, we may want to have an API where we return a
  // async iterator that emits commits.
  let commits = [];
  let start = await GitRefManager.resolve({ fs, gitdir, ref });
  let { type, object } = await GitObjectManager.read({ fs, gitdir, oid: start });
  if (type !== 'commit') {
    throw new Error(
      `The given ref ${ref} did not resolve to a commit but to a ${type}`
    )
  }
  let commit = GitCommit.from(object);
  let currentCommit = Object.assign({ oid: start }, commit.parse());
  if (signing) {
    currentCommit.payload = commit.withoutSignature();
  }
  commits.push(currentCommit);
  while (true) {
    if (depth !== undefined && commits.length === depth) break
    if (currentCommit.parent.length === 0) break
    let oid = currentCommit.parent[0];
    let gitobject;
    try {
      gitobject = await GitObjectManager.read({ fs, gitdir, oid });
    } catch (err) {
      commits.push({
        oid,
        error: err
      });
      break
    }
    let { type, object } = gitobject;
    if (type !== 'commit') {
      commits.push({
        oid,
        error: new Error(`Invalid commit parent ${oid} is of type ${type}`)
      });
      break
    }
    commit = GitCommit.from(object);
    currentCommit = Object.assign({ oid }, commit.parse());
    if (signing) {
      currentCommit.payload = commit.withoutSignature();
    }
    if (
      sinceTimestamp !== undefined &&
      currentCommit.author.timestamp <= sinceTimestamp
    ) {
      break
    }
    commits.push(currentCommit);
  }
  return commits
}

// import diff3 from 'node-diff3'

/**
 * Merge one or more branches (Currently, only fast-forward merges are implemented.)
 *
 * @link https://isomorphic-git.github.io/docs/merge.html
 */
async function merge ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs,
  ours,
  theirs,
  fastForwardOnly
}) {
  const fs = new FileSystem(_fs);
  let ourOid = await GitRefManager.resolve({
    fs,
    gitdir,
    ref: ours
  });
  let theirOid = await GitRefManager.resolve({
    fs,
    gitdir,
    ref: theirs
  });
  // find most recent common ancestor of ref a and ref b
  let baseOid = await findMergeBase({ gitdir, fs, refs: [ourOid, theirOid] });
  // handle fast-forward case
  if (baseOid === theirOid) {
    console.log(`'${theirs}' is already merged into '${ours}'`);
    return {
      oid: ourOid,
      alreadyMerged: true
    }
  }
  if (baseOid === ourOid) {
    console.log(`Performing a fast-forward merge...`);
    await GitRefManager.writeRef({ fs, gitdir, ref: ours, value: theirOid });
    return {
      oid: theirOid,
      fastForward: true
    }
  } else {
    // not a simple fast-forward
    if (fastForwardOnly) {
      throw new Error('A simple fast-forward merge was not possible.')
    }
    throw new Error('Non-fast-forward merges are not supported yet.')
  }
}

function compareAge (a, b) {
  return a.committer.timestamp - b.committer.timestamp
}

async function findMergeBase ({ gitdir, fs, refs }) {
  // Where is async flatMap when you need it?
  let commits = [];
  for (const ref of refs) {
    let list = await log$1({ gitdir, fs, ref, depth: 1 });
    commits.push(list[0]);
  }
  // Are they actually the same commit?
  if (commits.every(commit => commit.oid === commits[0].oid)) {
    return commits[0].oid
  }
  // Is the oldest commit an ancestor of the others?
  let sorted = commits.sort(compareAge);
  let candidate = sorted[0];
  let since = candidate.timestamp - 1;
  for (const ref of refs) {
    let list = await log$1({ gitdir, fs, ref, since });
    if (!list.find(commit => commit.oid === candidate.oid)) {
      candidate = null;
      break
    }
  }
  if (candidate) return candidate.oid
  // Is...
  throw new Error('Non-trivial merge not implemented at this time')
}

// import diff3 from 'node-diff3'

/**
 * Fetch and merge commits from a remote repository
 *
 * @link https://isomorphic-git.github.io/docs/pull.html
 */
async function pull ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs,
  ref,
  fastForwardOnly = false,
  emitter,
  authUsername,
  authPassword,
  singleBranch
}) {
  const fs = new FileSystem(_fs);
  // If ref is undefined, use 'HEAD'
  if (!ref) {
    ref = await GitRefManager.resolve({
      fs,
      gitdir,
      ref: 'HEAD',
      depth: 1
    });
  }
  console.log(`Using ref=${ref}`);
  // Fetch from the correct remote.
  let remote = await config({
    gitdir,
    fs,
    path: `branch.${ref}.remote`
  });
  let { fetchHead } = await fetch({
    dir,
    gitdir,
    fs,
    emitter,
    ref,
    remote,
    authUsername,
    authPassword,
    singleBranch
  });
  // Merge the remote tracking branch into the local one.
  await merge({
    gitdir,
    fs,
    ours: ref,
    theirs: fetchHead,
    fastForwardOnly
  });
  await checkout({
    dir,
    gitdir,
    fs,
    ref
  });
}

const types = {
  commit: 0b0010000,
  tree: 0b0100000,
  blob: 0b0110000,
  tag: 0b1000000,
  ofs_delta: 0b1100000,
  ref_delta: 0b1110000
};

/**
 * Push a branch
 *
 * @link https://isomorphic-git.github.io/docs/push.html
 */
async function push ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs,
  emitter,
  ref,
  remote = 'origin',
  url,
  authUsername,
  authPassword
}) {
  const fs = new FileSystem(_fs);
  // TODO: Figure out how pushing tags works. (This only works for branches.)
  if (url === undefined) {
    url = await config({ fs, gitdir, path: `remote.${remote}.url` });
  }
  let fullRef = ref.startsWith('refs/') ? ref : `refs/heads/${ref}`;
  let oid = await GitRefManager.resolve({ fs, gitdir, ref });
  let auth$$1;
  if (authUsername !== undefined && authPassword !== undefined) {
    auth$$1 = {
      username: authUsername,
      password: authPassword
    };
  }
  let GitRemoteHTTP$$1 = GitRemoteManager.getRemoteHelperFor({ url });
  let httpRemote = await GitRemoteHTTP$$1.discover({
    service: 'git-receive-pack',
    url,
    auth: auth$$1
  });
  let commits = await listCommits({
    fs,
    gitdir,
    start: [oid],
    finish: httpRemote.refs.values()
  });
  let objects = await listObjects({ fs, gitdir, oids: commits });
  let packstream = new PassThrough();
  let oldoid =
    httpRemote.refs.get(fullRef) || '0000000000000000000000000000000000000000';
  const capabilities = `report-status side-band-64k agent=git/${pkg.name}@${
    pkg.version
  }`;
  packstream.write(
    GitPktLine.encode(`${oldoid} ${oid} ${fullRef}\0 ${capabilities}\n`)
  );
  packstream.write(GitPktLine.flush());
  pack({
    fs,
    gitdir,
    oids: [...objects],
    outputStream: packstream
  });
  let { packfile, progress } = await GitRemoteHTTP$$1.connect({
    service: 'git-receive-pack',
    url,
    auth: auth$$1,
    stream: packstream
  });
  if (emitter) {
    progress.on('data', chunk => {
      let msg = chunk.toString('utf8');
      emitter.emit('message', msg);
    });
  }
  let result = {};
  // Parse the response!
  let response = '';
  let read = GitPktLine.streamReader(packfile);
  let line = await read();
  while (line !== true) {
    if (line !== null) response += line.toString('utf8') + '\n';
    line = await read();
  }

  let lines = response.toString('utf8').split('\n');
  // We're expecting "unpack {unpack-result}"
  line = lines.shift();
  if (!line.startsWith('unpack ')) {
    throw new Error(
      `Unparsable response from server! Expected 'unpack ok' or 'unpack [error message]' but got '${line}'`
    )
  }
  if (line === 'unpack ok') {
    result.ok = ['unpack'];
  } else {
    result.errors = [line.trim()];
  }
  for (let line of lines) {
    let status = line.slice(0, 2);
    let refAndMessage = line.slice(3);
    if (status === 'ok') {
      result.ok = result.ok || [];
      result.ok.push(refAndMessage);
    } else if (status === 'ng') {
      result.errors = result.errors || [];
      result.errors.push(refAndMessage);
    }
  }
  log(result);
  return result
}

async function listCommits ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs,
  start,
  finish
}) {
  const fs = new FileSystem(_fs);
  let startingSet = new Set();
  let finishingSet = new Set();
  for (let ref of start) {
    startingSet.add(await GitRefManager.resolve({ fs, gitdir, ref }));
  }
  for (let ref of finish) {
    // We may not have these refs locally so we must try/catch
    try {
      let oid = await GitRefManager.resolve({ fs, gitdir, ref });
      finishingSet.add(oid);
    } catch (err) {}
  }
  let visited = new Set();

  // Because git commits are named by their hash, there is no
  // way to construct a cycle. Therefore we won't worry about
  // setting a default recursion limit.
  async function walk (oid) {
    visited.add(oid);
    let { type, object } = await GitObjectManager.read({ fs, gitdir, oid });
    if (type !== 'commit') {
      throw new Error(`Expected type commit but type is ${type}`)
    }
    let commit = GitCommit.from(object);
    let parents = commit.headers().parent;
    for (oid of parents) {
      if (!finishingSet.has(oid) && !visited.has(oid)) {
        await walk(oid);
      }
    }
  }

  // Let's go walking!
  for (let oid of startingSet) {
    await walk(oid);
  }
  return visited
}

async function listObjects ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs,
  oids
}) {
  const fs = new FileSystem(_fs);
  let visited = new Set();

  // We don't do the purest simplest recursion, because we can
  // avoid reading Blob objects entirely since the Tree objects
  // tell us which oids are Blobs and which are Trees.
  async function walk (oid) {
    visited.add(oid);
    let { type, object } = await GitObjectManager.read({ fs, gitdir, oid });
    if (type === 'commit') {
      let commit = GitCommit.from(object);
      let tree = commit.headers().tree;
      await walk(tree);
    } else if (type === 'tree') {
      let tree = GitTree.from(object);
      for (let entry of tree) {
        visited.add(entry.oid);
        // only recurse for trees
        if (entry.type === 'tree') {
          await walk(entry.oid);
        }
      }
    }
  }

  // Let's go walking!
  for (let oid of oids) {
    await walk(oid);
  }
  return visited
}

async function pack ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs,
  oids,
  outputStream
}) {
  const fs = new FileSystem(_fs);
  let hash = createHash('sha1');
  function write (chunk, enc) {
    outputStream.write(chunk, enc);
    hash.update(chunk, enc);
  }
  function writeObject ({ stype, object }) {
    let lastFour, multibyte, length;
    // Object type is encoded in bits 654
    let type = types[stype];
    if (type === undefined) throw new Error('Unrecognized type: ' + stype)
    // The length encoding get complicated.
    length = object.length;
    // Whether the next byte is part of the variable-length encoded number
    // is encoded in bit 7
    multibyte = length > 0b1111 ? 0b10000000 : 0b0;
    // Last four bits of length is encoded in bits 3210
    lastFour = length & 0b1111;
    // Discard those bits
    length = length >>> 4;
    // The first byte is then (1-bit multibyte?), (3-bit type), (4-bit least sig 4-bits of length)
    let byte = (multibyte | type | lastFour).toString(16);
    write(byte, 'hex');
    // Now we keep chopping away at length 7-bits at a time until its zero,
    // writing out the bytes in what amounts to little-endian order.
    while (multibyte) {
      multibyte = length > 0b01111111 ? 0b10000000 : 0b0;
      byte = multibyte | (length & 0b01111111);
      write(pad(2, byte.toString(16), '0'), 'hex');
      length = length >>> 7;
    }
    // Lastly, we can compress and write the object.
    write(Buffer.from(pako.deflate(object)));
  }

  write('PACK');
  write('00000002', 'hex');
  // Write a 4 byte (32-bit) int
  write(pad(8, oids.length.toString(16), '0'), 'hex');
  for (let oid of oids) {
    let { type, object } = await GitObjectManager.read({ fs, gitdir, oid });
    writeObject({ write, object, stype: type });
  }
  // Write SHA1 checksum
  let digest = hash.digest();
  outputStream.end(digest);
  return outputStream
}

/**
 * Read a git object directly by its SHA1 object id
 *
 * @link https://isomorphic-git.github.io/docs/readObject.html
 */
async function readObject ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs,
  oid,
  format = 'parsed'
}) {
  const fs = new FileSystem(_fs);
  // GitObjectManager does not know how to parse content, so we tweak that parameter before passing it.
  const _format = format === 'parsed' ? 'content' : format;
  let result = await GitObjectManager.read({ fs, gitdir, oid, format: _format });
  if (format === 'parsed') {
    switch (result.type) {
      case 'commit':
        result.object = GitCommit.from(result.object).parse();
        break
      case 'tree':
        result.object = { entries: GitTree.from(result.object).entries() };
        break
      case 'blob':
        break
      case 'tag':
        throw new Error(
          'TODO: Parsing annotated tag objects still needs to be implemented!!'
        )
      default:
        throw new Error(`Unrecognized git object type: '${result.type}'`)
    }
    result.format = 'parsed';
  }
  return result
}

/**
 * Remove a file from the git index (aka staging area)
 *
 * Note that this does NOT delete the file in the working directory.
 *
 * @link https://isomorphic-git.github.io/docs/remove.html
 */
async function remove ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs,
  filepath
}) {
  const fs = new FileSystem(_fs);
  await GitIndexManager.acquire(
    { fs, filepath: `${gitdir}/index` },
    async function (index) {
      index.delete({ filepath });
    }
  );
  // TODO: return oid?
}

/**
 * Get the value of a symbolic ref or resolve a ref to its object id
 *
 * @link https://isomorphic-git.github.io/docs/resolveRef.html
 */
async function resolveRef ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs,
  ref,
  depth
}) {
  const fs = new FileSystem(_fs);
  return GitRefManager.resolve({
    fs,
    gitdir,
    ref,
    depth
  })
}

/**
 * Create a signed commit
 *
 * @link https://isomorphic-git.github.io/docs/sign.html
 */
async function sign ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs,
  privateKeys,
  openpgp
}) {
  const fs = new FileSystem(_fs);
  const oid = await GitRefManager.resolve({ fs, gitdir, ref: 'HEAD' });
  const { type, object } = await GitObjectManager.read({ fs, gitdir, oid });
  if (type !== 'commit') {
    throw new Error(
      `HEAD is not pointing to a 'commit' object but a '${type}' object`
    )
  }
  let commit = SignedGitCommit.from(object);
  commit = await commit.sign(openpgp, privateKeys);
  const newOid = await GitObjectManager.write({
    fs,
    gitdir,
    type: 'commit',
    object: commit.toObject()
  });
  // Update branch pointer
  // TODO: Use an updateBranch function instead of this.
  const branch = await GitRefManager.resolve({
    fs,
    gitdir,
    ref: 'HEAD',
    depth: 2
  });
  await fs.write(path.join(gitdir, branch), newOid + '\n');
}

/**
 * Tell whether a file has been changed
 *
 * @link https://isomorphic-git.github.io/docs/status.html
 */
async function status ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs,
  filepath
}) {
  const fs = new FileSystem(_fs);
  let ignored = await GitIgnoreManager.isIgnored({
    gitdir,
    dir,
    filepath,
    fs
  });
  if (ignored) {
    return 'ignored'
  }
  let headTree = await getHeadTree({ fs, gitdir });
  let treeOid = await getOidAtPath({
    fs,
    gitdir,
    tree: headTree,
    path: filepath
  });
  let indexEntry = null;
  // Acquire a lock on the index
  await GitIndexManager.acquire(
    { fs, filepath: `${gitdir}/index` },
    async function (index) {
      for (let entry of index) {
        if (entry.path === filepath) {
          indexEntry = entry;
          break
        }
      }
    }
  );
  let stats = null;
  try {
    stats = await fs._lstat(path.join(dir, filepath));
  } catch (err) {
    if (err.code !== 'ENOENT') {
      throw err
    }
  }

  let H = treeOid !== null; // head
  let I = indexEntry !== null; // index
  let W = stats !== null; // working dir

  const getWorkdirOid = async () => {
    if (I && !cacheIsStale({ entry: indexEntry, stats })) {
      return indexEntry.oid
    } else {
      let object = await fs.read(path.join(dir, filepath));
      let workdirOid = await GitObjectManager.hash({
        gitdir,
        type: 'blob',
        object
      });
      return workdirOid
    }
  };

  if (!H && !W && !I) return 'absent' // ---
  if (!H && !W && I) return '*absent' // -A-
  if (!H && W && !I) return '*added' // --A
  if (!H && W && I) {
    let workdirOid = await getWorkdirOid();
    return workdirOid === indexEntry.oid ? 'added' : '*added' // -AA : -AB
  }
  if (H && !W && !I) return 'deleted' // A--
  if (H && !W && I) {
    return treeOid === indexEntry.oid ? '*deleted' : '*deleted' // AA- : AB-
  }
  if (H && W && !I) {
    let workdirOid = await getWorkdirOid();
    return workdirOid === treeOid ? '*undeleted' : '*undeletemodified' // A-A : A-B
  }
  if (H && W && I) {
    let workdirOid = await getWorkdirOid();
    if (workdirOid === treeOid) {
      return workdirOid === indexEntry.oid ? 'unmodified' : '*unmodified' // AAA : ABA
    } else {
      return workdirOid === indexEntry.oid ? 'modified' : '*modified' // ABB : AAB
    }
  }
  /*
  ---
  -A-
  --A
  -AA
  -AB
  A--
  AA-
  AB-
  A-A
  A-B
  AAA
  ABA
  ABB
  AAB
  */
}

function cacheIsStale (
  { entry, stats }
) {
  // Comparison based on the description in Paragraph 4 of
  // https://www.kernel.org/pub/software/scm/git/docs/technical/racy-git.txt
  return (
    entry.mode !== stats.mode ||
    entry.mtime.valueOf() !== stats.mtime.valueOf() ||
    entry.ctime.valueOf() !== stats.ctime.valueOf() ||
    entry.uid !== stats.uid ||
    entry.gid !== stats.gid ||
    entry.ino !== stats.ino >> 0 ||
    entry.size !== stats.size
  )
}

async function getOidAtPath ({ fs, gitdir, tree, path: path$$1 }) {
  if (typeof path$$1 === 'string') path$$1 = path$$1.split('/');
  let dirname = path$$1.shift();
  for (let entry of tree) {
    if (entry.path === dirname) {
      if (path$$1.length === 0) {
        return entry.oid
      }
      let { type, object } = await GitObjectManager.read({
        fs,
        gitdir,
        oid: entry.oid
      });
      if (type === 'tree') {
        let tree = GitTree.from(object);
        return getOidAtPath({ fs, gitdir, tree, path: path$$1 })
      }
      if (type === 'blob') {
        throw new Error(`Blob found where tree expected.`)
      }
    }
  }
  return null
}

async function getHeadTree ({ fs, gitdir }) {
  // Get the tree from the HEAD commit.
  let oid = await GitRefManager.resolve({ fs, gitdir, ref: 'HEAD' });
  let { object: cobject } = await GitObjectManager.read({ fs, gitdir, oid });
  let commit = GitCommit.from(cobject);
  let { object: tobject } = await GitObjectManager.read({
    fs,
    gitdir,
    oid: commit.parseHeaders().tree
  });
  let tree = GitTree.from(tobject).entries();
  return tree
}

/**
 * Verify a signed commit
 *
 * @link https://isomorphic-git.github.io/docs/verify.html
 */
async function verify ({
  dir,
  gitdir = path.join(dir, '.git'),
  fs: _fs,
  ref,
  publicKeys,
  openpgp
}) {
  const fs = new FileSystem(_fs);
  const oid = await GitRefManager.resolve({ fs, gitdir, ref });
  const { type, object } = await GitObjectManager.read({ fs, gitdir, oid });
  if (type !== 'commit') {
    throw new Error(
      `'ref' is not pointing to a 'commit' object but a '${type}' object`
    )
  }
  let commit = SignedGitCommit.from(object);
  let keys = await commit.listSigningKeys(openpgp);
  let validity = await commit.verify(openpgp, publicKeys);
  if (!validity) return false
  return keys
}

/**
 * Return the version number of isomorphic-git
 *
 * @link https://isomorphic-git.github.io/docs/version.html
 */
function version () {
  return pkg.version
}

const utils = { auth, oauth2 };

export { utils, add, branch, checkout, clone, commit, config, fetch, findRoot, getRemoteInfo, indexPack, init, listBranches, listFiles, listTags, log$1 as log, merge, pull, push, readObject, remove, resolveRef, sign, status, verify, version };
