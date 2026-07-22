// Pins what ships inside the built VSIX.
//
// The Marketplace upload scanner rejects on grounds it does not name —
// the message points at metadata and identifies neither a file nor a
// rule (see #1106), so what the archive contains is worth failing CI
// over rather than discovering from a rejected upload. A stray file
// added here is invisible locally and expensive to diagnose later.
//
// Reads the .vsix itself rather than `vsce ls`. The two differ: vsce
// synthesises `extension.vsixmanifest` and `[Content_Types].xml`, and
// renames README/CHANGELOG/LICENSE on the way in, so `vsce ls` reports
// eight paths where the archive holds ten entries under different
// names. `vsce package` also re-runs `vscode:prepublish`, rebuilding
// `dist/` after any earlier inspection — so a check run against the
// working tree grades a directory that no longer exists by the time
// the artifact is produced. The archive is the thing that gets
// uploaded, so the archive is what gets asserted.
//
// Run after `npm run package`.

"use strict";

const fs = require("node:fs");
const path = require("node:path");

// Every entry the archive should hold. These are archive paths, which
// are not the repository's paths: vsce prefixes `extension/` and
// lowercases some names. Adding a genuinely new asset means adding it
// here in the same commit — that is the point of the check, not an
// obstacle to it.
const EXPECTED = [
    "[Content_Types].xml",
    "extension.vsixmanifest",
    "extension/LICENSE.txt",
    "extension/changelog.md",
    "extension/dist/extension.js",
    "extension/images/vera-icon.png",
    "extension/language-configuration.json",
    "extension/package.json",
    "extension/readme.md",
    "extension/syntaxes/vera.tmLanguage.json",
];

// An allowlist, so an unrecognised extension fails rather than passes.
// A denylist inverts the burden onto whoever maintains it: the first
// version of this check listed `.sh` and `.exe` and friends, and let
// through `.wasm` (this project's own compile target), `.command`,
// `.py`, a file simply named `helper`, and a file named `.sh` — since
// `path.extname` returns "" for both extensionless names and dotfiles.
const ALLOWED_EXTENSIONS = [
    ".js", ".json", ".md", ".png", ".txt", ".vsixmanifest", ".xml",
];

// Checked independently of both lists above. Extension and mode are
// different properties and neither implies the other: vsce preserves
// unix permissions into the archive, so a file with a wholly inert
// extension can still arrive executable. Whatever an upload scanner
// makes of a `.sh`, it is the mode bits that decide whether something
// in the package can be run.
const EXECUTABLE_MODE_BITS = 0o111;

const ZIP_EOCD_SIGNATURE = 0x06054b50;
const ZIP_CENTRAL_FILE_SIGNATURE = 0x02014b50;

/**
 * Read a zip's central directory: one {name, mode} per entry.
 *
 * Hand-rolled rather than adding a dependency, because a package whose
 * job is auditing what ships should not itself widen the dependency
 * surface. Every structural anomaly throws — a reader that returned []
 * on a malformed archive would report a clean, empty package.
 */
function readArchiveEntries(archivePath) {
    const buf = fs.readFileSync(archivePath);

    // The end-of-central-directory record sits at the end, after a
    // variable-length comment, so it is found by scanning backwards.
    let eocd = -1;
    for (let i = buf.length - 22; i >= 0; i--) {
        if (buf.readUInt32LE(i) === ZIP_EOCD_SIGNATURE) {
            eocd = i;
            break;
        }
    }
    if (eocd < 0) {
        throw new Error(
            `${archivePath} has no zip end-of-central-directory record ` +
            "— it is not a readable archive.",
        );
    }

    const count = buf.readUInt16LE(eocd + 10);
    if (count === 0) {
        throw new Error(`${archivePath} declares zero entries.`);
    }

    const entries = [];
    let offset = buf.readUInt32LE(eocd + 16);
    for (let n = 0; n < count; n++) {
        if (buf.readUInt32LE(offset) !== ZIP_CENTRAL_FILE_SIGNATURE) {
            throw new Error(
                `${archivePath}: bad central-directory header at entry ` +
                `${n} (offset ${offset}).`,
            );
        }
        const nameLength = buf.readUInt16LE(offset + 28);
        const extraLength = buf.readUInt16LE(offset + 30);
        const commentLength = buf.readUInt16LE(offset + 32);
        // The high 16 bits of the external attributes carry the unix
        // mode when the archive was written on a unix host; a zip
        // written on Windows leaves them zero, which reads as "no mode
        // recorded" and cannot trip the executable check.
        const externalAttributes = buf.readUInt32LE(offset + 38);
        const nameStart = offset + 46;
        entries.push({
            name: buf.toString("utf8", nameStart, nameStart + nameLength),
            mode: (externalAttributes >>> 16) & 0o7777,
        });
        offset = nameStart + nameLength + extraLength + commentLength;
    }
    if (entries.length !== count) {
        throw new Error(
            `${archivePath}: read ${entries.length} entries, header ` +
            `declared ${count}.`,
        );
    }
    return entries;
}

/** Locate the single built VSIX, or explain what to do instead. */
function findArchive() {
    const found = fs.readdirSync(__dirname)
        .filter((name) => name.endsWith(".vsix"))
        .sort();
    if (found.length === 0) {
        throw new Error(
            "no .vsix found — run `npm run package` first (this check " +
            "asserts on the built archive, not the working tree).",
        );
    }
    if (found.length > 1) {
        throw new Error(
            `${found.length} .vsix files present (${found.join(", ")}) ` +
            "— remove the stale ones so the check is unambiguous.",
        );
    }
    return path.join(__dirname, found[0]);
}

/**
 * Compare an archive's entries against what should be there.
 *
 * Pure, so the interesting cases are reachable without building a
 * VSIX. Returns a list of human-readable problems; empty means clean.
 */
function analyse(entries, expected) {
    const problems = [];

    // A reader that silently produced nothing would otherwise make
    // every later assertion vacuous.
    if (entries.length === 0) {
        problems.push("archive contains no entries at all");
        return problems;
    }

    const actual = entries.map((entry) => entry.name).sort();
    const wanted = [...expected].sort();

    // Checked before the comparisons below, which are by membership and
    // so cannot see a repeat: a zip may legally name the same path
    // twice, and readers disagree about which copy wins, so a second
    // entry under an allowlisted, inert, already-expected name would
    // otherwise satisfy every assertion here.
    const seen = new Set();
    const duplicates = [];
    for (const name of actual) {
        if (seen.has(name) && !duplicates.includes(name)) {
            duplicates.push(name);
        }
        seen.add(name);
    }
    for (const name of duplicates) {
        problems.push(`duplicate entry in the package: ${name}`);
    }

    for (const name of seen) {
        if (!wanted.includes(name)) {
            problems.push(`unexpected file in the package: ${name}`);
        }
    }
    for (const name of wanted) {
        if (!seen.has(name)) {
            problems.push(`expected file missing from the package: ${name}`);
        }
    }

    for (const entry of entries) {
        const extension = path.extname(entry.name).toLowerCase();
        if (!ALLOWED_EXTENSIONS.includes(extension)) {
            problems.push(
                `file with a non-allowlisted extension: ${entry.name} ` +
                `(${extension || "no extension"})`,
            );
        }
        if (entry.mode & EXECUTABLE_MODE_BITS) {
            problems.push(
                `executable file in the package: ${entry.name} ` +
                `(mode ${entry.mode.toString(8).padStart(4, "0")})`,
            );
        }
    }

    return problems;
}

function main() {
    const archive = findArchive();
    const entries = readArchiveEntries(archive);
    const problems = analyse(entries, EXPECTED);

    if (problems.length > 0) {
        console.error(`VSIX contents check failed (${path.basename(archive)}):`);
        for (const problem of problems) {
            console.error(`  - ${problem}`);
        }
        console.error(
            "\nIf the change is intended, update EXPECTED in " +
            "check-package-contents.js in the same commit. If an " +
            "executable or an unrecognised file type has appeared, work " +
            "out what pulled it in before allowing it (see #1106).",
        );
        process.exitCode = 1;
        return;
    }

    console.log(
        `VSIX contents OK — ${entries.length} entries in ` +
        `${path.basename(archive)}, all allowlisted extensions, none ` +
        "executable.",
    );
}

if (require.main === module) {
    main();
}

module.exports = { analyse, readArchiveEntries, ALLOWED_EXTENSIONS, EXPECTED };
