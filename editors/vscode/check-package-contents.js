// Pins the set of files that ship inside the VSIX.
//
// The Marketplace upload scanner rejects on package *contents*, and its
// message names neither the file nor the rule (see #1106). That makes
// the packaged inventory something worth failing CI over rather than
// discovering from a rejected upload: a stray file added here is
// invisible locally and expensive to diagnose after the fact.
//
// Run after `npm run build`, since `vsce ls` reports what would be
// packaged from the current working tree, `dist/` included.

"use strict";

const cp = require("node:child_process");
const path = require("node:path");

// Every path `vsce ls` should report, relative to editors/vscode.
// Adding a genuinely new asset means adding it here in the same commit
// — that is the point of the check, not an obstacle to it.
const EXPECTED = [
    "CHANGELOG.md",
    "LICENSE",
    "README.md",
    "dist/extension.js",
    "images/vera-icon.png",
    "language-configuration.json",
    "package.json",
    "syntaxes/vera.tmLanguage.json",
];

// Checked independently of the list above. Updating EXPECTED to match
// whatever the build happens to emit would silence the set comparison,
// so the category that actually draws scanner attention gets its own
// assertion that no list edit can wave through.
const FORBIDDEN_EXTENSIONS = [
    ".bat", ".bash", ".cmd", ".com", ".dll", ".dylib", ".exe",
    ".node", ".ps1", ".sh", ".so", ".zsh",
];

function packagedFiles() {
    const vsce = path.join(
        __dirname, "node_modules", ".bin",
        process.platform === "win32" ? "vsce.cmd" : "vsce",
    );
    const result = cp.spawnSync(vsce, ["ls"], {
        cwd: __dirname,
        encoding: "utf8",
    });
    if (result.error) {
        throw result.error;
    }
    if (result.status !== 0) {
        throw new Error(
            `vsce ls exited ${result.status}\n${result.stderr || ""}`,
        );
    }
    return result.stdout
        .split("\n")
        .map((line) => line.trim())
        .filter(Boolean)
        // vsce reports OS-native separators on Windows; compare in one
        // form so the expected list stays a single POSIX-style literal.
        .map((line) => line.split(path.sep).join("/"))
        .sort();
}

function main() {
    const actual = packagedFiles();
    const problems = [];

    const expected = [...EXPECTED].sort();
    const added = actual.filter((f) => !expected.includes(f));
    const removed = expected.filter((f) => !actual.includes(f));
    for (const f of added) {
        problems.push(`unexpected file in the package: ${f}`);
    }
    for (const f of removed) {
        problems.push(`expected file missing from the package: ${f}`);
    }

    for (const f of actual) {
        const ext = path.extname(f).toLowerCase();
        if (FORBIDDEN_EXTENSIONS.includes(ext)) {
            problems.push(
                `executable or native file in the package: ${f} ` +
                `(extension ${ext})`,
            );
        }
    }

    if (problems.length > 0) {
        console.error("VSIX contents check failed:");
        for (const problem of problems) {
            console.error(`  - ${problem}`);
        }
        console.error(
            "\nIf the change is intended, update EXPECTED in " +
            "check-package-contents.js in the same commit. If a " +
            "shell script or native binary has appeared, work out " +
            "what pulled it in before allowing it (see #1106).",
        );
        process.exitCode = 1;
        return;
    }

    console.log(`VSIX contents OK — ${actual.length} files, no executables.`);
}

main();
