"use strict";

const fs = require("node:fs");
const path = require("node:path");
const esbuild = require("esbuild");

const extensionRoot = __dirname;
const distDir = path.join(extensionRoot, "dist");
const terminateProcess = require.resolve(
    "vscode-languageclient/lib/node/terminateProcess.sh",
);

async function main() {
    fs.rmSync(distDir, { recursive: true, force: true });

    await esbuild.build({
        entryPoints: [path.join(extensionRoot, "extension.js")],
        bundle: true,
        external: ["vscode"],
        format: "cjs",
        legalComments: "eof",
        minify: true,
        outfile: path.join(distDir, "extension.js"),
        platform: "node",
        target: "node16",
    });

    const packagedTerminateProcess = path.join(
        distDir,
        "terminateProcess.sh",
    );
    fs.copyFileSync(terminateProcess, packagedTerminateProcess);
    fs.chmodSync(packagedTerminateProcess, 0o755);
}

main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
});
