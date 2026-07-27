# vim-veralang

Vim syntax highlighting for the [Vera programming language](https://veralang.dev/).
Ported from [`editors/vscode/syntaxes/vera.tmLanguage.json`](../vscode/syntaxes/vera.tmLanguage.json).

## Installation

### From the Vera repository

Clone the Vera repository (or navigate to an existing clone), then symlink `editors/vim-veralang` into Vim's package path:

```sh
git clone https://github.com/aallan/vera ~/src/vera
mkdir -p ~/.vim/pack/plugins/start
ln -s ~/src/vera/editors/vim-veralang ~/.vim/pack/plugins/start/vim-veralang
```

For Neovim, use `~/.local/share/nvim/site/pack/plugins/start/vim-veralang` instead. This is the native [Vim8 package][vim8pack] mechanism, so it needs no plugin manager.

### [Pathogen][p]

```sh
git clone https://github.com/aallan/vera ~/src/vera
ln -s ~/src/vera/editors/vim-veralang ~/.vim/bundle/vim-veralang
```

### [vim-plug][vp]

```vim
Plug 'aallan/vera', { 'rtp': 'editors/vim-veralang' }
```

## What gets highlighted

The same constructs as the VS Code and TextMate grammars:

- Slot references: `@Int.0`, `@Array<String>.result`, bare `@Type` bindings
- Contract keywords: `requires`/`ensures`/`effects`/`decreases`/`invariant`
- Control flow keywords: `if`/`then`/`else`/`match`/`let`/`in`/`where`/`handle`/`resume`/`with`
- Built-in effects and qualified effect operations (`IO.print`)
- ADT constructors, built-in and user-defined
- Declaration names: `fn`/`data`/`effect`/`ability`/`type`/`module`/`import`
- String interpolation (`\(...)`), recursively highlighted
- Nestable `{- -}` block comments
- Non-nesting `/* ... */` inline annotation comments (labels attached to a binding, e.g. `@Int /* width */`)
- The full operator set

See `syntax/veralang.vim` for the exact group-to-highlight mapping — each group is `hi default link`ed to a standard Vim group (`Keyword`, `Type`, `Function`, `Special`, `Operator`, etc.) so it works with any colorscheme.

`ftplugin/veralang.vim` also sets `commentstring`/`comments` so `gcc`-style comment plugins use `--`.

## Why the filetype is `veralang`, not `vera`

`.vera` files are detected as filetype `veralang` not `vera`.

Vim has shipped an unrelated `vera` filetype since 2005 -- the Synopsys **Vera** hardware verification language (`*.vr`, `*.vri`, `*.vrh`), bundled at [`$VIMRUNTIME/syntax/vera.vim`][oldsyn]. While it doesn't claim the `.vera` extension it use the file type `vera` which would cause conflicts.

[p]: https://github.com/tpope/vim-pathogen
[vp]: https://github.com/junegunn/vim-plug
[vim8pack]: https://vimhelp.org/repeat.txt.html#packages
[oldsyn]: https://github.com/vim/vim/blob/master/runtime/syntax/vera.vim
