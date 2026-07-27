" Vera filetype detection.
"
" Filetype is "veralang", not "vera" -- Vim has shipped an unrelated
" built-in "vera" filetype since 2005 (the Synopsys Vera hardware
" verification language, $VIMRUNTIME/syntax/vera.vim). Native pack/start
" packages load *after* $VIMRUNTIME in 'runtimepath', so if this plugin
" also claimed "vera", the built-in syntax/ftplugin files would load
" first, set b:current_syntax, and this plugin's own files would exit
" immediately via their b:current_syntax guard -- silently never applying.
" "veralang" sidesteps the collision entirely. See README.md.

au BufRead,BufNewFile *.vera set filetype=veralang
