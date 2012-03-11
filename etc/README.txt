This directory contains miscellaneous support files.

Support for Emacs
=================

The file `eff-mode.el` is a derived Emacs mode for editing eff files. It is
based on the [tuareg mode](http://www.emacswiki.org/emacs/TuaregMode) for
Ocaml and thus requires that you have a working `tuareg-mode`.

To use eff mode, copy `eff-mode.el` wherever you keep your Emacs lisp files
and put something like this in your `.emacs` file:

    (autoload 'eff-mode "<eff-mode-install-dir>/eff-mode" "Major mode for editing eff files" t)
    (setq auto-mode-alist (cons '("\\.eff$" . eff-mode) auto-mode-alist))

Support for Textmate
====================

The directory `eff.tmbundle` contains a Textmate editing mode for eff
files. Use it as you usually do.
