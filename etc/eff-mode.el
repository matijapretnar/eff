; Emacs mode for eff, derived from OCaml tuareg-mode. See LICENSE.txt
; for licensing information.
;
; This code could be much improved.
;
; To use the eff-mode, put this file somewhere and add something like the following
; in your .emacs file:
;
;   (autoload 'eff-mode "<eff-mode-install-dir>/eff-mode" "Major mode for editing eff files" t)
;   (setq auto-mode-alist (cons '("\\.eff$" . eff-mode) auto-mode-alist))

(defvar eff-keywords
  '("and"
    "as"
    "begin"
    "check"
    "do"
    "done"
    "downto"
    "else"
    "end"
    "effect"
    "finally"
    "for"
    "fun"
    "function"
    "handle"
    "handler"
    "if"
    "in"
    "match"
    "let"
    "new"
    "of"
    "operation"
    "rec"
    "val"
    "while"
    "to"
    "type"
    "then"
    "with"))

(defvar eff-constants
  '( 
    "asr"
    "false"
    "mod"
    "land"
    "lor"
    "lsl"
    "lsr"
    "lxor"
    "or"
    "true"))

(defvar eff-tab-width 2 "Width of tab for eff mode")

(defvar eff-font-lock-defaults
    `((
      ;; stuff between "
       ("\"\\.\\*\\?" . font-lock-string-face)
      ;; prefix and infix operators, can be improved
       ("+\\|,\\|;" . font-lock-keyword-face)
       ( ,(regexp-opt eff-keywords 'words) . font-lock-keyword-face)
       ( ,(regexp-opt eff-constants 'words) . font-lock-constant-face)
       )))

(define-derived-mode eff-mode
  tuareg-mode
  "Eff"
  "Major mode for eff (unfinished)."

  (setq font-lock-defaults eff-font-lock-defaults)

;  (when eff-tab-width (setq tab-width eff-tab-width))
;
;  (setq comment-start "(*")
;  (setq comment-end "*)")
)

(provide 'eff-mode)
