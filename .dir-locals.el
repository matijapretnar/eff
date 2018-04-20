;; Support for compiling in subdirectories from Emacs. Adapted from Coq source.
((nil
  . ((eval
      . (progn
          ;; root directory (ending with slash)
          (let ((eff-root-directory
                 (when buffer-file-name
                   (locate-dominating-file buffer-file-name ".dir-locals.el")))
                (eff-project-find-file
                 (and (boundp 'eff-project-find-file) eff-project-find-file)))

            ;; eff tags file
            (when eff-root-directory
              (setq tags-file-name (concat eff-root-directory "TAGS"))
              (add-to-list 'compilation-search-path eff-root-directory)
              ;; Setting the compilation directory to eff root. This is
              ;; mutually exclusive with the setting of default-directory
              ;; below.
              (if (not eff-project-find-file)
                  (setq compile-command (concat "make -C " eff-root-directory)))
              )
            (setq eff-executable (concat eff-root-directory "eff.native")))))))
 (tuareg-mode
  (show-trailing-whitespace . t))
 (eff-mode
  (show-trailing-whitespace . t)))
