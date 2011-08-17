(defvar gtl-mode-hook nil)
(defvar gtl-mode-map
  (let ((map (make-keymap)))
    (define-key map "\C-j" 'newline-and-indent)
    map)
  "Keymap for GTL major mode")

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.gtl\\'" . gtl-mode))

(defconst gtl-font-lock-keywords-1
  (list
   (cons "//.*" 'font-lock-comment-face)
   (cons "/\\*[^\\*]*\\*/" 'font-lock-comment-face)
   (cons (concat "\\<" (regexp-opt '("automaton" "state" "transition" "connect" "verify" "contract" "init") t) "\\>") 'font-lock-keyword-face)
   (cons (concat "\\<" (regexp-opt '("always" "until" "and" "or" "not" "implies" "after" "finally" "next") t) "\\>") 'font-lock-builtin-face)
   )
  "Highlighting expressions for GTL mode")

(defconst gtl-font-lock-keywords-2
  (append gtl-font-lock-keywords-1
	  (list
	   '("\\<\\(model\\)\\[\\([a-z]*\\)\\] *\\([a-z]*\\)"
	     (1 'font-lock-keyword-face nil t)
	     (2 'font-lock-constant-face nil t)
	     (3 'font-lock-function-name-face nil t)
	     )
	   '("\\<\\(instance\\) *\\([a-zA-Z0-9]+\\) *\\([a-zA-Z0-9]+\\)"
	     (1 'font-lock-keyword-face nil t)
	     (2 'font-lock-function-name-face nil t)
	     (3 'font-lock-variable-name-face nil t)
	     )
	   '("\\<\\([a-z][a-z0-9]*\\)\\.\\([a-z][a-z0-9]*\\)"
	     (1 'font-lock-variable-name-face nil t)
	     )
	   '("\\<\\(input\\|output\\) *\\([a-zA-Z0-9^{}(), ]+?\\) *\\([a-zA-Z]+\\);"
	     (1 'font-lock-keyword-face nil t)
	     (2 'font-lock-type-face nil t)
	     (3 'font-lock-variable-name-face nil t)
	     )
	   )))
	   

(defvar gtl-font-lock-keywords gtl-font-lock-keywords-2
  "Default highlighting expressions for GTL mode")

(defun gtl-indent-line ()
  "Indent current line as GTL code"
  (interactive)
  (beginning-of-line)
  (if (bobp)
      (indent-line-to 0)
    (let ((not-indented t) cur-indent)
      (if (looking-at "^[ \t]*}")
	  (progn
	    (save-excursion
	      (forward-line -1)
	      (setq cur-indent (- (current-indentation) 2)))
	    (if (< cur-indent 0)
		(setq cur-indent 0)))
	(save-excursion
	  (while not-indented
	    (forward-line -1)
	    (if (looking-at "^[ \t]*}")
		(progn
		  (setq cur-indent (current-indentation))
		  (setq not-indented nil))
	      (if (looking-at "^.*{[ \t]*$")
		  (progn
		    (setq cur-indent (+ (current-indentation) 2))
		    (setq not-indented nil))
		(if (bobp)
		    (setq not-indented nil)))))))
      (if cur-indent
	  (indent-line-to cur-indent)
	(indent-line-to 0)))))

(defvar gtl-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?_ "w" st)
    (modify-syntax-entry ?/ ". 124b" st)
    (modify-syntax-entry ?* ". 23" st)
    (modify-syntax-entry ?\n "> b" st)
    st) 
  "Syntax table for gtl-mode")

(defun gtl-mode ()
  "Major mode for editing GTL specifications"
  (interactive)
  (kill-all-local-variables)
  (set-syntax-table gtl-mode-syntax-table)
  (use-local-map gtl-mode-map)
  (set (make-local-variable 'font-lock-defaults) '(gtl-font-lock-keywords))
  (set (make-local-variable 'indent-line-function) 'gtl-indent-line)
  (setq major-mode 'gtl-mode)
  (setq mode-name "GTL")
  (run-hooks 'gtl-mode-hook))

(provide 'gtl-mode)

