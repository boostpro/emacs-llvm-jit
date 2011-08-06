;; Copyright (C) 1995, 1997, 1998 Free Software Foundation, Inc.
  (make-temp-name
   (expand-file-name (if (eq system-type 'ms-dos) "ar" "archive.tmp")
		     temporary-file-directory))
  (if archive-zip-use-pkzip '("pkunzip" "-e" "-o-") '("unzip" "-qq" "-c"))
  (if archive-zip-use-pkzip '("pkzip" "-u" "-P") '("zip" "-q"))
  "*If non-nil then zip file members may be down-cased.
This case fiddling will only happen for members created by a system
that uses caseless file names."
(defvar archive-remote nil "*Non-nil if the archive is outside file system.")
(make-variable-buffer-local 'archive-remote)
(put 'archive-remote 'permanent-local t)

(defvar archive-member-coding-system nil "Coding-system of archive member.")
(make-variable-buffer-local 'archive-member-coding-system)

  "Turn an integer like 0700 (i.e., 448) into a mode string like -rwx------."
  ;; FIXME: merge with tar-grind-file-mode.
  (string
    (if (zerop (logand  8192 mode))
	(if (zerop (logand 16384 mode)) ?- ?d)
      ?c) ; completeness
    (if (zerop (logand   256 mode)) ?- ?r)
    (if (zerop (logand   128 mode)) ?- ?w)
    (if (zerop (logand    64 mode))
	(if (zerop (logand  1024 mode)) ?- ?S)
      (if (zerop (logand  1024 mode)) ?x ?s))
    (if (zerop (logand    32 mode)) ?- ?r)
    (if (zerop (logand    16 mode)) ?- ?w)
    (if (zerop (logand     8 mode))
	(if (zerop (logand  2048 mode)) ?- ?S)
      (if (zerop (logand  2048 mode)) ?x ?s))
    (if (zerop (logand     4 mode)) ?- ?r)
    (if (zerop (logand     2 mode)) ?- ?w)
    (if (zerop (logand     1 mode)) ?- ?x)))
        (minute (logand (ash time -5) 63))
	     (typename (capitalize (symbol-name type))))
	;; Remote archives are not written by a hook.
	(if archive-remote nil
	  (make-local-variable 'write-contents-hooks)
	  (add-hook 'write-contents-hooks 'archive-write-file))

	(make-local-variable 'local-enable-local-variables)
	(setq local-enable-local-variables nil)

	;; Prevent loss of data when saving the file.
	(make-local-variable 'file-precious-flag)
	(setq file-precious-flag t)
	;; Archives which are inside other archives and whose
	;; names are invalid for this OS, can't be written.
	(setq archive-read-only
	      (or (not (file-writable-p (buffer-file-name)))
		  (and archive-subfile-mode
		       (string-match file-name-invalid-regexp
				     (aref archive-subfile-mode 0)))))

	;; An archive can contain another archive whose name is invalid
	;; on local filesystem.  Treat such archives as remote.
	(or archive-remote
	    (setq archive-remote
		  (or (string-match archive-remote-regexp (buffer-file-name))
		      (string-match file-name-invalid-regexp
				    (buffer-file-name)))))
      (archive-summarize nil)
  (define-key archive-mode-map "q" 'quit-window)
      '(menu-item "Alternate Display" archive-alternate-display
		  :enable (boundp (archive-name "alternate-display"))
		  :help "Toggle alternate file info display"))
      '(menu-item "View This File" archive-view
		  :help "Display file at cursor in View Mode"))
      '(menu-item "Display in Other Window" archive-display-other-window
		  :help "Display file at cursor in another window"))
      '(menu-item "Find in Other Window" archive-extract-other-window
		  :help "Edit file at cursor in another window"))
      '(menu-item "Find This File" archive-extract
		  :help "Extract file at cursor and edit it"))
      '(menu-item "Unmark All" archive-unmark-all-files
		  :help "Unmark all marked files"))
      '(menu-item "Flag" archive-flag-deleted
		  :help "Flag file at cursor for deletion"))
      '(menu-item "Unflag" archive-unflag
		  :help "Unmark file at cursor"))
      '(menu-item "Mark" archive-mark
		  :help "Mark file at cursor"))
      '(menu-item "Change Owner..." archive-chown-entry
		  :enable (fboundp (archive-name "chown-entry"))
		  :help "Change owner of marked files"))
      '(menu-item "Change Group..." archive-chgrp-entry
		  :enable (fboundp (archive-name "chgrp-entry"))
		  :help "Change group ownership of marked files"))
      '(menu-item "Change Mode..." archive-chmod-entry
		  :enable (fboundp (archive-name "chmod-entry"))
		  :help "Change mode (permissions) of marked files"))
      '(menu-item "Rename to..." archive-rename-entry
		  :enable (fboundp (archive-name "rename-entry"))
		  :help "Rename marked files"))
    ;;  '(menu-item "Copy to..." archive-copy))
      '(menu-item "Expunge Marked Files" archive-expunge
		  :help "Delete all flagged files from archive"))
       (items (list item1)))
	  ((looking-at "..-l[hz][0-9ds]-") 'lzh)
	  (t (error "Buffer format not recognized")))))
(defun archive-summarize (&optional shut-up)
is visible (and the real data of the buffer is hidden).
Optional argument SHUT-UP, if non-nil, means don't print messages
when parsing the archive."
  (set-buffer-multibyte nil)
    (or shut-up
	(message "Parsing archive file..."))
    (or shut-up
	(message "Parsing archive file...done."))
    (archive-summarize t)
	    (add-text-properties
	     (aref fil 1) (aref fil 2)
	     '(mouse-face highlight
	       help-echo "mouse-2: extract this file into a buffer")
	     text))
(defun archive-unique-fname (fname dir)
  "Make sure a file FNAME can be created uniquely in directory DIR.

If FNAME can be uniquely created in DIR, it is returned unaltered.
If FNAME is something our underlying filesystem can't grok, or if another
file by that name already exists in DIR, a unique new name is generated
using `make-temp-file', and the generated name is returned."
  (let ((fullname (expand-file-name fname dir))
	(alien (string-match file-name-invalid-regexp fname)))
    (if (or alien (file-exists-p fullname))
	(make-temp-file
	 (expand-file-name
	  (if (and (fboundp 'msdos-long-file-names)
		   (not (msdos-long-file-names)))
	      "am"
	    "arc-mode.")
	  dir))
      fullname)))

  (let ((coding-system-for-write 'no-conversion))
    (if archive-remote
	(let ((start (point-max))
	      ;; Sometimes ARCHIVE is invalid while its actual name, as
	      ;; recorded in its parent archive, is not.  For example, an
	      ;; archive bar.zip inside another archive foo.zip gets a name
	      ;; "foo.zip:bar.zip", which is invalid on DOS/Windows.
	      ;; So use the actual name if available.
	      (archive-name
	       (or (and archive-subfile-mode (aref archive-subfile-mode 0))
		   archive)))
	  (make-directory archive-tmpdir t)
	  (setq archive-local-name
		(archive-unique-fname archive-name archive-tmpdir))
	  (save-restriction
	    (widen)
	    (write-region start (point-max) archive-local-name nil 'nomessage))
	  archive-local-name)
      (if (buffer-modified-p) (save-buffer))
      archive)))
	    (coding-system-for-read 'no-conversion)
	    (lno (archive-get-lineno))
	  (setq archive-files nil)
	  (archive-mode t)
	  (goto-char archive-file-list-start)
	  (archive-next-line lno))
	    (message
	     "Buffer `%s' must be saved for changes to take effect"
	     (buffer-name (current-buffer))))
(defun archive-file-name-handler (op &rest args)
  (or (eq op 'file-exists-p)
      (let ((file-name-handler-alist nil))
	(apply op args))))

(defun archive-set-buffer-as-visiting-file (filename)
  "Set the current buffer as if it were visiting FILENAME."
  (save-excursion
    (goto-char (point-min))
    (let ((coding
	   (or coding-system-for-read
	       (and set-auto-coding-function
		    (save-excursion
		      (funcall set-auto-coding-function
			       filename (- (point-max) (point-min)))))
	       ;; dos-w32.el defines find-operation-coding-system for
	       ;; DOS/Windows systems which preserves the coding-system
	       ;; of existing files.  We want it to act here as if the
	       ;; extracted file existed.
	       (let ((file-name-handler-alist
		      '(("" . archive-file-name-handler))))
		 (car (find-operation-coding-system 'insert-file-contents
						    filename t))))))
      (if (and (not coding-system-for-read)
	       (not enable-multibyte-characters))
	  (setq coding
		(coding-system-change-text-conversion coding 'raw-text)))
      (if (and coding
	       (not (eq coding 'no-conversion)))
	  (decode-coding-region (point-min) (point-max) coding)
	(setq last-coding-system-used coding))
      (set-buffer-modified-p nil)
      (kill-local-variable 'buffer-file-coding-system)
      (after-insert-file-set-buffer-file-coding-system (- (point-max)
							  (point-min))))))

	 ;; Members with file names which aren't valid for the
	 ;; underlying filesystem, are treated as read-only.
         (read-only-p (or archive-read-only
			  view-p
			  (string-match file-name-invalid-regexp ename)))
	  (if (and
	       (null
		(let (;; We may have to encode file name arguement for
		      ;; external programs.
		      (coding-system-for-write
		       (and enable-multibyte-characters
			    file-name-coding-system))
		      ;; We read an archive member by no-conversion at
		      ;; first, then decode appropriately by calling
		      ;; archive-set-buffer-as-visiting-file later.
		      (coding-system-for-read 'no-conversion))
		  (condition-case err
		      (if (fboundp extractor)
			  (funcall extractor archive ename)
			(archive-*-extract archive ename
					   (symbol-value extractor)))
		    (error
		     (ding (message "%s" (error-message-string err)))
		     nil))))
	       just-created)
	      (progn
		(set-buffer-modified-p nil)
		(kill-buffer buffer))
	    (archive-set-buffer-as-visiting-file ename)
	    (goto-char (point-min))
	    (rename-buffer bufname)
	    (setq buffer-read-only read-only-p)
	    (setq buffer-undo-list nil)
	    (set-buffer-modified-p nil)
	    (setq buffer-saved-size (buffer-size))
	    (normal-mode)
	    ;; Just in case an archive occurs inside another archive.
	    (if (eq major-mode 'archive-mode)
		(progn
		  (setq archive-remote t)
		  (if read-only-p (setq archive-read-only t))
		  ;; We will write out the archive ourselves if it is
		  ;; part of another archive.
		  (remove-hook 'write-contents-hooks 'archive-write-file t)))
	    (run-hooks 'archive-extract-hooks)
	    (if archive-read-only
		(message "Note: altering this archive is not implemented."))))
      (or (not (buffer-name buffer))
	  (progn
	    (if view-p
		(view-buffer buffer (and just-created 'kill-buffer))
	      (if (eq other-window-p 'display)
		  (display-buffer buffer)
		(if other-window-p
		    (switch-to-buffer-other-window buffer)
		  (switch-to-buffer buffer))))))))
				    default-directory))
	 exit-status success)
    (setq exit-status
	  (apply 'call-process
		 (car command)
		 nil
		 nil
		 nil
		 (append (cdr command) (list archive name))))
    (cond ((and (numberp exit-status) (= exit-status 0))
	   (if (not (file-exists-p tmpfile))
	       (ding (message "`%s': no such file or directory" tmpfile))
	     (insert-file-contents tmpfile)
	     (setq success t)))
	  ((numberp exit-status)
	   (ding
	    (message "`%s' exited with status %d" (car command) exit-status)))
	  ((stringp exit-status)
	   (ding (message "`%s' aborted: %s" (car command) exit-status)))
	  (t
	   (ding (message "`%s' failed" (car command)))))
    (archive-delete-local tmpfile)
    success))
  (apply 'call-process
	 (car command)
	 nil
	 t
	 nil
	 (append (cdr command) (list archive name))))
  (save-excursion
    (save-restriction
      (message "Updating archive...")
      (widen)
      (let ((writer  (save-excursion (set-buffer archive-superior-buffer)
				     (archive-name "write-file-member")))
	    (archive (save-excursion (set-buffer archive-superior-buffer)
				     (archive-maybe-copy (buffer-file-name)))))
	(if (fboundp writer)
	    (funcall writer archive archive-subfile-mode)
	  (archive-*-write-file-member archive
				       archive-subfile-mode
				       (symbol-value writer)))
	(message "Updating archive...done"))
      (set-buffer archive-superior-buffer)
      (if (not archive-remote) (revert-buffer) (archive-maybe-update nil))))
  ;; Restore the value of last-coding-system-used, so that basic-save-buffer
  ;; won't reset the coding-system of this archive member.
  (if (local-variable-p 'archive-member-coding-system)
      (setq last-coding-system-used archive-member-coding-system))
  t)
	  ;; If the member is itself an archive, write it without
	  ;; the dired-like listing we created.
	  (if (eq major-mode 'archive-mode)
	      (archive-write-file tmpfile)
	    (write-region (point-min) (point-max) tmpfile nil 'nomessage))
	  ;; basic-save-buffer needs last-coding-system-used to have
	  ;; the value used to write the file, so save it before any
	  ;; further processing clobbers it (we restore it in
	  ;; archive-write-file-member, above).
	  (setq archive-member-coding-system last-coding-system-used)
	  (if enable-multibyte-characters
	      (setq ename
		    (encode-coding-string ename file-name-coding-system)))
(defun archive-write-file (&optional file)
    (let ((coding-system-for-write 'no-conversion))
      (write-region archive-proper-file-start (point-max)
		    (or file buffer-file-name) nil t)
      (set-buffer-modified-p nil))
	  (funcall func (buffer-file-name)
		   (if enable-multibyte-characters
		       (encode-coding-string newname file-name-coding-system)
		     newname)
		   descr)
(defun archive-mode-revert (&optional no-auto-save no-confirm)
    (let ((revert-buffer-function nil)
	  (coding-system-for-read 'no-conversion))
      (set-buffer-multibyte nil)
	(set-buffer-multibyte nil)
    (while (progn (goto-char p) 
		  (looking-at "\\(.\\|\n\\)\\(.\\|\n\\)-l[hz][0-9ds]-"))
	     (hdrlvl  (char-after (+ p 20)))
	     (efnname (let ((str (buffer-substring (+ p 22) (+ p 22 fnlen))))
			(if file-name-coding-system
			    (decode-coding-string str file-name-coding-system)
			  (string-as-multibyte str))))
	     (width (string-width ifnname))
	     mode modestr uid gid text path prname
	     )
	(if (= hdrlvl 0)
	    (setq mode    (if (= creator ?U) (archive-l-e (+ p2 8) 2) ?\666)
		  uid     (if (= creator ?U) (archive-l-e (+ p2 10) 2))
		  gid     (if (= creator ?U) (archive-l-e (+ p2 12) 2)))
	  (if (= creator ?U)
	      (let* ((p3 (+ p2 3))
		     (hsize (archive-l-e p3 2))
		     (etype (char-after (+ p3 2))))
		(while (not (= hsize 0))
		  (cond
		   ((= etype 2) (let ((i (+ p3 3)))
				  (while (< i (+ p3 hsize))
				    (setq path (concat path
						       (if (= (char-after i)
							      255)
							   "/"
							 (char-to-string
							  (char-after i)))))
				    (setq i (1+ i)))))
		   ((= etype 80) (setq mode (archive-l-e (+ p3 3) 2)))
		   ((= etype 81) (progn (setq uid (archive-l-e (+ p3 3) 2))
					(setq gid (archive-l-e (+ p3 5) 2))))
		   )
		  (setq p3 (+ p3 hsize))
		  (setq hsize (archive-l-e p3 2))
		  (setq etype (char-after (+ p3 2)))))))
	(setq prname (if path (concat path ifnname) ifnname))
	(setq modestr (if mode (archive-int-to-mode mode) "??????????"))
	(setq text    (if archive-alternate-display
				ifnname)))
        (setq maxlen (max maxlen width)
	      files (cons (vector prname ifnname fiddle mode (1- p))
    (set-buffer-multibyte default-enable-multibyte-characters)
      (set-buffer-multibyte nil)
      (set-buffer-multibyte nil)
             (efnname (let ((str (buffer-substring (+ p 46) (+ p 46 fnlen))))
			(if file-name-coding-system
			    (decode-coding-string str file-name-coding-system)
			  (string-as-multibyte str))))
			    ((memq creator '(0 5 6 7 10 11 15)) ; Dos etc.
			   (not (not (memq creator '(0 2 4 5 9))))
			   (string= (upcase efnname) efnname)))
	     (width (string-width ifnname))
        (setq maxlen (max maxlen width)
      (set-buffer-multibyte nil)
		((memq creator '(0 5 6 7 10 11 15)) ; Dos etc.
	     (fnlen   (or (string-match "\0" namefld) 13))
	     (efnname (let ((str
			     (concat
			      (if (> ldirlen 0)
				  (concat (buffer-substring
					   (+ p 58 lfnlen)
					   (+ p 58 lfnlen ldirlen -1))
					  "/")
				"")
			      (if (> lfnlen 0)
				  (buffer-substring (+ p 58)
						    (+ p 58 lfnlen -1))
				(substring namefld 0 fnlen)))))
			(if file-name-coding-system
			    (decode-coding-string str file-name-coding-system)
			  (string-as-multibyte str))))
	     (width (string-width ifnname))
        (setq maxlen (max maxlen width)
;; This line was a mistake; it is kept now for compatibility.
;; rms  15 Oct 98
(provide 'arc-mode)

;;; arc-mode.el ends here