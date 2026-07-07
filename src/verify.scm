;;; verify.scm
;;; Front-end verification.

;;; verify-scheme
;;; Syntax checking is deferred to a15's parse-scheme (see docs/notice.md),
;;; so the verifier is the identity pass.
(define verify-scheme (lambda (program) program))
