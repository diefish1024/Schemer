;;; verify.scm
;;; Front-end verification.

;;; verify-scheme
;;; Syntax checking is deferred to a15's parse-scheme (see docs/notice.md),
;;; so the verifier is the identity pass.
(define verify-scheme (lambda (program) program))

;;; verify-uil  (a8)
;;; Checks that the language-dependent front end produced well-formed UIL.
;;; Following the notice, we keep it an identity pass for now.
(define verify-uil (lambda (program) program))
