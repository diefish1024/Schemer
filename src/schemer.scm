;;; schemer.scm
;;; A compiler for a subset of Scheme targeting x86-64.
;;;
;;; This is the entry point loaded (once) by the generated test.scm, after
;;; match.scm, helpers.scm, fmts.pretty and driver.scm.  The compiler is
;;; split into per-stage modules; each pass is a top-level definition so
;;; the driver can invoke it via (eval pass-name).  We only load here, not
;;; inside any pass (see docs/notice.md).  Paths are relative to the repo
;;; root, which is the working directory when test.scm runs.

(load "src/utils.scm")     ; compiler-wide helpers (conflict graph, subst)
(load "src/verify.scm")    ; front-end verification
(load "src/alloc.scm")     ; register & frame allocation cluster (a4/a5)
(load "src/codegen.scm")   ; back end: intermediate language -> x86-64
