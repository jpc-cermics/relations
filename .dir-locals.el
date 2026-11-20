;;; Directory Local Variables
;;; For more information see (info "(emacs) Directory Variables")
;; see https://www.compart.com/en/unicode/U+xxxx
;; Keys are literal strings (not regexps): prettify-symbols uses regexp-opt.

((coq-mode
  (company-coq-dir-local-symbols .
   (("`&`"  . ?∩)    ;; U+2229
    ("`|`"  . ?∪)    ;; U+222A
    ("set0" . ?∅)    ;; U+2205
    ("`<`"  . ?⊊)    ;; U+228A
    ("`<=`" . ?⊆)    ;; U+2286
    ("`;`"  . ?⊙)    ;; U+2299
    ("\\in" . ?∈)    ;; U+2208
    ("^{+}" . "⁺")   ;; U+207A
    ("^{*}" . "*")    ;; U+20F0 (or "⋆" if the font renders it badly)
    ("^-1"  . "⁻¹")  ;; U+207B U+00B9
))))
