;;; Directory Local Variables
;;; For more information see (info "(emacs) Directory Variables")
;; see https://www.compart.com/en/unicode/U+xxxx

;; sum([2 2 0 8].* [16^3,16.^2,16^1,1]) -> 8712

((coq-mode
  (company-coq-dir-local-symbols .
   (("`&`" . 8745)  ;; ∩ U+2229
    ("`|`" . 8746)  ;; ∪ U+222A
    ("set0" . 8709) ;; ∅ U+2205
    ("`<`" . 8842) ;; ⊊ U+228A
    ("`<=`" . 8838) ;; ⊆ U+2286
    ("^\\+" . ?⁺) ;; ⁺ U+207A
    ("^\\-" . ?⁻) ;; ⁻ U+207B
    ("`;`" . 8857 )  ;;  U+2299
    ("\\in" . 8712 )  ;;  U+2208 or U+220A
))))
