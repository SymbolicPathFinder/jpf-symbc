; Proof of concept SMT regex implementation of Java String.trim()

(declare-const in_str String)

(declare-const out_str String)
(declare-const ws RegLan)
(declare-const nwc RegLan)

(assert (= out_str "abcd"))
(assert (str.prefixof " " in_str ))

(assert (and (str.in_re in_str (re.++ ws (str.to_re out_str) ws))
;; in_str = whitespace + out_str + whitespace
            (or (= out_str "")
                  (and (str.in_re out_str (re.++ nwc re.all)) (str.in_re out_str (re.++ re.all nwc))))))            
                  ;; To make sure out_str start & end with non-white char if it is not empty
(assert (= ws (re.union (re.+ (re.range (str.from_code 0) (str.from_code 32))) (str.to_re ""))))
; arbitrary length whitespace or empty string
(assert (= nwc (re.diff re.allchar (re.range (str.from_code 0) (str.from_code 32)))))
;(assert (out_str = "123"))
(check-sat)