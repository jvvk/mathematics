; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () Real)
(declare-fun y0 () Real)
(declare-fun x1 () Real)
(declare-fun y1 () Real)
(declare-fun x2 () Real)
(declare-fun y2 () Real)
(declare-fun x3 () Real)
(declare-fun y3 () Real)
(declare-fun x4 () Real)
(declare-fun y4 () Real)
(declare-fun x5 () Real)
(declare-fun y5 () Real)
(assert
 (>= x0 0.0))
(assert
 (<= x0 1.0))
(assert
 (>= y0 0.0))
(assert
 (<= y0 1.0))
(assert
 (>= x1 0.0))
(assert
 (<= x1 1.0))
(assert
 (>= y1 0.0))
(assert
 (<= y1 1.0))
(assert
 (>= x2 0.0))
(assert
 (<= x2 1.0))
(assert
 (>= y2 0.0))
(assert
 (<= y2 1.0))
(assert
 (>= x3 0.0))
(assert
 (<= x3 1.0))
(assert
 (>= y3 0.0))
(assert
 (<= y3 1.0))
(assert
 (>= x4 0.0))
(assert
 (<= x4 1.0))
(assert
 (>= y4 0.0))
(assert
 (<= y4 1.0))
(assert
 (>= x5 0.0))
(assert
 (<= x5 1.0))
(assert
 (>= y5 0.0))
(assert
 (<= y5 1.0))
(assert
 (= (+ (^ (- x0 x1) 2.0) (^ (- y0 y1) 2.0)) 1.0))
(assert
 (or (and (distinct x0 x1) true) (and (distinct y0 y1) true)))
(assert
 (or (and (distinct x0 x2) true) (and (distinct y0 y2) true)))
(assert
 (or (and (distinct x0 x3) true) (and (distinct y0 y3) true)))
(assert
 (or (and (distinct x0 x4) true) (and (distinct y0 y4) true)))
(assert
 (or (and (distinct x0 x5) true) (and (distinct y0 y5) true)))
(assert
 (let ((?x160 (- (* (- x3 x2) (- y1 y2)) (* (- y3 y2) (- x1 x2)))))
 (let ((?x155 (- (* (- x3 x2) (- y0 y2)) (* (- y3 y2) (- x0 x2)))))
 (let (($x170 (< ?x155 0.0)))
 (let ((?x148 (- (* (- x1 x0) (- y3 y0)) (* (- y1 y0) (- x3 x0)))))
 (let (($x165 (< ?x148 0.0)))
 (let ((?x143 (- (* (- x1 x0) (- y2 y0)) (* (- y1 y0) (- x2 x0)))))
 (or (and (> ?x143 0.0) (> ?x148 0.0)) (and (< ?x143 0.0) $x165) (and (> ?x155 0.0) (> ?x160 0.0)) (and $x170 (< ?x160 0.0)) (and (< x0 x2) (< x0 x3) (< x1 x2) (< x1 x3)) (and (> x0 x2) (> x0 x3) (> x1 x2) (> x1 x3)) (and (< y0 y2) (< y0 y3) (< y1 y2) (< y1 y3)) (and (> y0 y2) (> y0 y3) (> y1 y2) (> y1 y3))))))))))
(assert
 (let ((?x440 (- (* (- x4 x3) (- y1 y3)) (* (- y4 y3) (- x1 x3)))))
 (let (($x449 (< ?x440 0.0)))
 (let ((?x435 (- (* (- x4 x3) (- y0 y3)) (* (- y4 y3) (- x0 x3)))))
 (let (($x448 (< ?x435 0.0)))
 (let ((?x428 (- (* (- x1 x0) (- y4 y0)) (* (- y1 y0) (- x4 x0)))))
 (let (($x443 (< ?x428 0.0)))
 (let ((?x148 (- (* (- x1 x0) (- y3 y0)) (* (- y1 y0) (- x3 x0)))))
 (let (($x165 (< ?x148 0.0)))
 (or (and (> ?x148 0.0) (> ?x428 0.0)) (and $x165 $x443) (and (> ?x435 0.0) (> ?x440 0.0)) (and $x448 $x449) (and (< x0 x3) (< x0 x4) (< x1 x3) (< x1 x4)) (and (> x0 x3) (> x0 x4) (> x1 x3) (> x1 x4)) (and (< y0 y3) (< y0 y4) (< y1 y3) (< y1 y4)) (and (> y0 y3) (> y0 y4) (> y1 y3) (> y1 y4))))))))))))
(assert
 (let ((?x620 (- (* (- x5 x4) (- y1 y4)) (* (- y5 y4) (- x1 x4)))))
 (let (($x629 (< ?x620 0.0)))
 (let ((?x615 (- (* (- x5 x4) (- y0 y4)) (* (- y5 y4) (- x0 x4)))))
 (let ((?x608 (- (* (- x1 x0) (- y5 y0)) (* (- y1 y0) (- x5 x0)))))
 (let ((?x428 (- (* (- x1 x0) (- y4 y0)) (* (- y1 y0) (- x4 x0)))))
 (let (($x443 (< ?x428 0.0)))
 (or (and (> ?x428 0.0) (> ?x608 0.0)) (and $x443 (< ?x608 0.0)) (and (> ?x615 0.0) (> ?x620 0.0)) (and (< ?x615 0.0) $x629) (and (< x0 x4) (< x0 x5) (< x1 x4) (< x1 x5)) (and (> x0 x4) (> x0 x5) (> x1 x4) (> x1 x5)) (and (< y0 y4) (< y0 y5) (< y1 y4) (< y1 y5)) (and (> y0 y4) (> y0 y5) (> y1 y4) (> y1 y5))))))))))
(assert
 (= (+ (^ (- x1 x2) 2.0) (^ (- y1 y2) 2.0)) 1.0))
(assert
 (or (and (distinct x1 x2) true) (and (distinct y1 y2) true)))
(assert
 (or (and (distinct x1 x3) true) (and (distinct y1 y3) true)))
(assert
 (or (and (distinct x1 x4) true) (and (distinct y1 y4) true)))
(assert
 (or (and (distinct x1 x5) true) (and (distinct y1 y5) true)))
(assert
 (let ((?x858 (- (* (- x4 x3) (- y2 y3)) (* (- y4 y3) (- x2 x3)))))
 (let ((?x440 (- (* (- x4 x3) (- y1 y3)) (* (- y4 y3) (- x1 x3)))))
 (let (($x449 (< ?x440 0.0)))
 (let ((?x853 (- (* (- x2 x1) (- y4 y1)) (* (- y2 y1) (- x4 x1)))))
 (let (($x863 (< ?x853 0.0)))
 (let ((?x848 (- (* (- x2 x1) (- y3 y1)) (* (- y2 y1) (- x3 x1)))))
 (or (and (> ?x848 0.0) (> ?x853 0.0)) (and (< ?x848 0.0) $x863) (and (> ?x440 0.0) (> ?x858 0.0)) (and $x449 (< ?x858 0.0)) (and (< x1 x3) (< x1 x4) (< x2 x3) (< x2 x4)) (and (> x1 x3) (> x1 x4) (> x2 x3) (> x2 x4)) (and (< y1 y3) (< y1 y4) (< y2 y3) (< y2 y4)) (and (> y1 y3) (> y1 y4) (> y2 y3) (> y2 y4))))))))))
(assert
 (let ((?x1014 (- (* (- x5 x4) (- y2 y4)) (* (- y5 y4) (- x2 x4)))))
 (let (($x1021 (< ?x1014 0.0)))
 (let ((?x620 (- (* (- x5 x4) (- y1 y4)) (* (- y5 y4) (- x1 x4)))))
 (let (($x629 (< ?x620 0.0)))
 (let ((?x1009 (- (* (- x2 x1) (- y5 y1)) (* (- y2 y1) (- x5 x1)))))
 (let (($x1017 (< ?x1009 0.0)))
 (let ((?x853 (- (* (- x2 x1) (- y4 y1)) (* (- y2 y1) (- x4 x1)))))
 (let (($x863 (< ?x853 0.0)))
 (or (and (> ?x853 0.0) (> ?x1009 0.0)) (and $x863 $x1017) (and (> ?x620 0.0) (> ?x1014 0.0)) (and $x629 $x1021) (and (< x1 x4) (< x1 x5) (< x2 x4) (< x2 x5)) (and (> x1 x4) (> x1 x5) (> x2 x4) (> x2 x5)) (and (< y1 y4) (< y1 y5) (< y2 y4) (< y2 y5)) (and (> y1 y4) (> y1 y5) (> y2 y4) (> y2 y5))))))))))))
(assert
 (let ((?x1122 (- (* (- x0 x5) (- y2 y5)) (* (- y0 y5) (- x2 x5)))))
 (let (($x1131 (< ?x1122 0.0)))
 (let ((?x1117 (- (* (- x0 x5) (- y1 y5)) (* (- y0 y5) (- x1 x5)))))
 (let ((?x1110 (- (* (- x2 x1) (- y0 y1)) (* (- y2 y1) (- x0 x1)))))
 (let ((?x1009 (- (* (- x2 x1) (- y5 y1)) (* (- y2 y1) (- x5 x1)))))
 (let (($x1017 (< ?x1009 0.0)))
 (or (and (> ?x1009 0.0) (> ?x1110 0.0)) (and $x1017 (< ?x1110 0.0)) (and (> ?x1117 0.0) (> ?x1122 0.0)) (and (< ?x1117 0.0) $x1131) (and (< x1 x5) (< x1 x0) (< x2 x5) (< x2 x0)) (and (> x1 x5) (> x1 x0) (> x2 x5) (> x2 x0)) (and (< y1 y5) (< y1 y0) (< y2 y5) (< y2 y0)) (and (> y1 y5) (> y1 y0) (> y2 y5) (> y2 y0))))))))))
(assert
 (= (+ (^ (- x2 x3) 2.0) (^ (- y2 y3) 2.0)) 1.0))
(assert
 (or (and (distinct x2 x3) true) (and (distinct y2 y3) true)))
(assert
 (or (and (distinct x2 x4) true) (and (distinct y2 y4) true)))
(assert
 (or (and (distinct x2 x5) true) (and (distinct y2 y5) true)))
(assert
 (let ((?x1283 (- (* (- x5 x4) (- y3 y4)) (* (- y5 y4) (- x3 x4)))))
 (let ((?x1014 (- (* (- x5 x4) (- y2 y4)) (* (- y5 y4) (- x2 x4)))))
 (let (($x1021 (< ?x1014 0.0)))
 (let ((?x1278 (- (* (- x3 x2) (- y5 y2)) (* (- y3 y2) (- x5 x2)))))
 (let (($x1288 (< ?x1278 0.0)))
 (let ((?x1273 (- (* (- x3 x2) (- y4 y2)) (* (- y3 y2) (- x4 x2)))))
 (or (and (> ?x1273 0.0) (> ?x1278 0.0)) (and (< ?x1273 0.0) $x1288) (and (> ?x1014 0.0) (> ?x1283 0.0)) (and $x1021 (< ?x1283 0.0)) (and (< x2 x4) (< x2 x5) (< x3 x4) (< x3 x5)) (and (> x2 x4) (> x2 x5) (> x3 x4) (> x3 x5)) (and (< y2 y4) (< y2 y5) (< y3 y4) (< y3 y5)) (and (> y2 y4) (> y2 y5) (> y3 y4) (> y3 y5))))))))))
(assert
 (let ((?x1422 (- (* (- x0 x5) (- y3 y5)) (* (- y0 y5) (- x3 x5)))))
 (let (($x1427 (< ?x1422 0.0)))
 (let ((?x1122 (- (* (- x0 x5) (- y2 y5)) (* (- y0 y5) (- x2 x5)))))
 (let (($x1131 (< ?x1122 0.0)))
 (let ((?x155 (- (* (- x3 x2) (- y0 y2)) (* (- y3 y2) (- x0 x2)))))
 (let (($x170 (< ?x155 0.0)))
 (let ((?x1278 (- (* (- x3 x2) (- y5 y2)) (* (- y3 y2) (- x5 x2)))))
 (let (($x1288 (< ?x1278 0.0)))
 (or (and (> ?x1278 0.0) (> ?x155 0.0)) (and $x1288 $x170) (and (> ?x1122 0.0) (> ?x1422 0.0)) (and $x1131 $x1427) (and (< x2 x5) (< x2 x0) (< x3 x5) (< x3 x0)) (and (> x2 x5) (> x2 x0) (> x3 x5) (> x3 x0)) (and (< y2 y5) (< y2 y0) (< y3 y5) (< y3 y0)) (and (> y2 y5) (> y2 y0) (> y3 y5) (> y3 y0))))))))))))
(assert
 (= (+ (^ (- x3 x4) 2.0) (^ (- y3 y4) 2.0)) 1.0))
(assert
 (or (and (distinct x3 x4) true) (and (distinct y3 y4) true)))
(assert
 (or (and (distinct x3 x5) true) (and (distinct y3 y5) true)))
(assert
 (let ((?x1516 (- (* (- x0 x5) (- y4 y5)) (* (- y0 y5) (- x4 x5)))))
 (let ((?x1422 (- (* (- x0 x5) (- y3 y5)) (* (- y0 y5) (- x3 x5)))))
 (let (($x1427 (< ?x1422 0.0)))
 (let ((?x435 (- (* (- x4 x3) (- y0 y3)) (* (- y4 y3) (- x0 x3)))))
 (let (($x448 (< ?x435 0.0)))
 (let ((?x1511 (- (* (- x4 x3) (- y5 y3)) (* (- y4 y3) (- x5 x3)))))
 (or (and (> ?x1511 0.0) (> ?x435 0.0)) (and (< ?x1511 0.0) $x448) (and (> ?x1422 0.0) (> ?x1516 0.0)) (and $x1427 (< ?x1516 0.0)) (and (< x3 x5) (< x3 x0) (< x4 x5) (< x4 x0)) (and (> x3 x5) (> x3 x0) (> x4 x5) (> x4 x0)) (and (< y3 y5) (< y3 y0) (< y4 y5) (< y4 y0)) (and (> y3 y5) (> y3 y0) (> y4 y5) (> y4 y0))))))))))
(assert
 (= (+ (^ (- x4 x5) 2.0) (^ (- y4 y5) 2.0)) 1.0))
(assert
 (or (and (distinct x4 x5) true) (and (distinct y4 y5) true)))
(assert
 (= (+ (^ (- x5 x0) 2.0) (^ (- y5 y0) 2.0)) 1.0))
(assert
 (= y0 0.0))
(assert
 (or (= x0 0.0) (= x1 0.0) (= x2 0.0) (= x3 0.0) (= x4 0.0) (= x5 0.0)))
(check-sat)
