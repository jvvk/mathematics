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
 (let ((?x103 (+ (* (- x5 x0) (- x1 x0)) (* (- y5 y0) (- y1 y0)))))
 (>= ?x103 0.0)))
(assert
 (let ((?x145 (- (* (- x0 x5) (- y1 y5)) (* (- y0 y5) (- x1 x5)))))
 (< ?x145 0.0)))
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
 (let ((?x249 (- (* (- x3 x2) (- y1 y2)) (* (- y3 y2) (- x1 x2)))))
 (let ((?x244 (- (* (- x3 x2) (- y0 y2)) (* (- y3 y2) (- x0 x2)))))
 (let (($x259 (< ?x244 0.0)))
 (let ((?x237 (- (* (- x1 x0) (- y3 y0)) (* (- y1 y0) (- x3 x0)))))
 (let (($x254 (< ?x237 0.0)))
 (let ((?x232 (- (* (- x1 x0) (- y2 y0)) (* (- y1 y0) (- x2 x0)))))
 (or (and (> ?x232 0.0) (> ?x237 0.0)) (and (< ?x232 0.0) $x254) (and (> ?x244 0.0) (> ?x249 0.0)) (and $x259 (< ?x249 0.0)) (and (< x0 x2) (< x0 x3) (< x1 x2) (< x1 x3)) (and (> x0 x2) (> x0 x3) (> x1 x2) (> x1 x3)) (and (< y0 y2) (< y0 y3) (< y1 y2) (< y1 y3)) (and (> y0 y2) (> y0 y3) (> y1 y2) (> y1 y3))))))))))
(assert
 (let ((?x517 (- (* (- x4 x3) (- y1 y3)) (* (- y4 y3) (- x1 x3)))))
 (let (($x526 (< ?x517 0.0)))
 (let ((?x512 (- (* (- x4 x3) (- y0 y3)) (* (- y4 y3) (- x0 x3)))))
 (let (($x525 (< ?x512 0.0)))
 (let ((?x505 (- (* (- x1 x0) (- y4 y0)) (* (- y1 y0) (- x4 x0)))))
 (let (($x520 (< ?x505 0.0)))
 (let ((?x237 (- (* (- x1 x0) (- y3 y0)) (* (- y1 y0) (- x3 x0)))))
 (let (($x254 (< ?x237 0.0)))
 (or (and (> ?x237 0.0) (> ?x505 0.0)) (and $x254 $x520) (and (> ?x512 0.0) (> ?x517 0.0)) (and $x525 $x526) (and (< x0 x3) (< x0 x4) (< x1 x3) (< x1 x4)) (and (> x0 x3) (> x0 x4) (> x1 x3) (> x1 x4)) (and (< y0 y3) (< y0 y4) (< y1 y3) (< y1 y4)) (and (> y0 y3) (> y0 y4) (> y1 y3) (> y1 y4))))))))))))
(assert
 (let ((?x692 (- (* (- x5 x4) (- y1 y4)) (* (- y5 y4) (- x1 x4)))))
 (let (($x701 (< ?x692 0.0)))
 (let ((?x687 (- (* (- x5 x4) (- y0 y4)) (* (- y5 y4) (- x0 x4)))))
 (let ((?x680 (- (* (- x1 x0) (- y5 y0)) (* (- y1 y0) (- x5 x0)))))
 (let ((?x505 (- (* (- x1 x0) (- y4 y0)) (* (- y1 y0) (- x4 x0)))))
 (let (($x520 (< ?x505 0.0)))
 (or (and (> ?x505 0.0) (> ?x680 0.0)) (and $x520 (< ?x680 0.0)) (and (> ?x687 0.0) (> ?x692 0.0)) (and (< ?x687 0.0) $x701) (and (< x0 x4) (< x0 x5) (< x1 x4) (< x1 x5)) (and (> x0 x4) (> x0 x5) (> x1 x4) (> x1 x5)) (and (< y0 y4) (< y0 y5) (< y1 y4) (< y1 y5)) (and (> y0 y4) (> y0 y5) (> y1 y4) (> y1 y5))))))))))
(assert
 (= (+ (^ (- x1 x2) 2.0) (^ (- y1 y2) 2.0)) 1.0))
(assert
 (let ((?x862 (+ (* (- x0 x1) (- x2 x1)) (* (- y0 y1) (- y2 y1)))))
 (>= ?x862 0.0)))
(assert
 (let ((?x232 (- (* (- x1 x0) (- y2 y0)) (* (- y1 y0) (- x2 x0)))))
 (> ?x232 0.0)))
(assert
 (or (and (distinct x1 x2) true) (and (distinct y1 y2) true)))
(assert
 (or (and (distinct x1 x3) true) (and (distinct y1 y3) true)))
(assert
 (or (and (distinct x1 x4) true) (and (distinct y1 y4) true)))
(assert
 (or (and (distinct x1 x5) true) (and (distinct y1 y5) true)))
(assert
 (let ((?x928 (- (* (- x4 x3) (- y2 y3)) (* (- y4 y3) (- x2 x3)))))
 (let ((?x517 (- (* (- x4 x3) (- y1 y3)) (* (- y4 y3) (- x1 x3)))))
 (let (($x526 (< ?x517 0.0)))
 (let ((?x923 (- (* (- x2 x1) (- y4 y1)) (* (- y2 y1) (- x4 x1)))))
 (let (($x933 (< ?x923 0.0)))
 (let ((?x918 (- (* (- x2 x1) (- y3 y1)) (* (- y2 y1) (- x3 x1)))))
 (let (($x932 (< ?x918 0.0)))
 (or (and (> ?x918 0.0) (> ?x923 0.0)) (and $x932 $x933) (and (> ?x517 0.0) (> ?x928 0.0)) (and $x526 (< ?x928 0.0)) (and (< x1 x3) (< x1 x4) (< x2 x3) (< x2 x4)) (and (> x1 x3) (> x1 x4) (> x2 x3) (> x2 x4)) (and (< y1 y3) (< y1 y4) (< y2 y3) (< y2 y4)) (and (> y1 y3) (> y1 y4) (> y2 y3) (> y2 y4)))))))))))
(assert
 (let ((?x1080 (- (* (- x5 x4) (- y2 y4)) (* (- y5 y4) (- x2 x4)))))
 (let (($x1087 (< ?x1080 0.0)))
 (let ((?x692 (- (* (- x5 x4) (- y1 y4)) (* (- y5 y4) (- x1 x4)))))
 (let (($x701 (< ?x692 0.0)))
 (let ((?x1075 (- (* (- x2 x1) (- y5 y1)) (* (- y2 y1) (- x5 x1)))))
 (let (($x1083 (< ?x1075 0.0)))
 (let ((?x923 (- (* (- x2 x1) (- y4 y1)) (* (- y2 y1) (- x4 x1)))))
 (let (($x933 (< ?x923 0.0)))
 (or (and (> ?x923 0.0) (> ?x1075 0.0)) (and $x933 $x1083) (and (> ?x692 0.0) (> ?x1080 0.0)) (and $x701 $x1087) (and (< x1 x4) (< x1 x5) (< x2 x4) (< x2 x5)) (and (> x1 x4) (> x1 x5) (> x2 x4) (> x2 x5)) (and (< y1 y4) (< y1 y5) (< y2 y4) (< y2 y5)) (and (> y1 y4) (> y1 y5) (> y2 y4) (> y2 y5))))))))))))
(assert
 (let ((?x1181 (- (* (- x0 x5) (- y2 y5)) (* (- y0 y5) (- x2 x5)))))
 (let (($x1189 (< ?x1181 0.0)))
 (let ((?x145 (- (* (- x0 x5) (- y1 y5)) (* (- y0 y5) (- x1 x5)))))
 (let (($x146 (< ?x145 0.0)))
 (let ((?x1176 (- (* (- x2 x1) (- y0 y1)) (* (- y2 y1) (- x0 x1)))))
 (let ((?x1075 (- (* (- x2 x1) (- y5 y1)) (* (- y2 y1) (- x5 x1)))))
 (let (($x1083 (< ?x1075 0.0)))
 (or (and (> ?x1075 0.0) (> ?x1176 0.0)) (and $x1083 (< ?x1176 0.0)) (and (> ?x145 0.0) (> ?x1181 0.0)) (and $x146 $x1189) (and (< x1 x5) (< x1 x0) (< x2 x5) (< x2 x0)) (and (> x1 x5) (> x1 x0) (> x2 x5) (> x2 x0)) (and (< y1 y5) (< y1 y0) (< y2 y5) (< y2 y0)) (and (> y1 y5) (> y1 y0) (> y2 y5) (> y2 y0)))))))))))
(assert
 (= (+ (^ (- x2 x3) 2.0) (^ (- y2 y3) 2.0)) 1.0))
(assert
 (let ((?x1290 (+ (* (- x1 x2) (- x3 x2)) (* (- y1 y2) (- y3 y2)))))
 (>= ?x1290 0.0)))
(assert
 (let ((?x918 (- (* (- x2 x1) (- y3 y1)) (* (- y2 y1) (- x3 x1)))))
 (< ?x918 0.0)))
(assert
 (or (and (distinct x2 x3) true) (and (distinct y2 y3) true)))
(assert
 (or (and (distinct x2 x4) true) (and (distinct y2 y4) true)))
(assert
 (or (and (distinct x2 x5) true) (and (distinct y2 y5) true)))
(assert
 (let ((?x1344 (- (* (- x5 x4) (- y3 y4)) (* (- y5 y4) (- x3 x4)))))
 (let ((?x1080 (- (* (- x5 x4) (- y2 y4)) (* (- y5 y4) (- x2 x4)))))
 (let (($x1087 (< ?x1080 0.0)))
 (let ((?x1339 (- (* (- x3 x2) (- y5 y2)) (* (- y3 y2) (- x5 x2)))))
 (let (($x1349 (< ?x1339 0.0)))
 (let ((?x1334 (- (* (- x3 x2) (- y4 y2)) (* (- y3 y2) (- x4 x2)))))
 (or (and (> ?x1334 0.0) (> ?x1339 0.0)) (and (< ?x1334 0.0) $x1349) (and (> ?x1080 0.0) (> ?x1344 0.0)) (and $x1087 (< ?x1344 0.0)) (and (< x2 x4) (< x2 x5) (< x3 x4) (< x3 x5)) (and (> x2 x4) (> x2 x5) (> x3 x4) (> x3 x5)) (and (< y2 y4) (< y2 y5) (< y3 y4) (< y3 y5)) (and (> y2 y4) (> y2 y5) (> y3 y4) (> y3 y5))))))))))
(assert
 (let ((?x1483 (- (* (- x0 x5) (- y3 y5)) (* (- y0 y5) (- x3 x5)))))
 (let (($x1488 (< ?x1483 0.0)))
 (let ((?x1181 (- (* (- x0 x5) (- y2 y5)) (* (- y0 y5) (- x2 x5)))))
 (let (($x1189 (< ?x1181 0.0)))
 (let ((?x244 (- (* (- x3 x2) (- y0 y2)) (* (- y3 y2) (- x0 x2)))))
 (let (($x259 (< ?x244 0.0)))
 (let ((?x1339 (- (* (- x3 x2) (- y5 y2)) (* (- y3 y2) (- x5 x2)))))
 (let (($x1349 (< ?x1339 0.0)))
 (or (and (> ?x1339 0.0) (> ?x244 0.0)) (and $x1349 $x259) (and (> ?x1181 0.0) (> ?x1483 0.0)) (and $x1189 $x1488) (and (< x2 x5) (< x2 x0) (< x3 x5) (< x3 x0)) (and (> x2 x5) (> x2 x0) (> x3 x5) (> x3 x0)) (and (< y2 y5) (< y2 y0) (< y3 y5) (< y3 y0)) (and (> y2 y5) (> y2 y0) (> y3 y5) (> y3 y0))))))))))))
(assert
 (= (+ (^ (- x3 x4) 2.0) (^ (- y3 y4) 2.0)) 1.0))
(assert
 (let ((?x1557 (+ (* (- x2 x3) (- x4 x3)) (* (- y2 y3) (- y4 y3)))))
 (>= ?x1557 0.0)))
(assert
 (let ((?x1334 (- (* (- x3 x2) (- y4 y2)) (* (- y3 y2) (- x4 x2)))))
 (> ?x1334 0.0)))
(assert
 (or (and (distinct x3 x4) true) (and (distinct y3 y4) true)))
(assert
 (or (and (distinct x3 x5) true) (and (distinct y3 y5) true)))
(assert
 (let ((?x1598 (- (* (- x0 x5) (- y4 y5)) (* (- y0 y5) (- x4 x5)))))
 (let ((?x1483 (- (* (- x0 x5) (- y3 y5)) (* (- y0 y5) (- x3 x5)))))
 (let (($x1488 (< ?x1483 0.0)))
 (let ((?x512 (- (* (- x4 x3) (- y0 y3)) (* (- y4 y3) (- x0 x3)))))
 (let (($x525 (< ?x512 0.0)))
 (let ((?x1593 (- (* (- x4 x3) (- y5 y3)) (* (- y4 y3) (- x5 x3)))))
 (or (and (> ?x1593 0.0) (> ?x512 0.0)) (and (< ?x1593 0.0) $x525) (and (> ?x1483 0.0) (> ?x1598 0.0)) (and $x1488 (< ?x1598 0.0)) (and (< x3 x5) (< x3 x0) (< x4 x5) (< x4 x0)) (and (> x3 x5) (> x3 x0) (> x4 x5) (> x4 x0)) (and (< y3 y5) (< y3 y0) (< y4 y5) (< y4 y0)) (and (> y3 y5) (> y3 y0) (> y4 y5) (> y4 y0))))))))))
(assert
 (= (+ (^ (- x4 x5) 2.0) (^ (- y4 y5) 2.0)) 1.0))
(assert
 (let ((?x1700 (+ (* (- x3 x4) (- x5 x4)) (* (- y3 y4) (- y5 y4)))))
 (>= ?x1700 0.0)))
(assert
 (let ((?x1593 (- (* (- x4 x3) (- y5 y3)) (* (- y4 y3) (- x5 x3)))))
 (> ?x1593 0.0)))
(assert
 (or (and (distinct x4 x5) true) (and (distinct y4 y5) true)))
(assert
 (= (+ (^ (- x5 x0) 2.0) (^ (- y5 y0) 2.0)) 1.0))
(assert
 (let ((?x1742 (+ (* (- x4 x5) (- x0 x5)) (* (- y4 y5) (- y0 y5)))))
 (>= ?x1742 0.0)))
(assert
 (let ((?x687 (- (* (- x5 x4) (- y0 y4)) (* (- y5 y4) (- x0 x4)))))
 (> ?x687 0.0)))
(assert
 (or (= y0 0.0) (= y1 0.0) (= y2 0.0) (= y3 0.0) (= y4 0.0) (= y5 0.0)))
(assert
 (or (= x0 0.0) (= x1 0.0) (= x2 0.0) (= x3 0.0) (= x4 0.0) (= x5 0.0)))
(check-sat)
