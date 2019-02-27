(or
 (first (select var2locks x2))
 (and (not (first (select var2locks x2))) (= x1 y1))
 (and (not (first (select var2locks x2))) (not (= x1 y1)) (not (= x2 y2))))
