(or
 (and (= y1 (second (select var2locks y2))) (first (select var2locks x2)))

 (and (= y1 (second (select var2locks y2))) (not (first (select var2locks x2))) (member y2 varnames) (= x2 y2) (not (= x1 y1)))


 (and (= y1 (second (select var2locks y2))) (not (first (select var2locks x2))) (not (member y2 varnames)) (first (select var2locks y2)))

 (and (= y1 (second (select var2locks y2))) (not (first (select var2locks x2))) (not (member y2 varnames)) (not (first (select var2locks y2))) (= x2 y2) (not (= x1 y1)))


 (and (not (= y1 (second (select var2locks y2)))) (first (select var2locks x2)))

 (and (not (= y1 (second (select var2locks y2)))) (not (first (select var2locks x2))) (member y2 varnames) (= x2 y2) (not (= x1 y1)))


 (and (not (= y1 (second (select var2locks y2)))) (not (first (select var2locks x2))) (not (member y2 varnames)) (= x2 y2) (not (= x1 y1)))

; different variables, lock for y is not held
 (and (not (= y1 (second (select var2locks y2)))) (not (first (select var2locks x2))) (member y2 varnames) (not (= x2 y2)))

 (and (= y1 (second (select var2locks y2))) (not (first (select var2locks x2))) (member y2 varnames) (not (= x2 y2)))

 (and (= y1 (second (select var2locks y2))) (not (first (select var2locks x2))) (not (member y2 varnames)) (not (first (select var2locks y2))) (not (= x2 y2)))

 (and (not (= y1 (second (select var2locks y2)))) (not (first (select var2locks x2))) (not (member y2 varnames)) (not (= x2 y2))))
