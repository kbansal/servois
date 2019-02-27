(or
 ; different vars:
 (and (= x1 y1) (not (= x2 y2)))

 (and (not (= x1 y1)) (= x1 (second (select var2locks x2))) (not (first (select var2locks y2))) (not (= x2 y2)))

 (and (not (= x1 y1)) (not (= x1 (second (select var2locks x2)))) (not (= x2 y2))))

 ; same thread
 (and (= x1 y1) (= x2 y2) (not (= x1 (second (select var2locks x2)))) (first (select var2locks x2)))

                                        ; different threads, locked by the locker
 (and (not (= x1 y1)) (= x1 (second (select var2locks x2))) (first (select var2locks y2)))


                                        ; different threads, same var, locked by third party
 (and (not (= x1 y1)) (not (= x1 (second (select var2locks x2)))) (= x2 y2) (first (select var2locks y2)) (not (= y1 (second (select var2locks y2)))))

 
