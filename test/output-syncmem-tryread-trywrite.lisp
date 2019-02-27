; tryread(x1=tid, x2=var)  and   trywrite(y1=tid, y2=var, y3=value)
(or

 (= y3 (select contents y2))

 (and (not (= y3 (select contents y2)))
      (= x1 y1)
      (member x2 varnames)
      (= varnames (singleton x2))
      (= x2 y2)
      (= x1 (second (select var2locks x2)))
      (not (first (select var2locks y2))))

 (and (not (= y3 (select contents y2)))
      (= x1 y1)
      (member x2 varnames)
      (= varnames (singleton x2))
      (= x2 y2)
      (not (= x1 (second (select var2locks x2)))))

 (and (not (= y3 (select contents y2)))
      (= x1 y1)
      (member x2 varnames)
      (= varnames (singleton x2))
      (not (= x2 y2)))

 (and (not (= y3 (select contents y2)))
      (= x1 y1)
      (member x2 varnames)
      (not (= varnames (singleton x2)))
      (= x2 y2)
      (= x1 (second (select var2locks x2)))
      (not (first (select var2locks y2))))

 (and (not (= y3 (select contents y2))) (= x1 y1) (member x2 varnames)
      (not (= varnames (singleton x2))) (= x2 y2) (not (= x1 (second (select var2locks x2)))))

 (and (not (= y3 (select contents y2))) (= x1 y1) (member x2 varnames)
      (not (= varnames (singleton x2))) (not (= x2 y2)))

 (and (not (= y3 (select contents y2))) (= x1 y1) (not (member x2 varnames)) (= x2 y2) (= x1 (second (select var2locks x2))) (not (first (select var2locks y2))))

 (and (not (= y3 (select contents y2))) (= x1 y1) (not (member x2 varnames)) (= x2 y2) (not (= x1 (second (select var2locks x2)))))

 (and (not (= y3 (select contents y2))) (= x1 y1) (not (member x2 varnames)) (not (= x2 y2)))

 (and (not (= y3 (select contents y2))) (not (= x1 y1))))
