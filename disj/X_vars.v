
Variable (t1 t2 : ne_list (Lab * Tag)) (r1 r2 : list (Lab * Tag)) (q1 q2 s : Lab) (j1 j2 k : Tag).
Hypotheses (Hlc : last_common' t1 t2 r1 r2 (s,k))
           (Hpath1 : TPath (root,start_tag) (q1,j1) t1)
           (Hpath2 : TPath (root,start_tag) (q2,j2) t2)
(*           (Hneq : r1 <> r2) (* <-> r1 <> nil \/ r2 <> nil *)*)
           (Hloop : eq_loop q1 q2)
           (Htag : tl j1 = tl j2)
           (Htagleq : hd 0 j1 <= hd 0 j2). 
