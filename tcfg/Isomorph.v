Require Export ImplodeTCFG.

Section Iso.
  (*Context `(C : redCFG).*)
  Variables (Lab1 Lab2 : finType)
            (root1 : Lab1) (root2 : Lab2)
            (edge1 a_edge1 : Lab1 -> Lab1 -> bool)
            (edge2 a_edge2 : Lab2 -> Lab2 -> bool)
            (C1 : redCFG edge1 root1 a_edge1)
            (C2 : redCFG edge2 root2 a_edge2).

  Definition edge_morphism (L L' : finType) (e : L -> L -> bool) (e' : L' -> L' -> bool) (f : L -> L')
    := Proper ((fun x y => e x y = true) ==> (fun x y => e' x y = true)) f.

  Definition iso_cfg 
             `(C1 : redCFG Lab1 edge1 root1 a_edge1)
             `(C2 : redCFG Lab2 edge2 root2 a_edge2)
    := exists f g, edge_morphism edge1 edge2 f /\ edge_morphism a_edge1 a_edge2 f
              /\ f root1 = root2 /\ g root2 = root1 (* <-- this is redundant *)
              /\ edge_morphism edge2 edge1 g /\ edge_morphism a_edge2 a_edge1 g.

  Local Arguments TPath {_ _ _ _} _.              
  
  Lemma iso_impl_tlist (h h' : Lab) p i t
        (Hiso : iso_cfg C1 C2)
        (Hpath : TPath C1 (root1,start_tag) (p,i) t)
    : exists p' t', TPath C2 (root2,start_tag) (p',i) t'.
  Admitted.
  
End Iso.
Lemma impl_iso (h h' : Lab)
      (Heq : eq_loop h h')
  : iso_cfg (local_impl_CFG C h) (local_impl_CFG C h').      
Admitted.
