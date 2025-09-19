From Stdlib Require Import  Nat.     
From Stdlib Require Import Bool.    
From Stdlib Require Import List. 
Import ListNotations.
 
From Stdlib Require Import Lia.
From Stdlib Require Import Nat.
Import Arith.
From Stdlib Require Import Lists.ListDec.
From Stdlib Require Import List Decidable.



Lemma fun_out_same_means_same_element_of_lst
  {A B : Type }
  (a : A) {b : A}
  { f  : A -> B }
  { ld  : list A }
  (pf : f a = f b)
  (pf_a : In a ld)
  (pf_b : In b ld)
  (pf_ld : NoDup (map (fun y => f y)  ld) ):
  a = b.
  
  induction ld;
    inversion pf_a;
    inversion pf_ld;
    inversion pf_b.
  
  - rewrite <- H, H4.
    trivial.
  - pose proof (in_map (fun a  => f a) ld b  H4 ).
    simpl in H5.
    rewrite <- pf in H5.
    rewrite H in H0, H2.
    contradiction.
  - pose proof (in_map (fun a => f  a) ld a  H ).
    simpl in H5.
    rewrite pf in H5.
    rewrite H4 in H2.
    contradiction.
  - exact (IHld H H4 H3).
Qed.         
 


Lemma sub_list_length_le_list_length
  { A : Type }
  { l1 l2 : list A}
  (pf_l1 : NoDup l1)
  (pf_incl : incl l1 l2 )
  : length l1 <= length l2.
Proof.
  generalize dependent l2.
  induction l1; intros.
  - simpl in *; lia.
  - assert ( In a l2). {
      unfold incl in pf_incl.
      assert ( In a (a::l1) ) by apply in_eq.
      exact (pf_incl a H).
    }
    inversion pf_l1.
    pose proof (in_split a l2 H).
    inversion H4 as [l21 [l22 Hl2]].
    remember (l21++l22).
    assert ( length l1 <= length l0 ).
    {
      assert ( incl l1 l0). {
        unfold incl.
        intros.
        assert ( In a0 (a::l1) ). { apply in_cons; trivial. }
        assert (a0 <> a ). {
          intro. 
          rewrite H7 in H5.
          contradiction.
        }
        pose proof (pf_incl a0 H6).
        rewrite Hl2 in H8.
        pose proof ( in_elt_inv a0 a  l21 l22 H8).
        inversion H9. rewrite H10 in H7. contradiction.
        rewrite Heql0.
        trivial.
      }
      exact (IHl1 H3 l0 H5).
    }
    simpl.
    assert (length l2 = S (length l0) ).
    { rewrite Heql0.
      rewrite Hl2.
      rewrite ( app_length).
      assert ( length (a::l22) = S (length l22) ). {
        unfold length. lia.
      }
      rewrite H6.
      rewrite app_length.
      lia.
    }
    lia. 
Qed.      



(* Absolute difference function *)
Definition adiff (n m : nat) : nat :=
  match  n <? m with
  | true => m - n
  | false => n - m
  end.



Lemma adiff_reflex (n m : nat ) : (adiff n m = adiff m n ).
  unfold adiff.
  destruct ( n<?m ) eqn: NM.
  destruct ( m<? n) eqn: MN.
  apply Nat.ltb_lt in NM.  apply Nat.ltb_lt in MN.

  
  apply Nat.lt_asymm in NM.
  contradiction.
  trivial.
  destruct ( m<? n) eqn: MN.
  trivial.
  apply Nat.ltb_ge in NM. 
  apply Nat.ltb_ge in MN.
  apply Nat.le_ngt in NM. 
  apply Nat.le_ngt in MN.
  lia.
Qed.  



Lemma take_true_term_from_or : forall A B : Prop,
  (A \/ B) -> (A -> False) -> B.
Proof.
  intros A B H H1.
  destruct H as [HA | HB].
  - exfalso. apply H1. exact HA.
  - exact HB.
Qed.

Lemma NoDup_tail {A:Type} {l: list A} (pf: NoDup l) :  (NoDup (tail l)).
destruct l.
- trivial.
- destruct pf.
  + simpl. apply NoDup_nil.
  +    simpl.
       trivial.
Defined.

Lemma two_representation {A: Type}{x  : A}{xs : list A} :   x::xs = [x] ++ xs.
  trivial.
Defined.



Lemma equal_list_equal_head {A: Type }{a b :A } (y : A) {l1 l2 : list A} (pf: a::l1= b::l2) : hd y (a::l1) = hd y (b::l2).  
  induction l1.
-  rewrite <- pf.  trivial.
-  rewrite <- pf.  trivial.
Defined.

Lemma equal_list_equal_tail {A: Type} {l1 l2 : list A} : l1= l2 -> tl l1 = tl l2.
  induction l1.
  - intro. rewrite <-H. trivial.
  - intro. rewrite <- H. trivial.
Defined.

Lemma equal_append {A : Type} {xs ys : list A}{x y : A} : xs++[x] = ys++[y] -> [x]++xs = [y]++ys.
  intro.
  apply app_inj_tail in H.
  destruct H.
  rewrite H0.
  rewrite H.
  trivial.
Defined.



Ltac hide_left := 
match goal with 
|- ?lhs = _ =>remember lhs
end.

Ltac hide_right := 
match goal with 
|- _ = ?rhs =>remember rhs
end.



Lemma in_map_filter_l_gives_in_l {A B: Type} {x : B} {l : list A} {f1 : A -> B} {f2 : A -> bool}
  : In x (map f1 (filter f2 l)) -> In x (map f1 l).
  intros.
  induction l.
  - contradiction. 
  - simpl in *.
    destruct (f2 a) eqn:Hf2.
    + (* Case: f2 a = true *)
      simpl in H. destruct H as [H | H].
      * left. assumption.
      * right. exact (IHl H). 
    + (* Case: f2 a = false *)
      right. exact (IHl H). 
Qed.

  


Lemma l_nil_filter_nil {A : Type} ( l : list A) (f : A -> bool ) : l= []-> filter f l = []  .
intros. rewrite H. simpl. trivial.
Defined. 

Lemma filter_nil_l {A : Type} {l : list A} {f : A -> bool} :
  filter f l = [] -> forall x, In x l -> f x = false.
  intros H x Hx.
  induction l as [| h t IH].
  - (* Base case: l = [] *)
    inversion Hx.
  - (* Inductive step: l = h :: t *)
    simpl in H.
    destruct (f h) eqn:Hfh.
    + (* Case: f h = true *)
      inversion H.
    + (* Case: f h = false *)
      destruct Hx as [Hx | Hx].
      * (* Case: x = h *)
        subst. assumption.
      * (* Case: x is in t *)
        apply IH; assumption.
Qed.


Lemma filter_length2 {A } {f : A -> bool} {lst : list A}:  length (filter f lst) <= (length lst).
induction lst. 
simpl. 
trivial. 

simpl. 
destruct (f a). 
simpl. apply le_n_S.  trivial.
apply le_S. 
trivial. 
Defined.




Lemma filter_length_is_length_minus_remaining
  { A : Type }
  (l  : list A )
  (f  : A -> bool )
  :
  length (filter (fun y=> f y) l ) = (length l) - (length ( filter (fun y => negb (f y)) l ) ) .

  induction l.
  - trivial.
  - simpl.
    destruct (f a) eqn:FA.
    -- simpl.
       destruct ( length (filter (fun y : A => negb (f y)) l) ) eqn:Lf.
       rewrite IHl. lia.
       rewrite IHl. 
       rewrite Nat.sub_succ_r.
      
       assert ( 0 < length l - n ).
       pose proof (@filter_length2 A (fun y : A => negb (f y)) l ).
       lia.
       rewrite (Nat.succ_pred).  trivial. lia.
    -- simpl. trivial.
Qed.    


Lemma filter_on_Nodup
  { A : Type }
  ( l : list A )
  (pf_l : NoDup l)
  ( f : A -> bool )
  : NoDup ( filter f l ).
  induction l.
  simpl in *. trivial.
  inversion pf_l.
  simpl.
  destruct (f a).
  pose proof (IHl H2).
  apply NoDup_cons.
  intro.
  apply filter_In in H4.
  inversion H4. contradiction.
  trivial.
  exact (IHl H2).
Qed.  


Lemma nodup_map_filter
  { A B : Type }
  { l : list A }
  { g : A -> bool }
  { f : A -> B }
  (pf_l : NoDup (map f l) )
  : NoDup (map f ( filter g l )).
  induction l.
  simpl in *. trivial.
  inversion pf_l.
  simpl. 
  destruct (g a).
  pose proof (IHl H2).
  simpl.
  apply NoDup_cons.
  intro.
  apply  in_map_filter_l_gives_in_l in H4.
  contradiction.
  trivial.
  exact (IHl H2).
Qed.  




Lemma filter_sublist_length_at_most_list_length
  { A : Type }
  {l  : list A }
  (f g : A -> bool )
  (pf_l : NoDup l)
  :
  let l1 :=  (filter f l ) in
  let l2 :=  (filter g l ) in
  incl l1 l2 -> length l1 <= length l2.

  induction l; intros.
  - simpl in *.
    lia.
  - inversion pf_l.
    simpl in *. 
    destruct (f a), (g a).
    assert ( incl (filter f l) (filter g l) ). {
      unfold l1 in H.
      unfold incl in H.
      unfold l2 in H.
      unfold incl.
      intros.
      unfold incl in H.
      assert ( In a0 (a::filter f l) ).
      apply in_cons; trivial.
      pose proof (H a0 H5).
      inversion H6.
      rewrite <- H7 in H4.
      apply filter_In in H4.
      inversion H4.
      contradiction.
      trivial.
    }
    pose proof (IHl H3 H4).
    unfold l1.
    unfold l2.
    unfold length in *.
    lia.

    unfold incl in H.
    assert ( In a l1).
    unfold l1. apply in_eq.
    pose proof (H a H4).
    unfold l2 in H5.
    apply filter_In in H5.
    inversion H5.
    contradiction.
    assert ( incl (filter f l) (filter g l) ).
    unfold incl.
    intros.
    unfold incl in H.
    pose proof (H a0 H4).
    unfold l2 in H5.
    inversion H5.
    rewrite <- H6 in H4.
    apply filter_In in H4.
    inversion H4. contradiction.
    trivial.
    pose proof (IHl H3 H4).
    unfold l1 , l2.
    unfold length in *.
    lia.
    exact (IHl H3 H).
Qed.    
    
Lemma filter_sublist_length_at_most_list_length_v2
  { A : Type }
  {l  : list A }
  (f g : A -> bool )
  (pf_l : NoDup l)
  :
  let l1 :=  (filter (fun y => andb (negb (f y))(negb (g y))) l ) in
  let l2 :=  (filter (fun y => negb (g y) ) l ) in
  incl l1 l2 -> length l1 <= length l2.

  induction l; intros.
  - simpl in *.
    lia.
  - inversion pf_l.
    simpl in *. 
    destruct (negb (f a)),(negb (g a)).
    assert (incl (filter (fun y : A => negb (f y) && negb (g y)) l)
          (filter (fun y : A => negb (g y)) l) ). {
      unfold l1 in H.
      unfold incl in H.
      unfold l2 in H.
      unfold incl.
      intros.
      unfold incl in H.
      simpl in H.
      assert ( a = a0 \/ In a0 (filter (fun y : A => negb (f y) && negb (g y)) l) ).
      right; trivial.
      pose proof (H a0 H5).
      inversion H6.
      rewrite <- H7 in H4.
      apply filter_In in H4.
      inversion H4.
      contradiction.
      trivial.
    }
    pose proof (IHl H3 H4).
    unfold l1.
    unfold l2.
    simpl.
    unfold length in *.
    lia.

    simpl in l1.
    exact (IHl H3 H).

    simpl in l1.
    assert (incl (filter (fun y : A => negb (f y) && negb (g y)) l)
              (filter (fun y : A => negb (g y)) l) ).
    { unfold incl in H.
      unfold incl.
      intros.
      pose proof (H a0 H4).
      unfold l2 in H5.
      inversion H5.
      rewrite <- H6 in H4.
      apply filter_In in H4.
      inversion H4.
      contradiction.
      trivial.
    }
    pose proof (IHl H3 H4).
    unfold l1, l2, length.
    unfold length in H5.
    lia.

    simpl in l1.
    exact (IHl H3 H).
Qed.
    




Lemma filter_length_dffrnt_means_extra_element
  { A : Type }
  {l  : list A }
  (f g : A -> bool )
  (pf_l : NoDup l)
  :
  let l1 :=  (filter f l ) in
  let l2 :=  (filter g l ) in
  length l1 <  length l2 ->
  (* Definition incl (l m:list A) := forall a:A, In a l -> In a m. *)
   ~ incl l2 l1.
(*  exists x, In x l2 /\ ~ In x l1. *)

  intros.
  intro.
  unfold incl in H0.
  unfold l1, l2 in H0.
  

  pose proof (filter_sublist_length_at_most_list_length  g f pf_l H0).
  unfold l1, l2 in H.
  lia.

  
Qed.


Lemma filter_andb_eq_filter_on_filter
  { A : Type }
  ( l : list A )
  (f g : A -> bool )
  : filter (fun y => andb (f y) (g y)  ) l  = filter (fun y=>  g y) (filter (fun z =>  f z ) l). 
  induction l.
  trivial.
  simpl. 
  destruct (g a ) eqn: GA.
  destruct ( f a) eqn: FA.
  simpl.
  rewrite GA.
  rewrite IHl.
  trivial.
  simpl.
  trivial.
  destruct ( f a) eqn: FA. 
  simpl.
  rewrite GA.
  trivial.
  simpl.
  trivial.
Qed.  


Lemma filter_commutative
  { A : Type }
  ( l : list A )
  (f g : A -> bool )
  : filter f  (filter g l)   = filter g (filter f l). 
  induction l.
  trivial.
  simpl.  
  destruct (g a ) eqn: GA.
  destruct ( f a) eqn: FA.
  simpl.
  rewrite GA.
  rewrite FA.
  rewrite IHl.
  trivial.
  simpl.
  rewrite FA.
  trivial.
  destruct ( f a) eqn: FA. 
  simpl.
  rewrite GA.
  trivial.
  simpl.
  trivial.
Qed.  


Lemma forall_f_true_means_filter_fl_eq_l
  { A : Type }
  ( l : list A )
  (f  : A -> bool )
  (pf : forall a, In a l-> f a = true ) : filter f l = l.
  induction l.
  trivial.
  simpl.
  destruct (f a) eqn:FA.
  assert (forall a : A, In a l -> f a = true). {
    intros.
    assert ( In a0 (a::l) ).
    apply in_cons. trivial.
    exact (pf a0 H0).
  }
  rewrite (IHl H).
  trivial.
  assert ( In a (a::l) ) by apply in_eq.
  pose proof (pf a H ).
  rewrite FA in H0.
  inversion H0.
Qed.    



Lemma filter_andb_eq_filter_on_filter_negb
  { A : Type }
  ( l : list A )
  (f g : A -> bool )
  : filter (fun y => andb (negb (f y)) (negb (g y) )  ) l
    = filter (fun y=> negb (g y)) (filter (fun z =>  negb (f z) ) l). 
  induction l.
  trivial.
  simpl. 
  destruct (negb (g a )) eqn: GA.
  destruct (negb ( f a)) eqn: FA.
  simpl.
  rewrite GA.
  rewrite IHl.
  trivial.
  simpl.
  trivial.
  destruct (negb ( f a)) eqn: FA. 
  simpl.
  rewrite GA.
  trivial.
  simpl.
  trivial.
Qed.  


Lemma filter_f_negb_f_are_disjoint
  { A : Type }
  { x : A }
  ( l : list A )
  ( f : A -> bool )
  ( pf : decidable (In x l) )
  : 
    In x l -> ( In x (filter f l) <-> ~ In x (filter (fun y=> negb (f y)) l ) )
                /\ ( ~ In x (filter f l) <->  In x (filter (fun y=> negb (f y)) l ) ).
Proof.
  intros. 
  destruct (f x ) eqn:FA.
  - repeat split.
    --
      intros.
      intro.  
      apply filter_In in H1.
      inversion H1.
      rewrite FA in H3.
      inversion H3.
    -- intros. apply filter_In.
       split; trivial.
    --
      intros.
      rewrite filter_In in H0. 
     
      apply not_and in H0.
      inversion H0.
      contradiction. 
      rewrite FA in H1.
      exfalso.
      apply H1. trivial.

      trivial.
    --
      intros.
      apply filter_In in H0.
      inversion H0.
      rewrite FA in H2.
      inversion H2.
  - repeat split.
    -- 
      intros.
      intro.
      apply filter_In in H0.
      inversion H0.
      rewrite H3 in FA.
      inversion FA.
    --
      intros.      rewrite filter_In in H0. 
      apply not_and in H0.
      inversion H0.
      contradiction. 
      rewrite FA in H1.
      exfalso.
      apply H1. trivial.

      trivial.

    --
      intros.
      apply filter_In.
      split; trivial.
      rewrite FA.
      trivial.
    --
      intros.
      intro.
      apply filter_In in H1.
      inversion H1.
      rewrite H3 in FA; inversion FA.
Qed.

Lemma length_of_filter_FandGorH_eq_length_of_FandG_plus_FandH
  { A : Type }
  { l : list A }
  { f g h : A -> bool }
  ( pf_l : forall y, In y l -> (f y && g y) = true -> (h y) = true)
                                
  : length ( filter (fun y => f y && ( g y || negb (h y)) ) l )
    = length ( filter (fun y => f y && g y ) l)
      + length ( filter (fun y => f y && negb (h y)) l).
Proof.
  induction l.
  - trivial.
  - simpl.
    assert ((forall y : A,
         In y l ->
         (f y && g y = true -> h y = true) )).
    { intros. assert (In y (a:: l) ).  apply in_cons. trivial.
      exact (pf_l y H1 H0).
    }
    pose proof (IHl H).
    assert ( In a (a::l) ) by apply in_eq. 
    pose proof (pf_l a H1) as pf_l1.
    clear pf_l IHl H.

    destruct (f a ) eqn:FA.
    --
      destruct ( g  a) eqn:GA.
      ---
        destruct ( h  a) eqn:HA.
        ---- simpl.
             lia.        
        ---- simpl.
             assert (true && true = true) by trivial.
             pose proof (pf_l1 H).
             inversion H2.
      ---
        destruct ( h  a) eqn:HA.
        ---- simpl.
             lia.        
        ---- simpl. lia.
    -- simpl. trivial.
Qed.


Lemma not_in_filter_and_filter_negb_implies_not_in_l
  { A : Type }
  { x : A }
  ( l : list A )
  ( f : A -> bool )
  :
  (~ In x (filter f l)) /\ (~ In x (filter (fun y=> negb (f y)) l ) ) -> ~ In x l.
  intros.
  inversion H.
  assert ( In x l -> In x (filter f l) \/ In x (filter (fun y : A => negb (f y)) l) ).
  { intros.
    destruct (f x) eqn:FX.
    left. apply filter_In.
    split; trivial.
    right.
    apply filter_In.
    rewrite FX.
    split; trivial.
  }
  intro.
  pose proof (H2 H3).
  inversion H4; contradiction.
Qed.



  
Lemma triangular_ineq (x y g d1 d2: nat) : adiff  g x <= d1
                                  /\ adiff  g y <= d2
                                       -> adiff x y <= d1+d2.
  unfold adiff.
  intros.
  inversion H.
  destruct ( x <? y) eqn:xy.
  - destruct ( g <? x) eqn:xg.
    -- destruct ( g <? y) eqn:yg.
       apply Nat.ltb_lt in xg.
       apply Nat.ltb_lt in yg. 
       apply Nat.ltb_lt in xy.
       lia.
       apply Nat.ltb_lt in xg.
       apply Nat.ltb_lt in xy.
       apply Nat.ltb_ge in yg.
       lia.
    -- destruct ( g <? y) eqn:yg.
       apply Nat.ltb_lt in  yg.
       apply Nat.ltb_lt in  xy.
       apply Nat.ltb_ge in xg.
       lia.
       apply Nat.ltb_lt in  xy.
       apply Nat.ltb_ge in xg.
       apply Nat.ltb_ge in yg.
       lia.
  - destruct ( g <? x) eqn:xg.
    -- destruct ( g <? y) eqn:yg.
       apply Nat.ltb_lt in xg.
       apply Nat.ltb_lt in yg.
       apply Nat.ltb_ge in xy.
       lia.
       apply Nat.ltb_lt in xg.
       apply Nat.ltb_ge in yg.
       apply Nat.ltb_ge in xy.
       lia.
    -- destruct ( g <? y) eqn:yg.
       apply Nat.ltb_lt in  yg.
       apply Nat.ltb_ge in xg.
       apply Nat.ltb_ge in xy.
       lia.
       apply Nat.ltb_ge in xg.
       apply Nat.ltb_ge in yg.
       apply Nat.ltb_ge in xy.
       lia.
Qed.

Lemma filter_negb_negb_f_is_f
  {A : Type }
  (l : list A)
  (f : A -> bool )
  : filter (fun y=> negb (negb (f y)) ) l
    = filter (fun y => f y) l.
  induction l.
  trivial.
  simpl.
  rewrite negb_involutive.
  destruct (f a).
  f_equal; trivial.
  trivial.
Qed.




Lemma cons_eq_app : forall (A : Type) (z : A) (xs ys zs : list A),
  z :: zs = xs ++ ys ->
  (exists qs, xs = z :: qs /\ zs = qs ++ ys) \/
  (xs = nil /\ys = z :: zs).
Proof.
  destruct xs; intros ? ? H; simpl in H. 
    auto. 
    injection H. intros. subst. eauto.
Qed.

Lemma app_eq_cons : forall  (A : Type) (z : A) (xs ys zs : list A),
  xs ++ ys = z :: zs ->
  (exists qs, xs = z :: qs /\ zs = qs ++ ys) \/
  (xs = nil /\ ys = z :: zs).
Proof. auto using cons_eq_app. Qed.

Lemma all_prevous_to_head_of_filter_fun_a_is_false
  { A: Type }
  { x : A}
  { l l1 l2 xs: list A }
  { f : A -> bool }
  (pf_ND : NoDup l)
  (pf_l : l = l1++x::l2)
  (pf_f : filter (fun y => f y) l = x::xs)
  : filter( fun y=> f y) l1 = [].
  
  rewrite pf_l in *.
  clear pf_l l.
  rewrite filter_app in pf_f.
  apply app_eq_cons in pf_f.
  inversion pf_f as [[l3 [Hl1eq Hxseq]] | [Hl1nil Hfrem]].
  - apply NoDup_remove_2 in pf_ND.
    rewrite in_app_iff in pf_ND.
    exfalso. apply pf_ND.
    assert (In x ( filter (fun y : A => f y) l1) ) as Hinfl1. {
      rewrite Hl1eq. apply in_eq.
    }
    apply filter_In in Hinfl1. inversion Hinfl1.
    auto.
  - auto.
Qed.    
