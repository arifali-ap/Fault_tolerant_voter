Require Import  Nat.      
Require Import Bool.    
Require Import List. 
Import ListNotations.
Require Import Lia.
Import Arith.
Require Import Coq.Logic.Eqdep_dec.
Require Import BTProject.config.
Require Import BTProject.voter_state.
Require Import BTProject.library_using_list.
Require Import BTProject.gen_lemmas.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Decidable.
Require Import Coq.Logic.Decidable.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Init.Specif.  (* For surjective_pairing *)



Definition get_u_outputs_from_combined_list ( x : list (unit_output * unit_data )) : list unit_output :=
   (map ( fun f => fst f) x).    

Definition combine_lists
  { A B C : Type }
  { f  : B -> A}
  { g  : C -> A}
  {u_ids : list A} (pf_uids: NoDup u_ids)
  { input : list B } (pf_input :  map f input =  u_ids )
  { ud_lst : list C } (pf_ud_lst :  map g ud_lst =  u_ids  )
  : list (B * C) :=
  combine input ud_lst.


Lemma second_of_combine_lists_is_l2
  { A B C : Type }
  { f  : B -> A}
  { g  : C -> A}
  {u_ids : list A} (pf_uids: NoDup u_ids)
  { input : list B } (pf_input :  map f input =  u_ids )
  { ud_lst : list C } (pf_ud_lst :  map g ud_lst =  u_ids  )
 : map (fun h=> snd h) (combine_lists pf_uids pf_input pf_ud_lst) = ud_lst.
Proof.
  unfold combine_lists.
  generalize dependent input.
  generalize dependent u_ids.
  induction ud_lst; intros.
  - simpl in pf_ud_lst. 
    rewrite <- pf_ud_lst in pf_input.
    unfold get_u_ids_of_unit_output in pf_input.
    apply map_eq_nil in pf_input.
    rewrite pf_input; trivial.
  - destruct input, u_ids.
    -- inversion pf_ud_lst.
    -- inversion pf_input.
    -- inversion pf_input.
    --
      inversion pf_uids.
      inversion pf_input.
      inversion pf_ud_lst.
      
       simpl. f_equal. exact (IHud_lst u_ids H2 H7 input H5).
Qed.

Lemma first_of_combine_lists_is_l1
  { A B C : Type }
  { f  : B -> A}
  { g  : C -> A}
  {u_ids : list A} (pf_uids: NoDup u_ids)
  { input : list B } (pf_input :  map f input =  u_ids )
  { ud_lst : list C } (pf_ud_lst :  map g ud_lst =  u_ids  )
  : map (fun h=> fst h) (combine_lists pf_uids pf_input pf_ud_lst) = input.
Proof.
  unfold combine_lists.
  generalize dependent input.
  generalize dependent u_ids.
  induction ud_lst; intros.
  - simpl in pf_ud_lst. 
    rewrite <- pf_ud_lst in pf_input.
    unfold get_u_ids_of_unit_output in pf_input.
    apply map_eq_nil in pf_input.
    rewrite pf_input; trivial.
  - destruct input, u_ids.
    -- inversion pf_ud_lst.
    -- inversion pf_input.
    -- inversion pf_input.
    --
      inversion pf_uids.
      inversion pf_input.
      inversion pf_ud_lst.
      
       simpl. f_equal. exact (IHud_lst u_ids H2 H7 input H5).
Qed.



Lemma combine_lists_gen_props
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  ) 
  :
  let combl := (combine_lists pf_uids pf_input pf_ud_lst) in 
  forall x, In x combl  <->
         ( uid (fst x) = uid (u_output (snd x))
           /\ In (fst x) input /\ In (snd x) ud_lst ).
  split.
  {
    intros.
    unfold combine_lists in H.
    generalize dependent ud_lst.
    generalize dependent u_ids. 
    induction input; intros.
    -  
      simpl in pf_input.
      rewrite <- pf_input in pf_ud_lst.
      apply map_eq_nil in pf_ud_lst.
      rewrite pf_ud_lst in H. 
      inversion H.
    -  destruct u_ids, ud_lst.
       --
         apply map_eq_nil in pf_input.
         inversion pf_input.
       --
         apply map_eq_nil in pf_ud_lst.
         inversion pf_ud_lst.
       --
         simpl in pf_ud_lst.
         inversion pf_ud_lst.
       -- inversion pf_uids.
          inversion pf_input.
          inversion pf_ud_lst.
          inversion H.
          ---
            rewrite <- H4.
            unfold fst, snd.
            repeat split.
            rewrite H7; trivial.
            apply in_eq.
            apply in_eq.
          --- pose proof (IHinput u_ids H3
                            H6 ud_lst H8 H4).
              inversion H9 as [H9a [H9b H9c]].
              repeat split; trivial.
              apply in_cons; trivial.
              apply in_cons; trivial.
  }
  {
    intros.
    generalize dependent u_ids.
    generalize dependent input.
    induction ud_lst; intros.
    -- 
      inversion H as [H1 [H2 H3]]. inversion H3.
    -- 
      inversion H as [H1 [H2 H3]].
      destruct input, u_ids.
      --- inversion H2.
      --- inversion H2.
      --- inversion pf_ud_lst.
      --- inversion pf_uids.
          inversion pf_input.
          inversion pf_ud_lst.
          unfold combine_lists.
          simpl.
          inversion H2.
          ----
            inversion H3.
            ----- left. rewrite H7; rewrite H12.
            symmetry.
            apply surjective_pairing.
            -----
             
            assert ( In (uid u) (get_u_ids_of_unit_data ud_lst)).
            { unfold get_u_ids_of_unit_data.
              apply in_map_iff.
              exists (snd x).
              split. rewrite <- H1.
              rewrite H7. trivial.
              trivial.
            }
            rewrite H11 in H13.
            rewrite H8 in H13. contradiction.
          ----
            inversion H3. 
            -----  
            assert ( In u0 (get_u_ids_of_unit_output input)).
            { unfold get_u_ids_of_unit_output.
              apply in_map_iff.
              exists (fst x).
              split. rewrite H1.
              rewrite <- H12.
              trivial.
              trivial.
            }
            rewrite H9 in H13.
            contradiction.
            -----  right.
            assert (uid (fst x) = uid (u_output (snd x)) /\ In (fst x) input
                    /\ In (snd x) ud_lst ). {
              repeat split; trivial. }
            pose proof ( IHud_lst input H13 u_ids H6 H9 H11).
            unfold combine_lists in H14. trivial.
  }
Qed.

Lemma combine_lists_gen_props_data
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids )
  { new : list unit_data } (pf_new :  get_u_ids_of_unit_data new =  u_ids  ) 
  :
  let combl := (combine_lists pf_uids pf_ud_lst pf_new) in 
  forall x, In x combl  <->
         ( uid (u_output (fst x)) = uid (u_output (snd x))
           /\ In (fst x) ud_lst /\ In (snd x) new ).
  split.
  {
    intros.
    unfold combine_lists in H.
    generalize dependent new.
    generalize dependent u_ids. 
    induction ud_lst; intros.
    -   
      simpl in pf_ud_lst.
      rewrite <- pf_ud_lst in pf_new.
      apply map_eq_nil in pf_new.
      rewrite pf_new in H. 
      inversion H.
    -  destruct u_ids, new.
       --
         apply map_eq_nil in pf_ud_lst.
         inversion pf_ud_lst.
       --
         apply map_eq_nil in pf_new.
         inversion pf_new.
       --
         simpl in pf_new.
         inversion pf_new.
       -- inversion pf_uids.
          inversion pf_ud_lst.
          inversion pf_new.
          inversion H.
          ---
            rewrite <- H4.
            unfold fst, snd.
            repeat split.
            rewrite H7; trivial.
            apply in_eq.
            apply in_eq.
          --- pose proof (IHud_lst u_ids H3
                            H6 new H8 H4).
              inversion H9 as [H9a [H9b H9c]].
              repeat split; trivial.
              apply in_cons; trivial.
              apply in_cons; trivial.
  }
  {
    intros.
    generalize dependent u_ids.
    generalize dependent ud_lst.
    induction new; intros.
    -- 
      inversion H as [H1 [H2 H3]]. inversion H3.
    -- 
      inversion H as [H1 [H2 H3]].
      destruct ud_lst, u_ids.
      --- inversion H2.
      --- inversion H2.
      --- inversion pf_new.
      --- inversion pf_uids.
          inversion pf_ud_lst.
          inversion pf_new.
          unfold combine_lists.
          simpl.
          inversion H2.
          ----
            inversion H3.
            ----- left. rewrite H7; rewrite H12.
            symmetry.
            apply surjective_pairing.
            -----
             
            assert ( In (uid (u_output u)) (get_u_ids_of_unit_data new)).
            { unfold get_u_ids_of_unit_data.
              apply in_map_iff.
              exists (snd x).
              split. rewrite <- H1.
              rewrite H7. trivial.
              trivial.
            }
            rewrite H11 in H13.
            rewrite H8 in H13. contradiction.
          ----
            inversion H3. 
            -----  
            assert ( In u0 (get_u_ids_of_unit_data ud_lst)).
            { unfold get_u_ids_of_unit_data.
              apply in_map_iff.
              exists (fst x).
              split. rewrite H1.
              rewrite <- H12.
              trivial.
              trivial.
            }
            rewrite H9 in H13.
            contradiction.
            -----  right.
            assert (uid (u_output (fst x)) = uid (u_output (snd x)) /\ In (fst x) ud_lst
                    /\ In (snd x) new ). {
              repeat split; trivial. }
            pose proof ( IHnew ud_lst H13 u_ids H6 H9 H11).
            unfold combine_lists in H14. trivial.
  }
Qed.
Lemma fst_comb_lst_is_nodup
{ A B C : Type }
  { f1  : B -> A}
  { g  : C -> A}
  {u_ids : list A} (pf_uids: NoDup u_ids)
  { input : list B } (pf_input :  map f1 input =  u_ids )
  { ud_lst : list C } (pf_ud_lst :  map g ud_lst =  u_ids  )
  (f : B*C -> bool )
  :
  NoDup (map (fun h=> fst h) (filter f (combine_lists pf_uids pf_input pf_ud_lst)) ).

  assert (NoDup (map (fun h=> fst h) (combine_lists pf_uids pf_input pf_ud_lst) )).
  rewrite (first_of_combine_lists_is_l1 ).
  rewrite <-pf_input in pf_uids.  
  apply NoDup_map_inv in pf_uids. trivial. 
  exact ( nodup_map_filter  H ).
Qed.  
  
Lemma map_on_snd_comb_lst_fltr_is_nodup
  { A B C : Type }
  { f1  : B -> A}
  { g  : C -> A}
  {u_ids : list A} (pf_uids: NoDup u_ids)
  { input : list B } (pf_input :  map f1 input =  u_ids )
  { ud_lst : list C } (pf_ud_lst :  map g ud_lst =  u_ids  )
  {f : B*C -> bool }
  :
  NoDup (map g  (map (fun h=>  (snd h)) (filter f (combine_lists pf_uids pf_input pf_ud_lst)) )).

  remember (combine_lists pf_uids pf_input pf_ud_lst) as l.
  assert (NoDup (map g  (map (fun h=>  (snd h)) l ))).
  rewrite Heql.
  rewrite (second_of_combine_lists_is_l2 ).
  rewrite pf_ud_lst.  trivial.
  
  assert ( map (fun h => g (snd h)) l = map g ( map (fun h=> snd h) l ) ).
  { rewrite map_map. trivial. }
  rewrite <- H0 in H.
  rewrite map_map.
 
  exact ( nodup_map_filter H ).
Qed.  




Lemma combine_lst_nodup
{ A B C : Type }
  { f  : B -> A}
  { g  : C -> A}
  {u_ids : list A} (pf_uids: NoDup u_ids)
  { input : list B } (pf_input :  map f input =  u_ids )
  { ud_lst : list C } (pf_ud_lst :  map g ud_lst =  u_ids  ):
  NoDup  (combine_lists pf_uids pf_input pf_ud_lst).

  pose proof pf_uids.
  rewrite <- (pf_ud_lst) in H.
  apply NoDup_map_inv in H.
  
  rewrite <- ( second_of_combine_lists_is_l2 pf_uids pf_input pf_ud_lst) in H.
  apply NoDup_map_inv in H.
  trivial.
Qed.  


Definition hw_good_comb_check  (x : unit_output * unit_data)  : bool :=
  andb (not_iso_check (snd x)) ( hw_good_unit_check (fst x)).





(* List of good units from non isolated list *)
Definition hw_good_comb_lst  (l :list ( unit_output * unit_data)) : list  (unit_output * unit_data) :=
  filter (fun y=> hw_good_comb_check y) l.


Definition non_isltd_comb_lst  (l :list ( unit_output * unit_data)) : list  (unit_output * unit_data) :=
  filter (fun y=> not_iso_check (snd y)) l.


Lemma all_non_isltd (l : list (unit_output* unit_data) )
  : let non_iso_l := non_isltd_comb_lst l in
    forall x, In x non_iso_l -> (iso_status (u_status (snd x) ) ) = not_isolated.
  intros.
  unfold non_iso_l in H.
  unfold non_isltd_comb_lst in H.
  apply filter_In in H.
  inversion H.
  unfold not_iso_check in H1.
  destruct (iso_status (u_status (snd x))).
  inversion H1.
  trivial.
Qed.




Definition all_good_non_iso_lst
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  ) 
  : { l : list unit_output | Forall (fun x => In x input /\ In (uid x) (get_u_ids_of_unit_data (non_isolated_list ud_lst)) /\ hw_hlth (reading x) = good) l }.
  refine ( 
      let non_isltd_comb        := non_isltd_comb_lst
                                     (combine_lists  pf_uids pf_input pf_ud_lst) in
      let non_isltd_unit_outs   := map (fun x => (fst x) ) non_isltd_comb  in
      let good_outs             := filter (fun y => hw_good_unit_check y)
                                     non_isltd_unit_outs in
      exist _ good_outs _
    ).
  Proof.
  apply Forall_forall.
  intros.
  unfold good_outs in H.
  apply filter_In in H.
  inversion H.
  unfold non_isltd_unit_outs in H0.
  apply in_map_iff in H0.
  assert (get_u_ids_of_unit_output input = get_u_ids_of_unit_data ud_lst).
  rewrite pf_ud_lst. trivial.
  assert (  pf_nodup : NoDup (get_u_ids_of_unit_output input ) ).
  rewrite pf_input; trivial.  
  inversion H0 as [y [Hy1 Hy2]].
  
  unfold non_isltd_comb in Hy2. 
  unfold non_isltd_comb_lst in Hy2.
  apply filter_In in Hy2.
  inversion Hy2.
  pose proof ( combine_lists_gen_props pf_uids pf_input pf_ud_lst y).
  inversion H5 as [H3a H3b].
  pose proof (H3a H3).
  inversion H6 as [H4a [H4b H4c]]. 
 
  repeat split.
  rewrite <- Hy1; trivial.
  unfold get_u_ids_of_unit_data.
  apply in_map_iff.
  
  exists (snd y).
 
  split. {
    rewrite <- H4a. rewrite Hy1. trivial.
  }
  unfold non_isolated_list.
  apply filter_In.
  split; trivial.

  unfold hw_good_unit_check in H1.
  destruct (hw_hlth (reading x)).
  inversion H1.
  trivial.
Defined.
  
Definition num_of_bad_and_non_isolated
  { u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  ) :=
  let comb_lst := combine_lists  pf_uids pf_input pf_ud_lst in
  let not_iso_output_lst := map (fun x => fst x)
                              ( filter (fun y => not_iso_check (snd y) ) comb_lst) in
  let bad_non_iso_lst := filter (fun y => negb (hw_good_unit_check y) )
                           not_iso_output_lst in
  length ( bad_non_iso_lst ).

Lemma noDup_non_iso_good_lst
        
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  
  :
  let  l := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
  NoDup l.

Proof.    unfold l.   
    unfold all_good_non_iso_lst.
    simpl.
    unfold get_u_outputs_from_combined_list.
    assert ( NoDup ud_lst).
    { assert (NoDup (get_u_ids_of_unit_data ud_lst)).
      rewrite pf_ud_lst. trivial.
      unfold get_u_ids_of_unit_data in H.
      apply NoDup_map_inv in H.
      trivial.
    }
    
    assert ( NoDup input).
    { assert (NoDup (get_u_ids_of_unit_output input)) as Ni.
      rewrite pf_input. trivial.
      unfold get_u_ids_of_unit_output in Ni.
      apply NoDup_map_inv in Ni.
      trivial.
    } 
    pose proof (combine_lst_nodup pf_uids pf_input pf_ud_lst ).
      
    assert ( NoDup (non_isltd_comb_lst (combine_lists  pf_uids pf_input pf_ud_lst)) ). {
      unfold non_isltd_comb_lst. 
      exact (NoDup_filter (fun y : unit_output * unit_data => not_iso_check (snd y))  H1). }
    assert ( NoDup  (map (fun x0 : unit_output * unit_data => fst x0)
          (non_isltd_comb_lst
             (combine_lists  pf_uids pf_input pf_ud_lst))) ). {
    unfold non_isltd_comb_lst.  
      
    exact (fst_comb_lst_is_nodup
             pf_uids pf_input pf_ud_lst
             (fun y : unit_output * unit_data => not_iso_check (snd y))
              ).
    }
    exact (NoDup_filter (fun y : unit_output => hw_good_unit_check y) H3 ). 
Qed.  

Lemma noDup_uids_of_non_iso_good_lst
        
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  
  :
  let  l := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
  NoDup (get_u_ids_of_unit_output l).

Proof.
  generalize dependent u_ids.
  generalize dependent input.
  simpl in *.
  unfold combine_lists in *. 
  induction ud_lst; intros.
  -      
    simpl in *.
    pose proof pf_input.
    rewrite <- pf_ud_lst in H.
    apply map_eq_nil in H.
    rewrite H.
    simpl.
    apply NoDup_nil.
      -
        simpl in *.
        destruct u_ids, input.
        -- inversion pf_ud_lst.
        -- inversion pf_ud_lst.
        -- inversion pf_input.
        -- inversion pf_ud_lst.
           inversion pf_input.
           inversion pf_uids.
           simpl.
           destruct (not_iso_check a).
           simpl.
           destruct (hw_good_unit_check u0).
           simpl.
           pose proof (IHud_lst input u_ids H6 H3 H1). 
           apply NoDup_cons.
           intro.
           apply in_map_iff in H8.
           inversion H8 as [z [Hzuid Hzin]].
           apply filter_In in Hzin.
           inversion Hzin as [Hzinmap T].
           apply in_map_iff in Hzinmap.
           inversion Hzinmap as [zp [Hzpeqz HzpinNSC]].
           apply filter_In in HzpinNSC.
           inversion HzpinNSC as [HzpinC T2].
           pose proof (combine_lists_gen_props
                         H6 H3 H1 zp) as [[Hzpuid [Hzpinput Hzpud_lst]] T3] .
           exact HzpinC.
           rewrite Hzpeqz in Hzpinput.
           assert (In u u_ids). {
             rewrite <- H2.
             rewrite <- Hzuid.
             rewrite <- H3.
             apply in_map_iff.
             exists z.
             split; trivial. }
           contradiction.
           trivial.
           exact (IHud_lst input u_ids H6 H3 H1).
           
           exact (IHud_lst input u_ids H6 H3 H1).
Qed.




Lemma map_and_filter_on_fst_of_comb_list_is_equal_to_that_of_l1
  { A B C : Type }
  { f  : B -> A}
  { g  : C -> A}
  {u_ids : list A} (pf_uids: NoDup u_ids)
  { input : list B } (pf_input :  map f input =  u_ids )
  { ud_lst : list C } (pf_ud_lst :  map g ud_lst =  u_ids  )
  ( h   : B -> bool)
  : map (fun y => fst y) ( filter (fun y => h (fst y)) (combine_lists pf_uids pf_input pf_ud_lst) ) = filter (fun y => h y) input.
  generalize dependent u_ids.
  generalize dependent ud_lst.
  induction input.
  - trivial.
  - intros.
    destruct u_ids, ud_lst.
    -- inversion pf_input.
    -- inversion pf_input.
    -- inversion pf_ud_lst.
    -- inversion pf_input.
       inversion pf_uids.
       inversion pf_ud_lst.
       unfold combine_lists.
       simpl.
       destruct (h a).
       simpl.
       f_equal.
       exact (IHinput ud_lst u_ids H4 H1 H7).
       exact (IHinput ud_lst u_ids H4 H1 H7).
Qed.       
