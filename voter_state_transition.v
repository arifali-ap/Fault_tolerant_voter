From Stdlib Require Import  Nat.     
From Stdlib Require Import Bool.    
From Stdlib Require Import List. 
Import ListNotations.
From Stdlib Require Import Lia. 
Import Arith.
From Stdlib Require Import Logic.Eqdep_dec.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Logic.Decidable.
From Stdlib Require Import Logic.Decidable.
From Stdlib Require Import Classes.DecidableClass.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Classical.
From Stdlib Require Import Logic.Classical_Prop.

Require Import BTProject.config.
Require Import BTProject.voter_state.
Require Import BTProject.library.
Require Import BTProject.gen_lemmas.
Require Import BTProject.build_updated_u_data_lst.
Require Import BTProject.prime_switch.
Require Import BTProject.invalidate.
Require Import BTProject.find_faulty.
Require Import BTProject.combine.


Lemma pf_age_satisfied_bad_case
  {vs : voter_state}
  {lsd : list unit_data}
  (pf_lsd : get_u_ids_of_unit_data lsd = l u_ids )
  {x : unit_data}
  (pf_x :  uid (voter_output vs) = get_u_id_of_unit_data x
                          /\ In x lsd)
  (pf_h : hw_hlth (reading (u_output x)) = bad)
  :   S (output_age vs) = 0 <->  
        valid = valid /\ In (presrvd_data vs) lsd.
  
  repeat split.  
  - inversion H.
  - intro. inversion H as [Hvld Hin].
    inversion pf_x as [Huid Hxin].
    pose proof (pf_presrvd_data vs) as [Heqout [Hgd [Hniso Hnmis]]].
    assert ( uid (voter_output vs) = get_u_id_of_unit_data (presrvd_data vs) )
      as Heqid.
    { unfold get_u_id_of_unit_data. rewrite Heqout. trivial. }
    rewrite Huid in Heqid.
    assert (x = presrvd_data vs)
      as Hxeq by exact  (fun_out_same_means_same_element_of_lst
                           x Heqid Hxin Hin (mapped_list_nodup pf_lsd (pf_l u_ids))). 
    rewrite <- Hxeq in Hgd.
    rewrite Hgd in pf_h.
    inversion pf_h.
Qed.

Lemma pf_age_satisfied_mis_case
  {vs : voter_state}
  {lsd : list unit_data}
  (pf_lsd : get_u_ids_of_unit_data lsd = l u_ids )
  {x : unit_data}
  (pf_x :  uid (voter_output vs) = get_u_id_of_unit_data x
           /\ In x lsd)
  (pf_m : miscomp_status (u_status x) <> not_miscomparing)
  :   S (output_age vs) = 0 <->  
        valid = valid /\ In (presrvd_data vs) lsd.

  repeat split.  
  - inversion H.
  - intro. inversion H as [Hvld Hin].
    inversion pf_x as [Huid Hxin].
    pose proof (pf_presrvd_data vs) as [Heqout [Hgd [Hniso Hnmis]]].
    assert ( uid (voter_output vs) = get_u_id_of_unit_data (presrvd_data vs) )
      as Heqid.
    { unfold get_u_id_of_unit_data. rewrite Heqout. trivial. }
    rewrite Huid in Heqid.
    assert (x = presrvd_data vs)
      as Hxeq by exact  (fun_out_same_means_same_element_of_lst
                           x Heqid Hxin Hin (mapped_list_nodup pf_lsd (pf_l u_ids))).
    rewrite Hxeq in pf_m.
    contradiction.
Qed.


Lemma vs_is_valid
  {vs : voter_state}
  {all_unit_outputs : list unit_output}
  {pf_all_unit_outputs : get_u_ids_of_unit_output all_unit_outputs = l u_ids}
  {lsd : list unit_data}
  (pf_lsd : lsd = build_updated_u_data_lst (pf_l u_ids)
                    pf_all_unit_outputs (pf_ud_lst vs) )
  (pf_min_req :  min_required <= count_of_non_isolated_units lsd)
  {prm_unt : unit_data}
  (pf_prm_unt :  uid (voter_output vs) = get_u_id_of_unit_data prm_unt
                 /\ In prm_unt lsd)
  (pf_iso : iso_status (u_status prm_unt) = not_isolated)
  :  voter_validity vs = valid.
  
Proof.
   pose proof (pf_validity vs) as [[Hnv1 Hnv2][[Huid1 Hud2] Hhlnil]].
   
  assert (voter_validity vs <> not_valid ). {
    intro not. pose proof (Hnv2 not).
    pose proof ( build_updated_u_data_lst_do_not_increase_non_isolated_units
                   (pf_l u_ids)
                   pf_all_unit_outputs
                   (pf_ud_lst vs)
      ) as Hnonisocnt.  
    assert (min_required <= count_of_non_isolated_units (u_data_lst vs) ). 
    rewrite <- pf_lsd in Hnonisocnt.
    apply (Nat.le_trans
             min_required
             (count_of_non_isolated_units lsd)
             (count_of_non_isolated_units (u_data_lst vs))
             pf_min_req Hnonisocnt ).
    apply Nat.le_ngt in H0.
    contradiction.
  }

  inversion pf_prm_unt.
  assert (In (uid (u_output prm_unt))
              (get_u_ids_of_unit_data (non_isolated_list (lsd)))) as Hnisonw.
  { unfold get_u_ids_of_unit_data. apply in_map_iff.
    exists prm_unt.
    split; trivial.
    apply filter_In.
    split; trivial.
    unfold not_iso_check.
    rewrite pf_iso. trivial.
  }
  rewrite  pf_lsd in Hnisonw.
  pose proof ( not_isolated_after_update_implies_not_isolated_before
                 (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                 (uid (u_output prm_unt))  Hnisonw) as Hnisovs.
  unfold get_u_id_of_unit_data in Hnisovs.
  assert (voter_validity vs <> un_id ). {
    intro Hunid. pose proof (Hud2 Hunid) as  [Hcntge Houtiso].
    apply in_map_iff in Houtiso.
    inversion Houtiso as [y [Hyuid Hyiniso]].
    
    assert ( In (uid (u_output y))
               (get_u_ids_of_unit_data (non_isolated_list (u_data_lst vs))) )
      as  Hyniso. {
      rewrite Hyuid. rewrite H0; trivial.
    }
    apply in_map_iff in Hyniso.
    inversion Hyniso as [y1 [Hy1uid Hy1in]].
    apply filter_In in Hy1in, Hyiniso.
    inversion Hy1in as [Hy1inpq Hy1iso].
    inversion Hyiniso as [Hyinpq Hyiso].
    assert(y1 = y) as Hy1eqy
        by exact (fun_out_same_means_same_element_of_lst y1 Hy1uid Hy1inpq Hyinpq
                    (mapped_list_nodup (pf_ud_lst vs) (pf_l u_ids))).
    rewrite Hy1eqy in Hy1iso.
    rewrite Hy1iso in Hyiso.
    inversion Hyiso.
  }      
  destruct (voter_validity vs).
  trivial.
  contradiction.
  contradiction.
Qed.



Lemma vsout_not_isolated
  {vs : voter_state}
  {all_unit_outputs : list unit_output}
  {pf_all_unit_outputs : get_u_ids_of_unit_output all_unit_outputs = l u_ids}
  {lsd : list unit_data}
  (pf_lsd : lsd = build_updated_u_data_lst (pf_l u_ids)
                    pf_all_unit_outputs (pf_ud_lst vs) )
  {prm_unt : unit_data}
  (pf_prm_unt :  uid (voter_output vs) = get_u_id_of_unit_data prm_unt
                 /\ In prm_unt lsd)
  (pf_iso : iso_status (u_status prm_unt) = not_isolated)
  : let VSout := (find_data_of_a_given_unit_id (pf_ud_lst vs) (pf_v_output vs)) in
    iso_status (u_status (proj1_sig  VSout)) = not_isolated.

Proof.
  intro.
  inversion pf_prm_unt as  [Hcsuid Hcsin]. 
  assert (In (uid (u_output prm_unt))
            (get_u_ids_of_unit_data (non_isolated_list (lsd)))) as Hnisonw.
  { unfold get_u_ids_of_unit_data. apply in_map_iff.
    exists prm_unt.
    split; trivial.
    apply filter_In.
    split; trivial.
    unfold not_iso_check.
    rewrite pf_iso. trivial.
  }
  rewrite  pf_lsd in Hnisonw.
  pose proof ( not_isolated_after_update_implies_not_isolated_before
                 (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                 (uid (u_output prm_unt))  Hnisonw) as Hnisovs.
  unfold get_u_id_of_unit_data in Hnisovs.
  remember (proj2_sig  VSout) as f_vs.
  inversion f_vs as [Hvsoutuid Hvsoutin].
  clear Heqf_vs f_vs.
  unfold get_u_id_of_unit_data in *.
  pose proof (eq_stepl Hcsuid Hvsoutuid ) as Huideq.
  rewrite <- Huideq in Hnisovs.
  apply in_map_iff in Hnisovs.
  inversion Hnisovs as [y1 [Hy1uid Hy1inniso]].
  apply filter_In in Hy1inniso.
  inversion Hy1inniso as [Hy1in Hy1iso].
  assert (y1 = proj1_sig VSout) as Heqy1vsout
      by exact (fun_out_same_means_same_element_of_lst  y1 Hy1uid Hy1in Hvsoutin
                  (mapped_list_nodup (pf_ud_lst vs) (pf_l u_ids))).
  rewrite <- Heqy1vsout.
  exact (nisoc_t_not_isltd Hy1iso).
Qed.

Lemma risky_cnt_age_prop_satisfied_miscomp_or_mayb_case
  {vs : voter_state}
  {all_unit_outputs : list unit_output}
  {pf_all_unit_outputs : get_u_ids_of_unit_output all_unit_outputs = l u_ids}
  {lsd : list unit_data}
  (pf_lsd : lsd = build_updated_u_data_lst (pf_l u_ids)
                    pf_all_unit_outputs (pf_ud_lst vs) )
  (pf_min_req :  min_required <= count_of_non_isolated_units lsd)
  {prm_unt : unit_data}
  (pf_prm_unt :  uid (voter_output vs) = get_u_id_of_unit_data prm_unt
                 /\ In prm_unt lsd)
  (pf_m : miscomp_status (u_status prm_unt) <> not_miscomparing)
  (pf_iso : iso_status (u_status prm_unt) = not_isolated)
  :  S (output_age vs) = risky_count (u_status prm_unt).

Proof.
  assert (voter_validity vs = valid) as Hvld
    by exact (vs_is_valid pf_lsd pf_min_req pf_prm_unt pf_iso ).
  pose proof ( pf_risky_cnt vs Hvld) as Hpfrc.  
  inversion pf_prm_unt as  [Hcsuid Hcsin]. 
  
  pose proof (pf_validity vs) as [[Hnv1 Hnv2][[Huid1 Hud2] Hhlnil]].
  remember (find_data_of_a_given_unit_id (pf_ud_lst vs) (pf_v_output vs)) as VSout.
  remember (proj2_sig  VSout) as f_vs.
  inversion f_vs as [Hvsoutuid Hvsoutin].
  clear Heqf_vs f_vs.
  unfold get_u_id_of_unit_data in *.
  pose proof (eq_stepl Hcsuid Hvsoutuid ) as Huideq.
  assert (risky_cnt_prop (proj1_sig VSout) prm_unt) as Hrcp. {
    rewrite pf_lsd in Hcsin.
    exact (build_updated_u_data_lst_holds_risky_cnt_prop
                (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                  (proj1_sig VSout)
                  Hvsoutin  prm_unt  Hcsin Huideq).
  }
  unfold risky_cnt_prop in Hrcp.
    
  assert (  iso_status (u_status (proj1_sig  VSout)) = not_isolated )
    as Hnisovsout. {
    rewrite HeqVSout.
    exact (vsout_not_isolated pf_lsd pf_prm_unt pf_iso).
  }
  
  pose proof (Hrcp Hnisovsout)  as [Err1 Err2].
  inversion Err1.  
  { pose proof (pf_healthy prm_unt) as [PF1 PF2].
    pose proof (PF1 H) as [PF3a [PF3b PF3c]].
    rewrite PF3c in pf_m.
    contradiction.
  }
  lia.
Qed.


Lemma risky_cnt_age_prop_satisfied_bad
  {vs : voter_state}
  {all_unit_outputs : list unit_output}
  {pf_all_unit_outputs : get_u_ids_of_unit_output all_unit_outputs = l u_ids}
  {lsd : list unit_data}
  (pf_lsd : lsd = build_updated_u_data_lst (pf_l u_ids)
                    pf_all_unit_outputs (pf_ud_lst vs) )
  (pf_min_req :  min_required <= count_of_non_isolated_units lsd)
  {prm_unt : unit_data}
  (pf_prm_unt :  uid (voter_output vs) = get_u_id_of_unit_data prm_unt
                 /\ In prm_unt lsd)
  (pf_h : hw_hlth (reading (u_output prm_unt))  = bad)
  (pf_iso : iso_status (u_status prm_unt) = not_isolated)
  :  S (output_age vs) = risky_count (u_status prm_unt).

Proof.
  assert (voter_validity vs = valid) as Hvld
    by exact (vs_is_valid pf_lsd pf_min_req pf_prm_unt pf_iso ).
  pose proof ( pf_risky_cnt vs Hvld) as Hpfrc.  
  inversion pf_prm_unt as  [Hcsuid Hcsin]. 
  
  pose proof (pf_validity vs) as [[Hnv1 Hnv2][[Huid1 Hud2] Hhlnil]].
  remember (find_data_of_a_given_unit_id (pf_ud_lst vs) (pf_v_output vs)) as VSout.
  remember (proj2_sig  VSout) as f_vs.
  inversion f_vs as [Hvsoutuid Hvsoutin].
  clear Heqf_vs f_vs.
  unfold get_u_id_of_unit_data in *.
  pose proof (eq_stepl Hcsuid Hvsoutuid ) as Huideq.
  assert (risky_cnt_prop (proj1_sig VSout) prm_unt) as Hrcp. {
    rewrite pf_lsd in Hcsin.
    exact (build_updated_u_data_lst_holds_risky_cnt_prop
                (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                  (proj1_sig VSout)
                  Hvsoutin  prm_unt  Hcsin Huideq).
  }
  unfold risky_cnt_prop in Hrcp.
    
  assert (  iso_status (u_status (proj1_sig  VSout)) = not_isolated )
    as Hnisovsout. {
    rewrite HeqVSout.
    exact (vsout_not_isolated pf_lsd pf_prm_unt pf_iso).
  }
   
  pose proof (Hrcp Hnisovsout)  as [Err1 Err2].
  inversion Err1.  
  { pose proof (pf_healthy prm_unt) as [PF1 PF2].
    pose proof (PF1 H) as [PF3a [PF3b PF3c]].
    rewrite PF3a in pf_h.
    inversion pf_h.
  }
  lia.
Qed.




Lemma Helper_lemma_to_reduce_match_term
        {x : isolation}
        (pf_H : (if
         match x with
         | isolated => false
         | not_isolated => true
         end
        then false
                  else true) = true )
        (pf_x : x = not_isolated) : false = true.
  rewrite pf_x in pf_H. trivial.
Qed.

  



Lemma uid_of_vs_out_in_uids
  ( vs : voter_state )
  { new_q : list unit_data }
  ( pf_n_q : get_u_ids_of_unit_data new_q = l u_ids )  
  : In (uid (voter_output vs)) (get_u_ids_of_unit_data new_q).

    pose proof (pf_v_output vs).
    pose proof (pf_ud_lst vs).
    rewrite pf_n_q.
    rewrite <- H0.
    trivial.
Qed.


Definition miscomp_check_props
  ( vs new_vs : voter_state)
  {all_unit_outputs : list unit_output}
  (pf_all_unit_outputs : get_u_ids_of_unit_output all_unit_outputs = u_ids.(l)) :=
  ( simul_fault_prop (pf_l u_ids)  pf_all_unit_outputs (pf_ud_lst vs)
    -> min_required <= count_of_non_isolated_units vs.(u_data_lst)
    -> forall x,
        In x (u_data_lst vs)
        -> forall y,
          In y (u_data_lst new_vs)
          ->  forall z,
            In z all_unit_outputs
            -> (uid (u_output x) = uid (u_output y))
            -> (uid (u_output x) = uid z)  
            -> iso_status (u_status x) = not_isolated
            ->
              ( (* soundness a prop *)
                y.(u_status).(miscomp_status) = miscomparing
                -> adiff ground_truth z.(reading).(val)    > delta )
              (* soundness B prop *)
              /\  ( 
                  let  l := proj1_sig (all_good_non_iso_lst (pf_l u_ids)
                                         pf_all_unit_outputs (pf_ud_lst vs)) in
                  In z l
                  -> y.(u_status).(miscomp_status) = not_miscomparing
                  -> adiff ground_truth z.(reading).(val) <= 3*delta )
              (* completeness a prop *)
              /\
                ( let mis_flt_lmt := flt_lmt_among_good
                                       u_ids.(pf_l) pf_all_unit_outputs (pf_ud_lst vs) in
                  let l := proj1_sig
                             (all_good_non_iso_lst
                                u_ids.(pf_l) pf_all_unit_outputs (pf_ud_lst vs) ) in
                  length l > 2*mis_flt_lmt
                  -> z.(reading).(hw_hlth) = good 
                  -> adiff ground_truth z.(reading).(val) > 3*delta
                  -> y.(u_status).(miscomp_status) = miscomparing )
              (* completeness b prop *)
              /\
                ( let mis_flt_lmt := flt_lmt_among_good
                                       u_ids.(pf_l) pf_all_unit_outputs (pf_ud_lst vs) in
                  let l := proj1_sig (all_good_non_iso_lst
                                        u_ids.(pf_l) pf_all_unit_outputs (pf_ud_lst vs) ) in
                  length l > 2*mis_flt_lmt
                  -> In z l
                  -> adiff ground_truth z.(reading).(val) <= delta
                  -> y.(u_status).(miscomp_status) = not_miscomparing)
              /\
                ( let mis_flt_lmt := flt_lmt_among_good
                                       u_ids.(pf_l) pf_all_unit_outputs (pf_ud_lst vs) in
                  let l := proj1_sig (all_good_non_iso_lst
                                        u_ids.(pf_l) pf_all_unit_outputs (pf_ud_lst vs) ) in
                  In z l
                  -> miscomparing_many_check l mis_flt_lmt z = true
                  -> y.(u_status).(miscomp_status) = miscomparing )
              /\
                (  let mis_lst          := proj1_sig
                                             (miscomparing_lst
                                                (pf_l u_ids)
                                                pf_all_unit_outputs
                                                (pf_ud_lst vs) ) in
                   let mis_flt_lmt      := flt_lmt_among_good 
                                                (pf_l u_ids)
                                                pf_all_unit_outputs
                                                (pf_ud_lst vs) in
                   let rem_mis_flt_lmt  := mis_flt_lmt - length ( mis_lst ) in
                   let gd_non_iso_lst   := proj1_sig (all_good_non_iso_lst
                                                (pf_l u_ids)
                                                pf_all_unit_outputs
                                                (pf_ud_lst vs) )in
                   let negb_mis_lst     := filter
                                             (fun y =>
                                                negb (miscomparing_many_check
                                                        gd_non_iso_lst mis_flt_lmt y ) )
                                             gd_non_iso_lst in 
                  
                   In z negb_mis_lst
                   -> agreeing_many_check negb_mis_lst rem_mis_flt_lmt z = true
                   -> y.(u_status).(miscomp_status) = not_miscomparing )
  ).


Definition voter_state_transition_prop
  ( vs new_vs : voter_state)
  {all_unit_outputs : list unit_output}
  (pf_all_unit_outputs : get_u_ids_of_unit_output all_unit_outputs = u_ids.(l)) :=

  (* risky_cnt is properly updated : Property 9*)
  (  forall x, In x (u_data_lst vs)
               -> forall y, In y (u_data_lst new_vs)
                            -> (uid (u_output x) = uid (u_output y))
                            -> risky_cnt_prop x y )
                            
    (* unit switching only when selected unit is isolated *)
  /\  ( (uid (voter_output vs)) <> (uid (voter_output new_vs))
        -> In (uid(voter_output vs)) (get_u_ids_of_unit_data (isolated_list (u_data_lst new_vs))))
        
    (* switched snsr is the next highest priority healthy snsr*)
  /\  ( (uid (voter_output vs)) <> (uid (voter_output new_vs))
       -> exists l1 l2, (u_data_lst new_vs = l1++(presrvd_data new_vs)::l2)
                  -> healthy_unit_list l1 = nil)
          
    (* input data is copied to output vs  *)    
  /\  get_u_outputs_of_data new_vs.(u_data_lst) = all_unit_outputs
  
   (* age is updated properly *)
  /\  ( voter_validity new_vs <> not_valid
        -> (  output_age new_vs = S (output_age vs) \/ output_age new_vs = 0 ))
        
   (* age incremented means old output is retained *)
  /\  ( output_age new_vs <> 0 -> voter_output vs = voter_output new_vs )
  
   (* isolated remains isolated *)
  /\  (  forall x, In x (get_u_ids_of_unit_data   (isolated_list (u_data_lst vs))) -> 
                   In x (get_u_ids_of_unit_data   (isolated_list (u_data_lst new_vs))))
                   
  /\ (* invalid remain invalid *)
     (voter_validity vs = not_valid -> voter_validity new_vs = not_valid )

  /\ (* enough units -> valid *)
    (simul_fault_prop (pf_l u_ids)  pf_all_unit_outputs (pf_ud_lst vs)
     -> count_of_non_isolated_units (u_data_lst new_vs) >= min_required
     -> let mis_flt_lmt := flt_lmt_among_good
                             u_ids.(pf_l) pf_all_unit_outputs (pf_ud_lst vs) in
        let l := proj1_sig (all_good_non_iso_lst
                              u_ids.(pf_l) pf_all_unit_outputs (pf_ud_lst vs) ) in
        length l > 2*mis_flt_lmt
        -> voter_validity new_vs = valid )
        
  /\ (* enough non_isolated_units -> valid : version 2 *)
    (simul_fault_prop (pf_l u_ids)  pf_all_unit_outputs (pf_ud_lst vs)
       -> count_of_non_isolated_units (u_data_lst vs) > 2 * simul_max_fault
       -> voter_validity new_vs = valid )
       
  /\ (* No maybe_miscomparing *)
    (simul_fault_prop (pf_l u_ids)  pf_all_unit_outputs (pf_ud_lst vs)
     -> let mis_flt_lmt := flt_lmt_among_good
                             u_ids.(pf_l) pf_all_unit_outputs (pf_ud_lst vs) in
        let l := proj1_sig (all_good_non_iso_lst
                              u_ids.(pf_l) pf_all_unit_outputs (pf_ud_lst vs) ) in
        length l > 2*mis_flt_lmt
        -> forall x,
            In x (u_data_lst vs)
            -> forall y,
              In y (u_data_lst new_vs)                                            
              -> (uid (u_output x) = uid (u_output y))                   
              -> iso_status (u_status x) = not_isolated
              -> y.(u_status).(miscomp_status) <> maybe_miscomparing )
                                                    
  /\ (* soundness and completeness props of miscomparison check *)
    miscomp_check_props vs new_vs pf_all_unit_outputs.

Definition voter_state_transition
  (vs : voter_state)
  {all_unit_outputs: list unit_output}
  (pf_all_unit_outputs : get_u_ids_of_unit_output all_unit_outputs =  l (u_ids))
  : { x: voter_state |voter_state_transition_prop  vs x  pf_all_unit_outputs } .

refine (

  (* build_updated_u_data_lst : This function incorporate the new unit signals into the u_data_lst 
     and updates the unit status (iso status, miscomp status, risky_count etc) values  *)
  let new_p_ud_lst      := build_updated_u_data_lst
                                        (pf_l u_ids)
                                        pf_all_unit_outputs  vs.(pf_ud_lst) in 
  let pf_new_p_ud_lst   := build_updated_u_data_lst_preserves_uids (pf_l u_ids)
                          pf_all_unit_outputs vs.(pf_ud_lst) in
 
  
  let non_isolated_unit_count := count_of_non_isolated_units new_p_ud_lst in
  match le_dec min_required non_isolated_unit_count  with
  | right e => exist _
                 (build_invalidated_vs vs new_p_ud_lst pf_new_p_ud_lst   _  ) _
  | left  e =>
     
      let (prm_unt, pf_prm_unt) :=
        (@find_data_of_a_given_unit_id
           (l u_ids) new_p_ud_lst (uid (voter_output vs)) pf_new_p_ud_lst _    ) in 
      let prm_unt_iso := prm_unt.(u_status).(iso_status) in 
      match prm_unt.(u_status).(iso_status) as pu_ISO return
            prm_unt.(u_status).(iso_status) = pu_ISO ->
            { x: voter_state |  voter_state_transition_prop vs x
                                  pf_all_unit_outputs} with
      | isolated     => fun hyp =>
                         let hl_list := healthy_unit_list new_p_ud_lst in
                         match hl_list as HL return
                               hl_list = HL
                               -> {x: voter_state |
                                    voter_state_transition_prop
                                      vs x  pf_all_unit_outputs}
                         with
                         | []   => fun hyp2
                                   => exist  _
                                        (build_un_id_vs
                                           vs
                                           pf_all_unit_outputs
                                             _ _ )  _
                         | x::xs => fun hyp2
                                    => exist  _
                                         ( build_prime_switched_vs vs pf_new_p_ud_lst  e hyp2 _ )  _ 
                         end eq_refl
                             
      | not_isolated => fun hyp
                        => let prm_unt_r := prm_unt.(u_output).(reading).(hw_hlth) in
                           let prm_unt_m := prm_unt.(u_status).(miscomp_status) in 
                           match  prm_unt_m as pu_m, prm_unt_r as pu_r return
                                  prm_unt_m = pu_m -> prm_unt_r = pu_r ->
                                  { x: voter_state |
                                    voter_state_transition_prop vs x
                                      pf_all_unit_outputs}
                           with
                           | not_miscomparing, good
                             => fun h
                                => fun h2 => exist  _
                                               ( voter_state_build
                                                   new_p_ud_lst
                                                   pf_new_p_ud_lst
                                                   prm_unt.(u_output)
                                                         valid
                                                         0
                                                         prm_unt
                                                         _ _ _ _ _  _ _ _ ) _ 
                           | _, _
                             => fun h
                                => fun h2 => exist _
                                               ( voter_state_build
                                                   new_p_ud_lst
                                                   pf_new_p_ud_lst
                                                   (voter_output vs)
                                                   valid
                                                   (S (output_age vs))
                                                   (presrvd_data vs)
                                                   _
                                                   (pf_presrvd_data vs)
                                                   _ _  _ _ _ _) _            
                           end eq_refl eq_refl
      end eq_refl
  end      
  ). 
Unshelve.

9: { exact new_p_ud_lst. }
9: { trivial. }


(*  In (uid (voter_output vs))
   (get_u_ids_of_unit_data (isolated_list
   (build_updated_u_data_lst2 (pf_l u_ids)
   pf_all_unit_outputs (pf_ud_lst vs)))) *)
10: {
  inversion pf_prm_unt.
  unfold get_u_ids_of_unit_data.
  apply in_map_iff.
  exists prm_unt. split.
  unfold get_u_id_of_unit_data in H.
  symmetry. trivial.
  unfold isolated_list.
  apply filter_In.
  split. trivial.
  unfold negb. unfold not_iso_check. rewrite hyp. trivial.
}
(* In (uid (voter_output vs))
   (get_u_ids_of_unit_data new_p_ud_lst) *)
1: { exact (uid_of_vs_out_in_uids vs pf_new_p_ud_lst). }

(*  In (uid (voter_output vs))
   (get_u_ids_of_unit_data new_p_ud_lst) *)
9: {  exact (uid_of_vs_out_in_uids vs pf_new_p_ud_lst). }
 
(* In (uid (voter_output vs))
   (get_u_ids_of_unit_data new_p_ud_lst) *)   
15: {  exact (uid_of_vs_out_in_uids vs pf_new_p_ud_lst). }

(* In (uid (voter_output vs))
   (get_u_ids_of_unit_data new_p_ud_lst) *)    
29: {  exact (uid_of_vs_out_in_uids vs pf_new_p_ud_lst). }
 
(* S (output_age vs) = 0 <->  
 valid = valid /\ In (presrvd_data vs) new_p_ud_lst *) 
15: {  exact (pf_age_satisfied_bad_case pf_new_p_ud_lst pf_prm_unt h2). }

(*  S (output_age vs) = 0 <->
    valid = valid /\ In (presrvd_data vs) new_p_ud_lst *)
9: {
  assert (miscomp_status (u_status prm_unt) <> not_miscomparing). {
    intro Hmis.
    unfold prm_unt_m in h.
    rewrite Hmis in h.
    inversion h.
  }
  exact (pf_age_satisfied_mis_case pf_new_p_ud_lst pf_prm_unt H). }
  
(* S (output_age vs) = 0 <->  
 valid = valid /\ In (presrvd_data vs) new_p_ud_lst *) 
27: {assert (miscomp_status (u_status prm_unt) <> not_miscomparing). {
    intro Hmis.
    unfold prm_unt_m in h.
    rewrite Hmis in h.
    inversion h.
  }
  exact (pf_age_satisfied_mis_case pf_new_p_ud_lst pf_prm_unt H). }
 


(* count_of_non_isolated_units new_p_ud_lst < min_required *)
32: { pose proof ( not_le min_required non_isolated_unit_count  e).  lia.
}

-  (* voter_state_transition_prop vs
    (build_un_id_vs*)

  unfold build_un_id_vs.
  split. 
  -- (* risky_cnt_prop x y *)
    intros. 
    exact (build_updated_u_data_lst_holds_risky_cnt_prop (pf_l u_ids)
             pf_all_unit_outputs (pf_ud_lst vs) x H y H0 H1).
  -- split. 
     --- (*  In (uid (voter_output vs))
              (get_u_id s_of_unit_data (isolated_list
              (u_data_lst (move_to_transient_mode *)
       
       intro. contradiction H. trivial.
       
     ---
       {
         simpl.
         repeat split.
         + intro. contradiction.
         + (* get_u_outputs_of_data
               (u_data_lst (move_to_transient_mode *)
           exact (build_updated_u_data_lst_preserves_input_data
                    (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) ).
          + (*  output_age (move_to_transient_mode) = S (output_age vs) \/
                output_age (move_to_transient_mode ) = 0 *)
             left; trivial.
          + (* In x
               (get_u_ids_of_unit_data
               (isolated_list
               (u_data_lst (move_to_transient_mode *)
            exact ( once_isolated_remain_isolated_after_build_updated_u_data_lst
                      (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) ).
          +  intros Hv.
             pose proof (pf_validity vs) as [[Hinv1 Hinv2] T].
             pose proof (Hinv2 Hv) as Hltmin.
             assert (~ min_required <= non_isolated_unit_count). {
               pose proof  (build_updated_u_data_lst_do_not_increase_non_isolated_units
                              u_ids.(pf_l) pf_all_unit_outputs vs.(pf_ud_lst) ).
               fold new_p_ud_lst in H.
               simpl in H.
             lia.
             }
             contradiction.
             
             
          + intros H Hnisocnt Hl.
            pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H)
              as Hypo.
            pose proof (build_updated_u_data_lst_gives_at_lst_1_hlthy_data
                          (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                          Hypo Hl) as Inhl.
            inversion Inhl as [y [Hyin Hyhlthy]].
            assert ( In y hl_list ). { 
              unfold hl_list.
              apply filter_In.
              split; trivial.
              inversion Hyhlthy as [Hgd [Hniso Hnmis]].
              unfold hlthy_unit_check, not_iso_check,
                not_miscomp_unit_check, hw_good_unit_check.
              rewrite Hgd, Hniso, Hnmis; auto.
            }
            rewrite hyp2 in H0.
            inversion H0.

          + intros SFP Hcniso.
            pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) SFP)
              as Hypo.
            pose proof (sfp_and_gt_2smf_non_iso_implies_len_good_non_iso_gt_2mis_flt_lmt
                          (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                          SFP Hcniso) as Hl.
            pose proof (build_updated_u_data_lst_gives_at_lst_1_hlthy_data
                          (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                          Hypo Hl) as Inhl.
            inversion Inhl as [y [Hyin Hyhlthy]].
            assert ( In y hl_list ) as Hyinhl. {
              unfold hl_list.
              apply filter_In.
              split; trivial.
              inversion Hyhlthy as [Hgd [Hniso Hnmis]].
              unfold hlthy_unit_check, not_iso_check,
                not_miscomp_unit_check, hw_good_unit_check.
              rewrite Hgd, Hniso, Hnmis; auto.
            }
            rewrite hyp2 in Hyinhl.
            inversion Hyinhl.

          + intros Hsfp  Hl x Hxin y Hyin Hxuideqy Hxiso.
            pose proof (mis_fault_hypo (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) Hsfp)
              as Hypo.
            exact (build_updated_u_data_lst_holds_mayb_nil_when_enough_non_isolated
                     (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                     Hypo Hl x Hxin y Hyin Hxuideqy Hxiso).
          +

            intros Hmis.
            simpl in *.
            pose proof (mis_fault_hypo (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H)
              as Hypo.
            exact (build_updated_u_data_lst_holds_soundness_a_prop_of_miscomp_check
                     (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                     Hypo x H1 y H2 z H3 H4 H5 H6 Hmis).
         
          + 
            intros  l Zinl Hmis.
            simpl in *.
            pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H)
              as Hypo.
            exact (build_updated_u_data_lst_holds_soundness_b_prop_of_miscomp_check
                     (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                     Hypo x H1 y H2 z Zinl H4 H5 H6 Hmis).               

          +
            simpl.
            intros Hl Hgd H3d.
            pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H)
              as Hypo.
            exact (build_updated_u_data_lst_holds_cmpltnss_a_prop_of_miscomp_check
                     (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                     Hypo Hl x H1 y H2 z H3 H4 H5 H6 Hgd H3d).

          +
            intros  T2 l Hl Zinl H3d.
            pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H)
              as Hypo.
            exact (build_updated_u_data_lst_holds_cmpltnss_b_prop_of_miscomp_check
                     (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                     Hypo Hl x H1 y H2 z Zinl H4 H5 H6 H3d).
          + intros mis_lmt l Zinl Hmisprop.
            exact (build_updated_u_data_lst_holds_miscomp_check_true_case
                     (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                     x H1 y H2 z Zinl H4 H5 H6 Hmisprop).
          + intros Ml ms_lmt re_ms_lmt l l' Zinl' Hagrprop.
            exact (build_updated_u_data_lst_holds_agreeing_check_true_case
                     (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                     x H1 y H2 z Zinl' H4 H5 H6 Hagrprop).
                     
                        
        }            

(*  voter_state_transition_prop vs
    (proj1_sig
       (build_prime_switched_vs vs pf_new_p_ud_lst e hyp2 *)
 
-   repeat split. 
   --  (* switch unit risky count prop *)

      unfold build_prime_switched_vs in H0. simpl in H0.
     pose proof (build_updated_u_data_lst_holds_risky_cnt_prop  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)  x0 H y H0 H1 ).
     unfold risky_cnt_prop in H3.
     pose proof ( H3 H2).
     inversion H4. trivial.
  --  unfold build_prime_switched_vs in H0. 
     pose proof (build_updated_u_data_lst_holds_risky_cnt_prop  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)  x0 H y H0 H1 ).
     unfold risky_cnt_prop in H3.
     pose proof ( H3 H2).
     inversion H4 as [Ha [Hb Hc]].  trivial.
  --  unfold build_prime_switched_vs in H0.  
     pose proof (build_updated_u_data_lst_holds_risky_cnt_prop  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)  x0 H y H0 H1 ).
     unfold risky_cnt_prop in H3.
     pose proof ( H3 H2).
     inversion H4 as [Ha [Hb Hc]]. trivial.

(*uid (voter_output vs) <>
  uid
    (voter_output
       (proj1_sig
          (build_prime_switched_vs vs pf_new_p_ud_lst e hyp2*)     
  -- simpl.
     inversion pf_prm_unt.
     intro.
      unfold get_u_ids_of_unit_data.
      apply in_map_iff.
      exists prm_unt. split.
      unfold uid in H. 
      unfold get_u_id_of_unit_data in H.
      symmetry. trivial.
      unfold isolated_list.
      apply filter_In.
      split. trivial.
      unfold negb. unfold not_iso_check. rewrite hyp. trivial.
  -- simpl. intros.
     assert ( In x new_p_ud_lst) as Hxinnew. {
       assert ( In x hl_list ) as Hxinhl. {
         rewrite hyp2. apply in_eq. }
       apply filter_In in Hxinhl.
       inversion Hxinhl. trivial.
     }
     apply in_split in Hxinnew.
     inversion Hxinnew as [l1 [l2 Hneweql1xl2]].
     exists l1. exists l2.
     intros.
     clear H0.
     unfold hl_list in hyp2.
     unfold healthy_unit_list in *.
     assert ( NoDup new_p_ud_lst ) as Hndl. {
       assert (NoDup (get_u_ids_of_unit_data new_p_ud_lst) ). {
         unfold new_p_ud_lst.
         rewrite pf_new_p_ud_lst.
         exact (pf_l u_ids).
       }
       apply NoDup_map_inv in H0.
       trivial.
     }     
     exact (all_prevous_to_head_of_filter_fun_a_is_false
              Hndl Hneweql1xl2
              hyp2 ).
     
  -- unfold build_prime_switched_vs.
     exact (build_updated_u_data_lst_preserves_input_data  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) ).
  -- unfold build_prime_switched_vs. simpl. right; trivial.
  -- unfold build_prime_switched_vs. simpl. intro. contradiction H. trivial.
  -- unfold build_prime_switched_vs. simpl. exact ( once_isolated_remain_isolated_after_build_updated_u_data_lst (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) ).
  --  intros Hv. simpl.
      pose proof (pf_validity vs) as [[Hinv1 Hinv2] T].
      pose proof (Hinv2 Hv) as Hltmin.
      assert (~ min_required <= non_isolated_unit_count). {
        pose proof  (build_updated_u_data_lst_do_not_increase_non_isolated_units
                       u_ids.(pf_l) pf_all_unit_outputs vs.(pf_ud_lst) ).
        fold new_p_ud_lst in H.
        simpl in H.
        lia.
      }
      contradiction.
      
  -- intros Hsfp mis_flt_lmt l Hl a Hain b Hbin Hauideqb Haiso. 
            pose proof (mis_fault_hypo (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) Hsfp)
              as Hypo.
            exact (build_updated_u_data_lst_holds_mayb_nil_when_enough_non_isolated
                     (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                     Hypo Hl a Hain b Hbin Hauideqb Haiso).

  -- intros Hmis. 
     pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_soundness_a_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              Hypo x0 H1 y H2 z H3 H4 H5 H6 Hmis).
  -- intros  l Zinl Hmis. 
     pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_soundness_b_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
             Hypo x0 H1 y H2 z Zinl H4 H5 H6 Hmis).
  -- intros M L Hl Hgd H3d.
     pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_cmpltnss_a_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              Hypo Hl x0 H1 y H2 z H3 H4 H5 H6 Hgd H3d).
            
  -- intros  M L Hl Zinl H3d.
     pose proof (mis_fault_hypo (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_cmpltnss_b_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              Hypo Hl x0 H1 y H2 z Zinl H4 H5 H6 H3d).
            
  -- intros mis_lmt l Zinl Hmisprop.
     exact (build_updated_u_data_lst_holds_miscomp_check_true_case
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              x0 H1 y H2 z Zinl H4 H5 H6 Hmisprop).
  -- intros Ml ms_lmt re_ms_lmt l l' Zinl' Hagrprop.
            exact (build_updated_u_data_lst_holds_agreeing_check_true_case
                     (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                     x0 H1 y H2 z Zinl' H4 H5 H6 Hagrprop).
            





            
(*  voter_state_transition_prop vs
    {|
      u_data_lst := new_p_ud_lst;
      pf_ud_lst := pf_new_p_ud_lst;
      voter_output := voter_output vs;
      voter_validity := valid;
      output_age := S (output_age vs);
      presrvd_data := presrvd_data vs; *)
     
- repeat split.
  -- simpl in H0. 
     pose proof ( build_updated_u_data_lst_holds_risky_cnt_prop  (pf_l u_ids)  pf_all_unit_outputs 
                    (pf_ud_lst vs) x H y H0 H1 H2 ).
     inversion H3. trivial.
  -- simpl in *.
     pose proof ( build_updated_u_data_lst_holds_risky_cnt_prop   (pf_l u_ids) pf_all_unit_outputs 
                    (pf_ud_lst vs) x H y H0 H1 H2 ).
     inversion H3 as [Ha [Hb Hc]]. trivial.
  -- simpl in *.
     pose proof ( build_updated_u_data_lst_holds_risky_cnt_prop  (pf_l u_ids) pf_all_unit_outputs 
                    (pf_ud_lst vs) x H y H0 H1 H2 ).
     inversion H3 as [Ha [Hb Hc]]. trivial.
  -- simpl. intro. contradiction H. trivial.
  -- simpl. intro. contradiction. 
  -- simpl. exact ( build_updated_u_data_lst_preserves_input_data (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) ).

  -- simpl. left ; trivial.
  -- simpl. exact (once_isolated_remain_isolated_after_build_updated_u_data_lst
                      (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) ).
 --  intros Hv. simpl.
      pose proof (pf_validity vs) as [[Hinv1 Hinv2] T].
      pose proof (Hinv2 Hv) as Hltmin.
      assert (~ min_required <= non_isolated_unit_count). {
        pose proof  (build_updated_u_data_lst_do_not_increase_non_isolated_units
                       u_ids.(pf_l) pf_all_unit_outputs vs.(pf_ud_lst) ).
        fold new_p_ud_lst in H.
        simpl in H.
        lia.
      }
      contradiction.
      
  -- intros Hsfp mis_flt_lmt l Hl a Hain b Hbin Hauideqb Haiso. 
            pose proof (mis_fault_hypo (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) Hsfp)
              as Hypo.
            exact (build_updated_u_data_lst_holds_mayb_nil_when_enough_non_isolated
                     (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                     Hypo Hl a Hain b Hbin Hauideqb Haiso).

 
  -- intros Hmis. 
     pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_soundness_a_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              Hypo x H1 y H2 z H3 H4 H5 H6 Hmis).
  -- intros  l Zinl Hmis. 
     pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_soundness_b_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
             Hypo x H1 y H2 z Zinl H4 H5 H6 Hmis).
  -- intros M L Hl Hgd H3d.
     pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_cmpltnss_a_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              Hypo Hl x H1 y H2 z H3 H4 H5 H6 Hgd H3d).
            
  -- intros  M L Hl Zinl H3d.
     pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_cmpltnss_b_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              Hypo Hl x H1 y H2 z Zinl H4 H5 H6 H3d).
            
  -- intros mis_lmt l Zinl Hmisprop.
     exact (build_updated_u_data_lst_holds_miscomp_check_true_case
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              x H1 y H2 z Zinl H4 H5 H6 Hmisprop).
  -- intros Ml ms_lmt re_ms_lmt l l' Zinl' Hagrprop.
            exact (build_updated_u_data_lst_holds_agreeing_check_true_case
                     (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                     x H1 y H2 z Zinl' H4 H5 H6 Hagrprop).
            
           

     
(*  voter_state_transition_prop vs
    {|
      u_data_lst := new_p_ud_lst;
      pf_ud_lst := pf_new_p_ud_lst;
      voter_output := u_output prm_unt;
      voter_validity := valid;
      output_age := 0;
      presrvd_data := prm_unt; *)
     
- repeat split.
  --  simpl in H0;
     pose proof (build_updated_u_data_lst_holds_risky_cnt_prop (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) x H y H0 H1 H2);
     inversion H3 as [Ha [Hb Hc]];
     trivial.
     
  -- simpl in H0.
     pose proof (build_updated_u_data_lst_holds_risky_cnt_prop (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) x H y H0 H1 H2).
     inversion H3 as [Ha [Hb Hc]].
     trivial.
  
  -- simpl in H0.
     pose proof (build_updated_u_data_lst_holds_risky_cnt_prop (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) x H y H0 H1 H2).
     inversion H3 as [Ha [Hb Hc]].
     trivial.
  -- simpl. intro.
     inversion pf_prm_unt.
     unfold get_u_id_of_unit_data in H0.
     rewrite H0 in H. contradiction.
  -- intro; contradiction.
  -- simpl. exact (build_updated_u_data_lst_preserves_input_data (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) ).
  -- simpl.  left ; trivial.
  -- simpl. exact (once_isolated_remain_isolated_after_build_updated_u_data_lst
                     (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) ).
  --  intros Hv. simpl.
      pose proof (pf_validity vs) as [[Hinv1 Hinv2] T].
      pose proof (Hinv2 Hv) as Hltmin.
      assert (~ min_required <= non_isolated_unit_count). {
        pose proof  (build_updated_u_data_lst_do_not_increase_non_isolated_units
                       u_ids.(pf_l) pf_all_unit_outputs vs.(pf_ud_lst) ).
        fold new_p_ud_lst in H.
        simpl in H.
        lia.
      }
      contradiction.
      
  -- intros Hsfp mis_flt_lmt l Hl a Hain b Hbin Hauideqb Haiso. 
            pose proof (mis_fault_hypo (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) Hsfp)
              as Hypo.
            exact (build_updated_u_data_lst_holds_mayb_nil_when_enough_non_isolated
                     (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                     Hypo Hl a Hain b Hbin Hauideqb Haiso).

 
  -- intros Hmis. 
     pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_soundness_a_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              Hypo x H1 y H2 z H3 H4 H5 H6 Hmis).
  -- intros  l Zinl Hmis. 
     pose proof (mis_fault_hypo (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_soundness_b_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
             Hypo x H1 y H2 z Zinl H4 H5 H6 Hmis).
  -- intros M L Hl Hgd H3d.
     pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_cmpltnss_a_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              Hypo Hl x H1 y H2 z H3 H4 H5 H6 Hgd H3d).
            
  -- intros  M L Hl Zinl H3d.
     pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_cmpltnss_b_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              Hypo Hl x H1 y H2 z Zinl H4 H5 H6 H3d).
            
  -- intros mis_lmt l Zinl Hmisprop.
     exact (build_updated_u_data_lst_holds_miscomp_check_true_case
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              x H1 y H2 z Zinl H4 H5 H6 Hmisprop).
  -- intros Ml ms_lmt re_ms_lmt l l' Zinl' Hagrprop.
            exact (build_updated_u_data_lst_holds_agreeing_check_true_case
                     (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                     x H1 y H2 z Zinl' H4 H5 H6 Hagrprop).
            


- (*voter_state_transition_prop vs
    {|
      u_data_lst := new_p_ud_lst;
      pf_ud_lst := pf_new_p_ud_lst;
      voter_output := voter_output vs;
      voter_validity := valid;
      output_age := S (output_age vs); *)

  repeat split.
  -- simpl in H0.
     pose proof (build_updated_u_data_lst_holds_risky_cnt_prop
                   (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) x H y H0 H1 H2);
       inversion H3 as [Ha [Hb Hc]];
       trivial.
  -- simpl in H0.
     pose proof (build_updated_u_data_lst_holds_risky_cnt_prop
                   (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) x H y H0 H1 H2);
       inversion H3 as [Ha [Hb Hc]];
       trivial.
  -- simpl in H0.
     pose proof (build_updated_u_data_lst_holds_risky_cnt_prop
                   (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) x H y H0 H1 H2);
       inversion H3 as [Ha [Hb Hc]];
       trivial.
  --simpl. intro. inversion pf_prm_unt.
     unfold get_u_id_of_unit_data in H0.
     rewrite H0 in H. contradiction.
  --  simpl. intros.
      exfalso.
      apply H.
      inversion pf_prm_unt as [Ha1 Ha2].
      unfold get_u_id_of_unit_data in Ha1.
      trivial.

  -- simpl. exact (build_updated_u_data_lst_preserves_input_data
                     (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) ).
  -- simpl. right ; trivial.
  -- simpl. intros. contradiction.
  -- simpl. exact ( once_isolated_remain_isolated_after_build_updated_u_data_lst
                      (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) ).
  --  intros Hv. simpl.
      pose proof (pf_validity vs) as [[Hinv1 Hinv2] T].
      pose proof (Hinv2 Hv) as Hltmin.
      assert (~ min_required <= non_isolated_unit_count). {
        pose proof  (build_updated_u_data_lst_do_not_increase_non_isolated_units
                       u_ids.(pf_l) pf_all_unit_outputs vs.(pf_ud_lst) ).
        fold new_p_ud_lst in H.
        simpl in H.
        lia.
      }
      contradiction.
      
  -- intros Hsfp mis_flt_lmt l Hl a Hain b Hbin Hauideqb Haiso. 
            pose proof (mis_fault_hypo (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) Hsfp)
              as Hypo.
            exact (build_updated_u_data_lst_holds_mayb_nil_when_enough_non_isolated
                     (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                     Hypo Hl a Hain b Hbin Hauideqb Haiso).

 

  -- intros Hmis. 
     pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_soundness_a_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              Hypo x H1 y H2 z H3 H4 H5 H6 Hmis).
  -- intros  l Zinl Hmis. 
     pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_soundness_b_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
             Hypo x H1 y H2 z Zinl H4 H5 H6 Hmis).
  -- intros M L Hl Hgd H3d.
     pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_cmpltnss_a_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              Hypo Hl x H1 y H2 z H3 H4 H5 H6 Hgd H3d).
            
  -- intros  M L Hl Zinl H3d.
     pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_cmpltnss_b_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              Hypo Hl x H1 y H2 z Zinl H4 H5 H6 H3d).
            
  -- intros mis_lmt l Zinl Hmisprop.
     exact (build_updated_u_data_lst_holds_miscomp_check_true_case
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              x H1 y H2 z Zinl H4 H5 H6 Hmisprop).
  -- intros Ml ms_lmt re_ms_lmt l l' Zinl' Hagrprop.
            exact (build_updated_u_data_lst_holds_agreeing_check_true_case
                     (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                     x H1 y H2 z Zinl' H4 H5 H6 Hagrprop).
                        

(*  voter_state_transition_prop vs
    {|
      u_data_lst := new_p_ud_lst;
      pf_ud_lst := pf_new_p_ud_lst;
      voter_output := voter_output vs;
      voter_validity := valid;
      output_age := S (output_age vs);
      presrvd_data := presrvd_data vs; *)
      
-  repeat split. 
  -- pose proof ( build_updated_u_data_lst_holds_risky_cnt_prop
                    (pf_l u_ids)  pf_all_unit_outputs 
                    (pf_ud_lst vs) x H y H0 H1 H2 ) as [Hrcp].
     trivial.
  -- pose proof ( build_updated_u_data_lst_holds_risky_cnt_prop
                    (pf_l u_ids) pf_all_unit_outputs 
                    (pf_ud_lst vs) x H y H0 H1 H2 ) as [Ha [Hb Hc]].
     trivial.
  -- pose proof ( build_updated_u_data_lst_holds_risky_cnt_prop
                    (pf_l u_ids) pf_all_unit_outputs 
                    (pf_ud_lst vs) x H y H0 H1 H2 )
       as [Ha [Hb Hc]]. trivial.
  -- intro. contradiction H. trivial.
  -- intro. contradiction.
  -- exact ( build_updated_u_data_lst_preserves_input_data
                      (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) ).

  -- simpl. left ; trivial.
  -- exact (once_isolated_remain_isolated_after_build_updated_u_data_lst
                      (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) ).

 --  intros Hv. simpl.
      pose proof (pf_validity vs) as [[Hinv1 Hinv2] T].
      pose proof (Hinv2 Hv) as Hltmin.
      assert (~ min_required <= non_isolated_unit_count). {
        pose proof  (build_updated_u_data_lst_do_not_increase_non_isolated_units
                       u_ids.(pf_l) pf_all_unit_outputs vs.(pf_ud_lst) ).
        fold new_p_ud_lst in H.
        simpl in H.
        lia.
      }
      contradiction.
      
  -- intros Hsfp mis_flt_lmt l Hl a Hain b Hbin Hauideqb Haiso. 
            pose proof (mis_fault_hypo (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) Hsfp)
              as Hypo.
            exact (build_updated_u_data_lst_holds_mayb_nil_when_enough_non_isolated
                     (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                     Hypo Hl a Hain b Hbin Hauideqb Haiso).

 

  -- intros Hmis. 
     pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_soundness_a_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              Hypo x H1 y H2 z H3 H4 H5 H6 Hmis).
  -- intros  l Zinl Hmis. 
     pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_soundness_b_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
             Hypo x H1 y H2 z Zinl H4 H5 H6 Hmis).
  -- intros M L Hl Hgd H3d.
     pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_cmpltnss_a_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              Hypo Hl x H1 y H2 z H3 H4 H5 H6 Hgd H3d).
            
  -- intros  M L Hl Zinl H3d.
     pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_cmpltnss_b_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              Hypo Hl x H1 y H2 z Zinl H4 H5 H6 H3d).
            
  -- intros mis_lmt l Zinl Hmisprop.
     exact (build_updated_u_data_lst_holds_miscomp_check_true_case
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              x H1 y H2 z Zinl H4 H5 H6 Hmisprop).
  -- intros Ml ms_lmt re_ms_lmt l l' Zinl' Hagrprop.
            exact (build_updated_u_data_lst_holds_agreeing_check_true_case
                     (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                     x H1 y H2 z Zinl' H4 H5 H6 Hagrprop).
                        




     
(*  voter_state_transition_prop vs
    (build_invalidated_vs vs new_p_ud_lst pf_new_p_ud_lst *)
      
- unfold build_invalidated_vs. repeat split.
    -- simpl in H0. 
       pose proof (build_updated_u_data_lst_holds_risky_cnt_prop
                     (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) x H y H0 H1 H2);
       inversion H3 as [Ha [Hb Hc]];
       trivial.
  -- simpl in H0.
     pose proof (build_updated_u_data_lst_holds_risky_cnt_prop
                   (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) x H y H0 H1 H2);
       inversion H3 as [Ha [Hb Hc]];
       trivial.
  -- simpl in H0.
     pose proof (build_updated_u_data_lst_holds_risky_cnt_prop
                   (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) x H y H0 H1 H2);
       inversion H3 as [Ha [Hb Hc]];
       trivial.
     
  --  simpl. intro; contradiction H; trivial.
  -- intro; contradiction.
    --  simpl. exact (build_updated_u_data_lst_preserves_input_data
                        (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) ). 
  -- simpl. intro.  contradiction. 
  -- simpl. exact ( once_isolated_remain_isolated_after_build_updated_u_data_lst
                      (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) ).
  -- simpl.
     intros.
     contradiction.
  --  simpl. intros SFP Hcniso.
      assert (min_required <= non_isolated_unit_count ) as Hcnisonew.
      {      
        pose proof (build_updated_u_data_lst_have_gt_mx_lmt_non_isltd
                    (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                    SFP Hcniso).
        unfold min_required.
        fold new_p_ud_lst in H.
        simpl in H.
        unfold non_isolated_unit_count.
        lia.
      }
      contradiction.
      
  -- intros Hsfp mis_flt_lmt l Hl a Hain b Hbin Hauideqb Haiso. 
            pose proof (mis_fault_hypo (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) Hsfp)
              as Hypo.
            exact (build_updated_u_data_lst_holds_mayb_nil_when_enough_non_isolated
                     (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                     Hypo Hl a Hain b Hbin Hauideqb Haiso).

      
  -- intros Hmis. 
     pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_soundness_a_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              Hypo x H1 y H2 z H3 H4 H5 H6 Hmis).
  -- intros  l Zinl Hmis. 
     pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_soundness_b_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
             Hypo x H1 y H2 z Zinl H4 H5 H6 Hmis).
  -- intros M L Hl Hgd H3d.
     pose proof (mis_fault_hypo  (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_cmpltnss_a_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              Hypo Hl x H1 y H2 z H3 H4 H5 H6 Hgd H3d).
            
  -- intros  M L Hl Zinl H3d.
     pose proof (mis_fault_hypo (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs) H) as Hypo.
     exact (build_updated_u_data_lst_holds_cmpltnss_b_prop_of_miscomp_check
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              Hypo Hl x H1 y H2 z Zinl H4 H5 H6 H3d).
            
  -- intros mis_lmt l Zinl Hmisprop.
     exact (build_updated_u_data_lst_holds_miscomp_check_true_case
              (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
              x H1 y H2 z Zinl H4 H5 H6 Hmisprop).
  -- intros Ml ms_lmt re_ms_lmt l l' Zinl' Hagrprop.
            exact (build_updated_u_data_lst_holds_agreeing_check_true_case
                     (pf_l u_ids) pf_all_unit_outputs (pf_ud_lst vs)
                     x H1 y H2 z Zinl' H4 H5 H6 Hagrprop).
            



     
     
(*  min_required <= count_of_non_isolated_units new_p_ud_lst /\
  healthy_unit_list new_p_ud_lst = [] /\
  In (uid (voter_output vs))
    (get_u_ids_of_unit_data (isolated_list new_p_ud_lst)) *)
      
- repeat split; trivial.
  inversion pf_prm_unt.
  unfold get_u_ids_of_unit_data.
  apply in_map_iff.
  exists prm_unt.
  split.  
      unfold get_u_id_of_unit_data in H.
      symmetry. trivial.
      unfold isolated_list.
      apply filter_In.
      split. trivial.
      unfold negb. unfold not_iso_check. rewrite hyp. trivial.
      
- (*  pf_validity_prop (voter_output vs) valid new_p_ud_lst ) *)
 repeat split.
 --  intro.  pose proof (Nat.lt_nge (count_of_non_isolated_units new_p_ud_lst) min_required ) as [Hcont].  pose proof (Hcont H). contradiction.
 -- intro; inversion H.
 -- intro. inversion H as  [Hb Hc].
    unfold get_u_ids_of_unit_data in Hc.
    apply in_map_iff in Hc.
    inversion Hc as [Hca [Hcb Hcc]].
    inversion pf_prm_unt.
    unfold get_u_id_of_unit_data in H0.
    rewrite H0 in Hcb.
    unfold new_p_ud_lst in H1.
    unfold isolated_list in Hcc. apply filter_In in Hcc. inversion Hcc.
    pose proof (fun_out_same_means_same_element_of_lst Hca Hcb H2 H1 
                  (mapped_list_nodup pf_new_p_ud_lst (pf_l u_ids))).
    unfold negb in H3.
    unfold not_iso_check in H3. 
    rewrite H4 in H3.
    pose proof (Helper_lemma_to_reduce_match_term H3 hyp ).
    inversion H5.
 -- trivial.
 -- inversion H.
 -- intro. inversion H.

(* valid = valid ->
  In (uid (voter_output vs))
    (get_u_ids_of_unit_data (non_isolated_list new_p_ud_lst)) *)
    
- intro.  inversion  pf_prm_unt.
  rewrite H0.
  apply in_map_iff.
  exists prm_unt.
  split; trivial.
  apply filter_In.
  split; trivial.
  unfold not_iso_check. rewrite hyp. trivial.


-   (* risky_cnt_age_prop pf_new_p_ud_lst : when miscomparing *)
  assert (miscomp_status (u_status prm_unt) <> not_miscomparing) as Hmis. {
    intro Nm. unfold prm_unt_m in h.
    rewrite h in Nm.
    inversion Nm.
  }
  assert (new_p_ud_lst = build_updated_u_data_lst (pf_l u_ids)
                        pf_all_unit_outputs (pf_ud_lst vs) ) as pf_lsd by trivial.
  unfold risky_cnt_age_prop.
  intro.
  assert ( prm_unt = proj1_sig
                       (find_data_of_a_given_unit_id pf_new_p_ud_lst
                          (uid_of_vs_out_in_uids vs pf_new_p_ud_lst)) ) as Heqprm. {
    pose proof (proj2_sig
                  (find_data_of_a_given_unit_id pf_new_p_ud_lst
                     (uid_of_vs_out_in_uids vs pf_new_p_ud_lst)) ) as [Heqid Hin].
    inversion pf_prm_unt as [Heqidprm Hinprm].
    rewrite Heqid in Heqidprm.
    symmetry in Heqidprm.
    exact (fun_out_same_means_same_element_of_lst prm_unt Heqidprm Hinprm Hin 
             (mapped_list_nodup pf_new_p_ud_lst (pf_l u_ids))).
  }
  pose proof (risky_cnt_age_prop_satisfied_miscomp_or_mayb_case
                pf_lsd e  pf_prm_unt Hmis hyp) as Hreq.
  rewrite Heqprm in Hreq.
  exact Hreq.


- (* miscomparing case 
  valid <> not_valid ->
  forall x : unit_data,
  In x new_p_ud_lst ->
  iso_status (u_status x) = not_isolated ->
  S (output_age vs) - risky_count (u_status x) < persistence_lmt *)
  assert (new_p_ud_lst = build_updated_u_data_lst (pf_l u_ids)
                          pf_all_unit_outputs (pf_ud_lst vs) ) as pf_lsd by trivial.

  assert (S (output_age vs) = risky_count (u_status prm_unt) ) as Hageeqrc.
  {
    assert (miscomp_status (u_status prm_unt) <> not_miscomparing) as Hmis. {
      intro Nm. unfold prm_unt_m in h.
      rewrite h in Nm.
      inversion Nm.
    }
    exact (risky_cnt_age_prop_satisfied_miscomp_or_mayb_case
             pf_lsd e pf_prm_unt Hmis hyp).
  }

  assert ( S (output_age vs) < persistence_lmt ). {
    rewrite Hageeqrc.
    exact (not_isltd_rc_lt_pc hyp).
  }
  lia.
   
-
  (* pf_age_validity : miscomparing case *)

  unfold persistence_lmt. repeat split.
   -- intro.
      assert (miscomp_status (u_status prm_unt) <> not_miscomparing) as Hmis. {
        intro Nm. unfold prm_unt_m in h.
        rewrite h in Nm.
        inversion Nm.
      }
      assert (new_p_ud_lst = build_updated_u_data_lst (pf_l u_ids)
                            pf_all_unit_outputs (pf_ud_lst vs) ) as pf_lsd by trivial.
      unfold risky_cnt_age_prop.
      pose proof  (risky_cnt_age_prop_satisfied_miscomp_or_mayb_case
                     pf_lsd e pf_prm_unt Hmis hyp) as Hagerc.
      pose proof (pf_risky_count (u_status prm_unt)) as [Hlepc [Hiso_cs1 Hiso_cs2]].
      unfold persistence_lmt in *.
      rewrite Hagerc.
      inversion Hlepc.
      pose proof (Hiso_cs1 H1).
      rewrite H0 in hyp.
      inversion hyp.
      lia.
   --  intro.
      (* risky_cnt_age_prop pf_new_p_ud_lst : when miscomparing *)
      assert (miscomp_status (u_status  prm_unt) <> not_miscomparing) as Hmis. {
        intro Nm. unfold prm_unt_m in h.
        rewrite h in Nm.
        inversion Nm.
      }
      assert (new_p_ud_lst = build_updated_u_data_lst (pf_l u_ids)
                            pf_all_unit_outputs (pf_ud_lst vs) ) as pf_lsd by trivial.
      unfold risky_cnt_age_prop.
      pose proof  (risky_cnt_age_prop_satisfied_miscomp_or_mayb_case
                     pf_lsd e  pf_prm_unt Hmis hyp) as Hagerc.
      rewrite Hagerc in H.
      assert (~ risky_count (u_status prm_unt) <= S persistence_lmt_minus_1)
        as Hnot by lia.
      pose proof (pf_risky_count (u_status prm_unt)) as [Hlepc [Hiso_cs1 Hiso_cs2]].
      unfold persistence_lmt in *.
      contradiction.
   -- intro H. inversion H.

    
-   (*  pf_validity_prop (voter_output vs) valid new_p_ud_lst *)
  repeat split. 
    -- intro. pose proof (Nat.lt_nge (count_of_non_isolated_units new_p_ud_lst) min_required ) as [Hcont]. pose proof (Hcont H).
     contradiction.
  -- intro; inversion H. 
  -- intro. inversion H as  [Hb Hc].
     unfold get_u_ids_of_unit_data in Hc.
    apply in_map_iff in Hc.
    inversion Hc as [Hca [Hcb Hcc]]. 
    inversion  pf_prm_unt.
    unfold get_u_id_of_unit_data in H0.
    rewrite H0 in Hcb.
    unfold new_p_ud_lst in H1.
    unfold isolated_list in Hcc. apply filter_In in Hcc. inversion Hcc.
    
    pose proof (fun_out_same_means_same_element_of_lst Hca Hcb H2 H1 
                  (mapped_list_nodup pf_new_p_ud_lst (pf_l u_ids))).
    unfold negb in H4.
    unfold not_iso_check in H4. 
    rewrite H4 in H3.
    pose proof (Helper_lemma_to_reduce_match_term H3 hyp ).
    inversion H5.

  -- inversion H.
  -- inversion H.
  -- intro; inversion H.
     
- (*valid = valid ->
  In (uid (voter_output vs))
    (get_u_ids_of_unit_data (non_isolated_list new_p_ud_lst))*)
  
  intro.  inversion  pf_prm_unt.
  rewrite H0.
  apply in_map_iff.
  exists prm_unt.
  split; trivial.
  apply filter_In.
  split; trivial.
  unfold not_iso_check. rewrite hyp. trivial.

   
- (* risky_cnt_age_prop bad case *)

  assert (new_p_ud_lst = build_updated_u_data_lst (pf_l u_ids)
                        pf_all_unit_outputs (pf_ud_lst vs) ) as pf_lsd by trivial.
  intro.
  assert ( prm_unt = proj1_sig
                       (find_data_of_a_given_unit_id pf_new_p_ud_lst
                          (uid_of_vs_out_in_uids vs pf_new_p_ud_lst)) ) as Heqprm. {
    pose proof (proj2_sig
                  (find_data_of_a_given_unit_id pf_new_p_ud_lst
                     (uid_of_vs_out_in_uids vs pf_new_p_ud_lst)) ) as [Heqid Hin].
    inversion pf_prm_unt as [Heqidprm Hinprm].
    rewrite Heqid in Heqidprm.
    symmetry in Heqidprm.
    exact (fun_out_same_means_same_element_of_lst prm_unt Heqidprm Hinprm Hin 
             (mapped_list_nodup pf_new_p_ud_lst (pf_l u_ids))).
  }
  pose proof (risky_cnt_age_prop_satisfied_bad
             pf_lsd e   pf_prm_unt h2 hyp) as Hreq.
  rewrite Heqprm in Hreq.
  exact Hreq.

- (* bad case
    valid <> not_valid ->
    forall x :   unit_data,
    In x new_p_ud_lst ->
    iso_status (u_status x) = not_isolated ->
    S (output_age vs) - risky_count (u_status x) < persistence_lmt *)
  assert (new_p_ud_lst = build_updated_u_data_lst (pf_l u_ids)
                        pf_all_unit_outputs (pf_ud_lst vs) ) as pf_lsd by trivial.
  
  assert (S (output_age vs) = risky_count (u_status prm_unt) ) as Hageeqrc.
  {
    exact (risky_cnt_age_prop_satisfied_bad
             pf_lsd e pf_prm_unt h2 hyp).
  }

  intros.
  assert ( S (output_age vs) < persistence_lmt ). {
    rewrite Hageeqrc.
    exact (not_isltd_rc_lt_pc hyp).
  }
  lia.

-  (* pf_age_validity : bad case *)

  unfold persistence_lmt. repeat split.
   -- intro.
      assert (new_p_ud_lst = build_updated_u_data_lst (pf_l u_ids)
                            pf_all_unit_outputs (pf_ud_lst vs) ) as pf_lsd by trivial.
      unfold risky_cnt_age_prop.
      pose proof  ((risky_cnt_age_prop_satisfied_bad
             pf_lsd e  pf_prm_unt h2 hyp)) as Hagerc.
      pose proof (pf_risky_count (u_status prm_unt)) as [Hlepc [Hiso_cs1 Hiso_cs2]].
      unfold persistence_lmt in *.
      rewrite Hagerc.
      inversion Hlepc.
      pose proof (Hiso_cs1 H1).
      rewrite H0 in hyp.
      inversion hyp.
      lia.
   --  intro.
      assert (new_p_ud_lst = build_updated_u_data_lst (pf_l u_ids)
                            pf_all_unit_outputs (pf_ud_lst vs) ) as pf_lsd by trivial.
      unfold risky_cnt_age_prop.
      pose proof  (risky_cnt_age_prop_satisfied_bad
             pf_lsd e  pf_prm_unt h2 hyp) as Hagerc.
      rewrite Hagerc in H.
      assert (~ risky_count (u_status prm_unt) <= S persistence_lmt_minus_1)
        as Hnot by lia.
      pose proof (pf_risky_count (u_status prm_unt)) as [Hlepc [Hiso_cs1 Hiso_cs2]].
      unfold persistence_lmt in *.
      contradiction.
   -- intro H. inversion H.
-   
  
(*  In (uid (u_output prm_unt))
    (get_u_ids_of_unit_data new_p_ud_lst) *)    
  inversion pf_prm_unt.
  unfold get_u_ids_of_unit_data.
  apply in_map_iff. exists prm_unt.
  split; trivial.
 
  
- (* u_output prm_unt = u_output prm_unt /\ healthy_data prm_unt *)
  split; trivial.
  unfold healthy_data.
  repeat split; trivial. 
  
- (*  0 = 0 <-> valid = valid /\ In prm_unt new_p_ud_lst *)
  inversion pf_prm_unt.
  repeat split.
  trivial.

  
- (*  pf_validity_prop (u_output prm_unt) valid new_p_ud_lst *)
  repeat split.
  -- intro.
     pose proof (Nat.lt_nge (count_of_non_isolated_units new_p_ud_lst) min_required) as [C].
     pose proof (C H). contradiction.
  -- intro; inversion H.
  -- intro. inversion H as  [Hb Hc].
     unfold get_u_ids_of_unit_data in Hc.
    apply in_map_iff in Hc.
    inversion Hc as [Hca [Hcb Hcc]]. 
    inversion pf_prm_unt.
    unfold get_u_id_of_unit_data in H0.
    unfold new_p_ud_lst in H1.
    unfold isolated_list in Hcc. apply filter_In in Hcc. inversion Hcc.
    pose proof (fun_out_same_means_same_element_of_lst Hca Hcb H2 H1 
                  (mapped_list_nodup pf_new_p_ud_lst (pf_l u_ids))).
    unfold negb in H4.
    unfold not_iso_check in H4. 
    rewrite H4 in H3.
    pose proof (Helper_lemma_to_reduce_match_term H3 hyp ).
    inversion H5.

  -- inversion H.
  -- inversion H.
  -- intro; inversion H.   
- (*  valid = valid ->
  In (uid (u_output prm_unt))
    (get_u_ids_of_unit_data (non_isolated_list new_p_ud_lst)) *)
  intro.
  inversion pf_prm_unt.
  apply in_map_iff.
  exists prm_unt.
  split; trivial.
  apply filter_In.
  split; trivial.
  unfold not_iso_check. rewrite hyp. trivial.
  
  
-  (*  risky_cnt_age_prop  healthy case *)
  unfold risky_cnt_age_prop. intro.
  remember ((find_data_of_a_given_unit_id pf_new_p_ud_lst
              match pf_prm_unt with
              | conj _ H1 =>
                  match
                    in_map_iff (fun a : unit_data => uid (u_output a)) new_p_ud_lst
                      (uid (u_output prm_unt))
                  with
                  | conj _ H3 => H3
                  end
                    (ex_intro
                       (fun x : unit_data =>
                          uid (u_output x) = uid (u_output prm_unt) /\
                            In x new_p_ud_lst) prm_unt (conj eq_refl H1))
              end)) as f_s.
  remember (proj1_sig f_s) as s.
  remember (proj2_sig f_s) as fs.
  inversion fs as  [Hsuid Hsin].
  assert ( prm_unt = s ). {
    inversion pf_prm_unt as [Hcsuid Hcsin].
    rewrite <- Heqs in Hsuid, Hsin.
    exact ( fun_out_same_means_same_element_of_lst prm_unt Hsuid Hcsin Hsin 
              (mapped_list_nodup pf_new_p_ud_lst (pf_l u_ids))).
  }        
  pose proof (pf_healthy prm_unt) as [PFh1 PFh2].
  assert (healthy_data prm_unt).
  unfold healthy_data.
  repeat split; trivial.
  rewrite Heqf_s in Heqs.
  symmetry. pose proof (PFh2 H1).
  rewrite H0 in H2. rewrite Heqs in H2. trivial.

- intros. unfold persistence_lmt. lia.


-   (* pf_age_validity : healthy case *)

  unfold persistence_lmt. repeat split.
  -- intro.
     lia.
  --  intro.
      inversion H.
  -- intro H. inversion H.

-  (*  pf_validity_prop (voter_output vs) valid new_p_ud_lst *)
  repeat split.
  -- intro.
     pose proof (Nat.lt_nge (count_of_non_isolated_units new_p_ud_lst) min_required) as [C].
     pose proof (C H).
     contradiction.
  -- intro; inversion H. 
  -- intro. inversion H as  [Hb Hc].
     unfold get_u_ids_of_unit_data in Hc.
    apply in_map_iff in Hc.
    inversion Hc as [Hca [Hcb Hcc]].
    inversion pf_prm_unt.
    unfold get_u_id_of_unit_data in H0.
    rewrite H0 in Hcb.
    unfold new_p_ud_lst in H1.
    unfold isolated_list in Hcc. apply filter_In in Hcc. inversion Hcc.
    pose proof (fun_out_same_means_same_element_of_lst Hca Hcb H2 H1 
                  (mapped_list_nodup pf_new_p_ud_lst (pf_l u_ids))).
    unfold negb in H4.
    unfold not_iso_check in H4. 
    rewrite H4 in H3.
    pose proof (Helper_lemma_to_reduce_match_term H3 hyp ).
    inversion H5.
    
  -- inversion H.
  -- inversion H.
  -- intro; inversion H.

- (*valid = valid ->
  In (uid (voter_output vs))
    (get_u_ids_of_unit_data (non_isolated_list new_p_ud_lst))*)
  
  intro. inversion pf_prm_unt.
  rewrite H0.
  apply in_map_iff.
  exists prm_unt.
  split; trivial.
  apply filter_In.
  split; trivial.
  unfold not_iso_check. rewrite hyp. trivial.


-
  (* risky_cnt_age_prop pf_new_p_ud_lst : when maybe_miscomparing *)
   assert (new_p_ud_lst = build_updated_u_data_lst (pf_l u_ids)
                          pf_all_unit_outputs (pf_ud_lst vs) ) as pf_lsd by trivial.
   intro.
   assert (miscomp_status (u_status prm_unt) <> not_miscomparing) as Hmis. {
     intro Nm. unfold prm_unt_m in h.
     rewrite h in Nm.
     inversion Nm.
   }
   assert ( prm_unt = proj1_sig
                        (find_data_of_a_given_unit_id pf_new_p_ud_lst
                           (uid_of_vs_out_in_uids vs pf_new_p_ud_lst)) ) as Heqprm. {
     pose proof (proj2_sig
                   (find_data_of_a_given_unit_id pf_new_p_ud_lst
                      (uid_of_vs_out_in_uids vs pf_new_p_ud_lst)) ) as [Heqid Hin].
     inversion pf_prm_unt as [Heqidprm Hinprm].
     rewrite Heqid in Heqidprm.
     symmetry in Heqidprm.
     exact (fun_out_same_means_same_element_of_lst prm_unt Heqidprm Hinprm Hin 
              (mapped_list_nodup pf_new_p_ud_lst (pf_l u_ids))).
   }
   pose proof (risky_cnt_age_prop_satisfied_miscomp_or_mayb_case
                 pf_lsd e  pf_prm_unt Hmis hyp) as Hreq.
   rewrite Heqprm in Hreq.
   exact Hreq.
-
  (* maybe_miscomparing case 
  valid <> not_valid ->
  forall x : unit_data,
  In x new_p_ud_lst ->
  iso_status (u_status x) = not_isolated ->
  S (output_age vs) - risky_count (u_status x) < persistence_lmt *)
  assert (new_p_ud_lst = build_updated_u_data_lst (pf_l u_ids)
                        pf_all_unit_outputs (pf_ud_lst vs) ) as pf_lsd by trivial.
  
  assert (S (output_age vs) = risky_count (u_status prm_unt) ) as Hageeqrc.
  {
    assert (miscomp_status (u_status prm_unt) <> not_miscomparing) as Hmis. {
      intro Nm. unfold prm_unt_m in h.
      rewrite h in Nm.
      inversion Nm.
    }
    exact (risky_cnt_age_prop_satisfied_miscomp_or_mayb_case
             pf_lsd e pf_prm_unt Hmis hyp).
  }
  
  assert ( S (output_age vs) < persistence_lmt ). {
    rewrite Hageeqrc.
    exact (not_isltd_rc_lt_pc hyp).
  }
  lia.

-
    (* pf_age_validity : maybe_miscomparing case *)

  unfold persistence_lmt. repeat split.
   -- intro.
      assert (miscomp_status (u_status prm_unt) <> not_miscomparing) as Hmis. {
        intro Nm. unfold prm_unt_m in h.
        rewrite h in Nm.
        inversion Nm.
      }
      assert (new_p_ud_lst = build_updated_u_data_lst (pf_l u_ids)
                            pf_all_unit_outputs (pf_ud_lst vs) ) as pf_lsd by trivial.
      unfold risky_cnt_age_prop.
      pose proof  (risky_cnt_age_prop_satisfied_miscomp_or_mayb_case
                     pf_lsd e pf_prm_unt Hmis hyp) as Hagerc.
      pose proof (pf_risky_count (u_status prm_unt)) as [Hlepc [Hiso_cs1 Hiso_cs2]].
      unfold persistence_lmt in *.
      rewrite Hagerc.
      inversion Hlepc.
      pose proof (Hiso_cs1 H1).
      rewrite H0 in hyp.
      inversion hyp.
      lia.
   --  intro.
      (* risky_cnt_age_prop pf_new_p_ud_lst : when miscomparing *)
      assert (miscomp_status (u_status prm_unt) <> not_miscomparing) as Hmis. {
        intro Nm. unfold prm_unt_m in h.
        rewrite h in Nm.
        inversion Nm.
      }
      assert (new_p_ud_lst = build_updated_u_data_lst (pf_l u_ids)
                            pf_all_unit_outputs (pf_ud_lst vs) ) as pf_lsd by trivial.
      unfold risky_cnt_age_prop.
      pose proof  (risky_cnt_age_prop_satisfied_miscomp_or_mayb_case
                     pf_lsd e pf_prm_unt Hmis hyp) as Hagerc.
      rewrite Hagerc in H.
      assert (~ risky_count (u_status prm_unt) <= S persistence_lmt_minus_1)
        as Hnot by lia.
      pose proof (pf_risky_count (u_status prm_unt)) as [Hlepc [Hiso_cs1 Hiso_cs2]].
      unfold persistence_lmt in *.
      contradiction.
   -- intro H. inversion H.


  
Defined.


Lemma prime_unit_does_not_switch_frequently
  (vs : voter_state)
  {all_unit_outputs: list unit_output}
  (pf_all_unit_outputs : get_u_ids_of_unit_output all_unit_outputs =  l (u_ids)) :
  let new_vs := voter_state_transition vs pf_all_unit_outputs in
  voter_validity (proj1_sig new_vs) <> not_valid
    ->
      (output_age (proj1_sig new_vs) = S (output_age vs) \/
         output_age (proj1_sig new_vs) = 0 )
        
      /\ ((uid (voter_output vs)) <> (uid (voter_output (proj1_sig new_vs)))
         -> output_age (proj1_sig new_vs) = 0)
          
      /\ 
        ((output_age vs) < persistence_lmt -1 
         -> (uid (voter_output vs)) = (uid (voter_output (proj1_sig new_vs)))).
Proof.
  intros new_vs Hnvsvld.
  remember (proj2_sig new_vs). 
  inversion v as [Hr [Hnoswitch [T1 [T11 [Hageprop [Hsameout [T2 [T3 T4]]]]]]]]. 
  clear T1 T11 T2 T3 T4. 
  repeat split.
  -  exact (Hageprop Hnvsvld).
  -   intro Huidneq.
     pose proof (Hnoswitch Huidneq).
     pose proof (Hageprop Hnvsvld) as Hage.
     inversion Hage as [HageS | Hage0].
     assert (output_age (proj1_sig new_vs) <> 0 ) as Hagen0. {
       intro Hage0. rewrite Hage0 in HageS.
       inversion HageS.
     }
     pose proof (Hsameout Hagen0) as Hsmout.
     assert (uid (voter_output vs) = uid (voter_output (proj1_sig new_vs))). {
       rewrite Hsmout.
       reflexivity.
     }
     contradiction.
     exact Hage0.
  -  intro.
     assert (voter_validity vs = valid ) as Hv. {
       pose proof (pf_age_validity vs) as [[Hvld1 Hvld2] T].
       assert (output_age vs < persistence_lmt) as Hp by lia.
       exact (Hvld1 Hp).
     }
 (* destruct (Nat.eq_dec (output_age vs) 0 ). { 
    pose proof (pf_age vs) as [Hage0prop T].
    pose proof (Hage0prop e) as [Hvsvld Hcwin].
    clear T  Hage0prop. *)
    pose proof (pf_risky_cnt vs Hv).
    remember  (find_data_of_a_given_unit_id (pf_ud_lst vs) (pf_v_output vs)) as Hvsout.
    
    destruct (u_id_eq_dec  (uid (voter_output vs)) (uid (voter_output (proj1_sig new_vs)) ) ) as [Heqout | Hdifout].
    -- exact Heqout.
    --  
      pose proof (Hnoswitch Hdifout) as Hvsoutiso.
      apply in_map_iff in Hvsoutiso.
      inversion Hvsoutiso as [x [Huidx Hxiniso]].
      apply filter_In in Hxiniso.
      inversion Hxiniso as [Hxinnew Hxisoprop].
      apply negb_true_iff in Hxisoprop.
      pose proof (nisoc_f_isltd Hxisoprop) as Hxiso.
      pose proof (proj2_sig Hvsout) as [Hyequid Hyin].
      remember (proj1_sig Hvsout) as y. 
      rewrite <- Huidx in Hyequid.
      symmetry in Hyequid.
      pose proof (Hr y Hyin x Hxinnew Hyequid) as Hrcprop.
      unfold risky_cnt_prop in Hrcprop.
      simpl in H0.
      
      pose proof (proj2_sig Hvsout) as Hy2prop.
      inversion Hy2prop as [Huidy2 Hy2in].
      remember (proj1_sig Hvsout) as y2.
      assert ( y =  y2 ) as Heqy2y. {
        rewrite <- Huidx in Huidy2.
        rewrite <- Hyequid in Huidy2.
        exact (fun_out_same_means_same_element_of_lst y Huidy2 Hyin Hy2in 
                 (mapped_list_nodup (pf_ud_lst vs) (pf_l u_ids)) ).
      }
      rewrite <- Heqy2y in *.
      assert (iso_status (u_status y) = not_isolated ). {
        simpl in H0.
        
        pose proof (pf_risky_count (u_status y) ) as [Hrclepc [Hrceqpciso Hisorceqpc]].
        destruct (iso_status (u_status y)).
        assert (isolated = isolated ) as Htmp by reflexivity.
        pose proof (Hisorceqpc Htmp) as Hisoy.
        clear Htmp.
        rewrite <- H0 in Hisoy.
        rewrite Hisoy in H.
        assert (~ persistence_lmt < persistence_lmt - 1) as Hnot by lia.
        contradiction.
        reflexivity.
      } 
      pose proof (pf_risky_count (u_status x) ) as [Hrclepc [Hrceqpciso Hisorceqpc]].
      pose proof (Hisorceqpc Hxiso) as Hrceqpc.
      pose proof (Hrcprop H1) as [Hrceq0orS].
      inversion Hrceq0orS as [Hrceq0 | HrceqS]. 
      --- rewrite Hrceq0 in Hrceqpc.
          inversion Hrceqpc.
      ---
        assert (~ risky_count (u_status y) < persistence_lmt - 1 ) by lia.
        rewrite H0 in H.
        contradiction.
Qed.



Require Extraction.

Extraction Language OCaml.

Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Constant persistence_lmt_minus_1 => "(S (S (S (S O))))".
Extract Constant num_units => "(S (S (S (S (S O)))))".
Extract Constant delta_minus_1 => "(S O)".
Extract Constant simul_max_fault_minus_1 => "(S O)".
Extraction "./Extracted_OCaml_Code/voter_state_transition.ml" voter_state_transition.


