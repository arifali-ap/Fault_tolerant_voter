From Stdlib  Require Import  Nat.       
From Stdlib  Require Import Bool.    
From Stdlib  Require Import List. 
Import ListNotations.
From Stdlib  Require Import Lia.
Import Arith.
From Stdlib Require Import Logic.Eqdep_dec.
Require Import BTProject.config.
Require Import BTProject.voter_state.
Require Import BTProject.library.
Require Import BTProject.combine.
Require Import BTProject.find_faulty.
Require Import BTProject.gen_lemmas.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Logic.Decidable.
From Stdlib Require Import Logic.Decidable.
From Stdlib Require Import Classes.DecidableClass.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Init.Specif. 



Definition simul_fault_prop
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  
  :=
  let comb_lst := combine_lists pf_uids pf_input pf_ud_lst in
  let not_iso_output_lst := map (fun x => fst x)
                              ( filter (fun y => not_iso_check (snd y) ) comb_lst) in
  let bad_non_iso_lst := filter (fun y => negb (hw_good_unit_check y) )
                           not_iso_output_lst in
  let good_dev_grnd_truth_lst := filter (fun y => andb (hw_good_unit_check y)
                                                 (grnd_truth_dlta_dev_check y) )
                                   not_iso_output_lst in
  
  length ( bad_non_iso_lst ) +
  length ( good_dev_grnd_truth_lst)  <= simul_max_fault. 

 

Lemma mis_fault_hypo
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  :
  simul_fault_prop pf_uids pf_input pf_ud_lst ->
  let l := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst ) in
  let mis_flt_lmt := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
  length (dlta_dev_lst_grnd_truth l ) <= mis_flt_lmt.
Proof.
  intros.  
  unfold dlta_dev_lst_grnd_truth. 
  unfold mis_flt_lmt.
  unfold flt_lmt_among_good.
  unfold simul_fault_prop in H.
  unfold num_of_bad_and_non_isolated.
  unfold combine_lists in *. 
  remember (hw_good_unit_check ) as f. 
  remember (fun y => grnd_truth_dlta_dev_check y) as g.
  remember (map (fun x : unit_output * unit_data => fst x)
              (filter (fun y : unit_output * unit_data => not_iso_check (snd y))
                 (combine input ud_lst))). 

  assert ( (filter g l)
           = filter (fun y : unit_output => f y && g y) l0 ). {
    unfold l, all_good_non_iso_lst, combine_lists, non_isltd_comb_lst.
    simpl.
    rewrite <- Heqf,  <- Heql0.
    pose proof ( filter_andb_eq_filter_on_filter l0 f g).
    rewrite H0 in H.
    symmetry. trivial.
  }
  rewrite <- H0 in H.
  lia.
Qed.





Definition build_single_u_data_prop
  (x : unit_output * unit_data)
  (new : unit_data)
  (dev_lst mayb_lst: list unit_id )
  :=
  (risky_cnt_prop (snd x) new )
  /\ (u_output new) = (fst x)
  /\ (iso_status (snd x).(u_status) = isolated
      -> iso_status new.(u_status) = isolated)
  /\ (iso_status (new).(u_status) = not_isolated
      -> iso_status (snd x).(u_status) = not_isolated)
  /\ (iso_status (snd x).(u_status) = not_isolated ->
      (miscomp_status (u_status new) = miscomparing ->
       hw_hlth (reading (fst x)) = good
       /\ In (uid (fst x) ) dev_lst)
      /\ (In (uid (fst x) ) dev_lst  ->
          ~ In (uid (fst x) ) mayb_lst ->
          hw_hlth (reading (fst x)) = good ->
          miscomp_status (u_status new) = miscomparing
         ) 
      /\
        (miscomp_status (u_status new) = maybe_miscomparing
         ->  hw_hlth (reading (fst x)) = good
            /\In (uid (fst x) ) mayb_lst)
      /\ (In (uid (fst x) ) mayb_lst ->
          ~ In (uid (fst x) ) dev_lst  ->
         hw_hlth (reading (fst x)) = good ->
         miscomp_status (u_status new) = maybe_miscomparing
        )).

  
Definition incr_risky_count_and_update_iso_status_bad_case
  {x : unit_output * unit_data} 
  (pf_sd : (snd x).(u_status).(iso_status) = not_isolated)
  ( pf_bad : (fst x).(reading).(hw_hlth) = bad )
  :  unit_data.
(* This function takes a non-isolated unit and with current reading is a bad signal,
   and so it increment risky_count and if needed, isolate *)

  refine (
      let sd_s := (snd x).(u_status) in
      let so := (fst x) in
      let cnt := sd_s.(risky_count) in
      match lt_dec (S cnt) ( persistence_lmt )  with
      | left _  =>  unit_data_build so (unit_status_build (sd_s.(iso_status)) not_miscomparing (S sd_s.(risky_count)) _  ) _
      | right _ =>  unit_data_build so (unit_status_build isolated not_miscomparing (S sd_s.(risky_count)) _  )  _
      end 
    ).
  - split.
    -- intro.  exfalso; inversion H.
    -- intro. inversion H as [ Hab [Hb Hc]]. unfold so in Hab.
       rewrite pf_bad in Hab. exfalso; inversion Hab.
  - split.
    -- intro.  exfalso; inversion H.
    -- intro. inversion H as [ Hab [Hb Hc]]. unfold so in Hab.
       rewrite pf_bad in Hab. exfalso; inversion Hab.

       Unshelve.
  
       --- { split. apply Nat.lt_le_incl in l.
             trivial.
             split.
             - intro. exfalso. unfold cnt in l. rewrite H in l.
                apply Nat.lt_irrefl in l. trivial.
             - intro. pose proof (pf_risky_count sd_s). inversion H0. inversion H2.
                pose proof (H4 H).  unfold cnt in l.   rewrite H5 in l.
                exfalso. 
                apply Nat.nlt_succ_diag_l in l. trivial.
           }
       --- {  split. pose proof (pf_risky_count sd_s). inversion H as [Ha Hb].
              apply not_lt in n.
              inversion n.
              - unfold persistence_lmt. rewrite H1. unfold cnt.
                trivial.
              - unfold cnt in *.
                pose proof (Nat.le_antisymm (risky_count sd_s) persistence_lmt Ha H1).
                inversion Hb.
                pose proof (H3 H2). exfalso. unfold sd_s in H5.   rewrite H5 in pf_sd. inversion pf_sd.
              -  split.
                 -- intro. trivial.
                 -- intro. apply not_lt in n. inversion n.
                    --- unfold persistence_lmt.  symmetry. apply eq_S in H1. trivial.
                    --- pose proof (pf_risky_count sd_s).
                        inversion H2.
                        pose proof (Nat.le_antisymm (risky_count sd_s) persistence_lmt H3 H1).
                        inversion H4.
                        pose proof (H6 H5).
                        exfalso.  unfold sd_s in H8. rewrite H8 in pf_sd. inversion pf_sd.
           }
Defined.


Definition build_single_u_data_healthy_case
  {x : unit_output * unit_data}
  {dev_lst maybe_lst : list unit_id}
  ( pf_iso : (snd x).(u_status).(iso_status) = not_isolated)
  ( pf_good : (fst x).(reading).(hw_hlth) = good)
  (pf_miscomp : ~ In ( uid (fst x) )  maybe_lst /\ ~ In (uid (fst x) ) dev_lst ): unit_data.
  
(* This function takes a non-isolated unit and with current reading is a good and non-miscomparing signal,
   and so reset risky_count and miscom_status is set to not-miscomparing*)
  
  refine (
      unit_data_build (fst x) (unit_status_build ((snd x).(u_status).(iso_status)) not_miscomparing 0 _  ) _ 
    ).
  - split.
    -- intro.
       repeat split; trivial.
    -- intro. trivial. 

       Unshelve.
  
       + { split.
           - apply Nat.le_0_l.
           - split.
             -- intro. exfalso. unfold persistence_lmt in *. inversion H.

             -- intro. exfalso. rewrite H in pf_iso; inversion pf_iso.
           }
Defined. 





Definition incr_risky_count_and_update_iso_status_miscomp_case
  {x : unit_output * unit_data} 
  (pf_sd : (snd x).(u_status).(iso_status) = not_isolated)
  {dev_lst : list unit_id}
  ( pf_good : (fst x).(reading).(hw_hlth) = good)
  (pf_miscomp : In (uid (fst x))   dev_lst )
  :  unit_data.

(* This function takes a non-isolated unit and with current reading is good and miscomparing with other unit signal values,
   and so it increment risky_count and if needed, isolate *)
  
  refine (
      let sd_s := (snd x).(u_status) in
      let so := (fst x) in
      let cnt := sd_s.(risky_count) in
      match lt_dec (S cnt) (persistence_lmt )  with
      | left _  =>  unit_data_build so (unit_status_build (sd_s.(iso_status)) miscomparing (S sd_s.(risky_count)) _  ) _
      | right _ =>  unit_data_build so (unit_status_build isolated            miscomparing (S sd_s.(risky_count)) _  )  _
      end 
    ).
  - split.
    -- intro.  exfalso; inversion H.
    -- intro. inversion H as [Haa [Hb Hc]].
       exfalso; inversion Hc.
  - split.
    -- intro.  exfalso; inversion H.
    -- intro. inversion H as [Haa  [Hb Hc]].
       exfalso; inversion Hc.

       Unshelve.
  
       --- { split. apply Nat.lt_le_incl in l.
             trivial.
             split.
             - intro. exfalso. unfold cnt in l. rewrite H in l.
                apply Nat.lt_irrefl in l. trivial.
             - intro. pose proof (pf_risky_count sd_s). inversion H0. inversion H2.
                pose proof (H4 H).  unfold cnt in l.   rewrite H5 in l.
                exfalso. 
                apply Nat.nlt_succ_diag_l in l. trivial.
           }
       --- {  split. pose proof (pf_risky_count sd_s). inversion H as [Ha Hb].
              apply not_lt in n.
              inversion n.
              - unfold persistence_lmt. rewrite H1. unfold cnt.
                trivial.
              - unfold cnt in *.
                pose proof (Nat.le_antisymm (risky_count sd_s) persistence_lmt Ha H1).
                inversion Hb.
                pose proof (H3 H2). exfalso. unfold sd_s in H5.   rewrite H5 in pf_sd. inversion pf_sd.
              -  split.
                 -- intro. trivial.
                 -- intro. apply not_lt in n. inversion n.
                    --- unfold persistence_lmt.  symmetry. apply eq_S in H1. trivial.
                    --- pose proof (pf_risky_count sd_s).
                        inversion H2.
                        pose proof (Nat.le_antisymm (risky_count sd_s) persistence_lmt H3 H1).
                        inversion H4.
                        pose proof (H6 H5).
                        exfalso. unfold sd_s in H8;  rewrite H8 in pf_sd. inversion pf_sd.
           } 
Defined.





Definition incr_risky_count_and_update_iso_status_maybe_case {x : unit_output * unit_data} 
  (pf_sd : (snd x).(u_status).(iso_status) = not_isolated)
  {maybe_lst : list unit_id}
  ( pf_good : (fst x).(reading).(hw_hlth) = good)
  (pf_miscomp : In ( uid (fst x) )  maybe_lst )
  :  unit_data.

(* This function takes a non-isolated unit and with current reading is good and maybe miscomparing with other unit signal values,
   and so it increment risky_count and if needed, isolate *)
  
  refine (
      let sd_s := (snd x).(u_status) in
      let so := (fst x) in
      let cnt := sd_s.(risky_count) in
      match lt_dec (S cnt) (persistence_lmt )  with
      | left _  =>  unit_data_build so (unit_status_build (sd_s.(iso_status)) maybe_miscomparing (S sd_s.(risky_count)) _  ) _
      | right _ =>  unit_data_build so (unit_status_build isolated   maybe_miscomparing (S sd_s.(risky_count)) _  )  _
      end 
    ).
  - split.
    -- intro.  exfalso; inversion H.
    -- intro. inversion H as [Haa [Hb Hc]].
       exfalso; inversion Hc.
  - split.
    -- intro.  exfalso; inversion H.
    -- intro. inversion H as [Haa  [Hb Hc]].
       exfalso; inversion Hc.

       Unshelve.
  
       --- { split. apply Nat.lt_le_incl in l.
             trivial.
             split.
             - intro. exfalso. unfold cnt in l. rewrite H in l.
                apply Nat.lt_irrefl in l. trivial.
             - intro. pose proof (pf_risky_count sd_s). inversion H0. inversion H2.
                pose proof (H4 H).  unfold cnt in l.   rewrite H5 in l.
                exfalso. 
                apply Nat.nlt_succ_diag_l in l. trivial.
           }
       --- {  split. pose proof (pf_risky_count sd_s). inversion H as [Ha Hb].
              apply not_lt in n.
              inversion n.
              - unfold persistence_lmt. rewrite H1. unfold cnt.
                trivial.
              - unfold cnt in *.
                pose proof (Nat.le_antisymm (risky_count sd_s) persistence_lmt Ha H1).
                inversion Hb.
                pose proof (H3 H2). exfalso. unfold sd_s in H5.   rewrite H5 in pf_sd. inversion pf_sd.
              -  split.
                 -- intro. trivial.
                 -- intro. apply not_lt in n. inversion n.
                    --- unfold persistence_lmt.  symmetry. apply eq_S in H1. trivial.
                    --- pose proof (pf_risky_count sd_s).
                        inversion H2.
                        pose proof (Nat.le_antisymm (risky_count sd_s) persistence_lmt H3 H1).
                        inversion H4.
                        pose proof (H6 H5).
                        exfalso. unfold sd_s in H8;  rewrite H8 in pf_sd. inversion pf_sd.
           } 
Defined.




Definition update_u_data_frm_comb_elmnt_not_isoltd
  ( x: unit_output * unit_data )
  ( dev_lst : list unit_id )
  ( maybe_lst : list unit_id )
  ( pf_iso : (iso_status (u_status (snd x)) ) = not_isolated )
  :  { sd : unit_data | build_single_u_data_prop x sd dev_lst maybe_lst }.

  refine (

  let hw_stat := (hw_hlth (reading (fst x) )) in
  match hw_stat as HW return
        hw_stat = HW-> { sd : unit_data | build_single_u_data_prop x sd dev_lst maybe_lst } with
  | bad   => fun hyp => exist _ (incr_risky_count_and_update_iso_status_bad_case  pf_iso hyp ) _
  | good  => fun hyp => match in_dec u_id_eq_dec (uid (fst x)) dev_lst with
                        | left e => exist _
                                 (incr_risky_count_and_update_iso_status_miscomp_case
                                    pf_iso hyp e ) _ 
                        | right e =>
                            match in_dec u_id_eq_dec (uid (fst x)) maybe_lst with
                            | left f => exist _
                                            (incr_risky_count_and_update_iso_status_maybe_case
                                               pf_iso hyp f ) _
                            | right f => exist _
                                           (build_single_u_data_healthy_case pf_iso hyp
                                            _ ) _
                            end
                        end

  end eq_refl
    ).

  -
    unfold incr_risky_count_and_update_iso_status_bad_case.
    repeat split. 
    -- destruct lt_dec; right; trivial.
    --
      intros.
      simpl. right.
      destruct lt_dec; exact hyp.
    -- intros. destruct lt_dec; trivial.
    -- destruct lt_dec; trivial.
    -- intro. rewrite pf_iso in H; inversion H.
    -- intro. trivial.
    -- simpl. intros. destruct lt_dec; inversion H0.
    -- simpl. intros. destruct lt_dec; inversion H0.
    -- simpl. intros. destruct lt_dec.
       ---
         simpl in *.
         unfold hw_stat in hyp.
         rewrite hyp in H2.
         inversion H2.
      ---
         simpl in *.
         unfold hw_stat in hyp.
         rewrite hyp in H2.
         inversion H2.
    -- simpl. intros.
       destruct lt_dec;  inversion H0. 
    -- simpl. intros.
       destruct lt_dec;  inversion H0. 
    -- simpl. intros.
       destruct lt_dec.
       ---
         simpl in *.
         unfold hw_stat in hyp.
         rewrite hyp in H2.
         inversion H2.
       ---
         simpl in *.
         unfold hw_stat in hyp.
         rewrite hyp in H2.
         inversion H2.
    
  -
    unfold incr_risky_count_and_update_iso_status_miscomp_case.
    simpl.
    repeat split.
    -- destruct lt_dec; right; trivial.
    -- intro. left. destruct lt_dec; discriminate.
    -- intro. destruct lt_dec; trivial.
    -- destruct lt_dec; trivial.
    -- intro. rewrite pf_iso in H; inversion H.
    -- intros. trivial.
    -- intros. destruct lt_dec; trivial.
    -- simpl. intros. trivial.
    -- simpl. intros. 
       destruct lt_dec; trivial. 
    -- simpl. intros.
       destruct lt_dec; inversion H0.
    -- simpl. intros.
       destruct lt_dec; inversion H0.
    -- simpl. intros.
       destruct lt_dec.
        ---
         simpl in *.
         contradiction.
        ---
          simpl in *.
          contradiction.        
  -
    unfold incr_risky_count_and_update_iso_status_maybe_case.
    repeat split.
    -- destruct lt_dec; right; trivial.
    -- intro. left. destruct lt_dec; discriminate.
    -- intro. destruct lt_dec; trivial.
    -- destruct lt_dec; trivial.
    -- intro. rewrite pf_iso in H; inversion H.
    -- intros. trivial.
    -- intros. destruct lt_dec; inversion H0.
    -- intros. destruct lt_dec; inversion H0.
    -- intros. destruct lt_dec; contradiction.
    -- intros. destruct lt_dec; trivial.
    -- intros. destruct lt_dec; trivial.
    -- intros. destruct lt_dec; trivial. 
       
  -
    unfold build_single_u_data_healthy_case.
    repeat split.
    -- left; trivial.
    -- intro. simpl in *. inversion H0.
    -- simpl. intro.
       inversion H0. contradiction. unfold hw_stat in hyp.
       rewrite H1 in hyp. inversion hyp.
    -- intro. rewrite pf_iso in H; inversion H.
    -- intros. trivial.
    -- intros. inversion H0.
    -- intros. inversion H0.
    -- intros. simpl in *. contradiction.
    -- intros. inversion H0.
    -- intros. simpl in *. inversion H.
       inversion H0.
    -- intros. simpl in *. contradiction.
       Unshelve. 
       exact dev_lst.
       exact maybe_lst.
       split; trivial.
Defined.


    
Definition update_u_data_frm_comb_elmnt
  ( dev_lst : list unit_id )
  ( maybe_lst : list unit_id )
  ( x: unit_output * unit_data )
  : { sd : unit_data | build_single_u_data_prop x sd dev_lst maybe_lst }.
  refine (

  let stat := (iso_status (u_status (snd x)) ) in

  match stat as ISO return
        stat = ISO -> { sd : unit_data | build_single_u_data_prop x sd dev_lst maybe_lst }  with
  | isolated     => fun hyp => exist _ (unit_data_build (fst x) (u_status (snd x)) _ ) _
  | not_isolated => fun hyp => let (uniso, pf_uniso) :=
                                 (update_u_data_frm_comb_elmnt_not_isoltd
                                    x
                                    dev_lst
                                    maybe_lst
                                    hyp ) in
                               exist _ uniso pf_uniso
  end eq_refl).
  Unshelve.
  2: {  
    pose proof (pf_risky_count (u_status (snd x) )).
    inversion H as [H1 [H2 H3]].
    pose proof (H3 hyp).
    repeat split.
    rewrite H0 in H4; inversion H4.
    rewrite H0 in H4; inversion H4. 
    rewrite H0 in H4; inversion H4.
    intro. inversion H4 as [Ha [Hb Hc]].
    unfold stat in hyp.
    rewrite hyp in Hb. inversion Hb.
  }
  - repeat split.
    -- simpl. unfold stat in hyp. rewrite H in hyp. inversion hyp.
    -- simpl. unfold stat in hyp. rewrite hyp in H. inversion H.
    -- unfold stat in hyp. rewrite hyp in H. inversion H.
    -- intro. trivial.
    -- intros. inversion H. trivial.
    -- intros. unfold stat in hyp. simpl in *. rewrite hyp in H. inversion H.
    -- intros. unfold stat in hyp. simpl in *. rewrite hyp in H. inversion H.
    -- intros. simpl in *. unfold stat in hyp. rewrite hyp in H. inversion H.
    -- intros. unfold stat in hyp. simpl in *. rewrite hyp in H. inversion H.
    -- intros. unfold stat in hyp. simpl in *. rewrite hyp in H. inversion H.
    -- intros. unfold stat in hyp. simpl in *. rewrite hyp in H. inversion H.
Defined.  

Definition update_u_data_frm_comb_elmnt_for_map
  ( dev_lst : list unit_id )
  ( maybe_lst : list unit_id )
  ( x: unit_output * unit_data )
  := proj1_sig (update_u_data_frm_comb_elmnt dev_lst maybe_lst x).






Definition dev_uid_lst
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )                   
  :=
  let dev_outs    := miscomparing_lst pf_uids pf_input pf_ud_lst in
   map (fun y => uid y ) (proj1_sig dev_outs).
  

Definition maybe_uid_lst
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  :=
  let maybe_lst   := maybe_miscomparing_lst pf_uids pf_input pf_ud_lst in
  map (fun y => uid y ) (proj1_sig maybe_lst).


Definition build_updated_u_data_lst {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  : list unit_data :=
      let temp        := combine_lists pf_uids pf_input pf_ud_lst  in 
      let dev_uids    := dev_uid_lst pf_uids pf_input pf_ud_lst in
      let maybe_uids  := maybe_uid_lst pf_uids pf_input pf_ud_lst in
      
      map (update_u_data_frm_comb_elmnt_for_map dev_uids maybe_uids) temp .













(************************************************************************
********************************** Proofs *******************************
*************************************************************************
************************************************************************)

Lemma dev_lst_and_mayb_lst_are_disjoint
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  :      
      let dev_uids    := dev_uid_lst pf_uids pf_input pf_ud_lst in
      let maybe_uids  := maybe_uid_lst pf_uids pf_input pf_ud_lst in
      forall x, ( In x dev_uids -> ~ In x maybe_uids)
                /\ ( In x maybe_uids -> ~ In x dev_uids ) .
  intros.
  split.
  - 
    unfold dev_uids, maybe_uids.
    unfold maybe_uid_lst, dev_uid_lst.
    intros.
    intro. 
    apply in_map_iff in H0.
    inversion H0 as [x0 [Huid Hin]]. 
    pose proof (proj2_sig (maybe_miscomparing_lst pf_uids pf_input pf_ud_lst)) as Mayb_prop.
    rewrite Forall_forall in Mayb_prop.
    pose proof (Mayb_prop x0 Hin).
    inversion H1 as [H2a [H2b H2c]].
    clear Mayb_prop H1 H2c.

    rewrite <- Huid in H.
    apply in_map_iff in H.
    inversion H as [x1 [Huidx1 Hinx1]].
    pose proof (proj2_sig (miscomparing_lst pf_uids pf_input pf_ud_lst)) as Mis_prop.
    pose proof (Mis_prop x1 Hinx1).
    inversion H1.
    clear Mis_prop H1 H3.
    assert ( x1 = x0 ). {
      pose proof (noDup_uids_of_non_iso_good_lst
                    pf_uids pf_input pf_ud_lst ).
      exact ( fun_out_same_means_same_element_of_lst x1 Huidx1 H2 H2b H1).
    }
    rewrite H1 in Hinx1.
    contradiction.
  -
    unfold dev_uids, maybe_uids.
    unfold maybe_uid_lst, dev_uid_lst.
    intros.
    remember (proj2_sig (maybe_miscomparing_lst pf_uids pf_input pf_ud_lst)).
    pose proof f.
    clear Heqf f.
    rewrite Forall_forall in H0.
    apply in_map_iff in H.
    inversion H as [x0 [Hx0uid Hx0in]]. 
    pose proof (H0 x0 Hx0in).
    inversion H1 as [Hneginx0 [Hinx0 Ht]].
    clear H0 H1 Ht.
    rewrite in_map_iff.
    intro.
    inversion H0 as [x1 [Hx1uid Hx1in]].
    remember (proj2_sig (miscomparing_lst pf_uids pf_input pf_ud_lst)).
    pose proof a as Mis_prop.
    clear Heqa a.
    simpl in Mis_prop.
    pose proof (Mis_prop x1 Hx1in).
    inversion H1. 
    clear Mis_prop H1 H3.
    assert ( x1 = x0 ). {
      rewrite <- Hx0uid in Hx1uid.
      pose proof (noDup_uids_of_non_iso_good_lst
                    pf_uids pf_input pf_ud_lst ).
      exact ( fun_out_same_means_same_element_of_lst x1 Hx1uid H2 Hinx0 H1).
    }
    rewrite H1 in Hx1in.
    contradiction.
Qed.
   
    

    






Lemma u_output_independent_of_dev_and_maybe_list_helper
  (l1 l2 l3 l4 : list unit_id)
  :
  forall y,
     u_output (update_u_data_frm_comb_elmnt_for_map l1 l2 y)
       = u_output (update_u_data_frm_comb_elmnt_for_map l3 l4 y).
Proof.
  unfold update_u_data_frm_comb_elmnt_for_map.
  intro.
  remember (proj2_sig (update_u_data_frm_comb_elmnt l1 l2 y)).   
  remember (proj2_sig (update_u_data_frm_comb_elmnt l3 l4 y)).
  inversion b as [Hb1 [Hb2 Hb3]].
  inversion b0 as [Ha1 [Ha2 Ha3]].
  rewrite Ha2.
  rewrite Hb2.
  trivial.
Qed.


Lemma u_output_independent_of_dev_and_maybe_list_helper_fun
  (l1 l2 l3 l4 : list unit_id)
  :
  (fun y: unit_output*unit_data
   => u_output (update_u_data_frm_comb_elmnt_for_map l1 l2 y)) =
     ( fun y:unit_output*unit_data
       => u_output (update_u_data_frm_comb_elmnt_for_map l3 l4 y)).

  apply functional_extensionality.
  exact (u_output_independent_of_dev_and_maybe_list_helper l1 l2 l3 l4).
Qed.


Lemma u_output_independent_of_dev_and_maybe_list
  (l1 l2 l3 l4 : list unit_id): 
  forall y, map (fun x0 : unit_data => u_output x0)
              (map (update_u_data_frm_comb_elmnt_for_map l1 l2) y) = 
              map (fun x0 : unit_data => u_output x0)
                (map
                   (update_u_data_frm_comb_elmnt_for_map l3 l4) y).
Proof.
  intro.
  rewrite map_map.
  rewrite map_map.
  rewrite ( u_output_independent_of_dev_and_maybe_list_helper_fun l1 l2 l3 l4).
  trivial.
Qed.


Lemma build_updated_u_data_lst_preserves_input_data
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  ) :

  let new := build_updated_u_data_lst pf_uids  pf_input  pf_ud_lst in
  get_u_outputs_of_data new = input.
Proof.  
  intro. unfold new. 
  unfold build_updated_u_data_lst. 
  unfold combine_lists.
  generalize dependent u_ids.
  generalize dependent input. 
  induction ud_lst; intros. 
    
  - simpl in *.
    inversion pf_input.
    rewrite <- pf_ud_lst in H.
    unfold get_u_ids_of_unit_output in *.
    unfold combine_lists.
    apply map_eq_nil in H. 
    rewrite H.
    assert (@combine unit_output unit_data  input [] = [] ).
    rewrite H. trivial.
    rewrite H0.
    simpl.
    trivial.
  -     
   destruct u_ids, input.
    -- simpl in *. trivial.
    -- simpl in *.  inversion pf_input.
    -- simpl in *. trivial.
    --  
      inversion pf_ud_lst.
      inversion pf_input.
      inversion pf_uids.
      unfold get_u_outputs_of_data. 
      simpl.
      f_equal.
      ---
        unfold update_u_data_frm_comb_elmnt_for_map.
        pose proof  (proj2_sig  (update_u_data_frm_comb_elmnt (dev_uid_lst pf_uids pf_input pf_ud_lst)
                                   (maybe_uid_lst pf_uids pf_input pf_ud_lst) (u0, a))).
        inversion H7 as [Ha [Hb Hd]]. exact Hb.
      ---
        rewrite ( u_output_independent_of_dev_and_maybe_list
                   (dev_uid_lst pf_uids pf_input pf_ud_lst)
                     (maybe_uid_lst pf_uids pf_input pf_ud_lst)
                     (dev_uid_lst H6 H3 H1)
                     (maybe_uid_lst H6 H3 H1) ).
        exact (IHud_lst input u_ids H6 H3 H1).
Qed.



Lemma u_id_independent_of_dev_and_maybe_list_helper (l1 l2 l3 l4 : list unit_id) :
  forall y, uid (u_output (update_u_data_frm_comb_elmnt_for_map l1 l2 y))
       = uid (u_output (update_u_data_frm_comb_elmnt_for_map l3 l4 y)).
  unfold update_u_data_frm_comb_elmnt_for_map.
  intro.
  remember (proj2_sig (update_u_data_frm_comb_elmnt l1 l2 y)).   
  remember (proj2_sig (update_u_data_frm_comb_elmnt l3 l4 y)).
  inversion b as [Hb1 [Hb2 Hb3]].
  inversion b0 as [Ha1 [Ha2 Ha3]].
  rewrite Ha2.
  rewrite Hb2.
  trivial.
Qed.


Lemma u_id_independent_of_dev_and_maybe_list_helper_fun (l1 l2 l3 l4 : list unit_id) :
  (fun y: unit_output*unit_data => uid (u_output (update_u_data_frm_comb_elmnt_for_map l1 l2 y)))
  = ( fun y: unit_output*unit_data => uid (u_output (update_u_data_frm_comb_elmnt_for_map l3 l4 y))).


  apply functional_extensionality.
  exact (u_id_independent_of_dev_and_maybe_list_helper l1 l2 l3 l4).
Qed.





Lemma u_id_independent_of_dev_and_maybe_list
  (l1 l2 l3 l4 : list unit_id)  :
  forall y,  map (fun x0 : unit_data => uid (u_output x0)) (map
       (update_u_data_frm_comb_elmnt_for_map l1 l2) y) = 
          map (fun x0 : unit_data => uid (u_output x0)) (map
       (update_u_data_frm_comb_elmnt_for_map l3 l4) y).
Proof. 
    intro.
    rewrite map_map.
    rewrite map_map.
    rewrite ( u_id_independent_of_dev_and_maybe_list_helper_fun l1 l2 l3 l4).
    trivial.
Qed.





Lemma build_updated_u_data_lst_preserves_uids
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  ) :

  let new := build_updated_u_data_lst  pf_uids  pf_input pf_ud_lst in
  get_u_ids_of_unit_data new = u_ids.
Proof.  
  intro. unfold new.
  unfold build_updated_u_data_lst.
  unfold combine_lists.
  generalize dependent u_ids.
  generalize dependent input. 
  induction ud_lst; intros. 
   
  - simpl in *.  
    inversion pf_input. 
    rewrite <- pf_ud_lst in *.
    unfold get_u_ids_of_unit_output in *.
    apply map_eq_nil in H.
     assert (@combine unit_output unit_data  input [] = [] ).
    rewrite H. trivial.
    rewrite H0.
    simpl.
    trivial.
  -      
   destruct u_ids, input.
    -- simpl in *. trivial.
    -- simpl in *.  inversion pf_input.
    -- simpl in *. trivial.
    --  
      inversion pf_ud_lst.
      inversion pf_input.
      inversion pf_uids.
      simpl.
      f_equal.
      ---
        unfold update_u_data_frm_comb_elmnt_for_map.
        pose proof (proj2_sig  (update_u_data_frm_comb_elmnt (dev_uid_lst pf_uids pf_input pf_ud_lst)
             (maybe_uid_lst pf_uids pf_input pf_ud_lst) (u0, a)) ).
        inversion H7 as [Ha [Hb Hd]]. 
        assert (uid    (u_output
       (proj1_sig
          (update_u_data_frm_comb_elmnt (dev_uid_lst pf_uids pf_input pf_ud_lst)
             (maybe_uid_lst pf_uids pf_input pf_ud_lst) (u0, a))))
                = uid (fst (u0, a))). rewrite <- Hb. trivial.
        rewrite H8. trivial.
      ---
        rewrite ( u_id_independent_of_dev_and_maybe_list
                    (dev_uid_lst  pf_uids pf_input pf_ud_lst)
                    (maybe_uid_lst  pf_uids pf_input pf_ud_lst)
                    (dev_uid_lst H6 H3 H1)
                    (maybe_uid_lst H6 H3 H1) ).
        exact (IHud_lst input u_ids H6 H3 H1).
Qed.

Lemma once_isolated_remain_isolated_after_build_updated_u_data_lst_helper
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  ) :

  let new := build_updated_u_data_lst  pf_uids  pf_input pf_ud_lst in
  forall x,
    In x (isolated_list ud_lst)
    -> forall z,
      In z input /\ (uid z = uid (u_output x))
      -> forall y,
        In y new /\ (uid (u_output y)) = (uid (u_output x))
        -> In y (isolated_list new).

  intros.
  unfold new.
  unfold isolated_list. 
  apply filter_In.
  unfold build_updated_u_data_lst.
  unfold combine_lists. split.
  -  apply in_map_iff.
     exists (z,x). split.
     --
       unfold update_u_data_frm_comb_elmnt_for_map.
       remember (update_u_data_frm_comb_elmnt (dev_uid_lst pf_uids pf_input pf_ud_lst)
                     (maybe_uid_lst pf_uids pf_input pf_ud_lst) (z, x)).
       pose proof ( proj2_sig s ) as  [B1 [B2 B3]].
       assert ( In (proj1_sig s) new ). {
         unfold new. unfold build_updated_u_data_lst.
         unfold combine_lists.
         unfold update_u_data_frm_comb_elmnt_for_map.
         apply in_map_iff.
         exists (z,x). split. rewrite Heqs. trivial. 
         pose proof (combine_lists_gen_props pf_uids pf_input pf_ud_lst (z,x)) as [Hc1 Hc2].
         simpl in *.
         assert (uid z = uid (u_output x) /\ In z input /\ In x ud_lst). {
           inversion H0. repeat split; trivial.  unfold isolated_list in H.
           apply filter_In in H.
           inversion H; trivial.
         }
         exact (Hc2  H2).
       }
       inversion H0.
       inversion H1.
       simpl in *.
       rewrite <- B2 in H4.
       rewrite <- H6 in H4.
       
       pose proof (build_updated_u_data_lst_preserves_uids pf_uids pf_input pf_ud_lst)
         as Huid.
         
       exact (fun_out_same_means_same_element_of_lst (proj1_sig s) H4 H2 H5
             (mapped_list_nodup Huid pf_uids)).
     -- 
       pose proof (combine_lists_gen_props pf_uids pf_input pf_ud_lst (z,x))
       as [Hc1 Hc2].
       simpl in *.
       assert (uid z = uid (u_output x) /\ In z input /\ In x ud_lst). {
         inversion H0. repeat split; trivial.  unfold isolated_list in H.
         apply filter_In in H.
         inversion H; trivial.
       }
       exact (Hc2 H2).

  -  simpl in *.
     assert (iso_status (u_status x) = isolated). {
       unfold isolated_list in H.
       apply filter_In in H.
       inversion H as [Hx1 Hx2].
       unfold not_iso_check in Hx2.
       unfold negb in Hx2.
       destruct (iso_status (u_status x)).
       trivial.
       inversion Hx2.
     }
     inversion H1. unfold new in H3.
     unfold build_updated_u_data_lst in H3.
     unfold combine_lists in H3.
     apply in_map_iff in H3.
     inversion H3.
     inversion H5.
     unfold update_u_data_frm_comb_elmnt_for_map in H6.
     pose proof (proj2_sig
         (update_u_data_frm_comb_elmnt (dev_uid_lst pf_uids pf_input pf_ud_lst)
            (maybe_uid_lst pf_uids pf_input pf_ud_lst) x0) ) as [B1 [B2 [B3a B3b]]]. 
     clear B1 B3b.     
     pose proof (combine_lists_gen_props pf_uids pf_input pf_ud_lst x0) as [[Hx0uid [Hx0input Hx0ud_lst]] T].
     exact H7.
     clear T.
     rewrite H6 in B2.
     rewrite B2 in H4.
     assert ( In x ud_lst ). { unfold isolated_list in H.
                            apply filter_In in H.
                            inversion H; trivial.
     }
     rewrite Hx0uid in H4.       
     pose proof (fun_out_same_means_same_element_of_lst (snd x0) H4 Hx0ud_lst H8
                   (mapped_list_nodup pf_ud_lst pf_uids)).
     rewrite H9 in B3a.
     unfold not_iso_check; unfold negb.
     pose proof (B3a H2).
     rewrite H6 in H10.
     rewrite H10. trivial.
Qed.     

Lemma once_isolated_remain_isolated_after_build_updated_u_data_lst {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  ) :

  let new := build_updated_u_data_lst  pf_uids  pf_input pf_ud_lst in
  forall x, In x (get_u_ids_of_unit_data   (isolated_list ud_lst)) -> 
       In x (get_u_ids_of_unit_data   (isolated_list new)).

  unfold get_u_ids_of_unit_data. intros.
  apply in_map_iff.
  apply in_map_iff in H.
  inversion H as [Ha [Hb Hc]].
  remember (build_updated_u_data_lst pf_uids pf_input pf_ud_lst).
  remember (build_updated_u_data_lst_preserves_uids pf_uids pf_input pf_ud_lst).

  assert ( In x (get_u_ids_of_unit_data ud_lst) ). {
    unfold get_u_ids_of_unit_data.
    unfold isolated_list in Hc.
    apply filter_In in Hc.
    inversion Hc.
    apply in_map_iff. exists Ha. split; trivial.
  }
  assert ( In x (get_u_ids_of_unit_data (build_updated_u_data_lst pf_uids pf_input pf_ud_lst) )).
  {
    rewrite e.
    rewrite <- pf_ud_lst. trivial.
  }    
  remember ( find_data_of_a_given_unit_id  e H1 ).
  inversion s as [y [Hy1 Hy2]].
  exists y.
  unfold build_updated_u_data_lst in Hy2.
  unfold combine_lists in Hy2.
  apply in_map_iff in Hy2.
  inversion Hy2 as [zy [Hzy1 Hzy2]].  
  
  pose proof (once_isolated_remain_isolated_after_build_updated_u_data_lst_helper
                pf_uids pf_input pf_ud_lst Ha Hc (fst zy) ).
  assert (get_u_ids_of_unit_output input = get_u_ids_of_unit_data ud_lst ).
  rewrite pf_ud_lst; trivial.
  assert (length input = length ud_lst ). {
    assert (length (get_u_ids_of_unit_output input) =
              length (get_u_ids_of_unit_data ud_lst) ).
    rewrite H3. trivial.
    unfold get_u_ids_of_unit_output in H4.
    unfold get_u_ids_of_unit_data in H4.
    rewrite length_map in H4.
    rewrite length_map in H4.
    trivial.
  }
  
  pose proof (mapped_list_nodup pf_input pf_uids).
  pose proof (combine_lists_gen_props pf_uids pf_input pf_ud_lst zy).
  unfold combine_lists in H6.
  inversion H6.
  pose proof (H7 Hzy2).
  inversion H9 as [H9a [H9b H9c]].
  assert (In (fst zy) input /\ uid (fst zy) = uid (u_output Ha) ).
  split; trivial.
  unfold update_u_data_frm_comb_elmnt_for_map in Hzy1.
  remember (proj2_sig
           (update_u_data_frm_comb_elmnt (dev_uid_lst pf_uids pf_input pf_ud_lst)
              (maybe_uid_lst pf_uids pf_input pf_ud_lst) zy) ).
  inversion b as [Hb1 [Hb2 Hb3]].
  rewrite Hzy1 in Hb2.
  rewrite <- Hb2.
  rewrite Hb. rewrite Hy1.
  trivial.
  assert ( In y (build_updated_u_data_lst pf_uids pf_input pf_ud_lst) /\
             uid (u_output y) = uid (u_output Ha) ). {
    split.
    unfold build_updated_u_data_lst.
    unfold combine_lists.
    apply in_map_iff.
    exists zy. split; trivial.
    rewrite Hb.
    rewrite Hy1. trivial.
  }  
  pose proof (H2 H10 y H11).
  split.
  rewrite Hy1. trivial.
  rewrite Heql. trivial.

Qed.
  
Lemma not_isolated_after_update_implies_not_isolated_before
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  ) :

  let new := build_updated_u_data_lst  pf_uids  pf_input pf_ud_lst in
  forall x, In x (get_u_ids_of_unit_data   (non_isolated_list new)) -> 
       In x (get_u_ids_of_unit_data   (non_isolated_list ud_lst)).
  intros.
  unfold non_isolated_list in *.
  
  unfold get_u_ids_of_unit_data in *.
  apply in_map_iff in H.
  inversion H as [xd [Hxdeqx Hxdin]].
  pose proof (once_isolated_remain_isolated_after_build_updated_u_data_lst
                pf_uids pf_input pf_ud_lst ).
  assert ( ~ In xd (isolated_list new)).
  { unfold isolated_list.
    intro.
    apply filter_In in Hxdin, H1.
    inversion Hxdin.
    inversion H1.
    rewrite H3 in H5.
    inversion H5.
  }
  assert (get_u_ids_of_unit_data new = u_ids)  as pf_new_uids
    by exact (build_updated_u_data_lst_preserves_uids pf_uids pf_input pf_ud_lst)
     .
                                                   
  assert ( ~ In x (get_u_ids_of_unit_data (isolated_list new)) ). {
    unfold get_u_ids_of_unit_data.
    intro.
    apply in_map_iff in H2.
    inversion H2 as [x0 [Hx0uid Hx0in]].
    assert (x0 = xd). {
      unfold isolated_list in Hx0in.
      apply filter_In in Hxdin, Hx0in.
      inversion Hxdin.
      inversion Hx0in.
      rewrite <- Hx0uid in Hxdeqx.
      pose proof  (fun_out_same_means_same_element_of_lst xd
                     Hxdeqx H3 H5  (mapped_list_nodup pf_new_uids pf_uids)).
      symmetry.
      trivial.
    }
    rewrite H3 in Hx0in.
    contradiction.
  }

  assert (~ In x (get_u_ids_of_unit_data (isolated_list ud_lst)) ). {
    intro.
    pose proof (H0 x H3).
    unfold new in H2.
    contradiction.
  }
  
  unfold get_u_ids_of_unit_data in H3.
     unfold isolated_list in H3.
     assert ( In x (get_u_ids_of_unit_data ud_lst) ).
     { 
       unfold get_u_ids_of_unit_data in *.
       rewrite pf_ud_lst.
       rewrite <- pf_new_uids. 
       apply in_map_iff. 
       exists xd. 
       split; trivial.
       apply filter_In in Hxdin.
       inversion Hxdin. 
       trivial.
     }
     apply  in_map_iff in H4.
     inversion H4 as [yd [Hydeqx Hydin]].
     apply in_map_iff.
     exists yd.
     split; trivial.

     rewrite (in_map_iff) in H3.
     assert (~ In yd (filter (fun y : unit_data => negb (not_iso_check y)) ud_lst)).
     {
       intro.
       assert (exists x0 : unit_data,
          uid (u_output x0) = x /\
            In x0 (filter (fun y : unit_data => negb (not_iso_check y)) ud_lst)). {
         exists yd.
         split; trivial. }

       
       exact (H3 H6).
     }

     rewrite filter_In in H5.
     assert ( negb (not_iso_check yd) <> true ). {
       intro.
       assert (In yd ud_lst /\ negb (not_iso_check yd) = true).
       split; trivial.
       exact (H5 H7).
     }
     apply filter_In.
     split; trivial.
     apply eq_true_negb_classical in H6.
     trivial.
Qed.

Lemma build_updated_u_data_lst_do_not_decrease_isolated_units
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  :
  let new := build_updated_u_data_lst  pf_uids  pf_input pf_ud_lst in
    
  (length  (get_u_ids_of_unit_data   (isolated_list ud_lst)))
  <= length   (get_u_ids_of_unit_data   (isolated_list new)).

Proof.
  intro. 

  assert (get_u_ids_of_unit_data new = u_ids)
    by exact (build_updated_u_data_lst_preserves_uids
                pf_uids pf_input pf_ud_lst).
  assert (forall x : unit_id,
             In x (get_u_ids_of_unit_data (isolated_list (ud_lst))) ->
             In x (get_u_ids_of_unit_data (isolated_list new)) )
    by exact (once_isolated_remain_isolated_after_build_updated_u_data_lst
                pf_uids pf_input pf_ud_lst).

   assert ( NoDup (get_u_ids_of_unit_data   (isolated_list ud_lst)) ).
   {
     pose proof pf_uids.
     rewrite <- pf_ud_lst in H1.
     unfold get_u_ids_of_unit_data in *.
     unfold isolated_list.
     exact (nodup_map_filter
              H1 ).
   }
   
 
   exact ( sub_list_length_le_list_length
             H1 H0 ).
Qed.        




Lemma build_updated_u_data_lst_do_not_increase_non_isolated_units
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  : 
  let new := build_updated_u_data_lst  pf_uids  pf_input pf_ud_lst in
  count_of_non_isolated_units new <= count_of_non_isolated_units ud_lst.

  intros.
  assert (get_u_ids_of_unit_data new = u_ids)
    by exact (build_updated_u_data_lst_preserves_uids
                pf_uids pf_input pf_ud_lst).
  unfold count_of_non_isolated_units.
  unfold non_isolated_list. 

  assert ( (length  (get_u_ids_of_unit_data   (isolated_list ud_lst)))
           <= length   (get_u_ids_of_unit_data   (isolated_list new)) )
    by exact (build_updated_u_data_lst_do_not_decrease_isolated_units
                pf_uids pf_input pf_ud_lst).
  
  assert (length (isolated_list ud_lst) <= length (isolated_list new) ).
  { unfold get_u_ids_of_unit_data in H0. rewrite length_map in H0.
    rewrite length_map in H0. trivial.
  }
  unfold isolated_list in H1.
  rewrite (filter_length_is_length_minus_remaining ud_lst not_iso_check ).  
  rewrite (filter_length_is_length_minus_remaining new not_iso_check ).
  assert (length new = length ud_lst ). {
    assert (length (get_u_ids_of_unit_data new)
            = length ( get_u_ids_of_unit_data ud_lst ) ).
    rewrite pf_ud_lst. rewrite H. trivial. 
    unfold get_u_ids_of_unit_data in *.
    repeat rewrite length_map in H2. trivial.
  } lia.
Qed.



Lemma build_updated_u_data_lst_holds_risky_cnt_prop
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  ) :

  let new := build_updated_u_data_lst  pf_uids  pf_input pf_ud_lst in
  
  forall x, In x ud_lst -> forall y, In y new -> (uid (u_output x) = uid (u_output y))
              -> risky_cnt_prop x y.
  intros.

  unfold new in H0.
  unfold build_updated_u_data_lst in *.
  unfold combine_lists in *.
  apply in_map_iff in H0.
  inversion H0.
  unfold update_u_data_frm_comb_elmnt_for_map in H2. 
  pose proof (proj2_sig
         (update_u_data_frm_comb_elmnt (dev_uid_lst pf_uids pf_input pf_ud_lst)  
            (maybe_uid_lst pf_uids pf_input pf_ud_lst) x0))
    as [H3 [H4 H4b]].
  inversion H2.
  pose proof (combine_lists_gen_props  pf_uids pf_input pf_ud_lst x0)
    as [[Hx0uid [Hx0input Hx0ud_lst]] T].
  exact H6.
  rewrite H5 in H4.
  rewrite <- H4 in Hx0uid.
  rewrite <- H1 in Hx0uid.
  pose proof (fun_out_same_means_same_element_of_lst x Hx0uid H Hx0ud_lst 
                (mapped_list_nodup pf_ud_lst pf_uids) ).
  rewrite <- H5.
  rewrite H7.
  trivial.
Qed.



Lemma build_updated_u_data_lst_holds_soundness_a_prop_of_miscomp_check
        (*miscomparing_lst_deviates_more_than_delta_frm_grnd_truth *)
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )

  :
 
  let  l := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
  let mis_flt_lmt := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
  length (dlta_dev_lst_grnd_truth l ) <= mis_flt_lmt
  -> let new := build_updated_u_data_lst  pf_uids  pf_input pf_ud_lst in
     forall x, In x ud_lst
               -> forall y, In y  new
                               ->  forall z, In z input                                                  
                                             -> (uid (u_output x) = uid (u_output y))
                                             -> (uid (u_output x) = uid z)                                     
                                             -> iso_status (u_status x) = not_isolated
                                             -> y.(u_status).(miscomp_status) = miscomparing
                                             -> adiff ground_truth z.(reading).(val)    > delta.
Proof.
  unfold build_updated_u_data_lst.
  intros Hl x Hxin y Hyin z Hzin Huidxy Huidxz Hiso Hmis.  
  unfold update_u_data_frm_comb_elmnt_for_map in Hyin.
  unfold combine_lists in Hyin. 
  apply in_map_iff in Hyin.
  inversion Hyin as [zx [Ha Hb]].
  pose proof ( proj2_sig
              (update_u_data_frm_comb_elmnt (dev_uid_lst pf_uids pf_input pf_ud_lst)
                 (maybe_uid_lst pf_uids pf_input pf_ud_lst) zx))
    as [Hb1 [Hb2 [Hb3 [Hb4 Hb5]]]]. 
  rewrite Ha in Hb5.
  pose proof (combine_lists_gen_props pf_uids pf_input pf_ud_lst zx).
  inversion H.
  pose proof (H0 Hb).
  inversion H2 as [H2uid [H2input H2ud_lst]].
  clear H H0 H1 H2.
  rewrite Ha in Hb2.
  rewrite Hb2 in Huidxy.
  assert ( fst zx = z ). {
    rewrite Huidxy in Huidxz.
    exact (fun_out_same_means_same_element_of_lst (fst zx) Huidxz H2input Hzin
             (mapped_list_nodup pf_input pf_uids) ).
  }
  assert ( x = snd zx ). {
    rewrite H2uid in Huidxy.
    exact (fun_out_same_means_same_element_of_lst x Huidxy Hxin H2ud_lst
             (mapped_list_nodup pf_ud_lst pf_uids) ).
  }
  rewrite <- H0 in *.
  rewrite H in *.
  clear H2uid H2input H2ud_lst H H0.
  pose proof (Hb5 Hiso).
  inversion H as [Hb6 [Hb7 [ Hb8 Hb9]]].
  pose proof  (Hb6 Hmis) as [Hgd Hindev]. 

  unfold dev_uid_lst in Hindev.
  apply in_map_iff in Hindev.
  inversion Hindev as [d [Hduid Hdin]].

  pose proof ( miscomparing_lst_deviates_frm_grnd_truth pf_uids pf_input pf_ud_lst
                 Hl d Hdin).
  assert ( d = z). {
    unfold miscomparing_lst in Hdin.
    simpl in Hdin.
    apply filter_In in Hdin.
    inversion Hdin as [Hdinl temp].  
    unfold combine_lists in *.
    apply filter_In in Hdinl.
    inversion Hdinl as [Hdmapcomp temp2].
    apply in_map_iff in Hdmapcomp.
    clear Hdin H0 Hdinl temp temp2.
    inversion Hdmapcomp as [ab [Habuid Habin]].
    unfold non_isltd_comb_lst in Habin.
    apply filter_In in Habin.
    inversion Habin as [Habincomp temp].
    pose proof ( combine_lists_gen_props pf_uids pf_input pf_ud_lst ab) as [Habprop].
    pose proof (Habprop Habincomp) as [Hauidb [Hainput Hbud_lst]].
    clear Habin Habincomp temp Habprop H0.
    rewrite <- Habuid in *.
    exact ( fun_out_same_means_same_element_of_lst (fst ab) Hduid  Hainput Hzin
              (mapped_list_nodup pf_input pf_uids)).
  }
  rewrite H1 in H0.
  trivial.
Qed.



Lemma build_updated_u_data_lst_holds_cmpltnss_a_prop_of_miscomp_check
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  :
  let  l := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
  let mis_flt_lmt := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
  length (dlta_dev_lst_grnd_truth l ) <= mis_flt_lmt ->
  length l > 2 * mis_flt_lmt ->

  let new := build_updated_u_data_lst  pf_uids  pf_input pf_ud_lst in
  forall x,
    In x ud_lst
    -> forall y,
      In y new
      ->  forall z,
        In z input                                                  
        -> (uid (u_output x) = uid (u_output y))
        -> (uid (u_output x) = uid z)                                     
        -> iso_status (u_status x) = not_isolated
        -> z.(reading).(hw_hlth) = good 
        -> adiff ground_truth z.(reading).(val)    > 3*delta
        -> y.(u_status).(miscomp_status) = miscomparing .
 
  unfold build_updated_u_data_lst. 
  intros Hypo Hl x Hinx y Hiny z Hinz Huidxy Huidxz Hiso Hgd H3d. 
  unfold update_u_data_frm_comb_elmnt_for_map in Hiny.
  unfold combine_lists in Hiny.
  apply in_map_iff in Hiny.
  inversion Hiny as [zx [Hzx Hzxin]].
  remember ( proj2_sig
              (update_u_data_frm_comb_elmnt (dev_uid_lst pf_uids pf_input pf_ud_lst)
                 (maybe_uid_lst pf_uids pf_input pf_ud_lst) zx)).
  inversion b as [Hb1 [Hb2 [Hb3 [Hb4 Hb5]]]].
   
  rewrite Hzx in Hb5.
  pose proof (combine_lists_gen_props pf_uids pf_input pf_ud_lst zx) as [Hzxprop].
  pose proof (Hzxprop Hzxin) as [Hzuidx [Hinput Hud_lst]].
  rewrite Hzx in *.
  rewrite Hb2 in Huidxy.
  assert ( fst zx = z ). {
    rewrite Huidxy in Huidxz.
    exact (fun_out_same_means_same_element_of_lst (fst zx) Huidxz  Hinput Hinz
             (mapped_list_nodup pf_input pf_uids)).
  }
  assert ( x = snd zx ). {
    rewrite Hzuidx in Huidxy.
    exact (fun_out_same_means_same_element_of_lst x Huidxy Hinx Hud_lst
              (mapped_list_nodup pf_ud_lst pf_uids) ).
  }
  rewrite <- H1 in *.
  rewrite H0 in *.
  assert ( In (u_output y) (proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst)) ).
  { unfold all_good_non_iso_lst.
    simpl.
    unfold combine_lists.
    apply filter_In.
    split.
    - apply in_map_iff.
      exists zx.
      split.
      -- rewrite Hb2, H0. trivial.
      -- unfold non_isltd_comb_lst.
         apply filter_In.
         split; trivial.
         unfold not_iso_check.
         rewrite <- H1.
         rewrite Hiso. trivial.
    - unfold hw_good_unit_check.
      rewrite Hb2.
      rewrite Hgd; trivial.
  }
  rewrite <- Hb2 in *.
  pose proof (deviation_3delta_frm_grnd_truth_is_in_mis_list pf_uids pf_input pf_ud_lst
                Hypo Hl (u_output y) H2 H3d).
  assert (In (uid (u_output y)) (dev_uid_lst pf_uids pf_input pf_ud_lst) ).
  {
    unfold dev_uid_lst.
    apply in_map_iff.
    exists (u_output y).
    split; trivial.
  }
  pose proof (dev_lst_and_mayb_lst_are_disjoint pf_uids pf_input pf_ud_lst (uid (u_output y))) as [Hnin Hin].
  pose proof (Hb5 Hiso).
  inversion H5 as [T [Req T2]].
  exact (Req H4 (Hnin H4) Hgd).
Qed. 



Lemma build_updated_u_data_lst_holds_soundness_b_prop_of_miscomp_check
        (* not_miscomparing _means at_most_3delta_deviation *)
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )

  :
 
  let  (l, pf_l) := all_good_non_iso_lst pf_uids pf_input pf_ud_lst in
  let mis_flt_lmt := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
  length (dlta_dev_lst_grnd_truth l ) <= mis_flt_lmt
  -> let new := build_updated_u_data_lst  pf_uids  pf_input pf_ud_lst in
     forall x,
       In x ud_lst
       -> forall y,
         In y  new
         ->  forall z, In z l                                                  
                       -> (uid (u_output x) = uid (u_output y))
                       -> (uid (u_output x) = uid z)                                     
                       -> iso_status (u_status x) = not_isolated
                       -> y.(u_status).(miscomp_status) = not_miscomparing
                       -> adiff ground_truth z.(reading).(val) <= 3*delta.
Proof. 
  unfold build_updated_u_data_lst.  
  intros Hypo x Hxin y Hyin z Hzinl Huidxy Huidxz Hiso Hmis.  
  unfold update_u_data_frm_comb_elmnt_for_map in Hyin.
  unfold combine_lists in Hyin. 
  apply in_map_iff in Hyin.
  inversion Hyin as [zx [Ha Hb]].
  pose proof ( proj2_sig
              (update_u_data_frm_comb_elmnt (dev_uid_lst pf_uids pf_input pf_ud_lst)
                 (maybe_uid_lst pf_uids pf_input pf_ud_lst) zx))
    as [Hb1 [Hb2 [Hb3 [Hb4 Hb5]]]]. 
  rewrite Ha in Hb5. 
  pose proof (combine_lists_gen_props pf_uids pf_input pf_ud_lst zx).
  inversion H.
  pose proof (H0 Hb).
  inversion H2 as [H2uid [H2input H2ud_lst]].
  clear H H0 H1 H2.
  rewrite Ha in Hb2.
  rewrite Hb2 in Huidxy. 
  pose proof (proj2_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst)).
  rewrite Forall_forall in H.
  pose proof (H z Hzinl) as [Hzin[T Hzgd]].
  
  assert ( fst zx = z ). {
    rewrite Huidxy in Huidxz.
    exact (fun_out_same_means_same_element_of_lst (fst zx) Huidxz H2input Hzin
             (mapped_list_nodup pf_input pf_uids)).
  }
  assert ( x = snd zx ). {
    rewrite H2uid in Huidxy.
    exact (fun_out_same_means_same_element_of_lst x Huidxy Hxin H2ud_lst
             (mapped_list_nodup pf_ud_lst pf_uids)).
  } 
  rewrite H0 in *.
  rewrite <- H1 in *.
  clear H2uid H2input H2ud_lst H H0.
  pose proof (Hb5 Hiso) as [Hmis1 [Hmis2[Hmb1 Hmb2]]].
  pose proof ( in_not_mis_list_means_at_most_3delta_deviation
                 pf_uids pf_input pf_ud_lst Hypo).
  pose proof (dev_lst_and_mayb_lst_are_disjoint pf_uids pf_input pf_ud_lst (uid z)) as [Hnin Hin]. 
  assert (  ~ In (uid z) (dev_uid_lst pf_uids pf_input pf_ud_lst)  ). {
    intro.
    pose proof (Hmis2 H0 (Hnin H0) Hzgd).
    rewrite H2 in Hmis.
    inversion Hmis.
  }
  assert ( ~ In (uid z) (maybe_uid_lst pf_uids pf_input pf_ud_lst) ). {
    intro.
    pose proof (Hmb2 H2 H0 Hzgd).
    rewrite H3 in Hmis.
    inversion Hmis.
  }
  clear Hb5 Hmis1 Hmis2 Hmb1 Hmb2 Hb3 Hb4 Hb1 Hnin Hin. 

  pose proof (miscomparing_mayb_and_not_lists_are_disjoint
                pf_uids pf_input pf_ud_lst z Hzinl) as [[T1 T2][[T5 T6][T3 HinNt]]].
  clear T1 T2 T3 T5 T6.
  assert ( ~ In z (proj1_sig (maybe_miscomparing_lst pf_uids pf_input pf_ud_lst)) /\
             ~ In z (proj1_sig (miscomparing_lst pf_uids pf_input pf_ud_lst))).
  { split.
    intro.
    assert (In (uid z) (maybe_uid_lst pf_uids pf_input pf_ud_lst)). {
      unfold maybe_uid_lst.
      apply in_map_iff.
      exists z.
      split; trivial.
    }
    contradiction.
    intro.
    assert (In (uid z) (dev_uid_lst pf_uids pf_input pf_ud_lst)). {
      unfold dev_uid_lst.
      apply in_map_iff.
      exists z. 
      split; trivial.
    }
    contradiction.
  }
  exact (H z (HinNt H3)).
Qed.    
  





Lemma build_updated_u_data_lst_holds_cmpltnss_b_prop_of_miscomp_check
        (*atmost_delta_frm_grnd_truth_is_not_miscomparing*)
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  :
  let  l := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
  let mis_flt_lmt := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
  length (dlta_dev_lst_grnd_truth l ) <= mis_flt_lmt ->
  length l > 2 * mis_flt_lmt ->

  let new := build_updated_u_data_lst  pf_uids  pf_input pf_ud_lst in
  forall x,
    In x ud_lst
    -> forall y,
      In y new
      ->  forall z,
        In z l                                                  
        -> (uid (u_output x) = uid (u_output y))
        -> (uid (u_output x) = uid z)                                     
        -> iso_status (u_status x) = not_isolated
        -> adiff ground_truth z.(reading).(val)    <= delta
        -> y.(u_status).(miscomp_status) = not_miscomparing .

Proof.
  unfold build_updated_u_data_lst.  
  unfold update_u_data_frm_comb_elmnt_for_map.
  unfold combine_lists.
  intros Hypo Hl x Hxin y Hyin z Hzinl Huidxy Huidxz Hiso Hdlta.
    
  pose proof ( atmost_delta_frm_grnd_truth_is_not_miscomparing
                 pf_uids pf_input pf_ud_lst Hypo Hl z Hzinl Hdlta). 
  pose proof (miscomparing_mayb_and_not_lists_are_disjoint
                pf_uids pf_input pf_ud_lst z Hzinl) as [[T1 T2][[T5 T6][HinNt T3]]].
  pose proof (HinNt H) as [HzninMb HzinM].
  
  pose proof (noDup_uids_of_non_iso_good_lst
                pf_uids pf_input pf_ud_lst ) as NDuidl.
  assert (  ~ In (uid z) (dev_uid_lst pf_uids pf_input pf_ud_lst)  ) as HzninD. { 
    intro HzninD.
    unfold dev_uid_lst in HzninD.
    apply in_map_iff in HzninD.
    inversion HzninD as [t [Htuid Htin]].
    clear HzninD.
    assert (t = z). {
      apply filter_In in Htin.
      inversion Htin as [Htinl].
      exact (fun_out_same_means_same_element_of_lst
               t Htuid Htinl Hzinl NDuidl ).
    }
    rewrite H0 in Htin.
    contradiction.
  }

  assert ( ~ In (uid z) (maybe_uid_lst pf_uids pf_input pf_ud_lst) ) as HzninM. {
    intro HzninuidMb.
    unfold dev_uid_lst in HzninuidMb.
    apply in_map_iff in HzninuidMb.
    inversion HzninuidMb as [t [Htuid Htin]].
    clear HzninuidMb.
    assert (t = z). {
      apply filter_In in Htin. 
      inversion Htin as [HtinNm].
      apply filter_In in HtinNm. 
      inversion HtinNm as [Htinl].
      
      exact (fun_out_same_means_same_element_of_lst
               t Htuid Htinl Hzinl NDuidl ).
    }
    rewrite H0 in Htin.
    contradiction.
  }
  clear T1 T2 T3 T5 T6 HinNt HzninMb HzinM NDuidl.
  
  apply in_map_iff in Hyin.
  inversion Hyin as [zx [Ha Hb]].
  pose proof ( proj2_sig
              (update_u_data_frm_comb_elmnt (dev_uid_lst pf_uids pf_input pf_ud_lst)
                 (maybe_uid_lst pf_uids pf_input pf_ud_lst) zx))
    as [Hb1 [Hb2 [Hb3 [Hb4 Hb5]]]].
  pose proof (combine_lists_gen_props pf_uids pf_input pf_ud_lst zx)
    as [[Hzxuid [Hzxinput Hzxud_lst]] T].
  exact Hb.
  clear T.
  rewrite Ha in *.
  rewrite <- Hb2 in *.
  
  assert (x = snd zx ). {
    rewrite Hzxuid in Huidxy.
    exact (fun_out_same_means_same_element_of_lst
             x Huidxy Hxin Hzxud_lst (mapped_list_nodup pf_ud_lst pf_uids)).
  }
  rewrite <- H0 in Hb5.
  rewrite Huidxy in Huidxz.
  rewrite Huidxz in Hb5.
  pose proof (Hb5 Hiso) as [Hmis1 [Hmis2 [Hmb1 Hmb2]]].
  destruct (miscomp_status (u_status y)).
  - assert (miscomparing = miscomparing) as Hstat by trivial.
    pose proof (Hmis1 Hstat) as [Hgd Hindev].
    contradiction.
  - trivial.
  - assert (maybe_miscomparing = maybe_miscomparing) as Hstat by trivial.
    pose proof (Hmb1 Hstat) as [Hdg Hinmb].
    contradiction.
Qed.




Lemma build_updated_u_data_lst_holds_mayb_nil_when_enough_non_isolated
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  :
  let  l := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
  let mis_flt_lmt := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
  length (dlta_dev_lst_grnd_truth l ) <= mis_flt_lmt ->
  length l > 2 * mis_flt_lmt ->

  let new := build_updated_u_data_lst  pf_uids  pf_input pf_ud_lst in
  forall x,
    In x ud_lst
    -> forall y,
      In y new                                            
        -> (uid (u_output x) = uid (u_output y))                   
        -> iso_status (u_status x) = not_isolated
        -> y.(u_status).(miscomp_status) <> maybe_miscomparing .
Proof.

  
  unfold build_updated_u_data_lst.
  intros Hypo Hl x Hxin y Hyin Huidxy Hiso Hmb.  
  unfold update_u_data_frm_comb_elmnt_for_map in Hyin.
  unfold combine_lists in Hyin. 
  apply in_map_iff in Hyin.
  inversion Hyin as [zx [Ha Hb]].
  pose proof ( proj2_sig
              (update_u_data_frm_comb_elmnt (dev_uid_lst pf_uids pf_input pf_ud_lst)
                 (maybe_uid_lst pf_uids pf_input pf_ud_lst) zx))
    as [Hb1 [Hb2 [Hb3 [Hb4 Hb5]]]].
  rewrite Ha in Hb5.
  pose proof (combine_lists_gen_props pf_uids pf_input pf_ud_lst zx) as [Hzxprop].
  pose proof (Hzxprop Hb) as [Hzuidx [Hinput Hud_lst]].
  rewrite Ha in *.
  rewrite Hb2 in Huidxy.
  assert ( x = snd zx ). {
    rewrite Hzuidx in Huidxy.
    exact (fun_out_same_means_same_element_of_lst x Huidxy Hxin Hud_lst
             (mapped_list_nodup pf_ud_lst pf_uids)).
  }
  
  rewrite <- H0 in *.
  pose proof (Hb5 Hiso) as [T [T1 [R T2]]].
  pose proof (R Hmb) as [Hgd H1].
  apply in_map_iff in H1.
  inversion H1 as [t [Htp Hr]].
  rewrite (more_than_double_max_fault_units_means_zero_maybe
             pf_uids pf_input pf_ud_lst Hypo Hl) in Hr.
  inversion Hr.
Qed.




Lemma build_updated_u_data_lst_gives_at_lst_1_hlthy_data
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  :
  let  l := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
  let mis_flt_lmt := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
  length (dlta_dev_lst_grnd_truth l ) <= mis_flt_lmt ->
  length l > 2 * mis_flt_lmt ->

  let new := build_updated_u_data_lst  pf_uids  pf_input pf_ud_lst in
  exists y, In y new /\ healthy_data y.
Proof.
  remember ( build_updated_u_data_lst pf_uids pf_input pf_ud_lst) as new.
  intros l M Hypo Hl.
  
  pose proof (len_l_gt_2lmt_at_lst_1_not_mscmprng
                pf_uids pf_input pf_ud_lst Hypo Hl ) as T.
  inversion T as [p Hpinnm].
  clear T.
  pose proof (build_updated_u_data_lst_preserves_uids
                pf_uids pf_input pf_ud_lst) as pf_new.
  rewrite <- Heqnew in pf_new.
  simpl in pf_new.
  pose proof Hpinnm as Tpinnm.
  apply filter_In in Tpinnm.
  rewrite filter_In in Tpinnm.
  inversion Tpinnm as [[Hpinl T] T1] .  
  clear Tpinnm T T1.
  pose proof Hpinl as Tpinl.
  apply filter_In in Tpinl.
  rewrite in_map_iff in Tpinl. 
  inversion Tpinl as [[pq [Hpqfst Hpqin]] Hpgd].
  apply filter_In in Hpqin.
  inversion Hpqin as [HpqinC Hqiso].
  clear Hpqin Tpinl.
  pose proof (combine_lists_gen_props
                pf_uids pf_input pf_ud_lst pq) as [Hpqgp]. 
  clear H.
  pose proof (Hpqgp HpqinC) as [Hpquid [Hpinput Hqinud_lst]].
  rewrite Hpqfst in Hpinput.

  assert (In (uid p) (get_u_ids_of_unit_data new) ) as Hpinuid. {
    rewrite pf_new.
    rewrite <- pf_input.
    apply in_map_iff.
    exists p. split; trivial.
  }    

  remember (find_data_of_a_given_unit_id pf_new Hpinuid) as y.
  exists (proj1_sig y).
  remember (proj2_sig y).
  inversion a as [H Hyin]. 
  clear Heqa a.
  split; trivial.
  rewrite Heqnew in Hyin.
  unfold build_updated_u_data_lst in Hyin.
  unfold update_u_data_frm_comb_elmnt_for_map in Hyin.
  unfold combine_lists in Hyin. 
  apply in_map_iff in Hyin. 
  inversion Hyin as [ab [Hyequpdate Habin]].
  pose proof ( proj2_sig
              (update_u_data_frm_comb_elmnt (dev_uid_lst pf_uids pf_input pf_ud_lst)
                 (maybe_uid_lst pf_uids pf_input pf_ud_lst) ab))
    as [Hb1 [Hb2 [Hb3 [Hb4 Hb5]]]].
  clear  Hb3 Hb4.
  rewrite Hyequpdate in *.
  pose proof (combine_lists_gen_props pf_uids pf_input pf_ud_lst ab) as [Habprop].
  pose proof (Habprop Habin) as [Hauidb [Hainput Hbud_lst]].
  clear H0 Habprop.
  
  assert ( p = fst ab ). {
    assert (uid p = uid (fst ab) ). {
      rewrite <- Hb2.
      exact H.
    }
    exact (fun_out_same_means_same_element_of_lst p H0 Hpinput Hainput
           (mapped_list_nodup pf_input pf_uids)).
  }
  rewrite <- H0 in *.

  assert (snd ab = snd pq). {
    assert (uid (u_output (snd ab)) = uid (u_output (snd pq)) ). {
      rewrite <- Hpquid.
      rewrite <- Hauidb.
      rewrite Hpqfst.
      trivial.
    }
    exact (fun_out_same_means_same_element_of_lst (snd ab) H1 Hbud_lst Hqinud_lst
             (mapped_list_nodup pf_ud_lst pf_uids)).
  }
  rewrite <- H1 in *.
  pose proof (Hb5 (nisoc_t_not_isltd Hqiso))
    as [Hmis1 [Hmis2 [Hmb1 Hmb2]]].
  clear Hb5.
  assert (miscomp_status (u_status (proj1_sig y)) = not_miscomparing) as Hmb. {
    pose proof (miscomparing_mayb_and_not_lists_are_disjoint
                  pf_uids pf_input pf_ud_lst p Hpinl )
      as [[Hpmis1 Hpmis2] [[Hpmb1 Hpmb2] [Hpnm1 Hpnm2]]].
    pose proof (Hpnm1 Hpinnm) as [Hpninmis Hpninmb].
    clear Hpmis1 Hpmis2 Hpmb1 Hpmb2 Hpnm1 Hpnm2.
    destruct (miscomp_status (u_status (proj1_sig y))).
    - assert (miscomparing = miscomparing) by trivial.
      pose proof ( Hmis1 H2) as [Hgd H3].
      apply in_map_iff in H3.
      inversion H3 as [p' [Hp'uid Hp'in]]. 
      assert (p' = p). {
        remember (proj2_sig (miscomparing_lst pf_uids pf_input pf_ud_lst)).
        pose proof ( a p' Hp'in) as [Hp'inl].
        clear a Heqa H4.
        pose proof (noDup_uids_of_non_iso_good_lst pf_uids pf_input pf_ud_lst).
        exact (fun_out_same_means_same_element_of_lst p' Hp'uid Hp'inl Hpinl H4 ).
      }
      rewrite H4 in Hp'in.
      contradiction.
    - trivial.
    - assert (maybe_miscomparing = maybe_miscomparing) by trivial.
      pose proof (Hmb1 H2) as [Tt].
      apply in_map_iff in H3.
      inversion H3 as [p' [Hp'uid Hp'in]]. 
      assert (p' = p). {
        remember (proj2_sig (maybe_miscomparing_lst pf_uids pf_input pf_ud_lst)) as f.
        pose proof f as a.
        rewrite (Forall_forall) in a.
        pose proof ( a p' Hp'in) as [T [Hp'inl T2]].
        clear a Heqf f T2 T.
        pose proof (noDup_uids_of_non_iso_good_lst pf_uids pf_input pf_ud_lst).
        exact (fun_out_same_means_same_element_of_lst p' Hp'uid Hp'inl Hpinl H4 ).
      }
      rewrite H4 in Hp'in.
      contradiction.
  }

  assert (hw_hlth (reading (u_output (proj1_sig y))) = good ). {
    rewrite Hb2.
    unfold hw_good_unit_check in Hpgd.
    destruct (hw_hlth (reading p)).
    inversion Hpgd. trivial.
  }
  pose proof (Hb1 (nisoc_t_not_isltd Hqiso) ) as [He1 [He2 He3]].
  inversion He1.
  - pose proof (pf_healthy  (proj1_sig y)) as [Hpf1].
    exact (Hpf1 H3).
  - pose proof (He2 H3) as [Hnnm | Hbd].
    -- rewrite Hmb in Hnnm. contradiction.
    -- rewrite Hbd in H2. inversion H2.
Qed.




Definition miscomparing_check
  (x : unit_data) :=
 match (miscomp_status (u_status  x)) with
 | miscomparing => true
 | _            => false                   
 end.


Definition miscomparing_and_prev_non_isoltd_check_for_comb_data
  (y : unit_data*unit_data) :=
  not_iso_check (fst y)
  && miscomparing_check (snd y).


Lemma build_updated_u_data_lst_have_same_miscomparing_and_dev_lst
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  :
  let  l := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
  let mis_flt_lmt := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
  length (dlta_dev_lst_grnd_truth l ) <= mis_flt_lmt ->
  length l > 2 * mis_flt_lmt ->

  let new        := build_updated_u_data_lst  pf_uids  pf_input pf_ud_lst in
  let pf_new     := build_updated_u_data_lst_preserves_uids pf_uids pf_input pf_ud_lst in
  let comp_data  := combine_lists pf_uids pf_ud_lst pf_new in
  let mis_lst    := dev_uid_lst pf_uids pf_input pf_ud_lst in
  let mis_elmnts := map (fun y => snd y)
                      (filter
                         ( fun y
                           => miscomparing_and_prev_non_isoltd_check_for_comb_data y)
                         comp_data)
                        in
  length (mis_lst) = length (mis_elmnts).
Proof.
  intros.
  remember ( map (fun y => uid (u_output y)) mis_elmnts) as mis_elmnts_uids.
   assert (length mis_elmnts = length mis_elmnts_uids) as  Heqlenms. {
      rewrite Heqmis_elmnts_uids.
      rewrite length_map. trivial.
    }
   
  assert (length (mis_lst) <= length(mis_elmnts)). {
    assert (incl mis_lst mis_elmnts_uids). {
      unfold incl.
      intros.
      pose proof H1 as Hinxdev.
      apply in_map_iff in H1.
      inversion H1 as [x0 [Hx0uid Hx0in]].
      apply filter_In in Hx0in.
      inversion Hx0in as [Hx0inl].
      apply filter_In in Hx0inl.
      rewrite in_map_iff in Hx0inl.
      inversion Hx0inl as [[ x1 [Hfst Hinx1]] Hgd].
      apply filter_In in Hinx1.
      inversion Hinx1.
      pose proof (combine_lists_gen_props pf_uids pf_input pf_ud_lst x1) as [Hcl1 Hcl2].
      pose proof (Hcl1 H3) as [Huidfs [Hfin Hsin]].
      
      assert ( In a (get_u_ids_of_unit_data new) ) as pfain. {
        rewrite <- Hx0uid.
        rewrite <- Hfst.
        unfold new.
        rewrite pf_new.
        rewrite <- pf_input.
        apply in_map_iff.
        exists (fst x1). split; trivial.
      }

      rewrite Heqmis_elmnts_uids.
      apply in_map_iff.
      
      remember (find_data_of_a_given_unit_id pf_new pfain ) as pf_y.
      inversion pf_y as [y [Hyuid Hyin]].
      exists y. split. symmetry. trivial.
      apply in_map_iff.
      assert (In a (get_u_ids_of_unit_data ud_lst) ) as  pfainq. {
        rewrite pf_ud_lst. rewrite <- pf_new. trivial. }
      remember (find_data_of_a_given_unit_id pf_ud_lst pfainq ) as pf_x.
      inversion pf_x as [x [Hxuid Hxin]].
      exists (x, y). split; trivial.
      apply filter_In.
      split.
      pose proof (combine_lists_gen_props_data pf_uids pf_ud_lst pf_new (x,y))
        as [Hcld1 Hcld2].
      assert (uid (u_output (fst (x, y))) = uid (u_output (snd (x, y))) /\
         In (fst (x, y)) ud_lst /\
                In (snd (x, y))
                  (build_updated_u_data_lst pf_uids pf_input pf_ud_lst) )
        as Hcdlprop. {
        simpl. rewrite Hxuid in Hyuid.
        repeat split; trivial.
      }
      exact (Hcld2 Hcdlprop).
      assert (not_iso_check x = true) as Hisox. {
       
        assert (uid (u_output (snd x1)) = uid (u_output x) ). {
          rewrite Hfst in Huidfs.
          rewrite Hx0uid in Huidfs.
          rewrite <- Huidfs. trivial.
        }
        assert (snd x1 = x)                 
          by exact (fun_out_same_means_same_element_of_lst (snd x1) H5 Hsin Hxin
                      (mapped_list_nodup pf_ud_lst pf_uids)).
        rewrite <- H6; trivial.
      }         
      unfold miscomparing_and_prev_non_isoltd_check_for_comb_data.
      unfold miscomparing_check.
      simpl.
      rewrite Hisox.
      unfold get_u_id_of_unit_data in *.
      assert (miscomp_status (u_status y) = miscomparing ) as Hmisy. {
        unfold build_updated_u_data_lst in Hyin.
        unfold update_u_data_frm_comb_elmnt_for_map in Hyin.
        apply in_map_iff in Hyin.
        inversion Hyin as [x2 [Heqy Hx2in]].
        remember (proj2_sig
                    (update_u_data_frm_comb_elmnt (dev_uid_lst pf_uids pf_input pf_ud_lst)
                       (maybe_uid_lst pf_uids pf_input pf_ud_lst) x2)).
        simpl in b.
        pose proof b as Hbsprop.
        rewrite Heqy in Hbsprop.
        clear Heqb b.
        inversion Hbsprop as [T1 [Hyeqfx2 [T3 [T4 Hmisprop]]]]. 
        clear  T1  T3 T4.
        clear Hcl1 Hcl2.
        pose proof (combine_lists_gen_props pf_uids pf_input pf_ud_lst x2) as [Hcl1].
        pose proof (Hcl1 Hx2in) as [Hx2fs [Hx2fin Hx2sin]].
        assert (iso_status (u_status (snd x2)) = not_isolated). {
          
          assert (uid (u_output  x) = uid (u_output (snd x2))). {
            rewrite Hxuid in  Hyuid.            
            rewrite <- Hyeqfx2 in Hx2fs.
            rewrite Hyuid. trivial.
          }
          assert ( x = snd x2)
            by exact (fun_out_same_means_same_element_of_lst x H6 Hxin Hx2sin
                        (mapped_list_nodup pf_ud_lst pf_uids)).
          rewrite H7 in Hisox.
          exact (nisoc_t_not_isltd Hisox).
        }
        pose proof (Hmisprop H6) as [Hmis1 [Hmis2 [Hmb1 Hmb2]]].
        pose proof (dev_lst_and_mayb_lst_are_disjoint pf_uids pf_input pf_ud_lst a) as [Hindev].
        rewrite <- Hyeqfx2 in Hmis2.
        rewrite <- Hyuid in Hmis2.
        assert ( hw_hlth (reading (u_output y)) = good  ) as Hygd. {
          clear Hmisprop Hmis1 Hmis2 H5 Hmb1 Hmb2 Hbsprop Heqpf_y pf_y Hyin.
          clear Hinx1 Hcl1.
          clear Hx0in Hx0inl.
          assert (x0 = u_output y  ).
          { rewrite Hfst in Hfin.
            rewrite Hyuid in Hx0uid.
            rewrite <- Hyeqfx2 in Hx2fin.
            exact (fun_out_same_means_same_element_of_lst x0 Hx0uid Hfin Hx2fin
                     (mapped_list_nodup pf_input pf_uids)).
          }
          rewrite <- H5.
          unfold hw_good_unit_check in Hgd.
          destruct (hw_hlth (reading x0)).
          inversion Hgd. trivial.
        }            
            
        exact (Hmis2 Hinxdev (Hindev Hinxdev) Hygd ).
      }
      rewrite Hmisy.
      trivial.
    }
    assert ( NoDup mis_lst ). {
      unfold mis_lst, dev_uid_lst, miscomparing_lst.
      simpl.
      pose proof (noDup_uids_of_non_iso_good_lst pf_uids pf_input pf_ud_lst ).
      exact (nodup_map_filter H2).
    }
   
    assert (length mis_elmnts = length mis_elmnts_uids). {
      rewrite Heqmis_elmnts_uids.
      rewrite length_map. trivial.
    }
    rewrite Heqlenms.
    exact (sub_list_length_le_list_length H2 H1).
  }

  assert ( length mis_elmnts <= length mis_lst ). {
  
    assert (incl mis_elmnts_uids mis_lst). {
      unfold incl.
      rewrite Heqmis_elmnts_uids.
      intros a Hain.
      apply in_map_iff in Hain.
      inversion Hain as [x [Hxeqa Hxinmse]].
      apply in_map_iff in Hxinmse.
      inversion Hxinmse as [x0 [Hx0eq Hx0in]].
      apply filter_In in Hx0in.
      inversion Hx0in as [Hx0incd Hx0prop].
      unfold miscomparing_and_prev_non_isoltd_check_for_comb_data in Hx0prop.
      assert (iso_status (u_status (fst x0)) = not_isolated
              /\ miscomp_status (u_status (snd x0)) = miscomparing )
        as Hisomis. {
        apply andb_prop in Hx0prop.
        
        unfold miscomparing_check in Hx0prop.
        inversion Hx0prop as [Hisoprop Hmis].
        destruct (not_iso_check (fst x0) ) eqn:Hiso.
        split. exact (nisoc_t_not_isltd Hiso). 
        destruct (miscomp_status (u_status (snd x0))) .
        trivial. 
        inversion Hmis.
        inversion Hmis.
        inversion Hisoprop.
      }
      inversion Hisomis as [Hiso Hmis]. clear Hisomis.

      pose proof (combine_lists_gen_props_data pf_uids pf_ud_lst pf_new x0) as [Hcl].
      pose proof (Hcl Hx0incd) as [Hx0uids [Hx0fin Hx0sin]].
      clear H2 Hx0prop Hxinmse Hcl.
      apply in_map_iff in Hx0sin.
      inversion Hx0sin as [xy [Heqfx0 Hxyin]].
      unfold update_u_data_frm_comb_elmnt_for_map in Heqfx0.

      pose proof (proj2_sig
             (update_u_data_frm_comb_elmnt (dev_uid_lst pf_uids pf_input pf_ud_lst)
                (maybe_uid_lst pf_uids pf_input pf_ud_lst) xy)) as Hprj2.
      simpl in Hprj2.
      rewrite Heqfx0 in Hprj2.
      inversion Hprj2 as [T [Teqfxy [T2 [T3 Tmis]]]].
      assert (fst x0 = snd xy ) as Heqsxyfx0.
      {
        pose proof (combine_lists_gen_props pf_uids pf_input pf_ud_lst xy) as [Hcl].
        pose proof (Hcl Hxyin) as [Hxyequid [Hxin Hyin]].
        clear T Hcl H2 T2 T3.
        rewrite Teqfxy in Hx0uids.
        rewrite Hxyequid in Hx0uids.
        exact (fun_out_same_means_same_element_of_lst (fst x0) Hx0uids Hx0fin Hyin
                 (mapped_list_nodup pf_ud_lst pf_uids)).
      }
      rewrite Heqsxyfx0 in Hiso. 
      pose proof (Tmis Hiso) as [Hmis1]. 
      rewrite <- Hxeqa.
      rewrite <- Hx0eq.
      rewrite Teqfxy.
      pose proof (Hmis1 Hmis) as [HT N].
      trivial.
    }

    assert (NoDup mis_elmnts_uids). {
      rewrite Heqmis_elmnts_uids.
      unfold mis_elmnts.
      exact (map_on_snd_comb_lst_fltr_is_nodup pf_uids pf_ud_lst pf_new).
    }
    rewrite Heqlenms.
    exact (sub_list_length_le_list_length H3 H2).
   }

   lia.
Qed.      
         


Definition unhealthy_and_pre_non_isltd_check_for_comb_data
  (x : unit_data*unit_data) :=
  not_iso_check (fst x)
  && ( miscomparing_check (snd x)
  || negb (hw_good_unit_check (u_output (snd x)))).

Definition newly_isolated_check
  (x : unit_data*unit_data) :=
  andb  (not_iso_check (fst x)) (negb (not_iso_check (snd x))).


Lemma bads_lists_are_equal
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  { new_q : list unit_data } (pf_new_q :  get_u_ids_of_unit_data new_q =  u_ids  )
  (pf_new_q_eq_input : get_u_outputs_of_data new_q = input)

  : map (fun x : unit_data * unit_data => u_output (snd x))
      (filter
         (fun y : unit_data * unit_data =>
            not_iso_check (fst y) &&
              negb (hw_good_unit_check (u_output (snd y))))
         (combine_lists pf_uids pf_ud_lst pf_new_q))
    = filter
        (fun y : unit_output => negb (hw_good_unit_check y))
        (map (fun x : unit_output * unit_data => fst x)
           (filter
              (fun y : unit_output * unit_data =>
                 not_iso_check (snd y))
              (combine_lists pf_uids pf_input pf_ud_lst))).
Proof.
  unfold combine_lists.
  generalize dependent u_ids.
  generalize dependent ud_lst.
  generalize dependent new_q.

  induction input; intros.
  - 
    apply map_eq_nil in pf_new_q_eq_input.
    rewrite pf_new_q_eq_input.
    simpl in *.
    rewrite <- pf_input in pf_ud_lst.
    apply map_eq_nil in pf_ud_lst.
    rewrite pf_ud_lst. trivial.
  -
    destruct u_ids, ud_lst, new_q.
    -- inversion pf_input.
    -- inversion pf_input.
    -- inversion pf_input.
    -- inversion pf_input.
    -- inversion pf_ud_lst.
    -- inversion pf_ud_lst.
    -- inversion pf_new_q.
    -- inversion pf_input.
       inversion pf_ud_lst.
       inversion pf_new_q.
       inversion pf_uids.
       inversion pf_new_q_eq_input.
       simpl.
       rewrite H11.
       destruct (not_iso_check u0). 
       --- simpl.
           destruct ( negb (hw_good_unit_check (u_output u1))).
           simpl.
           f_equal.
           exact (IHinput new_q H11 ud_lst u_ids
                    H8 H1 H3 H5 ).
           exact (IHinput new_q H11 ud_lst u_ids
                          H8 H1 H3 H5 ).
       --- simpl.
           exact (IHinput new_q H11 ud_lst u_ids
                    H8 H1 H3 H5 ).
Qed.
  
Lemma build_updated_u_data_lst_have_le_lmt_newly_isltd
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  :

  simul_fault_prop pf_uids pf_input pf_ud_lst
                   
  -> let  l := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
     let mis_flt_lmt := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
     length l > 2 * mis_flt_lmt
  
  -> let new_q        := build_updated_u_data_lst  pf_uids  pf_input pf_ud_lst in
     let pf_new_q     := build_updated_u_data_lst_preserves_uids pf_uids pf_input pf_ud_lst in
     let comb_data    := combine_lists pf_uids pf_ud_lst pf_new_q in
     let newly_isoltd := map (fun y => snd y)
                           (filter
                              ( fun y => newly_isolated_check y) comb_data)
     in
     length (newly_isoltd) <= simul_max_fault.
Proof.
  intros SFP l mis_flt_lmt Hl new_q pf_new_q comb_data newly_isoltd.
  remember (map (fun y => snd y)
            (filter
               ( fun y => unhealthy_and_pre_non_isltd_check_for_comb_data y)
               comb_data) )
    as  unhealthy_pre_non_iso_lst.
  assert ( length (dlta_dev_lst_grnd_truth l) <= mis_flt_lmt) as Hmishypo
      by exact (mis_fault_hypo  pf_uids pf_input pf_ud_lst SFP).
  assert (incl newly_isoltd unhealthy_pre_non_iso_lst ) as Hincl. {
    unfold incl.
    intros a Hain.
    apply in_map_iff in Hain.
    inversion Hain as [xy [Hxyuid Hxyinfcd]].
    rewrite filter_In in Hxyinfcd.
    inversion Hxyinfcd as [Hxyincd Hxyprop].
    clear Hain Hxyinfcd.
    unfold newly_isolated_check in Hxyprop.
    rewrite Hequnhealthy_pre_non_iso_lst.
    apply in_map_iff.
    exists xy.
    split; trivial.
    apply filter_In.
    split; trivial.
    unfold unhealthy_and_pre_non_isltd_check_for_comb_data.
    unfold miscomparing_check.
    apply andb_prop in Hxyprop. 
    inversion Hxyprop as [Hisoxprop Hisoyprop].
    rewrite Hisoxprop.
    pose proof (combine_lists_gen_props_data pf_uids pf_ud_lst pf_new_q xy)
      as [Hcl1 Hcl2].
    pose proof (Hcl1 Hxyincd) as [Huidxeqy [Hxin Hyin]].
    clear Hcl1 Hcl2.
   
    
    destruct (miscomp_status (u_status (snd xy))) eqn:Hmis.
    - trivial.
    - 
      apply negb_true_iff in Hisoyprop. 
      pose proof (nisoc_f_isltd Hisoyprop) as Hisoy.
      apply in_map_iff in Hyin.
      inversion Hyin as [pq [Hupeqy Hpqin]].
      unfold update_u_data_frm_comb_elmnt_for_map in Hupeqy.
      pose proof (proj2_sig
                    (update_u_data_frm_comb_elmnt (dev_uid_lst pf_uids pf_input pf_ud_lst)
                       (maybe_uid_lst pf_uids pf_input pf_ud_lst) pq) ) as Hprj.
      rewrite Hupeqy in Hprj.
      inversion Hprj 
        as [Hrcp [Hyeqp T]].
      clear Hprj Hyin T.
      
      pose proof (pf_risky_count (u_status (snd xy))) as [T [Hrciso Hisorc]].
      unfold risky_cnt_prop in Hrcp.
      assert (iso_status (u_status (snd pq)) = not_isolated) as Hisoq. {
        assert (fst xy =  snd pq ) as Hxeqp. {
          pose proof (combine_lists_gen_props pf_uids pf_input pf_ud_lst pq) as [Hcl1 Hcl2].
          pose proof (Hcl1 Hpqin) as [Huidpeqq [Hpin Hqin]].
          clear Hcl1 Hcl2.
          rewrite <- Hyeqp in Huidpeqq.
          rewrite <- Huidxeqy in Huidpeqq.
          exact (fun_out_same_means_same_element_of_lst (fst xy) Huidpeqq Hxin Hqin
              (mapped_list_nodup pf_ud_lst pf_uids)).
        }
        rewrite Hxeqp in Hisoxprop.
        exact (nisoc_t_not_isltd Hisoxprop).
      }
      
      pose proof (Hrcp Hisoq) as [Hrc0n0 [Hrcn0prop T1]].
      clear Hrcp T T1.
      inversion Hrc0n0 as [Hrc0 | Hrcn0].
      --
        rewrite (Hisorc Hisoy) in Hrc0.
        inversion Hrc0.
      -- apply negb_true_iff.
         unfold hw_good_unit_check.
         pose proof (Hrcn0prop Hrcn0) as Hmisbad.
         inversion Hmisbad as  [Hnmis | Hbad].
         rewrite Hmis in Hnmis.
         contradiction.
         rewrite Hbad.
         trivial.
    - pose proof (build_updated_u_data_lst_holds_mayb_nil_when_enough_non_isolated
                    pf_uids pf_input pf_ud_lst Hmishypo Hl
                    (fst xy) Hxin (snd xy) Hyin Huidxeqy
                    (nisoc_t_not_isltd Hisoxprop)
        ).
      rewrite Hmis in H.
      contradiction.
  }

  assert (length newly_isoltd <= length unhealthy_pre_non_iso_lst) as Hnewly.
  {
    assert (NoDup newly_isoltd ) as Hnd. {
      unfold newly_isoltd.
      assert (NoDup (map (fun y : unit_data * unit_data => snd y) comb_data) )
        as Hndsnd. {
        unfold comb_data.
        rewrite (second_of_combine_lists_is_l2 pf_uids pf_ud_lst pf_new_q).
        
        pose proof  (mapped_list_nodup pf_new_q pf_uids) as Hnduid. 
        apply NoDup_map_inv in Hnduid.
        trivial.
      }
      exact (nodup_map_filter Hndsnd).
    }
    exact (sub_list_length_le_list_length Hnd Hincl).
  }
  

  assert ( forall x, In x comb_data ->
                (not_iso_check (fst x) && miscomparing_check (snd x) = true
                 -> hw_good_unit_check (u_output (snd x)) = true) ).
  {
    unfold miscomparing_check.
    unfold hw_good_unit_check.
    intros x Hxincl Hprop. 
    
    apply andb_prop in Hprop.
    inversion Hprop as [Hisofx Hmisprop].
    assert (miscomp_status (u_status (snd x)) = miscomparing ) as Hmis. {
      destruct (miscomp_status (u_status (snd x))).
      trivial.
      inversion Hmisprop.
      inversion Hmisprop.
    }
      
    pose proof (combine_lists_gen_props_data pf_uids pf_ud_lst pf_new_q x) as [Hxgp T].
    clear T.
    pose proof (Hxgp Hxincl) as [Hfxuideqsx [Hfxin Hsxin]].    
    apply in_map_iff in Hsxin.
    unfold update_u_data_frm_comb_elmnt_for_map in Hsxin.
    inversion Hsxin as [pq [Hprjeqsx Hpqin]].
    pose proof (proj2_sig
                  (update_u_data_frm_comb_elmnt (dev_uid_lst pf_uids pf_input pf_ud_lst)
                     (maybe_uid_lst pf_uids pf_input pf_ud_lst) pq) ) as Hprj.
    rewrite Hprjeqsx in Hprj.
    inversion Hprj as [Hrcp [Hyeqp [Ti [Tn Hmisprops]]]].
    clear Ti Tn Hrcp.
    assert (iso_status (u_status (snd pq)) = not_isolated) as Hsndpqiso. {
      assert ( fst x = snd pq ) as Heqfxq. {
        rewrite Hyeqp in Hfxuideqsx.
        pose proof (combine_lists_gen_props pf_uids pf_input pf_ud_lst pq) as [Hpqgp T].
        clear T.
        pose proof (Hpqgp Hpqin) as [Huideqpq [Hpin Hqin]].
        rewrite <- Hfxuideqsx in Huideqpq.
        exact (fun_out_same_means_same_element_of_lst (fst x) Huideqpq Hfxin Hqin 
                 (mapped_list_nodup pf_ud_lst pf_uids)).
      }
      rewrite Heqfxq in Hisofx.
      exact (nisoc_t_not_isltd Hisofx).
    }
    pose proof (Hmisprops Hsndpqiso) as [Hmis1 T].
    clear T Hmisprops.
    pose proof (Hmis1 Hmis ) as [Hgd Hindev].
    rewrite Hyeqp.
    rewrite Hgd.
    trivial.
  }   
  pose proof ( length_of_filter_FandGorH_eq_length_of_FandG_plus_FandH H).
  simpl in H0.
  unfold simul_fault_prop in SFP.
  assert (length
          (filter (fun y : unit_output => negb (hw_good_unit_check y))
             (map (fun x : unit_output * unit_data => fst x)
                (filter (fun y : unit_output * unit_data => not_iso_check (snd y))
                   (combine_lists pf_uids pf_input pf_ud_lst))))
          = length
         (filter
            (fun y : unit_data * unit_data =>
             not_iso_check (fst y) &&
               negb (hw_good_unit_check (u_output (snd y)))) comb_data) ).
  {
    remember (filter (fun y : unit_output => negb (hw_good_unit_check y))
             (map (fun x : unit_output * unit_data => fst x)
                (filter (fun y : unit_output * unit_data => not_iso_check (snd y))
                   (combine_lists pf_uids pf_input pf_ud_lst)))) as bad_lst_input.

    remember (map (fun x => u_output (snd x))
                (filter
                   (fun y  =>
                      not_iso_check (fst y) &&
                        negb (hw_good_unit_check (u_output (snd y))))
                   comb_data))
      as bad_lst_new_q.
    unfold comb_data in *.

    assert (bad_lst_input = bad_lst_new_q) as Hsamebad. 
      assert (get_u_outputs_of_data new_q = input) as Hsouteqinput
          by exact (build_updated_u_data_lst_preserves_input_data
                      pf_uids pf_input pf_ud_lst).
      rewrite Heqbad_lst_input.
      rewrite Heqbad_lst_new_q.
      symmetry.
      exact (bads_lists_are_equal pf_uids pf_input pf_ud_lst
               pf_new_q Hsouteqinput ).
      rewrite Hsamebad.
      rewrite Heqbad_lst_new_q.
      rewrite length_map.
      trivial.
  }      
  rewrite <- H1 in H0.
  clear H1.
  assert (length
         (filter
            (fun y : unit_data * unit_data =>
             not_iso_check (fst y) &&
             (miscomparing_check (snd y)
              || negb (hw_good_unit_check (u_output (snd y))))) comb_data)
          = length unhealthy_pre_non_iso_lst ). {
    unfold unhealthy_and_pre_non_isltd_check_for_comb_data in *.
    rewrite Hequnhealthy_pre_non_iso_lst.
    rewrite length_map.
    trivial.
  }
  rewrite H1 in H0.
  clear H1.
  assert (length
            (filter
               (fun y : unit_data * unit_data =>
                  not_iso_check (fst y) && miscomparing_check (snd y)) comb_data)
          <= mis_flt_lmt ).
  
  assert (length ( map (fun y : unit_data * unit_data => snd y)
                     (filter
                        (fun y : unit_data * unit_data =>
                           miscomparing_and_prev_non_isoltd_check_for_comb_data y)
                        comb_data))
          = length
              (filter
                 (fun y : unit_data * unit_data =>
                    not_iso_check (fst y) && miscomparing_check (snd y)) comb_data) ).
  { rewrite length_map. trivial. }
  rewrite <- H1.
  unfold comb_data.
  unfold pf_new_q.
  rewrite <- (build_updated_u_data_lst_have_same_miscomparing_and_dev_lst
               pf_uids pf_input pf_ud_lst  Hmishypo Hl).
  unfold dev_uid_lst.
  rewrite length_map.
  exact (len_mis_lst_le_mis_flt_lmt pf_uids pf_input pf_ud_lst Hmishypo).
  unfold mis_flt_lmt in H1.
  unfold flt_lmt_among_good in H1.
  unfold num_of_bad_and_non_isolated in H1.
  lia.
Qed.




Lemma non_isolated_list_new_eq_non_isolated_among_prev_non_isolated
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  { new_q : list unit_data } (pf_new_q : get_u_ids_of_unit_data new_q =  u_ids )
  (pf_iso : forall x, In x (get_u_ids_of_unit_data (isolated_list ud_lst)) ->
                      In x (get_u_ids_of_unit_data (isolated_list new_q)) )
  :
  map (fun y : unit_data * unit_data => snd y)
    (filter (fun y : unit_data * unit_data => not_iso_check (snd y))
       (filter (fun z : unit_data * unit_data => not_iso_check (fst z))
          (combine ud_lst new_q))) =
    non_isolated_list new_q.
Proof.
  generalize dependent u_ids.
  generalize dependent ud_lst.
  generalize dependent input.

  induction new_q; intros.
  - rewrite combine_nil.
    trivial.
  - destruct u_ids, ud_lst, input.
    -- inversion pf_new_q.
    -- inversion pf_new_q.
    -- inversion pf_new_q.
    -- inversion pf_new_q.
    -- inversion pf_input.
    -- inversion pf_ud_lst.
    -- inversion pf_input.
    -- inversion pf_input.
       inversion pf_uids.
       inversion pf_new_q.
       inversion pf_ud_lst.
       simpl.
       destruct (not_iso_check u0) eqn:Hisos0.
       ---
         simpl. 
         destruct (not_iso_check a) eqn:Hisoa.
         ----
           simpl.
           f_equal.
           assert ( (forall x : unit_id,
             In x (get_u_ids_of_unit_data (isolated_list ud_lst)) ->
             In x (get_u_ids_of_unit_data (isolated_list new_q)))) as Hisoprop. {
             intros.
             assert ( In x0 (get_u_ids_of_unit_data (isolated_list (u0 :: ud_lst))) ). {
               simpl.
               rewrite Hisos0.
               simpl.
               exact H5.
             }
             pose proof (pf_iso x0 H10).
             simpl in H11.
             rewrite Hisoa in H11.
             exact H11.
           }
           exact (IHnew_q input ud_lst Hisoprop u_ids H4 H1 H9 H7). 
         ----  
           assert ( (forall x : unit_id,
             In x (get_u_ids_of_unit_data (isolated_list ud_lst)) ->
             In x (get_u_ids_of_unit_data (isolated_list new_q)))) as Hisoprop. {
             intros.
             assert ( In x0 (get_u_ids_of_unit_data (isolated_list (u0 :: ud_lst))) ). {
               simpl.
               rewrite Hisos0.
               simpl.
               exact H5.
             }
             pose proof (pf_iso x0 H10).
             simpl in H11.
             rewrite Hisoa in H11.
             simpl in H11.
             inversion H11.
             apply in_map_iff in H5.
             inversion H5 as [x1 [Huidx1 Hx1in]].
             apply filter_In in Hx1in.
             inversion Hx1in as [Hx1inq Hx1iso].
             assert ( In u u_ids). {
               rewrite <- H6.
               rewrite <- H9.
               rewrite H12.
               apply in_map_iff.
               exists x1. split; trivial.
             }
             contradiction.
             exact H12.
           }
           exact (IHnew_q input ud_lst Hisoprop u_ids H4 H1 H9 H7).
       ---
         simpl. 
         destruct (not_iso_check a) eqn:Hisoa.
         ----
           assert ( In u  (get_u_ids_of_unit_data (isolated_list (u0 :: ud_lst)))).
           {
             apply in_map_iff.
             exists u0.
             split; trivial.
             apply filter_In.
             split. apply in_eq.
             rewrite Hisos0.
             trivial.
           }
           pose proof ( pf_iso u H5 ).
           apply in_map_iff in H10.
           inversion H10 as [b [Huid Hbinisol]].
           apply filter_In in Hbinisol.
           inversion Hbinisol as [Hbinnew Hbisoprop].
           assert ( a = b). {
             assert (In a (a::new_q) ) by apply in_eq.
             rewrite <- Huid in H6.
             exact (fun_out_same_means_same_element_of_lst
                     a H6 H11 Hbinnew  (mapped_list_nodup pf_new_q pf_uids)).
           }
           rewrite H11 in Hisoa.
           rewrite Hisoa in Hbisoprop.
           inversion Hbisoprop.
         ----
           assert ( (forall x : unit_id,
             In x (get_u_ids_of_unit_data (isolated_list ud_lst)) ->
             In x (get_u_ids_of_unit_data (isolated_list new_q)))) as Hisoprop. {
             intros.
             assert ( In x0 (get_u_ids_of_unit_data (isolated_list (u0 :: ud_lst))) ). {
               simpl.  
               rewrite Hisos0.
               simpl.
               right.
               exact H5.
             }
             pose proof (pf_iso x0 H10).
             simpl in H11.
             rewrite Hisoa in H11.
             simpl in H11.
             inversion H11.
             apply in_map_iff in H5.
             inversion H5 as [x1 [Huidx1 Hx1in]].
             apply filter_In in Hx1in.
             inversion Hx1in as [Hx1inq Hx1iso].
             assert ( In u u_ids). {
               rewrite <- H6.
               rewrite <- H9.
               rewrite H12.
               apply in_map_iff.
               exists x1. split; trivial.
             }
             contradiction.
             exact H12.
           }
           exact (IHnew_q input ud_lst Hisoprop u_ids H4 H1 H9 H7).
 Qed.        


Lemma sfp_and_gt_2smf_non_iso_implies_len_good_non_iso_gt_2mis_flt_lmt
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  :

  simul_fault_prop pf_uids pf_input pf_ud_lst
                   
  -> count_of_non_isolated_units ud_lst > 2 * simul_max_fault
                   
  -> let  l := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
     let mis_flt_lmt := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
     length l > 2 * mis_flt_lmt.

  intros Hsfp  Hcnisoq.
  remember (proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst)) as l.
  remember (flt_lmt_among_good pf_uids pf_input pf_ud_lst) as mis_flt_lmt.
  remember (map (fun x : unit_output * unit_data => fst x)
              (non_isltd_comb_lst (combine input ud_lst))) as nisocl.
  unfold count_of_non_isolated_units in Hcnisoq.
  assert (length (nisocl) = length (non_isolated_list ud_lst) ) as Heqlen. {
    
    assert (get_u_ids_of_unit_output nisocl = get_u_ids_of_unit_data
                                                ( non_isolated_list ud_lst)) as Heql1l2. {
      rewrite Heqnisocl.
      clear Hsfp Hcnisoq Heql l Heqmis_flt_lmt mis_flt_lmt .
      clear Heqnisocl nisocl.
      generalize dependent u_ids.
      generalize dependent input.
      
      induction ud_lst; intros.
      - simpl in *.
        assert (input = [] ) as Hin. {
          rewrite <- pf_ud_lst in pf_input.
          apply map_eq_nil in pf_input.
          exact pf_input.
        }
        rewrite Hin.
        trivial.
      - destruct u_ids, input.
        -- inversion pf_ud_lst.
        -- inversion pf_ud_lst.
        -- inversion pf_input.
        -- inversion pf_ud_lst.
           inversion pf_input.
           inversion pf_uids.
           simpl.
           unfold non_isltd_comb_lst.
           simpl.
           destruct (not_iso_check a).
           simpl.
           f_equal.
           rewrite H0. trivial.
           exact (IHud_lst input u_ids H6 H3 H1).
           
           exact (IHud_lst input u_ids H6 H3 H1).
    }
    assert (length (get_u_ids_of_unit_output nisocl)
            = length (get_u_ids_of_unit_data (non_isolated_list ud_lst)) ) as Heqlenmap. {
      rewrite Heql1l2. reflexivity. }
    unfold get_u_ids_of_unit_output in Heqlenmap.
    rewrite length_map in Heqlenmap.
    unfold get_u_ids_of_unit_data in Heqlenmap.
    rewrite length_map in Heqlenmap.
    exact Heqlenmap.
  }
  


  
    rewrite Heql.
    unfold all_good_non_iso_lst.
    simpl.
    unfold combine_lists in *.
    rewrite <- Heqnisocl.

    pose proof (filter_length_le
                  (fun y : unit_output => hw_good_unit_check y)
                  nisocl ) as Hfle.
    rewrite Heqmis_flt_lmt.
    unfold flt_lmt_among_good.
    unfold num_of_bad_and_non_isolated.
    unfold non_isltd_comb_lst in Heqnisocl.
    unfold combine_lists in *.
    rewrite <- Heqnisocl.
    pose proof (filter_length_le
                  (fun y : unit_output => negb (hw_good_unit_check y))
                  nisocl) as Hnfle.
    rewrite <- Heqlen in Hcnisoq.
    unfold simul_fault_prop in Hsfp.
    unfold combine_lists in *.
    rewrite <- Heqnisocl in *.
    pose proof (filter_length
                  (fun y : unit_output => hw_good_unit_check y)
                  nisocl ) as Hfl.
    lia.
Qed.




Lemma build_updated_u_data_lst_have_gt_mx_lmt_non_isltd
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  :

  simul_fault_prop pf_uids pf_input pf_ud_lst
  -> count_of_non_isolated_units ud_lst > 2 * simul_max_fault
 
  -> let new_q        := build_updated_u_data_lst  pf_uids  pf_input pf_ud_lst in
     count_of_non_isolated_units new_q > simul_max_fault.

Proof.
  intros Hsfp  Hcnisoq new_q.
  remember (proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst)) as l.
  remember (flt_lmt_among_good pf_uids pf_input pf_ud_lst) as mis_flt_lmt.
  remember (map (fun x : unit_output * unit_data => fst x)
              (non_isltd_comb_lst (combine input ud_lst))) as nisocl.
  unfold count_of_non_isolated_units in Hcnisoq.
  assert (length (nisocl) = length (non_isolated_list ud_lst) ) as Heqlen. {
    
    assert (get_u_ids_of_unit_output nisocl = get_u_ids_of_unit_data
                                                ( non_isolated_list ud_lst)) as Heql1l2. {
      rewrite Heqnisocl.
      clear Hsfp Hcnisoq new_q Heql l Heqmis_flt_lmt mis_flt_lmt .
      clear Heqnisocl nisocl.
      generalize dependent u_ids.
      generalize dependent input.
      
      induction ud_lst; intros.
      - simpl in *.
        assert (input = [] ) as Hin. {
          rewrite <- pf_ud_lst in pf_input.
          apply map_eq_nil in pf_input.
          exact pf_input.
        }
        rewrite Hin.
        trivial.
      - destruct u_ids, input.
        -- inversion pf_ud_lst.
        -- inversion pf_ud_lst.
        -- inversion pf_input.
        -- inversion pf_ud_lst.
           inversion pf_input.
           inversion pf_uids.
           simpl.
           unfold non_isltd_comb_lst.
           simpl.
           destruct (not_iso_check a).
           simpl.
           f_equal.
           rewrite H0. trivial.
           exact (IHud_lst input u_ids H6 H3 H1).
           
           exact (IHud_lst input u_ids H6 H3 H1).
    }
    assert (length (get_u_ids_of_unit_output nisocl)
            = length (get_u_ids_of_unit_data (non_isolated_list ud_lst)) ) as Heqlenmap. {
      rewrite Heql1l2. reflexivity. }
    unfold get_u_ids_of_unit_output in Heqlenmap.
    rewrite length_map in Heqlenmap.
    unfold get_u_ids_of_unit_data in Heqlenmap.
    rewrite length_map in Heqlenmap.
    exact Heqlenmap.
  }
  


  assert (length l > 2 * mis_flt_lmt ) as Hl. {
    rewrite Heql.
    unfold all_good_non_iso_lst.
    simpl.
    unfold combine_lists in *.
    rewrite <- Heqnisocl.

    pose proof (filter_length_le
                  (fun y : unit_output => hw_good_unit_check y)
                  nisocl ) as Hfle.
    rewrite Heqmis_flt_lmt.
    unfold flt_lmt_among_good.
    unfold num_of_bad_and_non_isolated.
    unfold non_isltd_comb_lst in Heqnisocl.
    unfold combine_lists in *.
    rewrite <- Heqnisocl.
    pose proof (filter_length_le
                  (fun y : unit_output => negb (hw_good_unit_check y))
                  nisocl) as Hnfle.
    rewrite <- Heqlen in Hcnisoq.
    unfold simul_fault_prop in Hsfp.
    unfold combine_lists in *.
    rewrite <- Heqnisocl in *.
    pose proof (filter_length
                  (fun y : unit_output => hw_good_unit_check y)
                  nisocl ) as Hfl.
    lia.
  }
  rewrite Heqmis_flt_lmt in Hl.
  rewrite Heql in Hl.
  pose proof (build_updated_u_data_lst_have_le_lmt_newly_isltd
                pf_uids pf_input pf_ud_lst Hsfp Hl).
  simpl in H.
  unfold newly_isolated_check in H.
  rewrite (filter_andb_eq_filter_on_filter) in H.
  remember (filter (fun z : unit_data * unit_data => not_iso_check (fst z))
              (combine_lists pf_uids pf_ud_lst
                    (build_updated_u_data_lst_preserves_uids pf_uids pf_input pf_ud_lst)))
    as lnisocl.
  
  pose proof (build_updated_u_data_lst_preserves_uids
                pf_uids pf_input pf_ud_lst ) as pf_new_q.
  simpl in pf_new_q.
  fold new_q in pf_new_q.
  assert (length lnisocl = length (non_isolated_list ud_lst) ) as Heqlenl. {
    assert ( map (fun y : unit_data * unit_data => fst y)
               lnisocl = non_isolated_list ud_lst ) as Heql1l2. {
      rewrite Heqlnisocl. fold new_q.
      clear Hsfp Hcnisoq  Heql l Heqmis_flt_lmt mis_flt_lmt Heqnisocl nisocl
        H Heqlnisocl lnisocl Hl Heqlen.
      unfold non_isolated_list.
      
      exact (map_and_filter_on_fst_of_comb_list_is_equal_to_that_of_l1
               pf_uids pf_ud_lst pf_new_q not_iso_check).
    }
    assert (length (map (fun y : unit_data * unit_data => fst y) lnisocl)
            = length (non_isolated_list ud_lst) ) as Heqlenl1l2. {
      rewrite Heql1l2. reflexivity.
    }    

    rewrite length_map in Heqlenl1l2.
    exact Heqlenl1l2.
  }  
  pose proof ( filter_length
                 (fun y : unit_data * unit_data => negb (not_iso_check (snd y)))
                 lnisocl ).
  simpl in H0.
  rewrite filter_negb_negb_f_is_f in H0.
  assert ( length
             (filter
                (fun y : unit_data * unit_data => not_iso_check (snd y))
                lnisocl) > simul_max_fault ).
  {
    rewrite <- Heqlenl in Hcnisoq.
    assert (length
         (filter (fun y : unit_data * unit_data => negb (not_iso_check (snd y)))
            lnisocl) <= simul_max_fault ). {
      rewrite length_map in H.
      trivial.
    }
    lia.
  }
  assert ( map (fun y : unit_data * unit_data => snd y) 
              (filter
                 (fun y : unit_data * unit_data => not_iso_check (snd y))
                 lnisocl)
           = non_isolated_list new_q ). {
    pose proof (once_isolated_remain_isolated_after_build_updated_u_data_lst
                  pf_uids pf_input pf_ud_lst).
    
    rewrite Heqlnisocl.
    exact (non_isolated_list_new_eq_non_isolated_among_prev_non_isolated
             pf_uids pf_input pf_ud_lst pf_new_q H2).
  }    

  assert (length ( map (fun y : unit_data * unit_data => snd y)
         (filter (fun y : unit_data * unit_data => not_iso_check (snd y)) lnisocl)) =
            length (non_isolated_list new_q) ).
  { rewrite H2. reflexivity. }
  rewrite length_map in H3.
  unfold count_of_non_isolated_units.
  rewrite <- H3.
  exact H1.
Qed.

Lemma build_updated_u_data_lst_holds_miscomp_check_true_case
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  :
  let  l := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
  let mis_flt_lmt := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
  let new := build_updated_u_data_lst  pf_uids  pf_input pf_ud_lst in
  forall x,
    In x ud_lst
    -> forall y,
      In y new
      ->  forall z,
        In z l                                                  
        -> (uid (u_output x) = uid (u_output y))
        -> (uid (u_output x) = uid z)                                     
        -> iso_status (u_status x) = not_isolated
        -> miscomparing_many_check l mis_flt_lmt z = true
        -> y.(u_status).(miscomp_status) = miscomparing .
Proof.  
  intros l mis_flt_lmt new  x Hxin y Hyin z Hzinl Huidxy Huidxz Hiso Hmischeck.
  unfold new in Hyin.
  unfold build_updated_u_data_lst in Hyin.  
  unfold update_u_data_frm_comb_elmnt_for_map in Hyin.
  unfold combine_lists in Hyin.

  pose proof (noDup_uids_of_non_iso_good_lst
                pf_uids pf_input pf_ud_lst ) as NDuidl.
  assert (  In (uid z) (dev_uid_lst pf_uids pf_input pf_ud_lst)  ) as HzinD. {
    apply in_map_iff.
    exists z.
    split ; trivial.
    apply filter_In.
    split; trivial.
  }
  
  apply in_map_iff in Hyin.
  inversion Hyin as [zx [Ha Hb]].
  pose proof ( proj2_sig
              (update_u_data_frm_comb_elmnt (dev_uid_lst pf_uids pf_input pf_ud_lst)
                 (maybe_uid_lst pf_uids pf_input pf_ud_lst) zx))
    as [Hb1 [Hb2 [Hb3 [Hb4 Hb5]]]].
  pose proof (combine_lists_gen_props pf_uids pf_input pf_ud_lst zx)
    as [[Hzxuid [Hzxinput Hzxud_lst]] T].
  exact Hb.
  clear T.
  rewrite Ha in *.
  rewrite <- Hb2 in *.
  
  assert (x = snd zx ) as Hxeqx. {
    rewrite Hzxuid in Huidxy.
    exact (fun_out_same_means_same_element_of_lst
             x Huidxy Hxin Hzxud_lst  (mapped_list_nodup pf_ud_lst pf_uids)).
  }
  rewrite <- Hxeqx in Hb5.
  rewrite Huidxy in Huidxz.
  rewrite Huidxz in Hb5.
  pose proof (Hb5 Hiso) as [Hmis1 [Hmis2 [Hmb1 Hmb2]]].
  assert ( ~ In (uid z) (maybe_uid_lst pf_uids pf_input pf_ud_lst)  ) as HzninM. {
    apply in_map_iff in HzinD.
    inversion HzinD as [z0 [Huidz0eqz Hz0inM]].
    assert ( In z0 l) as Hz0inl. {
      apply filter_In in Hz0inM.
      inversion Hz0inM. trivial.
    }
    assert (z0 = z ) as Hz0eqz by
        exact (fun_out_same_means_same_element_of_lst z0 Huidz0eqz Hz0inl Hzinl NDuidl).
    pose proof (miscomparing_mayb_and_not_lists_are_disjoint
                  pf_uids pf_input pf_ud_lst z Hzinl) as [[HzinMprop T2][[T5 T6][T1 T3]]].
    clear T1 T2 T3 T5 T6.
    rewrite Hz0eqz in Hz0inM.
    pose proof (HzinMprop Hz0inM) as [T HzninMb].
    clear T HzinMprop  Huidz0eqz Hz0inl Hz0inM Hz0eqz z0.
    intro HzinMb.
    apply in_map_iff in HzinMb.
    inversion HzinMb as [z0 [Huidz0eqz Hz0inM]].
    assert ( In z0 l) as Hz0inl. {
      apply filter_In in Hz0inM. 
      inversion Hz0inM as [Hz0infM T].
      apply filter_In in Hz0infM.
      inversion Hz0infM as [Hz0inl].
      trivial.
    }
    assert (z0 = z ) as Hz0eqz by
        exact (fun_out_same_means_same_element_of_lst z0 Huidz0eqz Hz0inl Hzinl NDuidl).
    rewrite Hz0eqz in Hz0inM.
    contradiction.
  }
  assert ( hw_hlth (reading (u_output y)) = good ) as Hgd. {
    apply filter_In in Hzinl.
    rewrite in_map_iff in Hzinl.
    inversion Hzinl as [[zx0 [Hfxeqz Hzx0inNiso]] Hzgdprop].
    apply filter_In in Hzx0inNiso.
    
    assert (u_output y = z ) as Heqzyout. {
      assert ( In z input ) as HzinIP. {
        inversion Hzx0inNiso as [Hzx0inCl].
        pose proof (combine_lists_gen_props pf_uids pf_input pf_ud_lst zx0) as [Hcl1].
        pose proof (Hcl1 Hzx0inCl) as [Huidfszx0 [HzinIP Hx0inQ]].
        rewrite <- Hfxeqz.
        trivial.
      }
      exact (fun_out_same_means_same_element_of_lst (u_output y) Huidxz Hzxinput HzinIP 
               (mapped_list_nodup pf_input pf_uids)).
    }
    rewrite Heqzyout.
    unfold hw_good_unit_check in Hzgdprop.
    destruct (hw_hlth (reading z)).
    inversion Hzgdprop.
    trivial.
  }
  exact (Hmis2 HzinD HzninM Hgd).
    
Qed.

Lemma build_updated_u_data_lst_holds_agreeing_check_true_case
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  :
  let mis_lst          := proj1_sig (miscomparing_lst pf_uids pf_input pf_ud_lst) in
  let mis_flt_lmt      := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
  let rem_mis_flt_lmt  := mis_flt_lmt - length ( mis_lst ) in
  let gd_non_iso_lst   := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
  let negb_mis_lst     := filter
                             (fun y =>
                                negb (miscomparing_many_check  gd_non_iso_lst mis_flt_lmt y ) )
                             gd_non_iso_lst in 
  let new := build_updated_u_data_lst  pf_uids  pf_input pf_ud_lst in
  forall x,
    In x ud_lst
    -> forall y,
      In y new
      ->  forall z,
        In z negb_mis_lst                                               
        -> (uid (u_output x) = uid (u_output y))
        -> (uid (u_output x) = uid z)                                     
        -> iso_status (u_status x) = not_isolated
        -> agreeing_many_check negb_mis_lst rem_mis_flt_lmt z = true
        -> y.(u_status).(miscomp_status) = not_miscomparing .
Proof.  
  intros mis_lst mis_flt_lmt rem_mis_flt_lmt
    l l' new x Hxin y Hyin z Hzinl' Huidxy Huidxz Hiso Hagrcheck.
  unfold new in Hyin.
  unfold build_updated_u_data_lst in Hyin.  
  unfold update_u_data_frm_comb_elmnt_for_map in Hyin.
  unfold combine_lists in Hyin.

  pose proof (noDup_uids_of_non_iso_good_lst
                pf_uids pf_input pf_ud_lst ) as NDuidl.
  assert ( In z l ) as Hzinl. {
    apply filter_In in Hzinl'.
    inversion Hzinl'. trivial.
  }


    assert (  ~ In (uid z) (dev_uid_lst pf_uids pf_input pf_ud_lst)  ) as HzninD. {
    intro HzninD.
    unfold dev_uid_lst in HzninD.
    apply in_map_iff in HzninD.
    inversion HzninD as [t [Htuid Htin]].
    clear HzninD.
    assert (t = z). {
      apply filter_In in Htin.
      inversion Htin as [Htinl].
      exact (fun_out_same_means_same_element_of_lst
               t Htuid Htinl Hzinl NDuidl ).
    }
    rewrite H in Htin.
    assert (~ In z (proj1_sig (miscomparing_lst pf_uids pf_input pf_ud_lst)) ) as HzninM.
    {    apply filter_In in Hzinl'.
         inversion Hzinl'.
         intros HzinM.
         apply filter_In in HzinM.
         inversion HzinM.
         fold l in H3.
         unfold mis_flt_lmt, flt_lmt_among_good in H1.
         rewrite H3 in H1.
         inversion H1.
    }
    contradiction.
  }
  assert ( ~ In (uid z) (maybe_uid_lst pf_uids pf_input pf_ud_lst) ) as HzninMb. {
    intro HzninuidMb.
    unfold dev_uid_lst in HzninuidMb.
    apply in_map_iff in HzninuidMb.
    inversion HzninuidMb as [t [Htuid Htin]].
    clear HzninuidMb.
    assert (t = z). {
      apply filter_In in Htin. 
      inversion Htin as [HtinNm].
      apply filter_In in HtinNm. 
      inversion HtinNm as [Htinl].
      
      exact (fun_out_same_means_same_element_of_lst
               t Htuid Htinl Hzinl NDuidl ).
    }
    assert (~ In t (proj1_sig (maybe_miscomparing_lst pf_uids pf_input pf_ud_lst)))
      as HzninMb. {
      intro HzinMb.
      apply filter_In in HzinMb.
      inversion HzinMb.
      clear HzinMb H0.
      unfold rem_mis_flt_lmt in Hagrcheck.
      fold mis_flt_lmt in H1.
      unfold mis_lst in Hagrcheck.
      unfold l', l in Hagrcheck.
      rewrite H in H1.
      fold l in H1, Hagrcheck.
      fold l' in H1, Hagrcheck.
      clear Htin.
      remember (length (proj1_sig (miscomparing_lst pf_uids pf_input pf_ud_lst))).
      apply negb_true_iff in H1.
      assert ( true = false ). {
        rewrite <- Hagrcheck.
        trivial.
      }
      inversion H0.
    }
    contradiction.
  }
  
  apply in_map_iff in Hyin.
  inversion Hyin as [zx [Ha Hb]].
  pose proof ( proj2_sig
              (update_u_data_frm_comb_elmnt (dev_uid_lst pf_uids pf_input pf_ud_lst)
                 (maybe_uid_lst pf_uids pf_input pf_ud_lst) zx))
    as [Hb1 [Hb2 [Hb3 [Hb4 Hb5]]]].
  pose proof (combine_lists_gen_props pf_uids pf_input pf_ud_lst zx)
    as [[Hzxuid [Hzxinput Hzxud_lst]] T].
  exact Hb.
  clear T.
  rewrite Ha in *.
  rewrite <- Hb2 in *.
  
  assert (x = snd zx ) as Hxeqx. {
    rewrite Hzxuid in Huidxy.
    exact (fun_out_same_means_same_element_of_lst
             x Huidxy Hxin Hzxud_lst  (mapped_list_nodup pf_ud_lst pf_uids)).
  }
  rewrite <- Hxeqx in Hb5.
  rewrite Huidxy in Huidxz.
  rewrite Huidxz in Hb5.
  pose proof (Hb5 Hiso) as [Hmis1 [Hmis2 [Hmb1 Hmb2]]].
  destruct (miscomp_status (u_status y)).
  - assert (miscomparing = miscomparing) as Ht by trivial.
    pose proof (Hmis1 Ht) as [Hgd Hind].
    contradiction.
  - trivial.
  - assert (maybe_miscomparing = maybe_miscomparing) as Ht by trivial.
    pose proof (Hmb1 Ht) as [Hgd Hind].
    contradiction.
    
Qed.

