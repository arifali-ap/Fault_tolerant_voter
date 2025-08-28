Require Import List.
Import ListNotations. 
Require Import Lia.
Require Import Nat.
Import Arith.
Require Import Lists.ListDec.
Require Import List Decidable.

Require Import BTProject.config.
Require Import BTProject.voter_state.
Require Import BTProject.library_using_list.
Require Import BTProject.gen_lemmas.
Require Import BTProject.combine.

Require Import Coq.Logic.FunctionalExtensionality.



Definition flt_lmt_among_good
  { u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  ) :=

  simul_max_fault - (num_of_bad_and_non_isolated pf_uids pf_input pf_ud_lst).
 
  


Definition miscomparing_lst
  { u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  ) :
  
  let l := all_good_non_iso_lst pf_uids pf_input pf_ud_lst in
  let mis_flt_lmt := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
  { ml : list unit_output | forall x, In x ml -> ( In x (proj1_sig l)) /\ miscomparing_many_prop  (proj1_sig l) mis_flt_lmt x }.


  refine (
      let l := all_good_non_iso_lst pf_uids pf_input pf_ud_lst in
      let mis_flt_lmt := simul_max_fault -  num_of_bad_and_non_isolated  pf_uids pf_input pf_ud_lst in
      let projl := proj1_sig l in
      exist _ (filter (fun y =>miscomparing_many_check  projl mis_flt_lmt y ) projl) _
    ).
  
 -  intros.  apply filter_In in H. 
   unfold miscomparing_many_check in H.
   rewrite Nat.ltb_lt in H.
   unfold miscomparing_many_prop.
   trivial.
Defined.





Lemma miscomparing_lst_deviates_frm_grnd_truth
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  
  :
  let  l := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
  let mis_flt_lmt := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
   length (dlta_dev_lst_grnd_truth l ) <= mis_flt_lmt ->
 
  let mis_list := proj1_sig (miscomparing_lst pf_uids pf_input pf_ud_lst) in
  forall x, In x (mis_list) -> adiff ground_truth (val (reading x) ) > delta .

  intros l Hm Hf mis_list x H.
  remember (proj2_sig (miscomparing_lst pf_uids pf_input pf_ud_lst)).
  pose proof ( a  x H ).  
  inversion H0. 
  remember  (dlta_dev_lst_grnd_truth l)
    as dev_dlta_grnd_truth_lst.

  remember (devn_lst_single_unit l x) as dev_2delta_x_lst.

  assert (length dev_dlta_grnd_truth_lst < length dev_2delta_x_lst ). {
    unfold miscomparing_many_prop in H2.
    unfold l in Heqdev_2delta_x_lst.
    rewrite <- Heqdev_2delta_x_lst in H2.
    lia.
  } 
  assert ( NoDup l ) by  exact (noDup_non_iso_good_lst pf_uids pf_input pf_ud_lst).
  assert (~  incl dev_2delta_x_lst dev_dlta_grnd_truth_lst ).
  {
    unfold dlta_dev_lst_grnd_truth in *.
    unfold devn_lst_single_unit in *.
    rewrite  Heqdev_dlta_grnd_truth_lst in *.
    rewrite Heqdev_2delta_x_lst in *.

    exact (filter_length_dffrnt_means_extra_element
                  (fun y : unit_output => grnd_truth_dlta_dev_check y)
                  (fun y : unit_output => unit_deviation_check  x y)
                  H4 H3).
  } 
  rewrite incl_Forall_in_iff in H5.
  apply neg_Forall_Exists_neg in H5.
  apply Exists_exists in H5.
  inversion H5 as [y [Yin Ynin]].
  rewrite Heqdev_2delta_x_lst in Yin.
  apply filter_In in Yin.
  inversion Yin.
  unfold unit_deviation_check in H7.
  apply Nat.ltb_lt in H7.
  rewrite  Heqdev_dlta_grnd_truth_lst in Ynin.
  unfold dlta_dev_lst_grnd_truth in Ynin.
  rewrite filter_In in Ynin.
  apply not_and in Ynin.
  inversion Ynin.
  contradiction.
  unfold grnd_truth_dlta_dev_check in H8.
  apply Bool.not_true_is_false in H8.
  apply Nat.ltb_ge in H8.
  apply not_le.
  intro.
  assert (adiff ground_truth (val (reading x)) <= delta
          /\ adiff ground_truth (val (reading y)) <= delta ).
  split; trivial.
  pose proof (triangular_ineq
                (val (reading x))
                (val (reading y))
                ground_truth
                delta
                delta
                H10).

  apply Nat.lt_nge in H7.
  unfold unit_adiff in H7.
  unfold threshold in H7.
  assert (adiff (val (reading x)) (val (reading y)) <= 2*delta) by lia. 
  contradiction.
  exact ( In_decidable unit_output_decidable y l).
  intros.
  exact ( in_dec unit_output_eq_dec x0  dev_dlta_grnd_truth_lst).
Qed.  






Lemma deviation_3delta_frm_grnd_truth_is_in_mis_list
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  
  :
  let  l := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
  let mis_flt_lmt := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
  length (dlta_dev_lst_grnd_truth l ) <= mis_flt_lmt ->
  length l > 2 * mis_flt_lmt ->
 
  let mis_list := proj1_sig (miscomparing_lst pf_uids pf_input pf_ud_lst) in
  forall x, In x l
       -> adiff ground_truth (val (reading x) ) > 3*delta
       -> In x (mis_list).
  
  intros l mis_flt_lmt H H0 mis_list x Hin H1.
  remember (filter (fun y=> negb (grnd_truth_dlta_dev_check y)) l).
  assert ( forall y, In y l0
                     -> (unit_adiff x y) > 2 * delta ).
  { intros.
    rewrite Heql0 in H2.
    apply filter_In in H2.
    inversion H2.
    unfold grnd_truth_dlta_dev_check in H4.
    unfold negb in H4.
    destruct (delta <? adiff ground_truth (val (reading y)) ) eqn:H4d.
    inversion H4.
    apply Nat.ltb_ge in H4d.
    apply not_le.
    intro.
    assert (adiff ground_truth (val (reading x)) <= 3 * delta).
    {
      unfold unit_adiff in H5.
      rewrite adiff_reflex in H4d, H5.
      assert (adiff (val (reading y)) ground_truth <= delta /\
                adiff (val (reading y)) (val (reading x)) <= 2 * delta ). { split; trivial. }
      pose proof (triangular_ineq ground_truth (val (reading x)) (val (reading y))
                    delta
                    (2*delta)
                    H6).
    
      lia.
    }
    
    apply Nat.le_ngt in H6.
    contradiction.
  } 
   
  unfold mis_list.
  unfold miscomparing_lst.
  unfold combine_lists.
  apply filter_In.
  split.
  trivial. 
  unfold miscomparing_many_check.
  apply Nat.ltb_lt.
  fold l.
  assert (length (l0 ) > mis_flt_lmt ). {
    pose proof (filter_length_is_length_minus_remaining l grnd_truth_dlta_dev_check).
    rewrite Heql0.
    unfold dlta_dev_lst_grnd_truth in H.
    lia.
  }
  
  assert (incl l0 (devn_lst_single_unit l x) ). {
    unfold incl.
    intros.
    unfold devn_lst_single_unit. 
    apply filter_In. 
    split.
    rewrite Heql0 in H4.
    apply filter_In in H4.
    inversion H4.
    trivial.
    pose proof (H2 a H4).
    unfold unit_deviation_check.
    apply Nat.ltb_lt.
    unfold threshold. trivial.
  }
  assert ( length l0 <= length (devn_lst_single_unit l x) ). {
    rewrite Heql0 .
    rewrite Heql0 in H4.
    unfold devn_lst_single_unit in *.
    exact (filter_sublist_length_at_most_list_length
                (fun y : unit_output => negb (grnd_truth_dlta_dev_check y))
                (fun y : unit_output => unit_deviation_check x y)
                (noDup_non_iso_good_lst pf_uids pf_input pf_ud_lst) H4 ).
  } 
  unfold mis_flt_lmt in H3.
  unfold flt_lmt_among_good in H3.
  lia.
Qed.





Lemma len_mis_lst_le_mis_flt_lmt
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  
  :
  let  l := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
  let mis_flt_lmt := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
  length (dlta_dev_lst_grnd_truth l ) <= mis_flt_lmt ->
  
  let mis_list := proj1_sig (miscomparing_lst pf_uids pf_input pf_ud_lst) in
  length (mis_list) <= mis_flt_lmt.
Proof.
  intros.
  apply not_gt.
  intro.
  pose proof (miscomparing_lst_deviates_frm_grnd_truth
                pf_uids pf_input pf_ud_lst H).
  assert ( incl
               (proj1_sig (miscomparing_lst pf_uids pf_input pf_ud_lst))
               (filter ( fun x => (delta <? adiff ground_truth (val (reading x)))) l) ).
  {
    unfold incl.
    intros.
    apply filter_In.
    remember (proj2_sig (miscomparing_lst pf_uids pf_input pf_ud_lst ) ).      
    simpl in a0.
    pose proof ( a0 a H2).
    inversion H3.
    split. trivial.
    apply Nat.ltb_lt.
    pose proof ( H1 a H2).
    lia.
  }
  assert ( NoDup l ) by  exact (noDup_non_iso_good_lst pf_uids pf_input pf_ud_lst).
   
  assert ((proj1_sig (miscomparing_lst pf_uids pf_input pf_ud_lst))
          = filter (fun x : unit_output => miscomparing_many_check l mis_flt_lmt x) l ) by trivial.
  
  rewrite H4 in H2.
  pose proof (  filter_sublist_length_at_most_list_length
                    ( fun x => miscomparing_many_check l mis_flt_lmt x)
                    (fun x =>  (delta <? adiff ground_truth (val (reading x))) )
                    H3 H2
      ).
    unfold dlta_dev_lst_grnd_truth in H.
    unfold grnd_truth_dlta_dev_check in H.
    assert (length (filter (fun x : unit_output => miscomparing_many_check l mis_flt_lmt x) l) <= mis_flt_lmt ) by lia.
    apply Nat.le_ngt in H6.
    assert (mis_flt_lmt <
              length (filter (fun x : unit_output => miscomparing_many_check l mis_flt_lmt x) l) ). 
    rewrite <- H4.
    unfold mis_list in H0.
    trivial.
    contradiction.
Qed.  










Definition maybe_miscomparing_lst
  { u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  ) :
  
  let mis_lst          := proj1_sig (miscomparing_lst pf_uids pf_input pf_ud_lst) in
  let mis_flt_lmt      := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
  let rem_mis_flt_lmt  := mis_flt_lmt - length ( mis_lst ) in
  let gd_non_iso_lst   := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
  let negb_mis_lst     := filter
                             (fun y =>
                                negb (miscomparing_many_check  gd_non_iso_lst mis_flt_lmt y ) )
                             gd_non_iso_lst in
  { mayb_l : list unit_output |
    Forall (fun x =>  ( ~ In x (mis_lst) )/\ ( In x (gd_non_iso_lst))
                  /\ rem_mis_flt_lmt >= length (agrng_lst_single_unit negb_mis_lst x)) mayb_l }.

  refine (
      let mis_lst          := proj1_sig (miscomparing_lst pf_uids pf_input pf_ud_lst) in
      let mis_flt_lmt      := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
      let rem_mis_flt_lmt  := mis_flt_lmt - length ( mis_lst ) in
      let gd_non_iso_lst   := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
      let negb_mis_lst     := filter
                                (fun y =>
                                   negb (miscomparing_many_check
                                            gd_non_iso_lst mis_flt_lmt y ) )
                                gd_non_iso_lst in
      exist _ (filter (fun y => negb (agreeing_many_check
                                      negb_mis_lst rem_mis_flt_lmt y )) negb_mis_lst) _
    ).
  
 -  apply Forall_forall. intros. apply filter_In in H.
    unfold agreeing_many_check in H.
    inversion H.
    unfold negb_mis_lst in H0.
    apply filter_In in H0.
    inversion H0.
    repeat split. 
    --
      unfold miscomparing_lst.
      simpl.
      rewrite filter_In.
      intro.
      inversion H4.
      apply Bool.negb_true_iff in H3.
      clear H4 H5.
      unfold gd_non_iso_lst, all_good_non_iso_lst in H3.
      simpl in H3.
      unfold mis_flt_lmt in H3.
      simpl in H3.
      unfold flt_lmt_among_good in H3.
      simpl in H3. 
      rewrite H6 in H3.
      inversion H3.
    -- trivial.
    --      
      inversion H.
      apply Bool.negb_true_iff in H1.
      apply (leb_complete_conv ) in H1.
      unfold rem_mis_flt_lmt, mis_lst, negb_mis_lst, gd_non_iso_lst, mis_flt_lmt in H1.
      lia.
Defined.


Lemma helpler1 {lmt l a a': nat }
  ( pf1:  l > 2 * lmt )
  ( pf2:  a <= lmt )
  ( pf3:  a' = l - a)
  : a' > lmt.
  rewrite pf3.
  lia.
Qed.
Lemma helpler2 {lmt l a b c m: nat }
  ( pf0: l > 2 * lmt )
  ( pf1:  b = l - m )
  ( pf2:   lmt - m >= a )
  ( pf3:  c = b - a)
  ( pf4:  m <= lmt )
  : c > lmt.
  rewrite pf3. 
  lia.
Qed.



Definition not_miscomparing_lst
  { u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  ) :
  
  let mis_lst          := proj1_sig (miscomparing_lst pf_uids pf_input pf_ud_lst) in
  let mis_flt_lmt      := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
  let rem_mis_flt_lmt  := mis_flt_lmt - length ( mis_lst ) in
  let gd_non_iso_lst   := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
  let negb_mis_lst     := filter
                             (fun y =>
                                negb (miscomparing_many_check  gd_non_iso_lst mis_flt_lmt y ) )
                             gd_non_iso_lst in
  { mayb_l : list unit_output |
    Forall (fun x =>  ( ~ In x (mis_lst) )/\ ( In x (gd_non_iso_lst))
                  /\ rem_mis_flt_lmt < length (agrng_lst_single_unit negb_mis_lst x)) mayb_l }.

  refine (
      let mis_lst          := proj1_sig (miscomparing_lst pf_uids pf_input pf_ud_lst) in
      let mis_flt_lmt      := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
      let rem_mis_flt_lmt  := mis_flt_lmt - length ( mis_lst ) in
      let gd_non_iso_lst   := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
      let negb_mis_lst     := filter
                                (fun y =>
                                   negb (miscomparing_many_check
                                            gd_non_iso_lst mis_flt_lmt y ) )
                                gd_non_iso_lst in
      exist _ (filter (fun y => (agreeing_many_check
                                      negb_mis_lst rem_mis_flt_lmt y )) negb_mis_lst) _
    ).
  
 -  apply Forall_forall. intros. apply filter_In in H.
    unfold agreeing_many_check in H.
    inversion H.
    unfold negb_mis_lst in H0.
    apply filter_In in H0.
    inversion H0.
    repeat split. 
    --
      unfold miscomparing_lst.
      simpl.
      rewrite filter_In.
      intro.
      inversion H4.
      apply Bool.negb_true_iff in H3.
      clear H4 H5.
      unfold gd_non_iso_lst, all_good_non_iso_lst in H3.
      simpl in H3.
      unfold mis_flt_lmt in H3.
      simpl in H3.
      unfold flt_lmt_among_good in H3.
      simpl in H3. 
      rewrite H6 in H3.
      inversion H3.
    -- trivial.
    --      
      inversion H.
      apply leb_complete in H5.
      unfold rem_mis_flt_lmt, mis_lst, negb_mis_lst, gd_non_iso_lst, mis_flt_lmt in H5.
      lia.
Defined.


Lemma miscomparing_mayb_and_not_lists_are_disjoint
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  :
  let gd_non_iso  := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
  let mis_lst     := proj1_sig (miscomparing_lst pf_uids pf_input pf_ud_lst) in
  let mayb_lst    := proj1_sig (maybe_miscomparing_lst pf_uids pf_input pf_ud_lst) in
  let not_lst     := proj1_sig (not_miscomparing_lst pf_uids pf_input pf_ud_lst) in
  let mis_flt_lmt := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
  (*length (dlta_dev_lst_grnd_truth gd_non_iso) <= mis_flt_lmt
  -> *)
  forall x,
      In x gd_non_iso ->
      ( In x mis_lst <->   ~In x not_lst /\ ~In x mayb_lst)
      /\  ( In x mayb_lst <-> ~In x mis_lst /\ ~In x not_lst)
      /\  ( In x not_lst <-> ~In x mayb_lst /\ ~In x mis_lst).
Proof.
  intros gd_non_iso mis_lst mayb_lst not_lst mis_flt_lmt x Hxingd.
  unfold mis_lst,  mayb_lst, not_lst.
  assert ( decidable ( In x gd_non_iso)) as Din
      by exact ( In_decidable unit_output_decidable x gd_non_iso).
  assert ( match num_of_bad_and_non_isolated pf_uids pf_input pf_ud_lst with
           | 0 => S simul_max_fault_minus_1
           | S l => simul_max_fault_minus_1 - l
           end =  mis_flt_lmt) as Heqlmt.
  { unfold mis_flt_lmt.
    unfold flt_lmt_among_good.
    trivial.
  }
  remember (filter (fun y : unit_output => negb (miscomparing_many_check
                                                  gd_non_iso mis_flt_lmt y)) gd_non_iso)
    as l.
  repeat split.   
  - intro Hin.
    pose proof (proj2_sig (not_miscomparing_lst pf_uids pf_input pf_ud_lst)) as Mb_prop.
    rewrite Forall_forall in Mb_prop.
    pose proof (Mb_prop x Hin) as [Hnin].
    contradiction.
  - intro Hin. 
    pose proof (proj2_sig (maybe_miscomparing_lst pf_uids pf_input pf_ud_lst)) as Mb_prop.
    rewrite Forall_forall in Mb_prop.
    pose proof (Mb_prop x Hin) as [Hnin].
    contradiction.

  - intros Hnin.
    inversion Hnin as [HninNt HninMb].
    simpl in *.
    fold gd_non_iso in HninMb, HninNt, Hnin.
    rewrite Heqlmt in *.
    fold mis_flt_lmt in HninMb, HninNt, Hnin.
    fold gd_non_iso.
    rewrite <- Heql in *.
  
    remember (fun y : unit_output =>
                 agreeing_many_check l
                   (mis_flt_lmt -
                    length
                      (filter
                         (fun y0 : unit_output =>
                          miscomparing_many_check gd_non_iso mis_flt_lmt y0) gd_non_iso))
                   y) as f.
    
    pose proof (not_in_filter_and_filter_negb_implies_not_in_l l f Hnin) as Hninl.   
    pose proof (filter_f_negb_f_are_disjoint gd_non_iso
                  (fun y : unit_output =>
                     miscomparing_many_check gd_non_iso mis_flt_lmt y)
                  Din Hxingd ) as [[Hin1 Hnin1] [Hnin2 Hin2]].
    rewrite Heql in Hninl.
    exact (Hnin1 Hninl).
    
    
  - intro.
    pose proof (proj2_sig (maybe_miscomparing_lst pf_uids pf_input pf_ud_lst)) as Mb_prop.
    rewrite Forall_forall in Mb_prop.
    pose proof (Mb_prop x H) as [Hnin].
    contradiction.
  - intro.
    pose proof (proj2_sig (maybe_miscomparing_lst pf_uids pf_input pf_ud_lst)) as Mb_prop.
    pose proof (proj2_sig (not_miscomparing_lst pf_uids pf_input pf_ud_lst)) as Nt_prop.
    rewrite Forall_forall in Mb_prop, Nt_prop.
    pose proof (Mb_prop x H) as [T[T2 Agr]].
    pose proof (Nt_prop x H0) as [T3[T4 Nagr]].
    apply Nat.lt_nge in Nagr.
    contradiction.
  - intro Hnin. 
    inversion Hnin as [HninM HninNt].
    clear Hnin.
    simpl in *.
    fold gd_non_iso in HninNt, HninM.
    fold mis_flt_lmt in HninNt, HninM.
    rewrite Heqlmt in *.
    fold gd_non_iso. fold mis_flt_lmt.
    rewrite <- Heql in *.
    pose proof (filter_f_negb_f_are_disjoint gd_non_iso
                  (fun y : unit_output =>
                     miscomparing_many_check gd_non_iso mis_flt_lmt y)
                  ( In_decidable unit_output_decidable x gd_non_iso)
                  Hxingd ) as [[Hin1 Hnin1] [Hnin2 Hin2]].
    rewrite <- Heql in *.
    pose proof (Hnin2 HninM) as Hxinl.
    clear Hin1 Hin2 Hnin1 Hnin2 HninM.
     
    remember (fun y : unit_output =>
                 agreeing_many_check l
                   (mis_flt_lmt -
                    length
                      (filter
                         (fun y0 : unit_output =>
                          miscomparing_many_check gd_non_iso mis_flt_lmt y0) gd_non_iso))
                   y) as f.
    pose proof (filter_f_negb_f_are_disjoint l
                  f ( In_decidable unit_output_decidable x l)
                  Hxinl ) as [[Hin1 Hnin1] [Hnin2 Hin2]].
    exact (Hnin2 HninNt).
    
  - intro.
    pose proof (proj2_sig (maybe_miscomparing_lst pf_uids pf_input pf_ud_lst)) as Mb_prop.
    pose proof (proj2_sig (not_miscomparing_lst pf_uids pf_input pf_ud_lst)) as Nt_prop.
    rewrite Forall_forall in Mb_prop, Nt_prop.
    pose proof (Mb_prop x H0) as [T[T2 Agr]].
    pose proof (Nt_prop x H) as [T3[T4 Nagr]].
    apply Nat.lt_nge in Nagr.
    contradiction.
  - intro.
    pose proof (proj2_sig (not_miscomparing_lst pf_uids pf_input pf_ud_lst)) as Mb_prop.
    rewrite Forall_forall in Mb_prop.
    pose proof (Mb_prop x H) as [Hnin].
    contradiction.
  - intro Hnin.  
    inversion Hnin as [HninMb HninM].
    clear Hnin.
    simpl in *.
    fold gd_non_iso in HninMb, HninM.
    fold mis_flt_lmt in HninMb, HninM.
    rewrite Heqlmt in *.
    fold gd_non_iso. fold mis_flt_lmt.
    rewrite <- Heql in *.
    pose proof (filter_f_negb_f_are_disjoint gd_non_iso
                  (fun y : unit_output =>
                     miscomparing_many_check gd_non_iso mis_flt_lmt y)
                  ( In_decidable unit_output_decidable x gd_non_iso)
                  Hxingd ) as [[Hin1 Hnin1] [Hnin2 Hin2]].
    rewrite <- Heql in *.
    pose proof (Hnin2 HninM) as Hxinl.
    clear Hin1 Hin2 Hnin1 Hnin2 HninM.
     
    remember (fun y : unit_output =>
                 agreeing_many_check l
                   (mis_flt_lmt -
                    length
                      (filter
                         (fun y0 : unit_output =>
                          miscomparing_many_check gd_non_iso mis_flt_lmt y0) gd_non_iso))
                   y) as f.
    pose proof (filter_f_negb_f_are_disjoint l
                  f ( In_decidable unit_output_decidable x l)
                  Hxinl ) as [[Hin1 Hnin1] [Hnin2 Hin2]].
    exact (Hnin1 HninMb).
Qed.
    
Lemma deviation_3delta_frm_grnd_truth_is_not_in_not_mis_list
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  
  :
  let  l := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
  let mis_flt_lmt := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
  length (dlta_dev_lst_grnd_truth l ) <= mis_flt_lmt ->
 
  let not_mis_lst := proj1_sig (not_miscomparing_lst pf_uids pf_input pf_ud_lst) in
  forall x, In x l
       -> adiff ground_truth (val (reading x) ) > 3*delta
       -> ~ In x (not_mis_lst).
Proof.
  intros.
  
  unfold not_mis_lst.
  remember (proj2_sig (not_miscomparing_lst pf_uids pf_input pf_ud_lst)).
  pose proof f as Notmis_prop.
  clear Heqf f.
  intro.
  rewrite Forall_forall in Notmis_prop.
  pose proof (Notmis_prop x H2).
  inversion H3 as [Hnin [Hinl Xnotmis_prop]].
  clear Notmis_prop H3 Hinl.
  
  remember (agrng_lst_single_unit
                      (filter
                         (fun y : unit_output =>
                          negb
                            (miscomparing_many_check
                               (proj1_sig
                                  (all_good_non_iso_lst pf_uids pf_input pf_ud_lst))
                               (flt_lmt_among_good pf_uids pf_input pf_ud_lst) y))
                         (proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst))) x)
    as agr_lst_x.
  assert ( forall y, In y agr_lst_x ->
                adiff ground_truth (val (reading y)) > delta ).
  {
    intros.
    apply not_ge.
    intro.
    rewrite Heqagr_lst_x in H3.
    unfold agrng_lst_single_unit in H3.
    apply filter_In in H3.
    inversion H3.
    unfold unit_agrmnt_check in H6.
    apply Bool.negb_true_iff in H6.
    unfold unit_deviation_check in H6.
    apply Nat.ltb_ge in H6.
    unfold threshold in H6.
    unfold unit_adiff in H6.
    assert ( adiff ground_truth (val (reading y)) <= delta ) by lia.
    
    assert ( adiff (val (reading y)) ground_truth <= delta /\
               adiff (val (reading y)) (val (reading x)) <= 2 * delta).
    {
      split.
      rewrite (adiff_reflex (val (reading y)) ground_truth).
      trivial.
      rewrite (adiff_reflex (val (reading y)) (val (reading x)) ).
      trivial. }
    pose proof (triangular_ineq
                  ground_truth
                  (val (reading x))
                  (val (reading y))
                  delta
                  (2*delta)
                   H8 ).
    assert ( adiff ground_truth (val (reading x)) <= 3 * delta) by lia.
    apply Arith_base.gt_not_le_stt in H1.
    contradiction.  
  }


  assert ( length agr_lst_x <=
             length (dlta_dev_lst_grnd_truth
                        (filter
                      (fun y : unit_output =>
                       negb
                         (miscomparing_many_check
                            (proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst))
                            (flt_lmt_among_good pf_uids pf_input pf_ud_lst) y))
                      (proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst)))
         ) ).
  {
    assert (incl agr_lst_x
              (dlta_dev_lst_grnd_truth
              (filter
                 (fun y : unit_output =>
                    negb
                      (miscomparing_many_check
                         (proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst))
                         (flt_lmt_among_good pf_uids pf_input pf_ud_lst) y))
                 (proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst)))) ).
    unfold incl.
    intros.
    apply filter_In.
    pose proof H4 as Hin.
    rewrite Heqagr_lst_x in H4.
    unfold agrng_lst_single_unit in H4.
    apply filter_In in H4.
    inversion H4.
    clear H4 H6.
    apply filter_In in H5.
    split.
    - apply filter_In. trivial.
    - pose proof (H3 a Hin).
      unfold grnd_truth_dlta_dev_check.
      apply Nat.ltb_lt.
      lia.
    - assert ( NoDup (filter
          (fun y : unit_output =>
           negb
             (miscomparing_many_check
                (proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst))
                (flt_lmt_among_good pf_uids pf_input pf_ud_lst) y))
          (proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst)))).
      assert ( NoDup l ) by  exact (noDup_non_iso_good_lst pf_uids pf_input pf_ud_lst).
      exact (filter_on_Nodup
               l
               H5
               (fun y : unit_output =>
        negb
          (miscomparing_many_check
             (proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst))
             (flt_lmt_among_good pf_uids pf_input pf_ud_lst) y)) ).
      rewrite Heqagr_lst_x in *. 
      unfold agrng_lst_single_unit in *.
      unfold dlta_dev_lst_grnd_truth in *.
      exact (filter_sublist_length_at_most_list_length
               (fun y : unit_output => unit_agrmnt_check x y)
               (fun y : unit_output => grnd_truth_dlta_dev_check y)
               H5
               H4 ).
  }

  unfold dlta_dev_lst_grnd_truth in *.
  rewrite (filter_commutative (proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst))
             (fun y : unit_output => grnd_truth_dlta_dev_check y)
             (fun y : unit_output =>
                negb
                  (miscomparing_many_check
                     (proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst))
                     (flt_lmt_among_good pf_uids pf_input pf_ud_lst) y)) ) in H4.
  fold l in H4.
  pose proof (filter_length
                (miscomparing_many_check l
                   (flt_lmt_among_good pf_uids pf_input pf_ud_lst)  )
                (filter (fun y : unit_output => grnd_truth_dlta_dev_check y) l) ).
  assert (filter
            (miscomparing_many_check l (flt_lmt_among_good pf_uids pf_input pf_ud_lst))
            (filter (fun y : unit_output => grnd_truth_dlta_dev_check y) l)
            = filter
            (miscomparing_many_check l (flt_lmt_among_good pf_uids pf_input pf_ud_lst))
            l).
  {  rewrite <- (filter_commutative l
             (fun y : unit_output => grnd_truth_dlta_dev_check y)
             (miscomparing_many_check l (flt_lmt_among_good pf_uids pf_input pf_ud_lst)) ).
     pose proof ( miscomparing_lst_deviates_frm_grnd_truth
                    pf_uids pf_input pf_ud_lst H).
     unfold grnd_truth_dlta_dev_check in *.
     assert (let mis_list := proj1_sig (miscomparing_lst pf_uids pf_input pf_ud_lst) in
       forall x : unit_output,
         In x mis_list -> delta <? adiff ground_truth (val (reading x)) = true ).
     { intros.
       pose proof (H6 x0 H7).
       apply Nat.ltb_lt.
       lia.
     }
     
     pose proof  (forall_f_true_means_filter_fl_eq_l
                    (proj1_sig (miscomparing_lst pf_uids pf_input pf_ud_lst))
                    (fun y : unit_output => delta <? adiff ground_truth (val (reading y)))
                    H7).
     unfold miscomparing_lst in H8.
     fold l in H8.
     simpl in H8.
     unfold flt_lmt_among_good.
     simpl.
     trivial.
  }
  
  assert (  length (filter (fun y : unit_output => grnd_truth_dlta_dev_check y) l) >
              mis_flt_lmt ).
  { rewrite H6 in H5.
    pose proof (Nat.lt_le_trans
                  (flt_lmt_among_good pf_uids pf_input pf_ud_lst -
                     length (proj1_sig (miscomparing_lst pf_uids pf_input pf_ud_lst)) )
                  (length agr_lst_x )
                  (length
         (filter
            (fun y : unit_output =>
             negb
               (miscomparing_many_check l (flt_lmt_among_good pf_uids pf_input pf_ud_lst)
                  y)) (filter (fun y : unit_output => grnd_truth_dlta_dev_check y) l)) )
                  Xnotmis_prop
                  H4 ).
    assert (proj1_sig (miscomparing_lst pf_uids pf_input pf_ud_lst)
                      = filter (miscomparing_many_check l (flt_lmt_among_good pf_uids pf_input pf_ud_lst))
                          l ). {
          
    unfold miscomparing_lst.
    fold l.
    simpl.
    unfold flt_lmt_among_good .
    simpl.
    trivial.
    }
    rewrite <- H8 in H5.
    lia.
  }
  
  apply Nat.le_ngt in H.
  contradiction.
Qed.



Lemma in_not_mis_list_means_at_most_3delta_deviation
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  
  :
  let  l := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
  let mis_flt_lmt := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
  length (dlta_dev_lst_grnd_truth l ) <= mis_flt_lmt ->
 
  let not_mis_lst := proj1_sig (not_miscomparing_lst pf_uids pf_input pf_ud_lst) in
  forall x, In x (not_mis_lst)
       -> adiff ground_truth (val (reading x) ) <= 3*delta .
Proof.
  intros.
  assert (In x l). {
    unfold not_mis_lst in *.
    unfold not_miscomparing_lst in *.
    apply filter_In in H0.
    inversion H0 as [HinNM].
    apply filter_In in HinNM.
    inversion HinNM. trivial.
  }  
pose proof (deviation_3delta_frm_grnd_truth_is_not_in_not_mis_list
              pf_uids pf_input pf_ud_lst
              H
              x H1).  
apply not_gt. 
intro.
pose proof (H2 H3).
unfold not_mis_lst in H1.
contradiction.
Qed.
 


Lemma atmost_delta_frm_grnd_truth_is_not_miscomparing
  {u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  
  :
  let  l := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
  let mis_flt_lmt := flt_lmt_among_good pf_uids pf_input pf_ud_lst in
  length (dlta_dev_lst_grnd_truth l ) <= mis_flt_lmt
  -> length l > 2*mis_flt_lmt 
 
  -> let not_mis_lst := proj1_sig (not_miscomparing_lst pf_uids pf_input pf_ud_lst) in
    forall x, In x l
         -> adiff ground_truth (val (reading x) ) <= delta
         -> In x (not_mis_lst).
Proof. 
  intros.
  unfold not_mis_lst.

  unfold dlta_dev_lst_grnd_truth in H.
  assert (length (filter (fun y : unit_output => grnd_truth_dlta_dev_check y) l)
          + length (filter (fun y : unit_output => negb( grnd_truth_dlta_dev_check y)) l)
                   = length l ). {
    pose proof (filter_length
                  (fun y : unit_output => grnd_truth_dlta_dev_check y)
                  l).
    simpl in H3. trivial.
  }


  
  assert (length (filter (fun y : unit_output => negb (grnd_truth_dlta_dev_check y)) l)
          >  mis_flt_lmt ) by lia. 

  remember (filter (fun y : unit_output => negb (grnd_truth_dlta_dev_check y)) l) as negb_grnd_truth_delta_lst.
  assert  (incl negb_grnd_truth_delta_lst (agrng_lst_single_unit l x) ).
  {
    unfold incl.
    intros.
    unfold agrng_lst_single_unit.
    apply filter_In.
    rewrite Heqnegb_grnd_truth_delta_lst in H5.
    apply filter_In in H5.
    inversion H5.
    split; trivial.
    unfold unit_agrmnt_check.
    apply Bool.negb_true_iff in H7.
    unfold grnd_truth_dlta_dev_check in H7.
    apply Nat.ltb_ge in H7.
    unfold unit_agrmnt_check.
    apply Bool.negb_true_iff.
    unfold unit_deviation_check.
    apply Nat.ltb_ge.
    unfold unit_adiff.
    unfold threshold.
    assert (adiff ground_truth (val (reading x)) <= delta /\
              adiff ground_truth (val (reading a)) <= delta ). { split; trivial. } 
    pose proof (triangular_ineq
                  (val (reading x))
                  (val (reading a))
                  ground_truth
                  delta
                  delta
                  H8).
    lia.
  }
 
  
  assert ( NoDup l ) by  exact (noDup_non_iso_good_lst pf_uids pf_input pf_ud_lst).
  unfold agrng_lst_single_unit in H5.
  rewrite Heqnegb_grnd_truth_delta_lst in H5.
  pose proof (filter_sublist_length_at_most_list_length
                (fun y : unit_output =>
                   negb (grnd_truth_dlta_dev_check y))
                (fun y : unit_output => unit_agrmnt_check x y)
                H6
                H5 ).
  assert (length
         (filter
            (fun y : unit_output => unit_agrmnt_check x y) l) > mis_flt_lmt ).
  { rewrite <- Heqnegb_grnd_truth_delta_lst in H7.
    lia.
  }
  
  assert (
      let mis_lst          := proj1_sig (miscomparing_lst pf_uids pf_input pf_ud_lst) in
      let rem_mis_flt_lmt  := mis_flt_lmt - length ( mis_lst ) in
      let negb_mis_lst     := filter
                                (fun y =>
                                   negb (miscomparing_many_check
                                            l mis_flt_lmt y ) )
                                l in
      agreeing_many_check  negb_mis_lst rem_mis_flt_lmt x = true ).
  {
    intros.
    unfold agreeing_many_check.
    apply Nat.ltb_lt. 
    unfold rem_mis_flt_lmt.
    unfold agrng_lst_single_unit.
    unfold negb_mis_lst.
    apply not_ge.
    intro.

    assert ( length (filter (fun y : unit_output => unit_agrmnt_check x y) l)
                    =  ( length
                           (filter (fun y : unit_output => unit_agrmnt_check x y)
                              (filter
                                 (fun y : unit_output => negb (miscomparing_many_check l mis_flt_lmt y))
                                 l)) )
                       +
                         length
                           (filter (fun y : unit_output => unit_agrmnt_check x y)
                              (filter
                                 (fun y : unit_output =>  (miscomparing_many_check l mis_flt_lmt y))
                                 l)) ).
     rewrite filter_commutative.
     remember (length
                 (filter (fun y : unit_output => negb (miscomparing_many_check l mis_flt_lmt y))
                    (filter (fun y : unit_output => unit_agrmnt_check x y) l)) ).
     rewrite filter_commutative.
     rewrite Heqn.
     symmetry.
     pose proof  (filter_length
                (fun y : unit_output =>
        miscomparing_many_check l mis_flt_lmt y)
                (filter (fun y : unit_output => unit_agrmnt_check x y)
                   l) ). 
     lia.
     pose proof (filter_length_le
            (fun y : unit_output => unit_agrmnt_check x y)
            (filter
               (fun y : unit_output =>
                  miscomparing_many_check l mis_flt_lmt y) l) ).
     assert ( mis_lst = (filter
                           (fun y : unit_output =>
                              miscomparing_many_check l mis_flt_lmt y) l) ).
     {
       unfold mis_lst, miscomparing_lst.
       fold l.
       simpl.
       unfold mis_flt_lmt.
       unfold flt_lmt_among_good.
       trivial.
     }
     
     rewrite <- H12 in *.
     assert ( length mis_lst <= mis_flt_lmt ).
     exact ( len_mis_lst_le_mis_flt_lmt
                    pf_uids pf_input pf_ud_lst H).
     assert (length
               (filter
                  (fun y : unit_output => unit_agrmnt_check x y) l) <= mis_flt_lmt ).
     lia.
     apply Nat.le_ngt in H14.
     contradiction.
  }
(*  clear Heqnegb_grnd_truth_delta_lst negb_grnd_truth_delta_lst
                                     H3 H4 H5 H7 H8.  *)
  unfold not_miscomparing_lst. 
  fold l.
  simpl.
  apply filter_In. 
  split.
  2: { trivial. }
    apply filter_In.
  split; trivial. 
  apply Bool.negb_true_iff. 
  unfold miscomparing_many_check.
  apply Nat.ltb_ge.
  unfold devn_lst_single_unit.
  rewrite <- Heqnegb_grnd_truth_delta_lst in H7.  
  assert (length negb_grnd_truth_delta_lst
          >= length l - mis_flt_lmt ) by lia.
  assert (length (filter (fun y : unit_output => unit_agrmnt_check x y) l) >=
            length l - mis_flt_lmt) by lia.
  pose proof ( filter_length
                 (fun y : unit_output => unit_deviation_check x y)
                 l ).
  simpl in H12.
  unfold unit_agrmnt_check in H11.
  lia.  
Qed.
                                       




Lemma more_than_double_max_fault_units_means_zero_maybe
        
  { u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  :
  let gd_non_iso  := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
  let mis_flt_lmt := flt_lmt_among_good pf_uids pf_input pf_ud_lst in 
  length (dlta_dev_lst_grnd_truth gd_non_iso ) <= mis_flt_lmt
  -> length gd_non_iso > 2*mis_flt_lmt
  -> let mayb_list := proj1_sig (maybe_miscomparing_lst pf_uids pf_input pf_ud_lst) in
     mayb_list = nil.
 
  intros.  
  remember (proj2_sig (maybe_miscomparing_lst pf_uids pf_input pf_ud_lst)) as pf_myb.
  inversion pf_myb. 
  - symmetry. trivial.
  - rewrite Forall_forall in H3.
    inversion H2 as [Hnin [Hin Myb_prop]].
    assert ( miscomparing_many_check gd_non_iso  mis_flt_lmt x =false ).
    {
      unfold miscomparing_lst in Hnin. 
      simpl in Hnin.
      rewrite (filter_In) in Hnin.
      apply not_and in Hnin.
      -
        inversion Hnin. 
        -- contradiction.
        -- simpl in *.
           apply Bool.not_true_is_false in H4.
           unfold mis_flt_lmt.
           unfold flt_lmt_among_good.
           unfold num_of_bad_and_non_isolated.
           unfold all_good_non_iso_lst.
           simpl.
           trivial.
      - unfold combine_lists in *.
        exact ( In_decidable unit_output_decidable x
                  (filter (fun y : unit_output => hw_good_unit_check y)
                     (map (fun x0 : unit_output * unit_data => fst x0)
                        (non_isltd_comb_lst (combine input ud_lst))))).
    } 
    clear Heqpf_myb pf_myb H2 H3 H1.
    unfold miscomparing_many_check in H4.
    apply Nat.ltb_ge in H4.
    
    pose proof (len_mis_lst_le_mis_flt_lmt
                  pf_uids pf_input pf_ud_lst H). 
    
    unfold devn_lst_single_unit in H4.
    assert ((fun y : unit_output => unit_deviation_check x y) =
              (fun y : unit_output => negb (unit_agrmnt_check x y) ) ). {
      apply functional_extensionality.
      unfold unit_agrmnt_check.
      intros.
      rewrite (Bool.negb_involutive (unit_deviation_check x x0)).
      trivial.
    }
    remember (filter
                (fun y : unit_output =>
                   negb
                     (miscomparing_many_check
                        (proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst))
                        (flt_lmt_among_good pf_uids pf_input pf_ud_lst) y)) gd_non_iso)
      as negb_miscomp_gn_non_iso.

    pose proof (filter_length_is_length_minus_remaining
                 negb_miscomp_gn_non_iso
                  (unit_agrmnt_check x)   ) .
    unfold agrng_lst_single_unit in Myb_prop.
    assert ( length negb_miscomp_gn_non_iso
             =  length gd_non_iso
               - length (proj1_sig (miscomparing_lst pf_uids pf_input pf_ud_lst)) ).
    { 
      pose proof (filter_length_is_length_minus_remaining
                    gd_non_iso
                    ( miscomparing_many_check
                        (proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst))
                        (flt_lmt_among_good pf_uids pf_input pf_ud_lst)) ) .
      pose proof (filter_length_le
                    (fun y : unit_output =>
                       negb
                         ( miscomparing_many_check
                             (proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst))
                             (flt_lmt_among_good pf_uids pf_input pf_ud_lst) y))
                    gd_non_iso ). 
      unfold miscomparing_lst. 
      simpl in *.
      unfold flt_lmt_among_good in *.
      simpl in *.
      unfold gd_non_iso in *.
      rewrite Heqnegb_miscomp_gn_non_iso in * .
      rewrite H5.
      lia.
    } 
    assert ( length
               (filter (fun y : unit_output => negb (unit_agrmnt_check x y))
                  negb_miscomp_gn_non_iso )  > mis_flt_lmt ).
    {
      assert ( length
                 (filter (fun y : unit_output => negb (unit_agrmnt_check x y))
                   negb_miscomp_gn_non_iso)
               =  length negb_miscomp_gn_non_iso
                  - length (filter (fun y : unit_output =>  (unit_agrmnt_check x y))
                        negb_miscomp_gn_non_iso ) ). {
        pose proof (filter_length_le
                      (fun y : unit_output => negb (unit_agrmnt_check x y))
                      negb_miscomp_gn_non_iso ).
        rewrite H3.
        rewrite Heqnegb_miscomp_gn_non_iso in *.
        lia.
      }
      rewrite Heqnegb_miscomp_gn_non_iso in *.

      exact ( helpler2 H0 H5 Myb_prop H6 H1 ).
    }
    
    assert (length (filter (fun y : unit_output => negb (unit_agrmnt_check x y))
                      gd_non_iso) > mis_flt_lmt).
    {
      assert (incl
                (filter (fun y : unit_output => negb (unit_agrmnt_check x y))
                   negb_miscomp_gn_non_iso)
                (filter (fun y : unit_output => negb (unit_agrmnt_check x y))
                   gd_non_iso) ).
      {
        unfold incl.
        intros.
        apply filter_In in H7.
        apply filter_In.
        inversion H7.
        split.
        rewrite Heqnegb_miscomp_gn_non_iso in H8.
        apply filter_In in H8.
        inversion H8; trivial.
        trivial.
      }
      
      pose proof ( filter_andb_eq_filter_on_filter_negb
                     gd_non_iso
                     (miscomparing_many_check
                        (proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst))
                        (flt_lmt_among_good pf_uids pf_input pf_ud_lst) )
                     (unit_agrmnt_check x) ).
      rewrite <- Heqnegb_miscomp_gn_non_iso in H8.
      rewrite <- H8 in H7.
      pose proof (filter_sublist_length_at_most_list_length_v2
                    (miscomparing_many_check
                       (proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst))
                       (flt_lmt_among_good pf_uids pf_input pf_ud_lst) )
                    (unit_agrmnt_check x)
                    (noDup_non_iso_good_lst pf_uids pf_input pf_ud_lst)
                    H7 ).
      fold gd_non_iso in H9, H8, H6.
      rewrite H8 in H9.
      lia.
    }
    rewrite <- H2 in H7.
    apply Nat.le_ngt in H4.
    contradiction.
Qed.

Lemma len_l_gt_2lmt_len_mis_plus_len_nmis_eq_len_l
        
  { u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  :
  let gd_non_iso  := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
  let mis_flt_lmt := flt_lmt_among_good pf_uids pf_input pf_ud_lst in 
  length (dlta_dev_lst_grnd_truth gd_non_iso ) <= mis_flt_lmt
  -> length gd_non_iso > 2*mis_flt_lmt
  -> let mis_list := proj1_sig (miscomparing_lst pf_uids pf_input pf_ud_lst) in
     let nmis_list := proj1_sig (not_miscomparing_lst pf_uids pf_input pf_ud_lst) in
     length gd_non_iso = length mis_list + length nmis_list.

  intros.
  pose proof (more_than_double_max_fault_units_means_zero_maybe
                pf_uids pf_input pf_ud_lst H H0).
  simpl.
  assert (length gd_non_iso =
            length mis_list +
              length (filter
                        (fun y : unit_output =>
                           negb (miscomparing_many_check gd_non_iso  mis_flt_lmt y) )
                        gd_non_iso)). {
    pose proof (filter_length
                  (fun y : unit_output =>
                     (miscomparing_many_check gd_non_iso  mis_flt_lmt y) )
                  gd_non_iso ).
    unfold mis_list, miscomparing_lst.
    fold gd_non_iso.
    simpl.
    simpl in H2.
    unfold mis_flt_lmt in H2.
    unfold flt_lmt_among_good in H2.
    simpl in H2.
    unfold mis_flt_lmt.
    unfold flt_lmt_among_good.
    simpl.
    lia.
  }    
  remember (filter
            (fun y : unit_output =>
               negb (miscomparing_many_check gd_non_iso mis_flt_lmt y)) gd_non_iso)
    as Rem_l.
  assert (length Rem_l = length nmis_list + length (proj1_sig (maybe_miscomparing_lst pf_uids pf_input pf_ud_lst)) ). {
    unfold nmis_list, not_miscomparing_lst.
    simpl.
    simpl in HeqRem_l.
    rewrite HeqRem_l.
    simpl in gd_non_iso.
    fold gd_non_iso.
    fold mis_flt_lmt.
    unfold flt_lmt_among_good in mis_flt_lmt.
    simpl in mis_flt_lmt.
    fold mis_flt_lmt.
    rewrite <- HeqRem_l.
    remember (fun y : unit_output =>
        agreeing_many_check Rem_l
          (mis_flt_lmt -
           length
             (filter
                (fun y0 : unit_output =>
                   miscomparing_many_check gd_non_iso mis_flt_lmt y0) gd_non_iso)) y)
      as f.
    symmetry.
    exact (filter_length f Rem_l).
  }
  rewrite H1 in H3.
  simpl in H3.
  lia.
Qed.


Lemma helper
  { a b c d : nat}
  (pf1 : a = b + c)
  (pf2 : b <= d)
  (pf3 : a > 2 * d) : c <> 0.
  lia.
Qed.

Lemma len_l_gt_2lmt_at_lst_1_not_mscmprng
  { u_ids : list unit_id} (pf_uids: NoDup u_ids)
  { input : list unit_output } (pf_input :  get_u_ids_of_unit_output input =  u_ids )
  { ud_lst : list unit_data } (pf_ud_lst :  get_u_ids_of_unit_data ud_lst =  u_ids  )
  :
  let gd_non_iso  := proj1_sig (all_good_non_iso_lst pf_uids pf_input pf_ud_lst) in
  let mis_flt_lmt := flt_lmt_among_good pf_uids pf_input pf_ud_lst in 
  length (dlta_dev_lst_grnd_truth gd_non_iso ) <= mis_flt_lmt
  -> length gd_non_iso > 2*mis_flt_lmt
  -> let nmis_list := proj1_sig (not_miscomparing_lst pf_uids pf_input pf_ud_lst) in
    exists x, In x nmis_list.
Proof.
  
  intros.
  assert (length nmis_list <> 0 ). {
    pose proof (len_l_gt_2lmt_len_mis_plus_len_nmis_eq_len_l
                  pf_uids pf_input pf_ud_lst H H0).
    assert (length (proj1_sig (miscomparing_lst pf_uids pf_input pf_ud_lst)) <= mis_flt_lmt)
      by exact (len_mis_lst_le_mis_flt_lmt
                  pf_uids pf_input pf_ud_lst H).
    fold gd_non_iso in H1.
    exact (helper H1 H2 H0).
  }
  
  assert ( nmis_list <> nil ). {
    intro.
    apply length_zero_iff_nil in H2.
    rewrite H2 in H1. contradiction.
  }
  apply exists_last in H2.
  inversion H2 as [l [x Hx]].
  exists x. rewrite Hx.
  apply in_or_app.
  right. apply in_eq.
Qed.




