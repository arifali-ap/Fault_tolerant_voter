From Stdlib Require Import Nat.  
From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Lia.
Import Arith.
From Stdlib Require Import Logic.Eqdep_dec.
From Stdlib Require Import Classes.EquivDec.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Lists.ListDec.
From Stdlib Require Import List Decidable.
Require Import BTProject.gen_lemmas.
Require Import BTProject.config.
Require Import BTProject.voter_state.


Definition risky_cnt_prop   (old  :   unit_data) (new :  unit_data) :=
  iso_status old.(u_status) = not_isolated ->
  (risky_count new.(u_status) = 0  \/
     risky_count new.(u_status) = S (risky_count ( old).(u_status)))
  /\ ( (risky_count new.(u_status) = S (risky_count ( old).(u_status))) <-> (miscomp_status (u_status new) <> not_miscomparing \/ hw_hlth (reading (u_output new)) = bad ) )  .



Definition non_isolated_list_of_vs (vs: voter_state ) : list unit_data :=  
  non_isolated_list vs.(u_data_lst).




(* List of good units from non isolated list *)
Definition hw_good_non_isltd_unit_lst_of_vs (vs : voter_state) : list unit_data :=
 hw_good_non_isltd_unit_lst vs.(u_data_lst).


(* List of good units from non isolated list *)
Definition healthy_unit_list_of_vs (vs : voter_state) : list unit_data :=
  healthy_unit_list vs.(u_data_lst).




Definition deviation_check (u_data: unit_data)  : bool :=
  delta <? adiff ground_truth (val  (u_data.(u_output)).(reading)).

Definition transient_check (u_data : unit_data) : bool :=
  0 <?  (u_data.(u_status)).(risky_count).



 

Definition unit_adiff ( x y : unit_output )
  :=
  adiff (val (reading x)) (val (reading y)).

Definition grnd_truth_dlta_dev_check ( a : unit_output)
  :=  delta <? adiff ground_truth (val (reading a)).

Definition unit_deviation_check ( a b : unit_output )
  := threshold <? (unit_adiff a b). 

Definition unit_agrmnt_check ( a b : unit_output )
  := negb (unit_deviation_check a b).

Definition devn_lst_single_unit  
  (l : list unit_output) (x : unit_output)
  :=
  (filter (fun y => unit_deviation_check x y) l ).

Definition dlta_dev_lst_grnd_truth
  (l : list unit_output) :=
  filter (fun y=> grnd_truth_dlta_dev_check y) l.

Definition agrng_lst_single_unit 
  (l : list unit_output)
   (x : unit_output) :=
  (filter (fun y => unit_agrmnt_check  x y ) l ).


Definition miscomparing_many_check 
  (l : list unit_output)
  (mis_flt_lmt : nat )
  (x : unit_output)
  :=
  mis_flt_lmt <? length (devn_lst_single_unit l x).

Definition miscomparing_many_prop 
  (l : list unit_output)
  ( mis_flt_lmt : nat )
  (x : unit_output) :=
  mis_flt_lmt < length (devn_lst_single_unit  l x).



(* We need to have x agree with at least mis_flt_lmt other elements.
   Since x is in l, we need to have the length of agreeng list to be at least mis_flt_lmt+1. *)

Definition agreeing_many_check
  (l : list unit_output)
  (mis_flt_lmt : nat )
  (x : unit_output)
  :=  (mis_flt_lmt) <? length (agrng_lst_single_unit l x).









(*




Definition transient_count (vs: voter_state): nat := length (filter (fun y=> transient_check y) (non_isolated_list_of_vs vs)).

Definition deviation_count (vs: voter_state): nat := length (filter (fun y => deviation_check y ) (healthy_unit_list_of_vs (vs)) ).

Definition unhealthy_count (vs: voter_state): nat := length (non_isolated_list_of_vs(vs)) - length(healthy_unit_list_of_vs(vs)).
    

Definition equal_ud_lst (vs1 vs2 : voter_state) := (u_data_lst vs2) = (u_data_lst vs1).

Definition equal_u_outputs (vs1 vs2 : voter_state) :=
  get_u_outputs_of_data (u_data_lst vs2) = get_u_outputs_of_data (u_data_lst vs1).

Definition equal_output_uids (vs1 vs2 :voter_state) :=
  ( In (uid vs1.(voter_output)) (get_u_ids_of_unit_data (non_isolated_list_of_vs vs2))
             ->  (uid vs1.(voter_output)) = (uid vs2.(voter_output)) ).


*)




Lemma hlthy_unit_check_true_is_healthy_data {x : unit_data} (pf: hlthy_unit_check x = true):
  healthy_data x.
  unfold hlthy_unit_check, not_iso_check,
    not_miscomp_unit_check, hw_good_unit_check in *.
  repeat rewrite andb_true_iff in *.
  unfold healthy_data.
  destruct (miscomp_status (u_status x)) eqn:Hmis.
  inversion pf as [[Hi Hm] Hh].
  inversion Hm.
  destruct ( hw_hlth (reading (u_output x))) eqn:Hr.
  inversion pf as [[Hi Hm] Hh].
  inversion Hh.
  destruct (iso_status (u_status x)) eqn:Hiso.
  inversion pf as [[Hi Hm] Hh].
  inversion Hi.
  auto.
  inversion pf as [[Hi Hm] Hh].
  inversion Hm.
Qed.





Lemma helper_atleast_1_hlthy { a b c : nat } : ( a -b < c) -> (  c <= a) ->(0 < c) -> b >= 1.
  Proof.
  intros  H1 H2 H3.
  

  destruct c as [|c'].
  - inversion H3.
  - assert ( a <> 0). intro. rewrite H in H2. inversion H2.
    assert ( b <> 0 ). intro.  rewrite H0 in H1. rewrite Nat.sub_0_r in H1.
    apply Nat.lt_nge in H1. contradiction.
    
    apply  (Nat.neq_0_lt_0 b) in H0.  trivial.

Qed.
 
Lemma atleast_one_healthy
  { l : list unit_data }
  (pf1_l : count_of_unhealthy_non_isolated_unit l < min_required)
  (pf2_l:  min_required <= count_of_non_isolated_units l) :
  healthy_unit_list l <> nil.
Proof.
  unfold count_of_unhealthy_non_isolated_unit in *.
  assert ( 0 < min_required ). { unfold min_required.  apply Nat.lt_0_succ. }
  pose proof (helper_atleast_1_hlthy pf1_l pf2_l H).
  intro.
  apply length_zero_iff_nil in H1.
  rewrite H1 in H0. inversion H0.
Qed.


Fixpoint in_uid_list (x : unit_id) (lst_uids : list unit_id) : bool :=
  match lst_uids with
  | nil => false
  | y :: ys => if unit_id_eqb x y then true else in_uid_list x ys
  end.

Definition remove_uids (l1 : list unit_id) (l2: list unit_output) : list unit_output :=
  filter (fun x => negb (in_uid_list (uid x) l1)) l2.    
 
Instance signal_health_eq_type : EqDec signal_health eq.
Proof.
  unfold EqDec.
  intros x y.
  destruct x, y.
  -  left. reflexivity.
  -  right.  discriminate.
  -  right. discriminate.
  - left. reflexivity.
Defined.

Definition signal_health_eq_dec (n m : signal_health) : {n = m} + {n <> m} :=
  equiv_dec n m.




Instance signal_eq_type : EqDec signal eq.
Proof.
  unfold EqDec.
  intros x y.
  destruct x, y.
  destruct (Nat.eq_dec val0 val) as [Heq | Hneq].
  destruct (signal_health_eq_dec hw_hlth0 hw_hlth) as [Hheq | Hhneq].
  - left. subst. reflexivity.
  - right. subst. intros H. inversion H. rewrite H1 in Hhneq. contradiction.
  - right. intros H. inversion H. rewrite H1 in Hneq. contradiction. 
Defined.

Definition signal_eq_dec (n m : signal) : {n = m} + {n <> m} :=
  equiv_dec n m.



Instance unit_output_eq_type : EqDec unit_output eq.
Proof.
  unfold EqDec.
  intros x y.
  destruct x, y.
  destruct (u_id_eq_dec uid0 uid) as [Heq | Hneq].
  destruct (signal_eq_dec reading0 reading) as [Hreq | Hrneq].
  - left. subst. reflexivity.
  - right. intros H. inversion H.  rewrite H1 in Hrneq. contradiction.
  - right. intros H. inversion H. rewrite H2 in Hneq. contradiction. 
    
Defined.
(*
Definition unit_output_eq_dec (n m : unit_output) : {n = m} + {n <> m} :=
  equiv_dec n m.
*)
Definition unit_output_eq_dec : forall n m : unit_output,  {n = m} + {n <> m}.
  intros.
  exact (equiv_dec n m).
Defined.

Definition unit_output_decidable  : forall x y : unit_output, decidable ( x = y).
  unfold decidable.
  intros.
  pose proof (unit_output_eq_dec x y ).
  destruct H.
  left; trivial.
  right; trivial.
Defined.


Definition incl_dec_l1 (l1 : list unit_output) :
  forall l2 : list unit_output, {incl l1 l2} + {~ incl l1 l2}.
  intros.
  exact ( incl_dec unit_output_eq_dec l1 l2).
Defined.



Lemma nisoc_t_not_isltd
  { x : unit_data }
  (pf_x : not_iso_check x = true)
  : iso_status (u_status x) = not_isolated.
Proof.
  unfold not_iso_check in pf_x.
  destruct (iso_status (u_status x)).
  inversion pf_x.
  trivial.
Qed.


Lemma nisoc_f_isltd
  { x : unit_data }
  (pf_x : not_iso_check x = false)
  : iso_status (u_status x) = isolated.
Proof.
  unfold not_iso_check in pf_x.
  destruct (iso_status (u_status x)).
  trivial.
  inversion pf_x.
Qed.


Lemma not_isltd_rc_lt_pc
  { x : unit_data }
  (pf_x : iso_status (u_status x) = not_isolated)
  : risky_count (u_status x) < persistence_lmt.

  pose proof (pf_risky_count (u_status x)) as [Hlepc [Heqpciso Hisoeqpc]].
  inversion Hlepc.
  rewrite (Heqpciso H0) in pf_x.
  inversion pf_x.
  unfold persistence_lmt.
  lia.
Qed.

  
Lemma voter_state_age_bound
  (vs : voter_state)
  :
(*  (voter_validity vs) <> not_valid ->
  (output_age vs) <= 2*(persistence_lmt-1). *)

  
  count_of_non_isolated_units (u_data_lst vs) >= min_required
  -> (output_age vs) <= 2*(persistence_lmt-1).

  
Proof.
  intros Hcniso.
  assert ( (voter_validity vs) <> not_valid ) as Hnnv. {
    intro.
    pose proof (pf_validity vs) as [Hr].
    inversion Hr.
    pose proof (H2 H).
    apply Arith_base.lt_not_le_stt in H3.
    contradiction.
  }    
  pose proof (pf_age_bound vs Hnnv).
  assert ( non_isolated_list (u_data_lst vs) <> nil ).
  {
    pose proof (pf_validity vs) as [[Hnv1 Hnv2] [[Huid1 Huid2] [Huid3 Hv]]].
    intro.
    assert (count_of_non_isolated_units (u_data_lst vs) < min_required ).
    unfold count_of_non_isolated_units.
    rewrite H0.
    simpl.
    unfold min_required.
    lia.
    pose proof (Hnv1 H1).
    rewrite H2 in Hnnv.
    contradiction.
  }
  apply exists_last in H0.
  inversion H0 as [l1 [a]].
  assert ( In a ( non_isolated_list (u_data_lst vs) ) ).
  {
    rewrite e.
    apply in_or_app.
    right. apply in_eq.
  }
  apply filter_In in H1.
  inversion H1.
  
  assert (iso_status (u_status a) = not_isolated)
           by exact (nisoc_t_not_isltd H3).
  pose proof (H a H2 H4).
  assert (risky_count (u_status a) < persistence_lmt)
           by exact (not_isltd_rc_lt_pc H4).
  lia.
Qed.    
    


