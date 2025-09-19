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

Inductive signal_health :=
| bad  : signal_health
| good : signal_health.


Record signal := signal_build {
                     val     : nat;
                     hw_hlth : signal_health;
                     }.


Inductive unit_id :=
  uid_con : nat -> unit_id.

Record uid_list := uid_list_build {
                       l : list unit_id;
                       pf_l : NoDup l;
                     }.

Definition create_uid_list  (l: list nat)(pf_l : NoDup l) : uid_list.
  refine (
      let x := map (fun y =>  uid_con y) l in
      uid_list_build x
        (NoDup_map_NoDup_ForallPairs _ _ pf_l)).
  unfold ForallPairs. 
  intros a b Hain Hbin Haeqb.
  inversion Haeqb. trivial.
Defined.

Definition u_ids := create_uid_list (seq 1 num_units) (seq_NoDup num_units 1).  



(* This record is used to store the output from a single unit. *)
Record unit_output := unit_output_build {
                          reading : signal;    (* Includes Hardware Health Status *)
                          uid     : unit_id; 
                          }.



Inductive isolation :=
| isolated     : isolation
| not_isolated : isolation.

Inductive validity_status :=
| valid     : validity_status
| un_id     : validity_status (* when there are un-identifiable faults present *)
| not_valid : validity_status.

Inductive miscomparison_status :=
| miscomparing : miscomparison_status
| not_miscomparing : miscomparison_status
| maybe_miscomparing : miscomparison_status.



(* The information kept by the voter for a single unit *)
Record unit_status := unit_status_build {
                          iso_status     : isolation;
                          miscomp_status : miscomparison_status;
                          risky_count    : nat; (* Cumulative information of both miscomparison 
                                                   and hardware faults from the recent cycles *)
                          pf_risky_count   : risky_count <= persistence_lmt
                                             /\ ( risky_count = persistence_lmt <-> iso_status = isolated) ;
                        }.



Record unit_data := unit_data_build { 
                        u_output       : unit_output; 
                        u_status       : unit_status;
                        pf_healthy     : (risky_count u_status) = 0 <->
                                           ( hw_hlth  (reading u_output) = good 
                                             /\ (iso_status u_status) = not_isolated
                                             /\ (miscomp_status u_status) = not_miscomparing );
                        
                      }.


Definition signal_val_of_unit_data (s : unit_data) : nat :=
  val (reading (u_output s)).


Definition get_u_id_of_unit_data  (a : unit_data) : unit_id :=
  a.(u_output).(uid).


Definition get_u_ids_of_unit_output  (l : list unit_output) : list unit_id :=
  map ( fun a => uid a) l.  
Definition get_u_ids_of_unit_data  (l : list unit_data) : list unit_id :=
  map ( fun a => uid (u_output a)) l.



Definition get_u_outputs_of_data ( l_sd : list unit_data ) : list unit_output
  := map (fun x => (u_output x) ) l_sd.


Definition get_u_status_of_data (l_sd : list unit_data) : list unit_status
  := map (fun x =>  (u_status x) ) l_sd.



Definition healthy_data (x : unit_data ) := ( x.(u_output).(reading).(hw_hlth) = good )
                                            /\ ( x.(u_status).(iso_status) = not_isolated)
                                            /\ ( x.(u_status).(miscomp_status) = not_miscomparing).



Definition not_iso_check ( u_data : unit_data ) : bool :=
  match ((u_data.(u_status)).(iso_status)) with
  | not_isolated => true
  | isolated     => false
  end.

Definition non_isolated_list (l :  list unit_data  ) : list unit_data :=
  filter (fun y=> not_iso_check y) l.


Definition isolated_list ( l : list unit_data ): list unit_data :=
  filter (fun y=> negb (not_iso_check y)) l.


Definition hw_good_unit_check (s_o : unit_output) : bool :=
  match (s_o).(reading).(hw_hlth) with
  | good => true
  | bad  => false
  end.



(* List of good signal and non isolated units *)
Definition hw_good_non_isltd_unit_lst (l :  list unit_data ) : list unit_data :=
  filter (fun y=> andb (not_iso_check y) (hw_good_unit_check (u_output y)) )l.


Definition not_miscomp_unit_check (u_data : unit_data) : bool :=
  match (u_data.(u_status)).(miscomp_status) with
  | not_miscomparing => true
  | _                => false                         
  end.

Definition hlthy_unit_check (sd : unit_data) : bool :=
  not_iso_check sd
  && not_miscomp_unit_check sd
  && hw_good_unit_check (u_output sd).



(* List of good not_miscomparing units from non isolated list *)
Definition healthy_unit_list (l : list unit_data) : list unit_data :=
  filter (fun y=> hlthy_unit_check y) l.



Definition count_of_non_isolated_units (l : list unit_data ) :=
  length ( non_isolated_list l).


Definition count_of_unhealthy_non_isolated_unit ( l : list unit_data ) :=
  count_of_non_isolated_units l - length ( healthy_unit_list l).


Instance unit_id_eq_dec : EqDec unit_id eq.
Proof.
  unfold EqDec.
  intros x y.
  destruct x, y.
  destruct (Nat.eq_dec n n0) as [Heq | Hneq].
  - left. subst. reflexivity.
  - right. intros H. inversion H. apply Hneq. assumption.
Defined.

Definition u_id_eq_dec (n m : unit_id) : {n = m} + {n <> m} :=
  equiv_dec n m.

(* Equality function for unit_id *)
Definition unit_id_eqb (id1 id2 : unit_id) : bool :=
  match u_id_eq_dec   id1 id2 with
  |left _ => true
  | right _ => false 
  end.


(* Equality function for unit_id *)
Definition unit_id_eqb2 (id1 id2 : unit_id) : bool :=
  match id1, id2 with
  | uid_con n1, uid_con n2 => Nat.eqb n1 n2
  end.

Definition unit_id_eq_check (look_for: unit_output) (u_data : unit_data) : bool :=
  unit_id_eqb (uid look_for) (get_u_id_of_unit_data u_data). 




Lemma unit_id_equal {a b : unit_id} (pf: unit_id_eqb a b = true ) : a = b.
  unfold unit_id_eqb in pf. unfold u_id_eq_dec in pf. unfold EquivDec.equiv_dec in pf.
  unfold unit_id_eq_dec in pf. unfold Equivalence.equiv in pf. destruct a. destruct b.
  destruct (Nat.eq_dec n n0) in pf.
  - rewrite e. trivial.
  - discriminate pf.
Qed.



Definition output_uid_eql_lst (l : list unit_data) (out: unit_id) : list unit_data :=
 
  filter (fun y=> unit_id_eqb (out) (uid (u_output y))) l.


Lemma in_means_exists
  {ud_lst: list unit_data}
  {out : unit_id }
  (pf1 : ( In  out  (get_u_ids_of_unit_data ud_lst) ) ) :
  ( exists sd, In sd ud_lst /\ (unit_id_eqb out (uid (u_output sd))) = true ).
  unfold get_u_ids_of_unit_data in pf1.
  simpl in *.
  apply in_map_iff in pf1. 
  destruct pf1 as [sd [H_eq H_in]].
  exists sd.
  split.
  - trivial.
  - unfold unit_id_eq_check. unfold unit_id_eqb. unfold u_id_eq_dec. unfold EquivDec.equiv_dec. unfold unit_id_eq_dec. destruct ( out). unfold get_u_id_of_unit_data.  rewrite H_eq.  destruct (Nat.eq_dec n n ).
    -- trivial.
    -- contradiction.
Qed.  


Definition find_data_of_a_given_unit_id
  {u_ids : list unit_id}
  {ud_lst : list unit_data }
  {out : unit_id}
  (pf_ud_lst : get_u_ids_of_unit_data ud_lst =  u_ids)
  (pf_in : In out (get_u_ids_of_unit_data ud_lst))
  :{x: unit_data |  out = get_u_id_of_unit_data x /\ In x ud_lst  }.
 
  remember (output_uid_eql_lst ud_lst out ) as ls eqn:Heqn.
  pose proof (in_means_exists pf_in).
  
  generalize dependent u_ids.
  induction ls; intros.
  - exfalso.
    inversion H.
    unfold output_uid_eql_lst in Heqn.
    assert (In x (filter (fun y => unit_id_eqb out (uid (u_output y))) (ud_lst))) as Hin.
    {     apply filter_In; trivial. }
    rewrite <- Heqn in Hin.
    exact ( in_nil  Hin).
  - unfold output_uid_eql_lst in Heqn.
    assert ( In a (filter (fun y : unit_data => unit_id_eqb (out) (uid (u_output y))) (ud_lst) )). { rewrite <- Heqn. apply in_eq. }
    apply filter_In in H0.
    inversion H0. unfold unit_id_eqb in H2.
    pose proof (unit_id_equal H2).
    assert (out = get_u_id_of_unit_data a /\
              In a (ud_lst)). { split. trivial. trivial. }  
     exact (exist _  a H4).
Defined.  



(* 1) If there are no enough non-isolated units the validity will be not_valid and vice versa
   2) If there are enough (at least min_required) non-isolated units but the prime unit is isolated and 
      in the current cycle there are no other healthy units to choose as the master unit, 
      the voter_validity will be un_id. Which means we are waiting for some more cycles to get
      an healthy unit to act as prime unit.
      In this case the voter_output will be the last healthy value of the recently isolated prime unit.
   3) If there are enough non_isolated units and there is atleast one healthy unit, then the validity will always be valid
*)

Definition pf_validity_prop
  (out: unit_output) (pf_v : validity_status ) (ud_lst : list unit_data) :=
  (count_of_non_isolated_units ud_lst < min_required  <->  pf_v = not_valid )
  /\ (( min_required <= count_of_non_isolated_units ud_lst
        /\ In (uid out) (get_u_ids_of_unit_data (isolated_list ud_lst))) <-> pf_v = un_id )
  /\ ( pf_v = un_id -> (healthy_unit_list ud_lst) = nil )
  /\ (( min_required <= count_of_non_isolated_units ud_lst
        /\ ((healthy_unit_list ud_lst) <> nil) ) -> pf_v = valid ).

Definition risky_cnt_age_prop
  {ud_lst : list unit_data }
  {voter_out : unit_output}
  (pf_ud_lst : get_u_ids_of_unit_data ud_lst = l u_ids)
  (pf_in : In (uid voter_out) (get_u_ids_of_unit_data ud_lst))
  (output_age : nat )
  (voter_validity : validity_status)

  :=
  voter_validity = valid ->
  let voter_out_data := find_data_of_a_given_unit_id pf_ud_lst pf_in in
  output_age =  ( risky_count (u_status (proj1_sig voter_out_data))) .

Record voter_state := voter_state_build {
                          u_data_lst    : list unit_data;
                          (* On unit switching, the next unit is selected  
                                          as per this u_data_lst list order *)
                          pf_ud_lst        : get_u_ids_of_unit_data u_data_lst   = u_ids.(l);
                          voter_output  : unit_output;
                          voter_validity: validity_status;
                          output_age    : nat;                          
                          presrvd_data : unit_data;
                          pf_v_output   : In (uid voter_output)
                                            (get_u_ids_of_unit_data u_data_lst);
                          pf_presrvd_data   : presrvd_data.(u_output) = voter_output
                                          /\ healthy_data presrvd_data ;
                          pf_age        : output_age = 0 <->
                                            (voter_validity = valid
                                             /\ In presrvd_data u_data_lst);
                          pf_validity   : pf_validity_prop
                                            voter_output voter_validity u_data_lst;
                          pf_out_not_isolated :  voter_validity = valid ->
                                                 In (uid voter_output)
                                                   (get_u_ids_of_unit_data
                                                      (non_isolated_list u_data_lst));
                          pf_risky_cnt    : risky_cnt_age_prop pf_ud_lst
                                              pf_v_output
                                              output_age
                                              voter_validity;
                          pf_age_bound   : voter_validity <> not_valid
                                           -> forall x,
                              In x u_data_lst
                              -> x.(u_status).(iso_status) = not_isolated 
                              -> output_age - x.(u_status).(risky_count)
                                 < persistence_lmt;
                          pf_age_validity : (output_age < persistence_lmt <-> voter_validity = valid )
                                            /\ (output_age >= 2*persistence_lmt <-> voter_validity = not_valid)
                        }.

