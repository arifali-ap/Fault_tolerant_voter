From Stdlib Require Import  Nat.     
From Stdlib Require Import Bool.    
From Stdlib Require Import List. 
Import ListNotations.
From Stdlib Require Import Lia.
Import Arith.
From Stdlib Require Import Logic.Eqdep_dec.
Require Import BTProject.config.
Require Import BTProject.voter_state.
Require Import BTProject.library.
Require Import BTProject.gen_lemmas.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Logic.Decidable.
From Stdlib Require Import Logic.Decidable.
From Stdlib Require Import Classes.DecidableClass.
From Stdlib Require Import Program.Equality.

Lemma healthy_list_contains_only_healthy_units (ud_lst: list unit_data) : forall x, In x (healthy_unit_list ud_lst) <-> ( healthy_data x /\ In x ud_lst).
  
  split.
  * intros.
    apply filter_In in H. inversion H.
    pose proof (hlthy_unit_check_true_is_healthy_data H1). auto.
 
  * intros. inversion H; unfold healthy_data in H0;
      inversion H0 as [h1 [h2 h3]]. apply filter_In; split; auto.
    **  unfold hlthy_unit_check, not_iso_check,
          not_miscomp_unit_check, hw_good_unit_check in *.
        rewrite h1, h2, h3. auto.
Qed.


Definition build_prime_switched_vs
  (iso_updated_vs:voter_state)
  {new_p_ud_lst : list unit_data}
  (pf_new_p_ud_lst :  get_u_ids_of_unit_data new_p_ud_lst = l u_ids)
  (pf_min:  min_required <= count_of_non_isolated_units new_p_ud_lst)
  { x: unit_data }
  { xs: list unit_data }
  (pf_hl_list : healthy_unit_list new_p_ud_lst = x::xs )
  (pf_current_isolated : In (uid (voter_output iso_updated_vs)) (get_u_ids_of_unit_data (isolated_list new_p_ud_lst) ) )
  : voter_state. (*  { x : voter_state | build_prime_switched_vs_prop iso_updated_vs x new_p_ud_lst}. *)
  
  refine (
      (* exist _ *) (voter_state_build
                       new_p_ud_lst
                       pf_new_p_ud_lst
                       x.(u_output)
                           valid
                           0
                           x
                           _ _ _  _ _  _ _ _)
    ).
   
  Unshelve.
  8: { apply in_map_iff.
       exists x.
       repeat split.
       assert ( In x (healthy_unit_list new_p_ud_lst)) as Hinhl. {
         rewrite pf_hl_list. apply in_eq. }
       apply filter_In in Hinhl.
       inversion Hinhl; trivial.
  }
    -(* u_output x = u_output x /\ healthy_data x *) 
    split; trivial.
    assert (hlthy_unit_check x = true ) as Hhl. {
      assert ( In x (filter (fun y : unit_data => hlthy_unit_check y)
                       new_p_ud_lst )).  {
        unfold healthy_unit_list in pf_hl_list.
        rewrite pf_hl_list; apply in_eq. }
      apply filter_In in H.
      inversion H.
      trivial.
    }
    exact (hlthy_unit_check_true_is_healthy_data Hhl).   

  - (* 0 = 0 <-> valid = valid /\ In x new_p_ud_lst *)
    repeat split. assert (In x ( healthy_unit_list new_p_ud_lst)).
    { rewrite pf_hl_list; apply in_eq. } 
    unfold healthy_unit_list in H0.
    apply filter_In in H0.
    inversion H0; trivial.
    
    
    
  - (* pf_validity_prop (u_output x) valid new_p_ud_lst *)
    repeat split. intro.  apply Nat.lt_nge in H. contradiction.
    intro. inversion H.
    intro. inversion H as  [H1 H2].
    assert ( In x (healthy_unit_list new_p_ud_lst)). { rewrite pf_hl_list. apply in_eq. }
    pose proof (@healthy_list_contains_only_healthy_units new_p_ud_lst x) as OH. 
    inversion OH as [OHa OHb].
    pose proof (OHa H0) as OHc. inversion OHc as [OHchd OHCin].
    unfold get_u_ids_of_unit_data in H2. apply in_map_iff in H2.
    inversion H2 as [H2x [H2uid H2In]].
    unfold isolated_list in H2In.
    apply filter_In in H2In.
    inversion H2In as [H2xIn H2xIso].
    pose proof (fun_out_same_means_same_element_of_lst H2x H2uid H2xIn OHCin
                  (mapped_list_nodup pf_new_p_ud_lst (pf_l u_ids))
).
    rewrite H3 in H2xIso.
    unfold healthy_data in OHchd. inversion OHchd as [hl1 [hl2 hl3]].
    unfold not_iso_check in H2xIso.
    rewrite hl2 in H2xIso.
    inversion H2xIso.
    trivial.
    inversion H.
    intro; inversion H.

  - (*  valid = valid -> In (uid (u_output x)) (get_u_ids_of_unit_data (non_isolated_list new_p_ud_lst)) *)
    intro. apply in_map_iff.
    exists x. split; trivial.
    apply filter_In.
    assert ( In x ( healthy_unit_list new_p_ud_lst) ). { rewrite pf_hl_list. apply in_eq. }
    pose proof (@healthy_list_contains_only_healthy_units new_p_ud_lst x).
    inversion  H1.
    pose proof (H2 H0).
    inversion H4.
    split; trivial.
    unfold healthy_data in H5.
    inversion H5 as [Ha [Hb Hc]].
    unfold not_iso_check. rewrite Hb. trivial.

  - (*  risky_cnt_age_prop pf_new_p_ud_lst *)
    unfold risky_cnt_prop.
    intro.     
    pose proof ( pf_healthy x) as H1.
    remember (proj2_sig (find_data_of_a_given_unit_id pf_new_p_ud_lst
      (match
         in_map_iff (fun a : unit_data => uid (u_output a)) new_p_ud_lst
           (uid (u_output x))
       with
       | conj _ x1 => x1
       end
         (ex_intro
            (fun x0 : unit_data =>
             uid (u_output x0) = uid (u_output x) /\ In x0 new_p_ud_lst) x
            (conj eq_refl
               match
                 match
                   filter_In (fun y : unit_data => hlthy_unit_check y) x new_p_ud_lst
                 with
                 | conj x0 _ => x0
                 end
                   (eq_ind_r (fun l : list unit_data => In x l) (in_eq x xs) pf_hl_list)
               with
               | conj x0 _ => x0
               end))) )).
    inversion a.
    
    assert ( In x new_p_ud_lst ). {
      
      assert ( In x (healthy_unit_list new_p_ud_lst) ).
      rewrite pf_hl_list.
      apply in_eq.
      unfold healthy_unit_list in H3.
      apply filter_In in H3.
      inversion H3.
      trivial.
    }
    pose proof (fun_out_same_means_same_element_of_lst x H0 H3 H2 
                  (mapped_list_nodup pf_new_p_ud_lst (pf_l u_ids)) ).
    inversion H1 as [H5 H6]. 
    assert ( healthy_data x).
    { assert ( In x (healthy_unit_list new_p_ud_lst) ) as H7.
      { rewrite pf_hl_list. apply in_eq. } 
      unfold healthy_unit_list in H7.
      apply filter_In in H7. inversion H7.
      exact ( hlthy_unit_check_true_is_healthy_data H9).
    }
    
    rewrite H4 in H7.
    rewrite H4 in H6.
    symmetry.
    exact (H6 H7).
  - intros.
    unfold persistence_lmt.
    lia.
  -  unfold persistence_lmt. repeat split.
    -- intro. lia.
    -- intro. inversion H.
    -- intro. inversion H.
Defined.
