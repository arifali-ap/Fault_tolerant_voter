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

Require Import BTProject.build_updated_u_data_lst.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Logic.Decidable.
From Stdlib Require Import Logic.Decidable.
From Stdlib Require Import Classes.DecidableClass.
From Stdlib Require Import Program.Equality.
 

(* if there are no enough non_isolated units present, make the output as invalid *)
Definition build_invalidated_vs
  (vs: voter_state)
  (new_p_ud_lst : list unit_data )
  (pf_new_p_ud_lst : get_u_ids_of_unit_data new_p_ud_lst = l u_ids)
  (pf_min_required : count_of_non_isolated_units (new_p_ud_lst) < min_required)
  : voter_state.
  
  refine (  voter_state_build
              (new_p_ud_lst)
              (pf_new_p_ud_lst)
              (voter_output vs)
              not_valid
              invalid_age
              (presrvd_data vs)
              _
              (pf_presrvd_data vs)
              _ _ _ _ _ _).
  Unshelve. 
  
  7: { (* In (uid (voter_output vs)) (get_u_ids_of_unit_data new_p_ud_lst) *)
    pose proof (pf_v_output vs).
    pose proof (pf_ud_lst vs).
    rewrite <- pf_new_p_ud_lst in H0.
    rewrite H0 in H. trivial.
  }
  - (* pf_age *)
    repeat split. inversion H. inversion H.
    -- intros.  inversion H. inversion H0.  
  - (* pf_validity_prop *)
    repeat split.   intro. trivial.
    intro. inversion H.  apply Nat.le_ngt in H0. contradiction.
    inversion H.
    inversion H. 
    intro. inversion H.
    intro. inversion H. apply Nat.le_ngt in H0. contradiction.
  - (*pf_out_not_isolated*)
    intro. inversion H.
  - (* risky_cnt_age_prop *) unfold risky_cnt_prop. intro.  inversion H.
  - (*pf_age_bound  *) intros. exfalso; apply H; trivial.
  - (*pf_age_validity  *)
    repeat split. intros. 
    assert ( ~ ( 2 * persistence_lmt < persistence_lmt) ). {
      lia.
    }
    contradiction.
    intro. inversion H. 
    intro; trivial. unfold invalid_age. lia.
Defined.


Lemma helper_m
  {x y z : nat }
  (pf1 : x < z )
  (pf2 : y > z )
  (pf3 : y < 2*z )
  : y - x < 2*z.
  
  
lia.
Qed.



(* if there are no enough healthy units present, make the output as un_id *)
Definition build_un_id_vs
  (vs: voter_state)
  {new_p_ud_lst : list unit_data }
  {all_unit_outputs: list unit_output}
  (pf_all_unit_outputs : get_u_ids_of_unit_output all_unit_outputs =  l (u_ids))
  (pf_new_p_ud_lst : new_p_ud_lst = build_updated_u_data_lst
                                        (pf_l u_ids)
                                        pf_all_unit_outputs  vs.(pf_ud_lst)  )
  (pf_min_required : ( min_required <= count_of_non_isolated_units new_p_ud_lst
                       /\ healthy_unit_list new_p_ud_lst = nil
                       /\  In (uid (voter_output vs))
                             (get_u_ids_of_unit_data (isolated_list new_p_ud_lst))))
  
  : voter_state.
  
  refine (  voter_state_build
              (new_p_ud_lst)
              _
              (voter_output vs)
              un_id
              (S (output_age vs))
              (presrvd_data vs)
              _
              (pf_presrvd_data vs)
              _ _ _ _ _ _).



  Unshelve.    
  7: { (* get_u_ids_of_unit_data new_p_ud_lst = l u_ids *)
    pose proof (pf_v_output vs).
    pose proof (pf_ud_lst vs).
    pose proof (build_updated_u_data_lst_preserves_uids (pf_l u_ids)
                  pf_all_unit_outputs vs.(pf_ud_lst)).
    rewrite pf_new_p_ud_lst. trivial.
  }
  - (* pf_age *)
    repeat split.
    -- inversion H.
    -- intros. exfalso. exact (Nat.neq_succ_0 (output_age vs) H ).
    -- intro. inversion H. inversion H0.
       
  - (* pf_validity_prop *)
    inversion pf_min_required as [Ha [Hb Hc]].
    repeat split.
    --
      intro.  apply Nat.le_ngt in Ha. contradiction.
    --
      intro.  inversion H. 
    -- trivial.
    -- trivial.
    -- intro.  trivial.
    -- intro. inversion H. rewrite Hb in H1. contradiction.
  
  - (*pf_out_not_isolated*)
    intro. inversion H.
  - (*pf_risky_cnt *)
    intro. inversion H.
  - (*pf_age_bound  *) intros H x Hxin Hxiso. 
     
     inversion pf_min_required as [Hmin [Hnil Hiso]].
     assert (voter_validity vs <> not_valid) as Hvsvld. {
       assert ( min_required <= count_of_non_isolated_units (u_data_lst vs) )
         as Hminvs. {
         assert (count_of_non_isolated_units new_p_ud_lst
                 <= count_of_non_isolated_units (u_data_lst vs)).
         { rewrite pf_new_p_ud_lst.
           exact (build_updated_u_data_lst_do_not_increase_non_isolated_units
                    u_ids.(pf_l) pf_all_unit_outputs vs.(pf_ud_lst) ).
         }
         lia.
       }
       pose proof (pf_validity vs) as Hpfvld.
       inversion Hpfvld as [[Hnot1 Hnot2] Hrem]. 
       intro not.
       pose proof (Hnot2 not) as Hnmin.
       apply Nat.le_ngt in Hnmin.
       apply Hnmin. 
       lia.
     }
     
     pose proof ( pf_age_bound vs Hvsvld) as Hpfagevs.
     assert ( forall y, In y (u_data_lst vs) ->
                        uid (u_output y) = uid (u_output x)
                        -> risky_cnt_prop  y x ) as Hpfrcx.     {
       intros y Hyin Hequid.
       pose proof (build_updated_u_data_lst_holds_risky_cnt_prop
                   u_ids.(pf_l) pf_all_unit_outputs vs.(pf_ud_lst) ) as Hpfrcprop.
       rewrite pf_new_p_ud_lst in Hxin.
       exact (Hpfrcprop y Hyin x Hxin Hequid).
     }

     (* Going to find the corresponding y (same uid as x) in (u_data_lst vs) *)
     (* Step 1 : Assert the uid of x is in uids of u_data_lst vs
        Step 2 : Get the corresponding data *)
     assert (In (uid (u_output x) ) (get_u_ids_of_unit_data (u_data_lst vs) ) )
       as Huidxinq.
     {
       pose proof (build_updated_u_data_lst_preserves_uids
                     u_ids.(pf_l) pf_all_unit_outputs vs.(pf_ud_lst) ) as pf_ud_lst_new.
       pose proof (pf_ud_lst vs) as pf_ud_lst.
       rewrite pf_ud_lst.
       rewrite <- pf_ud_lst_new.
       unfold get_u_ids_of_unit_data.
       rewrite <- pf_new_p_ud_lst.
       apply in_map_iff.
       exists x.
       split; trivial.
     }

     (* Getting y *)
     apply in_map_iff in Huidxinq.
     inversion Huidxinq as [y [Hyeqx Hyin]].
     
     (* Use risky_cont_prop y x to show the risky count in incrimented by 1 *)
     assert ( iso_status (u_status y) = not_isolated ) as Hyiso.
     {
       pose proof (not_isolated_after_update_implies_not_isolated_before
                     (pf_l u_ids) pf_all_unit_outputs
                     (pf_ud_lst vs) ) as Hniso.
       assert ( In (uid (u_output x))
                  (get_u_ids_of_unit_data (non_isolated_list new_p_ud_lst)) ) as Hxinniso.
       {
         apply in_map_iff. 
         exists x.
         split; trivial.
         apply filter_In.
         split; trivial.
         unfold not_iso_check.
         rewrite Hxiso.
         trivial.
       }
       rewrite pf_new_p_ud_lst in Hxinniso.
       pose proof (Hniso (uid (u_output x) ) Hxinniso) as Hxinnisovs.
       apply in_map_iff in Hxinnisovs.
       inversion Hxinnisovs as [y1 [Hy1uid Hy1in]].
       apply filter_In in Hy1in.
       inversion Hy1in as [Hy1inq Hy1iso].
       rewrite<- Hyeqx in Hy1uid.
       assert ( y1 = y) as Heqy1y
           by exact (fun_out_same_means_same_element_of_lst  y1 Hy1uid Hy1inq Hyin 
                       (mapped_list_nodup (pf_ud_lst vs) (pf_l u_ids))).
       rewrite Heqy1y in Hy1iso.
       exact (nisoc_t_not_isltd Hy1iso).
     }

     pose proof (Hpfrcx y Hyin Hyeqx Hyiso) as [Hrc0orS [Hrsk Hhl]].
     inversion Hrc0orS as [Hrc0 | Hrcs].
    -- (* risky_count = 0 *)
      pose proof (pf_healthy x) as [Hpf1 Hpf2].
        pose proof (Hpf1 Hrc0) as [Hgd [Hniso Hnmis]].
        assert (In x (healthy_unit_list new_p_ud_lst) ) as HxinH.
        { apply filter_In.
          split; trivial.
          unfold hlthy_unit_check, not_iso_check ,
            not_miscomp_unit_check, hw_good_unit_check.
          
          repeat rewrite andb_true_iff.
          repeat split.
          rewrite Hniso; trivial.
          rewrite Hnmis; trivial.
          rewrite Hgd; trivial.
        }
        rewrite Hnil in HxinH.
        inversion HxinH.
     -- (* risky_count is S *) 
       pose proof (Hpfagevs y Hyin Hyiso).
       lia.

       
  - (* pf_age_validity *)
    repeat split.
    -- intro.
       pose proof (pf_age_validity vs) as [[Hpav1 Hpav2] [Hpavnt1 Hpavnt2]].
       destruct (voter_validity vs) eqn:Hv.
       ---
         (* Valid case *)
         (* Here we prove by contradiction.
            find contradiction for the selected unit is isolated in pf_min_required *)
         
         pose proof (pf_risky_cnt vs Hv) as Hpfrcvs.
         remember (find_data_of_a_given_unit_id (pf_ud_lst vs) (pf_v_output vs))
           as Hout.
         
         simpl in Hpfrcvs.
         pose proof (pf_risky_count (u_status (proj1_sig Hout))) as HpfrcHout.
         inversion pf_min_required as [Hmin [Hnil Hiso]].
         apply in_map_iff in Hiso.
         inversion Hiso as [x [Hxeqo Hxin]].
         apply filter_In in Hxin.
         inversion Hxin as [Hxinnew Hisoprop].
         apply negb_true_iff in Hisoprop.
         pose proof (nisoc_f_isltd Hisoprop) as Hisox.
         pose proof (pf_risky_count (u_status x)) as [Hpfx [Hxiso1 Hxiso2]].
         pose proof (Hxiso2 Hisox) as Hrceqpcx.
         pose proof (proj2_sig Hout) as Houtprop.
         remember (proj1_sig Hout) as y.
         simpl in Houtprop.
         inversion Houtprop as [Huidxeqy Hyin].
         assert (iso_status (u_status y) = not_isolated ) as Hnisoy. {
           pose proof (pf_out_not_isolated vs Hv) as Hpfoni.
           apply in_map_iff in Hpfoni.
           inversion Hpfoni as [y0 [Huidy0eqy Hy0innisol]].
           apply filter_In in Hy0innisol.
           inversion Hy0innisol as [Hy0inq Hy0isoprop].
           rewrite Huidxeqy in Huidy0eqy.
           assert ( y0 = y )
             as Hy0eqy by exact (fun_out_same_means_same_element_of_lst
                                   y0 Huidy0eqy Hy0inq Hyin
                                   (mapped_list_nodup (pf_ud_lst vs) (pf_l u_ids)) ).
           rewrite Hy0eqy in *.
           exact (nisoc_t_not_isltd Hy0isoprop).
         }
         rewrite <- Hxeqo in Huidxeqy.
         rewrite pf_new_p_ud_lst in Hxinnew.
         symmetry in Huidxeqy.
         pose proof (build_updated_u_data_lst_holds_risky_cnt_prop
                       u_ids.(pf_l) pf_all_unit_outputs
                               vs.(pf_ud_lst) y Hyin x Hxinnew Huidxeqy Hnisoy)
           as  [Hrcx0orSy T].
         clear T.
         inversion Hrcx0orSy as [Hrcx0 | HrcxSy].
         ---- rewrite Hrceqpcx in Hrcx0.
              inversion Hrcx0.
         ---- pose proof ((pf_risky_cnt vs) Hv) as Hpfrcage.
              rewrite <- HeqHout in Hpfrcage.
              simpl in Hpfrcage.
              rewrite <- Heqy in Hpfrcage.
              assert (risky_count (u_status x) <> persistence_lmt) as Hneqpc
                  by lia.
              contradiction.
       ---
         (* un_id case *)
         assert (output_age vs < persistence_lmt ) by lia.
         pose proof (Hpav1 H0).
         inversion H1.
       ---
         (* not_valid case *)
         assert (output_age vs < persistence_lmt ) by lia.
         pose proof (Hpav1 H0).
         inversion H1.
    -- intro H. inversion H.
    -- intro Hagevs.
       pose proof (pf_age_validity vs) as [[Hpav1 Hpav2] [Hpavnt1 Hpavnt2]].
       destruct (voter_validity vs) eqn:Hv.
       ---
         assert (valid = valid ) by trivial.
         assert (~ output_age vs < persistence_lmt ) by lia.
         pose proof (Hpav2 H).
         contradiction.
       ---
         assert (~ output_age vs <= 2 * (persistence_lmt - 1)) as Hnot. {
           unfold persistence_lmt in *.
           lia.
         }         
         pose proof (pf_validity vs) as [Hnv [[Huid1 Huid2] T]].
         pose proof (Huid2 Hv) as [Hmin].
         pose proof (voter_state_age_bound vs Hmin).
         contradiction.
       ---   
         inversion pf_min_required as [Hmin [Hnil Hiso]].
         assert (min_required <= count_of_non_isolated_units (u_data_lst vs)) as Hminq. {
           assert (count_of_non_isolated_units new_p_ud_lst
                   <= count_of_non_isolated_units (u_data_lst vs)).
           { rewrite pf_new_p_ud_lst.
             exact (build_updated_u_data_lst_do_not_increase_non_isolated_units
                      u_ids.(pf_l) pf_all_unit_outputs vs.(pf_ud_lst) ).
           }
           lia.
         }
         assert (~ min_required <= count_of_non_isolated_units (u_data_lst vs))
           as Hnmin. {
           pose proof (pf_validity vs) as [[Hnv1 Hnv2] T].
           pose proof (Hnv2 Hv) as Hltmin.
           lia.
         }
         contradiction.
    -- intro H. inversion H.
  -
    (* In (uid (voter_output vs)) (get_u_ids_of_unit_data new_p_ud_lst) *)
    pose proof (pf_v_output vs).
    pose proof (pf_ud_lst vs).
    pose proof (build_updated_u_data_lst_preserves_uids (pf_l u_ids)
                  pf_all_unit_outputs vs.(pf_ud_lst)).
    rewrite pf_new_p_ud_lst.
    rewrite H1.
    rewrite <- H0. trivial.
Defined.
