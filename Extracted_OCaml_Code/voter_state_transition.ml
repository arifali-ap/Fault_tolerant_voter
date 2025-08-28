
type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| _::l' -> S (length l')

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

module Nat =
 struct
  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n m =
    leb (S n) m

  (** val eq_dec : nat -> nat -> sumbool **)

  let rec eq_dec n m =
    match n with
    | O -> (match m with
            | O -> Left
            | S _ -> Right)
    | S n0 -> (match m with
               | O -> Right
               | S n1 -> eq_dec n0 n1)
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a::l0 -> (f a)::(map f l0)

(** val seq : nat -> nat -> nat list **)

let rec seq start = function
| O -> []
| S len0 -> start::(seq (S start) len0)

(** val in_dec : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> sumbool **)

let rec in_dec h a = function
| [] -> Right
| y::l0 ->
  let s = h y a in (match s with
                    | Left -> Left
                    | Right -> in_dec h a l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x::l0 -> (match f x with
            | True -> x::(filter f l0)
            | False -> filter f l0)

(** val combine : 'a1 list -> 'a2 list -> ('a1, 'a2) prod list **)

let rec combine l l' =
  match l with
  | [] -> []
  | x::tl ->
    (match l' with
     | [] -> []
     | y::tl' -> (Pair (x, y))::(combine tl tl'))

(** val le_lt_dec : nat -> nat -> sumbool **)

let rec le_lt_dec n m =
  match n with
  | O -> Left
  | S n0 -> (match m with
             | O -> Right
             | S n1 -> le_lt_dec n0 n1)

(** val le_gt_dec : nat -> nat -> sumbool **)

let le_gt_dec =
  le_lt_dec

(** val le_dec : nat -> nat -> sumbool **)

let le_dec =
  le_gt_dec

(** val lt_dec : nat -> nat -> sumbool **)

let lt_dec n m =
  le_dec (S n) m

(** val simul_max_fault_minus_1 : nat **)

let simul_max_fault_minus_1 = (S O)

(** val persistence_lmt_minus_1 : nat **)

let persistence_lmt_minus_1 = (S (S (S (S O))))

(** val num_units : nat **)

let num_units = (S (S (S (S (S O)))))

(** val delta_minus_1 : nat **)

let delta_minus_1 = (S O)

(** val simul_max_fault : nat **)

let simul_max_fault =
  S simul_max_fault_minus_1

(** val persistence_lmt : nat **)

let persistence_lmt =
  S persistence_lmt_minus_1

(** val min_required : nat **)

let min_required =
  S simul_max_fault

(** val delta : nat **)

let delta =
  S delta_minus_1

(** val threshold : nat **)

let threshold =
  mul (S (S O)) delta

(** val invalid_age : nat **)

let invalid_age =
  mul (S (S O)) persistence_lmt

type 'a eqDec = 'a -> 'a -> sumbool

(** val equiv_dec : 'a1 eqDec -> 'a1 -> 'a1 -> sumbool **)

let equiv_dec eqDec0 =
  eqDec0

(** val adiff : nat -> nat -> nat **)

let adiff n m =
  match Nat.ltb n m with
  | True -> sub m n
  | False -> sub n m

type signal_health =
| Bad
| Good

type signal = { val0 : nat; hw_hlth : signal_health }

type unit_id = nat
  (* singleton inductive, whose constructor was uid_con *)

type uid_list =
  unit_id list
  (* singleton inductive, whose constructor was uid_list_build *)

(** val create_uid_list : nat list -> uid_list **)

let create_uid_list l =
  map (fun y -> y) l

(** val u_ids : uid_list **)

let u_ids =
  create_uid_list (seq (S O) num_units)

type unit_output = { reading : signal; uid : unit_id }

type isolation =
| Isolated
| Not_isolated

type validity_status =
| Valid
| Un_id
| Not_valid

type miscomparison_status =
| Miscomparing
| Not_miscomparing
| Maybe_miscomparing

type unit_status = { iso_status : isolation;
                     miscomp_status : miscomparison_status; risky_count : 
                     nat }

type unit_data = { u_output : unit_output; u_status : unit_status }

(** val not_iso_check : unit_data -> bool **)

let not_iso_check u_data =
  match u_data.u_status.iso_status with
  | Isolated -> False
  | Not_isolated -> True

(** val non_isolated_list : unit_data list -> unit_data list **)

let non_isolated_list l =
  filter not_iso_check l

(** val hw_good_unit_check : unit_output -> bool **)

let hw_good_unit_check s_o =
  match s_o.reading.hw_hlth with
  | Bad -> False
  | Good -> True

(** val not_miscomp_unit_check : unit_data -> bool **)

let not_miscomp_unit_check u_data =
  match u_data.u_status.miscomp_status with
  | Not_miscomparing -> True
  | _ -> False

(** val hlthy_unit_check : unit_data -> bool **)

let hlthy_unit_check sd =
  match match not_iso_check sd with
        | True -> not_miscomp_unit_check sd
        | False -> False with
  | True -> hw_good_unit_check sd.u_output
  | False -> False

(** val healthy_unit_list : unit_data list -> unit_data list **)

let healthy_unit_list l =
  filter hlthy_unit_check l

(** val count_of_non_isolated_units : unit_data list -> nat **)

let count_of_non_isolated_units l =
  length (non_isolated_list l)

(** val unit_id_eq_dec : unit_id eqDec **)

let unit_id_eq_dec =
  Nat.eq_dec

(** val u_id_eq_dec : unit_id -> unit_id -> sumbool **)

let u_id_eq_dec n m =
  equiv_dec unit_id_eq_dec n m

(** val unit_id_eqb : unit_id -> unit_id -> bool **)

let unit_id_eqb id1 id2 =
  match u_id_eq_dec id1 id2 with
  | Left -> True
  | Right -> False

(** val output_uid_eql_lst : unit_data list -> unit_id -> unit_data list **)

let output_uid_eql_lst l out =
  filter (fun y -> unit_id_eqb out y.u_output.uid) l

(** val find_data_of_a_given_unit_id :
    unit_id list -> unit_data list -> unit_id -> unit_data **)

let find_data_of_a_given_unit_id _ ud_lst out =
  let ls = output_uid_eql_lst ud_lst out in
  (match ls with
   | [] -> assert false (* absurd case *)
   | y::_ -> y)

type voter_state = { u_data_lst : unit_data list; voter_output : unit_output;
                     voter_validity : validity_status; output_age : nat;
                     presrvd_data : unit_data }

(** val unit_adiff : unit_output -> unit_output -> nat **)

let unit_adiff x y =
  adiff x.reading.val0 y.reading.val0

(** val unit_deviation_check : unit_output -> unit_output -> bool **)

let unit_deviation_check a b =
  Nat.ltb threshold (unit_adiff a b)

(** val unit_agrmnt_check : unit_output -> unit_output -> bool **)

let unit_agrmnt_check a b =
  negb (unit_deviation_check a b)

(** val devn_lst_single_unit :
    unit_output list -> unit_output -> unit_output list **)

let devn_lst_single_unit l x =
  filter (fun y -> unit_deviation_check x y) l

(** val agrng_lst_single_unit :
    unit_output list -> unit_output -> unit_output list **)

let agrng_lst_single_unit l x =
  filter (fun y -> unit_agrmnt_check x y) l

(** val miscomparing_many_check :
    unit_output list -> nat -> unit_output -> bool **)

let miscomparing_many_check l mis_flt_lmt x =
  Nat.ltb mis_flt_lmt (length (devn_lst_single_unit l x))

(** val agreeing_many_check :
    unit_output list -> nat -> unit_output -> bool **)

let agreeing_many_check l mis_flt_lmt x =
  Nat.ltb mis_flt_lmt (length (agrng_lst_single_unit l x))

(** val combine_lists :
    ('a2 -> 'a1) -> ('a3 -> 'a1) -> 'a1 list -> 'a2 list -> 'a3 list -> ('a2,
    'a3) prod list **)

let combine_lists _ _ _ =
  combine

(** val non_isltd_comb_lst :
    (unit_output, unit_data) prod list -> (unit_output, unit_data) prod list **)

let non_isltd_comb_lst l =
  filter (fun y -> not_iso_check (snd y)) l

(** val all_good_non_iso_lst :
    unit_id list -> unit_output list -> unit_data list -> unit_output list **)

let all_good_non_iso_lst u_ids0 input ud_lst =
  let non_isltd_comb =
    non_isltd_comb_lst
      (combine_lists (fun a -> a.uid) (fun a -> a.u_output.uid) u_ids0 input
        ud_lst)
  in
  let non_isltd_unit_outs = map fst non_isltd_comb in
  filter hw_good_unit_check non_isltd_unit_outs

(** val num_of_bad_and_non_isolated :
    unit_id list -> unit_output list -> unit_data list -> nat **)

let num_of_bad_and_non_isolated u_ids0 input ud_lst =
  let comb_lst =
    combine_lists (fun a -> a.uid) (fun a -> a.u_output.uid) u_ids0 input
      ud_lst
  in
  let not_iso_output_lst =
    map fst (filter (fun y -> not_iso_check (snd y)) comb_lst)
  in
  let bad_non_iso_lst =
    filter (fun y -> negb (hw_good_unit_check y)) not_iso_output_lst
  in
  length bad_non_iso_lst

(** val flt_lmt_among_good :
    unit_id list -> unit_output list -> unit_data list -> nat **)

let flt_lmt_among_good u_ids0 input ud_lst =
  sub simul_max_fault (num_of_bad_and_non_isolated u_ids0 input ud_lst)

(** val miscomparing_lst :
    unit_id list -> unit_output list -> unit_data list -> unit_output list **)

let miscomparing_lst u_ids0 input ud_lst =
  let l = all_good_non_iso_lst u_ids0 input ud_lst in
  let mis_flt_lmt =
    sub simul_max_fault (num_of_bad_and_non_isolated u_ids0 input ud_lst)
  in
  filter (fun y -> miscomparing_many_check l mis_flt_lmt y) l

(** val maybe_miscomparing_lst :
    unit_id list -> unit_output list -> unit_data list -> unit_output list **)

let maybe_miscomparing_lst u_ids0 input ud_lst =
  let mis_lst = miscomparing_lst u_ids0 input ud_lst in
  let mis_flt_lmt = flt_lmt_among_good u_ids0 input ud_lst in
  let rem_mis_flt_lmt = sub mis_flt_lmt (length mis_lst) in
  let gd_non_iso_lst = all_good_non_iso_lst u_ids0 input ud_lst in
  let negb_mis_lst =
    filter (fun y ->
      negb (miscomparing_many_check gd_non_iso_lst mis_flt_lmt y))
      gd_non_iso_lst
  in
  filter (fun y -> negb (agreeing_many_check negb_mis_lst rem_mis_flt_lmt y))
    negb_mis_lst

(** val incr_risky_count_and_update_iso_status_bad_case :
    (unit_output, unit_data) prod -> unit_data **)

let incr_risky_count_and_update_iso_status_bad_case x =
  let sd_s = (snd x).u_status in
  let so = fst x in
  let cnt = sd_s.risky_count in
  (match lt_dec (S cnt) persistence_lmt with
   | Left ->
     { u_output = so; u_status = { iso_status = sd_s.iso_status;
       miscomp_status = Not_miscomparing; risky_count = (S
       sd_s.risky_count) } }
   | Right ->
     { u_output = so; u_status = { iso_status = Isolated; miscomp_status =
       Not_miscomparing; risky_count = (S sd_s.risky_count) } })

(** val build_single_u_data_healthy_case :
    (unit_output, unit_data) prod -> unit_id list -> unit_id list -> unit_data **)

let build_single_u_data_healthy_case x _ _ =
  { u_output = (fst x); u_status = { iso_status =
    (snd x).u_status.iso_status; miscomp_status = Not_miscomparing;
    risky_count = O } }

(** val incr_risky_count_and_update_iso_status_miscomp_case :
    (unit_output, unit_data) prod -> unit_id list -> unit_data **)

let incr_risky_count_and_update_iso_status_miscomp_case x _ =
  let sd_s = (snd x).u_status in
  let so = fst x in
  let cnt = sd_s.risky_count in
  (match lt_dec (S cnt) persistence_lmt with
   | Left ->
     { u_output = so; u_status = { iso_status = sd_s.iso_status;
       miscomp_status = Miscomparing; risky_count = (S sd_s.risky_count) } }
   | Right ->
     { u_output = so; u_status = { iso_status = Isolated; miscomp_status =
       Miscomparing; risky_count = (S sd_s.risky_count) } })

(** val incr_risky_count_and_update_iso_status_maybe_case :
    (unit_output, unit_data) prod -> unit_id list -> unit_data **)

let incr_risky_count_and_update_iso_status_maybe_case x _ =
  let sd_s = (snd x).u_status in
  let so = fst x in
  let cnt = sd_s.risky_count in
  (match lt_dec (S cnt) persistence_lmt with
   | Left ->
     { u_output = so; u_status = { iso_status = sd_s.iso_status;
       miscomp_status = Maybe_miscomparing; risky_count = (S
       sd_s.risky_count) } }
   | Right ->
     { u_output = so; u_status = { iso_status = Isolated; miscomp_status =
       Maybe_miscomparing; risky_count = (S sd_s.risky_count) } })

(** val update_u_data_frm_comb_elmnt_not_isoltd :
    (unit_output, unit_data) prod -> unit_id list -> unit_id list -> unit_data **)

let update_u_data_frm_comb_elmnt_not_isoltd x dev_lst maybe_lst =
  let hw_stat = (fst x).reading.hw_hlth in
  (match hw_stat with
   | Bad -> incr_risky_count_and_update_iso_status_bad_case x
   | Good ->
     (match in_dec u_id_eq_dec (fst x).uid dev_lst with
      | Left -> incr_risky_count_and_update_iso_status_miscomp_case x dev_lst
      | Right ->
        (match in_dec u_id_eq_dec (fst x).uid maybe_lst with
         | Left ->
           incr_risky_count_and_update_iso_status_maybe_case x maybe_lst
         | Right -> build_single_u_data_healthy_case x dev_lst maybe_lst)))

(** val update_u_data_frm_comb_elmnt :
    unit_id list -> unit_id list -> (unit_output, unit_data) prod -> unit_data **)

let update_u_data_frm_comb_elmnt dev_lst maybe_lst x =
  let stat = (snd x).u_status.iso_status in
  (match stat with
   | Isolated -> { u_output = (fst x); u_status = (snd x).u_status }
   | Not_isolated ->
     update_u_data_frm_comb_elmnt_not_isoltd x dev_lst maybe_lst)

(** val update_u_data_frm_comb_elmnt_for_map :
    unit_id list -> unit_id list -> (unit_output, unit_data) prod -> unit_data **)

let update_u_data_frm_comb_elmnt_for_map =
  update_u_data_frm_comb_elmnt

(** val dev_uid_lst :
    unit_id list -> unit_output list -> unit_data list -> unit_id list **)

let dev_uid_lst u_ids0 input ud_lst =
  let dev_outs = miscomparing_lst u_ids0 input ud_lst in
  map (fun y -> y.uid) dev_outs

(** val maybe_uid_lst :
    unit_id list -> unit_output list -> unit_data list -> unit_id list **)

let maybe_uid_lst u_ids0 input ud_lst =
  let maybe_lst = maybe_miscomparing_lst u_ids0 input ud_lst in
  map (fun y -> y.uid) maybe_lst

(** val build_updated_u_data_lst :
    unit_id list -> unit_output list -> unit_data list -> unit_data list **)

let build_updated_u_data_lst u_ids0 input ud_lst =
  let temp =
    combine_lists (fun a -> a.uid) (fun a -> a.u_output.uid) u_ids0 input
      ud_lst
  in
  let dev_uids = dev_uid_lst u_ids0 input ud_lst in
  let maybe_uids = maybe_uid_lst u_ids0 input ud_lst in
  map (update_u_data_frm_comb_elmnt_for_map dev_uids maybe_uids) temp

(** val build_prime_switched_vs :
    voter_state -> unit_data list -> unit_data -> unit_data list ->
    voter_state **)

let build_prime_switched_vs _ new_p_ud_lst x _ =
  { u_data_lst = new_p_ud_lst; voter_output = x.u_output; voter_validity =
    Valid; output_age = O; presrvd_data = x }

(** val build_invalidated_vs :
    voter_state -> unit_data list -> voter_state **)

let build_invalidated_vs vs new_p_ud_lst =
  { u_data_lst = new_p_ud_lst; voter_output = vs.voter_output;
    voter_validity = Not_valid; output_age = invalid_age; presrvd_data =
    vs.presrvd_data }

(** val build_un_id_vs :
    voter_state -> unit_data list -> unit_output list -> voter_state **)

let build_un_id_vs vs new_p_ud_lst _ =
  { u_data_lst = new_p_ud_lst; voter_output = vs.voter_output;
    voter_validity = Un_id; output_age = (S vs.output_age); presrvd_data =
    vs.presrvd_data }

(** val voter_state_transition :
    voter_state -> unit_output list -> voter_state **)

let voter_state_transition vs all_unit_outputs =
  let new_p_ud_lst =
    build_updated_u_data_lst u_ids all_unit_outputs vs.u_data_lst
  in
  let non_isolated_unit_count = count_of_non_isolated_units new_p_ud_lst in
  (match le_dec min_required non_isolated_unit_count with
   | Left ->
     let f =
       find_data_of_a_given_unit_id u_ids new_p_ud_lst vs.voter_output.uid
     in
     (match f.u_status.iso_status with
      | Isolated ->
        let hl_list = healthy_unit_list new_p_ud_lst in
        (match hl_list with
         | [] -> build_un_id_vs vs new_p_ud_lst all_unit_outputs
         | x::xs ->
           build_prime_switched_vs vs
             (build_updated_u_data_lst u_ids all_unit_outputs vs.u_data_lst)
             x xs)
      | Not_isolated ->
        let c_s_r = f.u_output.reading.hw_hlth in
        let c_s_m = f.u_status.miscomp_status in
        (match c_s_m with
         | Not_miscomparing ->
           (match c_s_r with
            | Bad ->
              { u_data_lst = new_p_ud_lst; voter_output = vs.voter_output;
                voter_validity = Valid; output_age = (S vs.output_age);
                presrvd_data = vs.presrvd_data }
            | Good ->
              { u_data_lst = new_p_ud_lst; voter_output = f.u_output;
                voter_validity = Valid; output_age = O; presrvd_data = f })
         | _ ->
           { u_data_lst = new_p_ud_lst; voter_output = vs.voter_output;
             voter_validity = Valid; output_age = (S vs.output_age);
             presrvd_data = vs.presrvd_data }))
   | Right -> build_invalidated_vs vs new_p_ud_lst)
