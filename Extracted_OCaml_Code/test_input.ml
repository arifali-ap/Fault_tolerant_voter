open Voter_state_transition
(*function to convert int to nat*)
let rec  int_to_nat n =
  if n<=0 then O else S (int_to_nat (n-1))

(*function to convert nat to int*)
let rec nat_to_int n=
  match n with 
    O->0|
    S x->1+nat_to_int x

(*intial voter_state*)
let sig_init:signal={
    val0=int_to_nat 0;
    hw_hlth=Good;
  }

let u_status_init:unit_status={
    iso_status =Not_isolated;
    miscomp_status=Not_miscomparing;
    risky_count=int_to_nat 0;
  }

let voter_state_init:voter_state=
  let ls=List.init
           5(fun i->{
               u_output={
                 reading=sig_init;
                 
                 uid=int_to_nat( i+1);
               };
               u_status=u_status_init;}
           )  in
  {
    u_data_lst=ls;
    
    voter_output={
        reading=sig_init;
        uid=(int_to_nat 1);
      };
    
    voter_validity=Valid;
    
    output_age=int_to_nat 0;
    
    presrvd_data=List.hd ls;
  }
(*end of initial voter_state*)



(*sample input *)
let sample_lst:unit_output list=[
    (*first value*)  {      
      reading={
        val0=int_to_nat 10;
        hw_hlth=Good;
      };
      uid=int_to_nat 1;
    };
    (*second value*) {      
      reading={
        val0=int_to_nat 9;
        hw_hlth=Good;
      };
      uid=int_to_nat 2;
    };
    (*third value*) {
        reading={
          val0=int_to_nat 11;
          hw_hlth=Bad;
        };
        uid=int_to_nat 3;
      };
    (*fourth value*)  {
        reading={
          val0=int_to_nat 8;
          hw_hlth=Good;
        };
        uid=int_to_nat 4;
      };
    (*fifth value*)    {
        reading={
          val0=int_to_nat 15;
          hw_hlth=Good;
        };
        uid=int_to_nat 5;
      };
  ]

(*end of sample input *)



(*function to print Validity status*)
let print_v_valid v =
  match v with 
    Valid->print_endline "Validity Status: Valid"|
    Un_id->print_endline "Validity Status: Un_id"|
    Not_valid->print_endline "Validity Status: Not_valid";;

(*function to print output age*)
let print_op_age n=
  Printf.printf "Output age: %d" n;;


(*function to print unit_output*)
let print_u_op up=
  Printf.printf "  Unit ID: %d \n"(nat_to_int up.uid) ;
  Printf.printf "  Signal Value: %d\n"(nat_to_int up.reading.val0);
  match up.reading.hw_hlth with 
    Good->print_endline "  Signal health: Good "|
    Bad->print_endline "  Signal health: Bad" ;;

(*function to print unit_data*)
let  print_unit_data (pvd:unit_data)=
  print_u_op (pvd.u_output);
  (*printing unit_status*)
  (match pvd.u_status.iso_status with
    Isolated->print_endline "  Isolation status: Isolated"|
    Not_isolated->print_endline "  Isolation status: Not Isolated" );
  
  (match pvd.u_status.miscomp_status with 
    Miscomparing->print_endline "  Miscomparing status: Miscomparing "|
    Not_miscomparing->print_endline "  Miscomparing status: Not miscomparing"|
    Maybe_miscomparing->print_endline "  Miscomparing status: Maybe miscomapring");
  
  Printf.printf "  Risky count: %d\n\n" (nat_to_int pvd.u_status.risky_count);;
 




(*function to print unit_data list*)
let  print_u_data_list (d:unit_data list)=
  List.iter print_unit_data d;;


(*function to print voter_state*)
let  print_voter_state (vs:voter_state)=
  print_v_valid vs.voter_validity;
  print_endline"";
  print_op_age (nat_to_int vs.output_age);
  print_endline"\n";
  print_endline"Voter output: ";
  print_u_op vs.voter_output;
  print_endline "\nPreserved Data for next cycle: ";
  print_unit_data vs.presrvd_data;
  print_endline "\nUpdated Unit Data List";
  print_u_data_list vs.u_data_lst ;;



let()=
  (*printing input voter_state*)
  print_endline"Input Voter State\n";
  print_voter_state(voter_state_init);
  print_endline"\n ---------------------------------------------------------------------------------------------\n";
  
  (*printing output voter_state*)
  print_endline"Output Voter State";
  print_endline"";
  print_voter_state (voter_state_transition  voter_state_init sample_lst);
