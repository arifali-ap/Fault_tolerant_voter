rm -f ./Extracted_OCaml_Code/voter_state_transition.*
rm -f ./Extracted_OCaml_Code/output
make clean
coq_makefile -f _CoqProject -o Makefile
make
