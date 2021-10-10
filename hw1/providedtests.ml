open Assert
open Hellocaml

(* These tests are provided by you -- they will NOT be graded *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let provided_tests : suite = [
  Test ("Student-Provided Tests For Problem 1-3", [
    ("case1", assert_eqf (fun () -> 42) prob3_ans );
    ("case2", assert_eqf (fun () -> 25) (prob3_case2 17) );
    ("case3", assert_eqf (fun () -> prob3_case3) 64);
  ]);

  Test ("Student-Provided Tests For Problem 4-4", [
    ("case1", assert_eqf (fun () -> interpret [] (Const 42L)) 42L);
    ("case2", assert_eqf (fun () -> interpret [("x", 42L)] (Var "x")) 42L);
    ("case3", (fun () -> try ignore (interpret [] (Var "x")); failwith "bad interpret" with Not_found -> ()));
    ("case4", assert_eqf (fun () -> interpret ctxt2 e3) (-63L));
  ]);

  Test ("Student-Provided Tests For Problem 4-5", [
      ("case1", assert_eqf (fun () -> optimize (Add (Const 42L, Const 42L))) (Const 84L));
      ("case2", assert_eqf (fun () -> optimize (Add (Const 42L, Const 0L))) (Const 42L));
      ("case3", assert_eqf (fun () -> optimize (Add (Const 0L, Const (-42L)))) (Const (-42L)));
      ("case4", assert_eqf (fun () -> optimize (Add (Var "x", Const 42L))) (Add (Var "x", Const 42L)));
      ("case5", assert_eqf (fun () -> optimize (Add (Const 42L, Var "x"))) (Add (Const 42L, Var "x")));
      ("case6", assert_eqf (fun () -> optimize (Add (Var "x", Const 0L))) (Var "x"));
      ("case7", assert_eqf (fun () -> optimize (Add (Const 0L, Var "x"))) (Var "x"));

      ("case8", assert_eqf (fun () -> optimize (Mult (Const 6L, Const 7L))) (Const 42L));
      ("case9", assert_eqf (fun () -> optimize (Mult (Var "x", Const 42L))) (Mult (Var "x", Const 42L)));
      ("case10", assert_eqf (fun () -> optimize (Mult (Const 42L, Var "x"))) (Mult (Const 42L, Var "x")));
      ("case11", assert_eqf (fun () -> optimize (Mult (Const 6L, (Add (Const 4L, Const 3L))))) (Const 42L));
      ("case12", assert_eqf (fun () -> optimize (Mult (Var "x", Const 0L))) (Const 0L));
      ("case13", assert_eqf (fun () -> optimize (Mult (Const 0L, Var "x"))) (Const 0L));
      ("case14", assert_eqf (fun () -> optimize (Mult (Var "x", Const 1L))) (Var "x"));
      ("case15", assert_eqf (fun () -> optimize (Mult (Const 1L, Var "x"))) (Var "x"));

      ("case16", assert_eqf (fun () -> optimize (Neg (Const 1L))) (Const (-1L)));
      ("case17", assert_eqf (fun () -> optimize (Neg (Neg (Var "x")))) (Var "x"));

      ("case18", assert_eqf (fun () -> optimize (Add (e3, Neg e3))) (Const 0L));
      ("case19", assert_eqf (fun () -> optimize (Mult ((Neg e3), (Neg e3)))) (Mult(e3, e3)));

      ("case20", assert_eqf (fun () -> optimize (Add (Const 3L, Mult (Const 0L, Var "x")))) (Const 3L));
    ]);

    Test ("Student-Provided Tests For Problem 5", [
        ("case1", assert_eqf (fun () -> compile (Const 42L)) [IPushC 42L]);
        ("case2", assert_eqf (fun () -> compile (Var "x")) [IPushV "x"]);
        ("case3", assert_eqf (fun () -> compile (Add (Var "x", Const 42L))) [IPushV "x"; IPushC 42L; IAdd]);
        ("case4", assert_eqf (fun () -> compile (Mult (Var "x", Const 42L))) [IPushV "x"; IPushC 42L; IMul]);
        ("case5", assert_eqf (fun () -> compile (Neg (Var "x"))) [IPushV "x"; INeg]);
        ("case6", assert_eq (interpret ctxt2 e3) (run ctxt2 (compile e3)));
        ("case7", assert_eq (interpret ctxt2 e2) (run ctxt2 (compile e2)));
        ("case8", assert_eq (interpret ctxt2 e1) (run ctxt2 (compile e1)));
        ("case8", assert_eq (interpret ctxt1 e2) (run ctxt1 (compile e2)));
        ("case8", assert_eq (interpret ctxt1 e1) (run ctxt1 (compile e1)));
      ]);
] 
