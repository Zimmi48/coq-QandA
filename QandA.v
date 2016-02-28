Require Import Coq.Lists.List.
Require Import Io.All.
Require Import Io.System.All.
Require Import ListString.All.

Import ListNotations.
Import C.Notations.

(* not using notation do! because of indentation with Emacs *)
Definition QandA (_ : list LString.t) : (C.t System.effect unit) :=
  let! _ := System.log (LString.s "Player 1: Enter a question") in
  let! q := System.read_line in
  let! _ := System.log (LString.s "Player 1: Enter the answer") in
  let! a := System.read_line in
  match (q, a) with
  | (Some q, Some a) =>
    let! _ := System.system (LString.s "clear") in
    let! _ :=
       System.log (LString.s "Player 2: Press enter to start") in
    let! _ := System.read_line in
    let! _ :=
       System.log (q ++ LString.s " (you have ten seconds to give the answer)") in
    let! a' :=
       choose System.read_line
              (let! _ := System.system (LString.s "sleep 10") in
               ret None) in
    match a' with
    | Some a' =>
      if LString.eqb a a'
      then System.log (LString.s "Good answer!")
      else System.log (LString.s "Bad answer!")
    | None => System.log (LString.s "Too late!")
    end
  | _ => ret tt
  end.

Definition QandA_goodAnswer
           (argv : list LString.t) (q a r : LString.t)
  : (Run.t (QandA argv) tt).
Proof.
  eapply Run.Let.
  exact (Run.log_ok (LString.s "Player 1: Enter a question")).
  eapply Run.Let.
  exact (Run.read_line_ok q).
  eapply Run.Let.
  exact (Run.log_ok (LString.s "Player 1: Enter the answer")).
  eapply Run.Let.
  exact (Run.read_line_ok a).
  eapply Run.Let.
  exact (Run.system_ok _ true).
  eapply Run.Let.
  exact (Run.log_ok (LString.s "Player 2: Press enter to start")).
  eapply Run.Let.
  exact (Run.read_line_ok r).
  eapply Run.Let.
  exact (Run.log_ok (q ++ LString.s " (you have ten seconds to give the answer)")).
  eapply Run.Let. {
    eapply Run.ChooseLeft.
    exact (Run.read_line_ok a).
  }
  change (Run.t (if LString.eqb a a
                 then log (LString.s "Good answer!")
                 else log (LString.s "Bad answer!")) tt).
  rewrite LString.eqb_same_is_eq.
  exact (Run.log_ok (LString.s "Good answer!")).
Defined.

Definition QandA_badAnswer
           (argv : list LString.t)
           (q a a' r : LString.t) (H : a <> a')
  : (Run.t (QandA argv) tt).
Proof.
  eapply Run.Let.
  exact (Run.log_ok (LString.s "Player 1: Enter a question")).
  eapply Run.Let.
  exact (Run.read_line_ok q).
  eapply Run.Let.
  exact (Run.log_ok (LString.s "Player 1: Enter the answer")).
  eapply Run.Let.
  exact (Run.read_line_ok a).
  eapply Run.Let.
  exact (Run.system_ok _ true).
  eapply Run.Let.
  exact (Run.log_ok (LString.s "Player 2: Press enter to start")).
  eapply Run.Let.
  exact (Run.read_line_ok r).
  eapply Run.Let.
  exact (Run.log_ok (q ++ LString.s " (you have ten seconds to give the answer)")).
  eapply Run.Let. {
    eapply Run.ChooseLeft.
    exact (Run.read_line_ok a').
  }
  change (Run.t (if LString.eqb a a'
                 then log (LString.s "Good answer!")
                 else log (LString.s "Bad answer!")) tt).
  case_eq (LString.eqb a a'). {
    intros H2; exfalso.
    now apply LString.eqb_implies_eq in H2.
  }
  intros _.
  exact (Run.log_ok (LString.s "Bad answer!")).
Defined.

Definition main := Extraction.launch QandA.
Extraction "QandA" main.