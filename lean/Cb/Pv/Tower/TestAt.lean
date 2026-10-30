-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tower/TestAt.lean: a proximity test on a group of oracle messages whose stages stand at any
form on the fold's input code, not only at the arranged form.

A test on a group begins with an arrangement without rounds (`arrOwn`, `arrRide`,
Cb/Pv/Tower/First.lean). In Cb/Pv/Tower/Test.lean the stages behind it stand at the batched form
carried along (`GShape.form`, Cb/Ld/LdGroupFold.lean), which is 0 on every row that holds no
member's row. The arrangement's reduction does not read the form. So the same reductions are laid
here with the stages at a form F that is a letter. What is asked in the place of the arrangement's
own theorem is named: that the arrangement is knowledge sound into the first stage's joint at F.
Definitions, statements and proofs.
Main names (Sh, Sb, sl, Z as in Cb/Pv/Tower/Test.lean; F : a form on `Sh.Cin.J`):
  `ArrOwnInto Sh Sb sl Z F`, `ArrRideInto Sh Sb sl Z F`: the two statements on the arrangement.
    `arrRideInto_of_own`: the second follows from the first. `arrOwnInto_form`: at the arranged
    form the first holds under `Sh.OK`.
  `testRideAt Sh Sb sl Z F T`: the arrangement, then the test with the data T at the form F, whose
    first fold's mask is in the input. `testRideAt_form`: at the arranged form it is `testRide`.
    `testRideAt_know` (under `ArrRideInto` and the conditions of all blocks of T), `_point`,
    `_local`, `_len`; `testRideAt_out`: under the pick the verifier puts out the last step's
    verdict where the stages arrive (`TowR.course`, Cb/Pv/Tower/Runs.lean).
  `testOwnAt Sh Sb sl Z F T`: the like for a test that begins without a rider: `_form`, `_know`,
    `_out`, `_point`, `_local`.
Limits: `ArrOwnInto` is shown here at the arranged form alone. No form F other than that is written
here, and nothing says that a form is any program's. Both makers give a reduction from the group's
joint (`EndR`, `EndO`): the round before a test and what is carried beside it are those of
Cb/Pv/Tower/Test.lean (`runRide`, `runOwn`), which read no form. The limits of the files named hold
here. Nothing on an honest prover.

-/
import Cb.Pv.Tower.RunsOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tower
open Iop Prob Hiop IOR

variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  (Sh : GShape G) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  (F : Slf E (BSt Sb Z) Sh.Cin.J)

/-! ## What is asked of the arrangement -/

/-- The arrangement is knowledge sound into the first stage's joint at the form F. -/
def ArrOwnInto : Prop :=
  (arrOwn Sh Sb sl Z).red.Know (firstInOwn Sb sl Z).on (firstInOwn Sb sl Z).relR
    (stageInOwn Sh.par F G.e).relR (fun _ _ w => Sh.rho.dn w) ()

/-- The same while the fold's mask is handed on. -/
def ArrRideInto : Prop :=
  (arrRide Sh Sb sl Z).red.Know (firstInRide Sh Sb sl Z).on (firstInRide Sh Sb sl Z).relR
    (stageInRide Sh.par F G.e).relR (fun _ _ w => Sh.rho.dn w) ()

theorem arrRideInto_of_own (h : ArrOwnInto Sh Sb sl Z F) : ArrRideInto Sh Sb sl Z F :=
  know_keepE Sh.par.Cw.nat (arrOwn Sh Sb sl Z) (firstInOwn Sb sl Z) (stageInOwn Sh.par F G.e)
    (fun _ _ w => Sh.rho.dn w) () h

theorem arrOwnInto_form (h : Sh.OK) : ArrOwnInto Sh Sb sl Z (Sh.form Sb sl Z) :=
  arrOwn_know Sh Sb sl Z h

/-! ## A test whose first fold's mask is in the input -/

section Ride
variable (T : TowR (wholeJ Sh.par F G.e) Sh.par.Cw.nat)

/-- The arrangement, then the test at the form F. -/
noncomputable def testRideAt : EndR (G.joint Sb sl Z) Sh.par.Cw.nat :=
  ⟨(arrRide Sh Sb sl Z).seq T.toEnd.R,
    IOR.extSeq (arrRide Sh Sb sl Z) T.toEnd.R (fun _ _ w => Sh.rho.dn w) T.toEnd.ext 0,
    Err.app (s := (arrRide Sh Sb sl Z).shape) () T.toEnd.e⟩

theorem testRideAt_form (T : TowR (wholeJ Sh.par (Sh.form Sb sl Z) G.e) Sh.par.Cw.nat) :
    testRideAt Sh Sb sl Z (Sh.form Sb sl Z) T = testRide Sh Sb sl Z T := rfl

theorem testRideAt_know (hA : ArrRideInto Sh Sb sl Z F) (hT : T.HypK) :
    (testRideAt Sh Sb sl Z F T).Know :=
  know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 hA (T.know hT) fun _ _ _ _ _ => trivial

theorem testRideAt_point : Nonempty (testRideAt Sh Sb sl Z F T).R.shape.IsPoint :=
  T.toEnd_point.elim fun p => ⟨Shape.IsPoint.append (s := (arrRide Sh Sb sl Z).shape) () p⟩

theorem testRideAt_local (h : Sh.OK) (hT : T.HypK) (hR : T.Reads) :
    (testRideAt Sh Sb sl Z F T).R.IsLocal :=
  (arrRide_local Sh Sb sl Z h).seq (T.toEnd_local hT hR)

theorem testRideAt_len : (testRideAt Sh Sb sl Z F T).R.shape.length = T.len := T.toEnd_len

/-- The arrangement changes no statement; the test goes on at the arranged word. -/
theorem testRideAt_out (h : T.Pick) (x : E × BSt Sb Z) (y : (G.C.ext.prod Sh.par.Cw.nat).Str)
    (τ : Tr (testRideAt Sh Sb sl Z F T).R.shape) :
    (testRideAt Sh Sb sl Z F T).R.out x y τ = T.course x ((arrRide Sh Sb sl Z).imp y ()) τ :=
  T.out_course h x ((arrRide Sh Sb sl Z).imp y ()) τ

end Ride

/-! ## A test that begins without a rider -/

section Own
variable (T : EndO (wholeJ Sh.par F G.e))

/-- The arrangement, then a test at the form F that begins at the fold's input code. -/
noncomputable def testOwnAt : EndO (G.joint Sb sl Z) :=
  ⟨(arrOwn Sh Sb sl Z).seq T.R,
    IOR.extSeq (arrOwn Sh Sb sl Z) T.R (fun _ _ w => Sh.rho.dn w) T.ext 0,
    Err.app (s := (arrOwn Sh Sb sl Z).shape) () T.e⟩

theorem testOwnAt_form (T : EndO (wholeJ Sh.par (Sh.form Sb sl Z) G.e)) :
    testOwnAt Sh Sb sl Z (Sh.form Sb sl Z) T = testOwn Sh Sb sl Z T := rfl

theorem testOwnAt_know (hA : ArrOwnInto Sh Sb sl Z F) (hT : T.Know) :
    (testOwnAt Sh Sb sl Z F T).Know :=
  know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 hA hT fun _ _ _ _ _ => trivial

theorem testOwnAt_out (x : E × BSt Sb Z) (y : G.C.ext.Str)
    (τ : Tr (testOwnAt Sh Sb sl Z F T).R.shape) :
    (testOwnAt Sh Sb sl Z F T).R.out x y τ = T.R.out x ((arrOwn Sh Sb sl Z).imp y ()) τ := rfl

theorem testOwnAt_point (h : Nonempty T.R.shape.IsPoint) :
    Nonempty (testOwnAt Sh Sb sl Z F T).R.shape.IsPoint :=
  h.elim fun p => ⟨Shape.IsPoint.append (s := (arrOwn Sh Sb sl Z).shape) () p⟩

theorem testOwnAt_local (h : Sh.OK) (hT : T.R.IsLocal) : (testOwnAt Sh Sb sl Z F T).R.IsLocal :=
  (arrOwn_local Sh Sb sl Z h).seq hT

end Own

end Cb.Pv.Tower

#print axioms Cb.Pv.Tower.arrRideInto_of_own
#print axioms Cb.Pv.Tower.testRideAt_know
#print axioms Cb.Pv.Tower.testRideAt_local
#print axioms Cb.Pv.Tower.testRideAt_out
#print axioms Cb.Pv.Tower.testOwnAt_know
#print axioms Cb.Pv.Tower.testOwnAt_local
