-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPartBatRe.lean: the plan's data for the fifth part of the object (the test for
linear constraints at N instances) over what the end of a request leaves: the test's data are read
off the final batching's last claim; and three standard oracle messages at the toy.

The object is one record with a configuration and, over it, the sub-protocols of the proof system,
as five terms. The test for linear constraints is the proximity test with claims that follows a
preamble.
Definitions, statements and proofs. A tool for guards against empty theorems; no parameter of a
protocol.
It puts together: Cb/Obj/LdObjectReqEnd.lean (`R : LdORE F E Kc`: the end of a request; `R.O`, the
test's data; at all states the mask part is a linear form in the entries left, and "more" says that
the rows of a fixed family hold), Cb/Obj/LdObjectPartPlan.lean (the standard plan over any test O),
Cb/Obj/LdObjectPartBatO.lean (the fifth part `PBat` over any "on", senders a parameter).



Generic, for any R with finitely many open rows:
  `R.stdPO posAll ..`: the plan's data at `R.O`: "rest" := the coefficients of the mask part
    (`R.restC`); "more" := the open rows, with the claim as state.
  `Spec.ldPartBatRe_facts`: the two facts on `R.O` that the plan asks: nothing assumed beyond the
    hypotheses of the statements and whatever the arguments hold as proofs.
At the toy:
  `ReToy.mU`, `ReToy.mO`, `ReToy.mOne`: standard oracle messages under the code of seven points and
    dimension 4 (Cb/Ld/LdRelToy7d4.lean: distance 4, radius 2: not below half the distance; hides
    three long positions). `mOne` holds the batching's three own entries and one name, and its pad.
  `mOne_inj`: its placing is injective.














Limits: this file says nothing on the moves in front of the end of the request, and does not say
that they end where R begins. On security: it evaluates no error and says no level of security.




Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectPartBatO
import Cb.Obj.LdObjectReqEndToy
import Cb.Obj.LdObjectOnBToy
import Cb.Obj.LdObjectOnBStd2
import Cb.Obj.LdObjectTerms
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The plan's data over what the end of a request leaves. -/
@[reducible] def LdORE.stdPO {F E Kc : Type} [Field F] [Fintype F] [Field E]
    [Fintype E] [Algebra F E] (R : LdORE F E Kc) [Fintype R.Bn] {P : Type} [Fintype P]
    (posAll : ∀ o : R.O.toC.S.O, P → (R.O.toC.S.om o).P) (er tb₁ tb₂ tb₃ d bad L2 Lc : ℕ) :
    StdPO R.O P :=
  { slR := R.restC, BM := R.Bn, rowsA := fun b cl n => R.sl b ((R.X.stOf cl).1.2 b) n,
    tgA := fun cl b => (R.X.stOf cl).1.1 b, posAll := posAll, er := er, tb₁ := tb₁, tb₂ := tb₂,
    tb₃ := tb₃, d := d, bad := bad, L2 := L2, Lc := Lc }

/-- States the two facts on `R.O`. -/
def Spec.ldPartBatRe_facts (F E Kc : Type) [Field F] [Fintype F] [Field E]
    [Fintype E] [Algebra F E] : Prop :=
  ∀ (R : LdORE F E Kc),
    (∀ cl m, R.O.restM cl m = Slf.val R.restC cl (R.O.S.ents m)) ∧
    ∀ cl m,
      R.O.more cl m ↔
      rowsHold (fun b cl n => R.sl b ((R.X.stOf cl).1.2 b) n)
        (fun cl b => (R.X.stOf cl).1.1 b) cl (R.O.S.ents m)

theorem ldPartBatRe_facts (F E Kc : Type) [Field F] [Fintype F] [Field E]
    [Fintype E] [Algebra F E] :
    Spec.ldPartBatRe_facts F E Kc := fun R =>
  ⟨(ldORE_rest F E Kc R).1, fun cl m => ldORE_more F E Kc R cl m⟩

namespace ReToy
open LdToy LdToy7 LdToy74

noncomputable section

@[reducible] def mU : StdM K P74 := toyStd74 (Fin C7.k) (Fin 2) plcK
@[reducible] def mO : StdM K P74 := toyStd74 Unit Empty fun _ e => e.elim

/-- The rows of the one oracle message of the instance: the batching's three own entries and one
name. -/
def Rw1 : Type := WBt ⊕ Unit

instance : Fintype Rw1 := inferInstanceAs (Fintype (WBt ⊕ Unit))
instance : DecidableEq Rw1 := Classical.decEq _

/-- An oracle message that holds the batching's three own entries and one name, and its pad. -/
@[reducible] def mOne : StdM K P74 := toyStd74 Rw1 Rw1 fun i j => decide (j = i)

theorem mOne_inj : Function.Injective (fun (i : Rw1) (j : Rw1) => decide (j = i)) := fun a b h => by
  have h1 := congrFun h a
  simpa using h1

end
end ReToy

open LdToy LdToy7 LdToy74 ReToy

end Cb
