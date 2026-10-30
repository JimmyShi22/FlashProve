-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPartLin.lean: for the toy object: the second part of the object (the test for linear
constraints at one instance, over what weights-formedness leaves) with the standard plan, for any
data W of preamble and test (`LdOWf`, Cb/Obj/LdObjectWf.lean): its bundle of hypotheses from the
premises of `Spec.ldPartLin_hyp`: `D.Hyp` of the plan's data, `Sn.OK` of the senders, and conditions
on codes, on places and on numbers.

The object (`LdObj`, Cb/Obj/LdObject.lean) is one record with a configuration and, over it, the
sub-protocols of the proof system, as five terms.
Definitions, statements (`Cb.Spec.ldPartLin_facts`, `Cb.Spec.ldPartLin_hyp`) and proofs. A tool for
guards against empty theorems; no parameter of a protocol.
Cb/Obj/LdObjectParts.lean cuts the record `LdObjP` (Cb/Obj/LdObjectPlan.lean), from which an object
is made, and its hypotheses into five parts; its second part (`PLin A`, `Ln.Hyp`) is about the test
over `A.W.O`, which is read off the preamble. The standard plan over a variable test is
Cb/Obj/LdObjectPartPlan.lean's (`StdPO O P`); here it is taken at O := `W.O`.

Main names:
  `W.stdPO nAt posAll ..`: the plan's data at `W.O`: "rest" := the mask part of the tensor row as a
    form on named places (`W.restF nAt`, Cb/Obj/LdObjectWfRest.lean); "more" := the filed rows as
    forms on named places (`W.rowsA nAt`, `W.tgA`, Cb/Obj/LdObjectWfRows.lean).
  `Spec.ldPartLin_facts`: the two facts on `W.O` that the plan asks, from "the named entries are
    entries of the messages, at different places" (`EntAt nAt`).
  `D.part Bw Sn εf dT dT₀ : PLin ⟨W, Bw⟩`, for `D : StdPO W.O P`.
  `Spec.ldPartLin_hyp`: for non-empty `Fin W.Cf.C₀.n` and P: `D.Hyp`, `Sn.OK`, the bound εf on the
    fold's bad points, distinct places (`W.O.py` injective), and the numbers: tb₂ + tb₃ ≤ what each
    message of the preamble bears; tb₂ ≤ tW; tb₁ ≤ tU; tb₁ + tb₂ ≤ tO ⇒ `(D.part ..).Hyp`.

Limits: this file does not say that the conditions can be met. It builds no senders: `Sn` is a
parameter and `Sn.OK` a premise.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectParts
import Cb.Obj.LdObjectPartPlanProofs
import Cb.Obj.LdObjectWfRowsProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The plan's data over what weights-formedness leaves. -/
@[reducible] def LdOWf.stdPO (W : LdOWf F E) {P : Type} [Fintype P]
    (nAt : W.P.N → W.P.S.Ent) (posAll : ∀ o : W.O.toC.S.O, P → (W.O.toC.S.om o).P)
    (er tb₁ tb₂ tb₃ d bad L2 Lc : ℕ) : StdPO W.O P :=
  { slR := W.restF nAt, BM := W.RB, rowsA := W.rowsA nAt, tgA := W.tgA, posAll := posAll, er := er,
    tb₁ := tb₁, tb₂ := tb₂, tb₃ := tb₃, d := d, bad := bad, L2 := L2, Lc := Lc }

/-- The second part of the object. -/
def StdPO.part {W : LdOWf F E} [Nonempty (Fin W.Cf.C₀.n)] {P : Type} [Fintype P]
    [Nonempty P] (D : StdPO W.O P) (Bw : W.P.Blk) (Sn : W.O.toC.P.Snd) (εf : ℕ)
    (dT : W.O.toC.P.W0) (dT₀ : W.O.P.W0) : PLin (⟨W, Bw⟩ : PWf F E) :=
  { εf := εf, Sn := Sn, q₀ := fun U => U = ∅, dT := dT, dT₀ := dT₀, p := D.pl,
    TP := D.T, b' := fun _ => D.tb₃ }

end

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The two facts on `W.O`. -/
def ldPartLin_facts : Prop :=
  ∀ (W : LdOWf F E) (nAt : W.P.N → W.P.S.Ent), W.P.EntAt nAt →
    (∀ cl m, W.O.restM cl m = (W.restF nAt).val cl (W.O.S.ents m)) ∧
    ∀ cl m, W.O.more cl m ↔ rowsHold (W.rowsA nAt) W.tgA cl (W.O.S.ents m)

/-- The bundle of the second part. -/
def ldPartLin_hyp : Prop :=
  ∀ (W : LdOWf F E) [Nonempty (Fin W.Cf.C₀.n)] (P : Type) [Fintype P] [Nonempty P] (D : StdPO W.O P)
      (Bw : W.P.Blk) (Sn : W.O.toC.P.Snd) (εf : ℕ) (dT : W.O.toC.P.W0) (dT₀ : W.O.P.W0),
    D.Hyp → Sn.OK → W.O.toC.P.FoldErr W.O.on0 εf → Function.Injective W.O.py →
    (∀ a, D.tb₂ + D.tb₃ ≤ Bw.t a) → (∀ a, D.tb₂ ≤ Sn.tW a) → (∀ a, D.tb₁ ≤ Sn.tU a) →
    (∀ a, D.tb₁ + D.tb₂ ≤ Sn.tO a) → (D.part Bw Sn εf dT dT₀).Hyp

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldPartLin_facts : Spec.ldPartLin_facts F E := fun W nAt h =>
  ⟨fun cl m => (ldOWfRest_val F E W nAt h cl m).symm, fun cl m => ldOWfRows_more F E W nAt h cl m⟩

theorem ldPartLin_hyp : Spec.ldPartLin_hyp F E := by
  intro W _ P _ _ D Bw Sn εf dT dT₀ h hS hF hpy hA hW hU hO
  obtain ⟨t1, t2, t3⟩ := stdPO_three h
  exact
    { snd := hS, q₀e := rfl, fold := hF, pyInj := hpy, rest := stdPO_rest h,
      saysA := t1, left := t2, leftQ := t3
      needA := fun a =>
        le_of_eq_of_le (stdPO_needA a) (hA a),
          needW := fun a => le_of_eq_of_le (stdPO_needW a) (hW a)
      needU := fun a =>
        le_of_eq_of_le (stdPO_needU a) (hU a),
          needO := fun a => le_of_eq_of_le (stdPO_needO a) (hO a)
      test₁ := stdPO_d1 h, test₂ := stdPO_d2 h }

end
end Cb
