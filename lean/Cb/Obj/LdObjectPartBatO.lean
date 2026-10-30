-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPartBatO.lean: the fifth part of the object (the test for linear constraints at N
instances) over any "on", with the standard plan and tests: its data, and its bundle of hypotheses.

The object is one record with a configuration and, over it, the sub-protocols of the proof system,
as five terms. The test for linear constraints is the proximity test with claims that follows a
preamble.
Definitions, statements (`Cb.Spec.stdPO_needV`, `Cb.Spec.stdPO_partB`) and proofs.
The fifth part of Cb/Obj/LdObjectParts.lean is `PBat Cf on` with `Bt.Hyp`.
Cb/Obj/LdObjectPartBat.lean has it over an "on" that the standard test builds for itself. Here "on"
is any value (what a request's preamble leaves, read off its end), and plan and tests are those of
Cb/Obj/LdObjectPartPlan.lean (`D : StdPO on.ol P`), which serve the offline test too.

Main names:
  `D.partB ..`: the part. Its regime (`onB`) is that in which the index decodes with its record. Its
    senders are a parameter (`SnB`). Its first test (G_u's and Ω's families: the head of
    Cb/Obj/LdObjectPartPlan.lean) is run once, by the shared part; the second (all that is kept) and
    the third (all rows on what the preamble left) are run in every slot. Of the oracles left, its
    bound (`qaB`) allows nothing of the further oracles (`E₀`) and at most `ba a` long positions of
    the member a.
  `Spec.stdPO_partB`: `(D.partB ..).Hyp`, for non-empty `Fin Cf.C₀.n` and P, from: the index code
    has its distance, e' + eM is below it, the places are distinct; 1 ≤ N; `D.Hyp` (the two facts on
    "on": "rest" is a form on the entries left, "more" is finitely many rows; and conditions on
    codes); `SnB.OK` and `SnB.Apart`; the numbers: tb₂ + tb₃ ≤ ba a (a slot's own message that was
    left lies in the slot's second and third test); tb₂ ≤ `SnB.tW a`; tb₁ ≤ `SnB.tU a`;
    tb₁ + N · tb₂ ≤ `SnB.tO a`.

Notation: "on": a value of `LdOLd Cf` (Cb/Obj/LdObject.lean: what a preamble leaves and the data of
the test behind it); G_u, Ω (the head of Cb/Ld/LdLin.lean): the members `iU`, `iO` of two of the
three families that the test sends (`NU`, `NO`); `SnB.tW a`, `SnB.tU a`, `SnB.tO a`: natural numbers
(`LdLinP.Snd`, Cb/Ld/LdLin.lean: numbers of long positions that the encodings bear).

Limits: this file does not say that the hypotheses can be met together at a given "on". It says
nothing on splitting.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectPartPlanProofs
import Cb.Ld.LdLinClosePlanOneBProofs
import Cb.Obj.LdObjectPartBat
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace StdPO
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E}
  [Nonempty (Fin Cf.C₀.n)] {on : LdOLd Cf} {P : Type} [Fintype P] [Nonempty P] (D : StdPO on.ol P)

/-- The part. -/
@[reducible] def partB (N : ℕ) (SnB : on.ol.toC.P.Snd) (ba : on.ol.toC.Sa.O → ℕ)
    (x₀ : D.T.St₁ × on.ol.toC.S.Smp) (y₀ : (on.ol.toC.E₀.prod on.ol.toC.S.ext).Str)
    (d : on.ol.toC.P.W0) (d₀ : on.ol.P.W0) (ya : on.ol.toC.P.Ea.Str) : PBat Cf on where
  N := N
  onB := on.ol.onDec
  SnB := SnB
  qaB := on.ol.toC.Sa.qFam (E₀ := on.ol.toC.E₀) (fun U => U = ∅) ba
  εfB := 0
  dB := d
  dB₀ := d₀
  yB := ya
  pB := D.pl
  TB := D.T
  q₀B := fun U => U = ∅
  bB' := D.X.bOne N
  baB := ba
  tie' := fun _ _ _ _ => True
  cA' := (D.X.oneA (fun a => a.2.elim, ())).cA
  same' := (D.X.oneA (fun a => a.2.elim, ())).same
  x₀ := x₀
  y₀ := y₀
  QV' := D.X.oneV N (fun U => U = ∅) (fun a => a.2.elim, ())

end StdPO

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The four counts. -/
def stdPO_needV : Prop :=
  ∀ (O : LdOL F E) (P : Type) [Fintype P] [Nonempty P] (D : StdPO O P) (N : ℕ),
    (∀ a, D.T.D₁.need (D.T.D₂.needV N (fun a => O.toC.isSh a.1) (D.X.bOne N))
        (.inl (.inl (.inl a))) = D.tb₂ + D.tb₃) ∧
    (∀ a, D.T.D₁.need (D.T.D₂.needV N (fun a => O.toC.isSh a.1) (D.X.bOne N))
        (.inl (.inl (.inr a))) = D.tb₂) ∧
    (∀ a,
      D.T.D₁.need (D.T.D₂.needV N (fun a => O.toC.isSh a.1) (D.X.bOne N)) (.inl (.inr a)) = D.tb₁) ∧
    ∀ a, D.T.D₁.need (D.T.D₂.needV N (fun a => O.toC.isSh a.1) (D.X.bOne N)) (.inr a) =
      D.tb₁ + N * D.tb₂

/-- The bundle of hypotheses of the fifth part, over any "on". -/
def stdPO_partB : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (on : LdOLd Cf) (P : Type) [Fintype P] [Nonempty P]
      (D : StdPO on.ol P) (N : ℕ) (SnB : on.ol.toC.P.Snd) (ba : on.ol.toC.Sa.O → ℕ)
      (x₀ : D.T.St₁ × on.ol.toC.S.Smp) (y₀ : (on.ol.toC.E₀.prod on.ol.toC.S.ext).Str)
      (d : on.ol.toC.P.W0) (d₀ : on.ol.P.W0) (ya : on.ol.toC.P.Ea.Str),
    HasDist Cf.C₀.G Cf.C₀.d → on.e' + Cf.eM < Cf.C₀.d → Function.Injective on.py →
    1 ≤ N → D.Hyp → SnB.OK → SnB.Apart → (∀ a, D.tb₂ + D.tb₃ ≤ ba a) →
    (∀ a, D.tb₂ ≤ SnB.tW a) → (∀ a, D.tb₁ ≤ SnB.tU a) →
    (∀ a, D.tb₁ + N * D.tb₂ ≤ SnB.tO a) → (D.partB N SnB ba x₀ y₀ d d₀ ya).Hyp

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

omit [Fintype F] in
theorem stdPO_needV : Spec.stdPO_needV F E := by
  intro O P _ _ D N
  refine ⟨fun a => ?_, fun a => ?_, fun a => ?_, fun a => ?_⟩ <;>
    simp [LdRunD.need, LdRunD.needV, LdLinC.isSh, LdLinC.isU, LdLinC.isL, LdRowsD.bOne]

omit [Fintype F] in
theorem stdPO_partB : Spec.stdPO_partB F E := by
  intro Cf _ on P _ _ D N SnB ba x₀ y₀ d d₀ ya hd he hpy hN h hS hAp hA hW hU hO
  obtain ⟨t1, t2, t3⟩ := stdPO_three h
  obtain ⟨n1, n2, n3, n4⟩ := stdPO_needV F E on.ol P D N
  exact
    { sndB := hS
      apartB := hAp
      fitsB := (ldOB_fits F E on.ol).1
      foldB := ldOB_foldErr F E on.ol hd he
      pyInjB := hpy
      monoB := fun U V hVU hU' => ⟨Finset.eq_empty_of_forall_notMem fun i hi => by
          have h1 : i ∈ U.toLeft := Finset.mem_toLeft.2 (hVU (Finset.mem_toLeft.1 hi))
          rw [hU'.1] at h1
          exact absurd h1 (Finset.notMem_empty _),
            fun a => (cnt_mono fun _ hx => hVU hx).trans (hU'.2 a)⟩
      shared := stdPO_shared
      restB := stdPO_rest h
      saysAB := t1
      leftB := t2
      leftQB := fun V hV => ⟨(t3 V hV).1, fun a => ((t3 V hV).2 a).trans (by
        have h2 := need_le_needV D.X.run N hN (fun a => on.ol.toC.isSh a.1.1) (fun _ => 0) a
        have h3 : D.X.run.need (fun _ => 0) a = D.tb₃ := by simp [LdRunD.need]
        rw [h3] at h2
        exact h2)⟩
      leftKB := ldRowsOneB_kb E _ _ _ _ _ _ D.X _ N (fun _ hk => hk) (stdPO_d3 h)
      leftV :=
        ldRowsOneB_v E _ _ _ _ on.ol.toC D.pl _ _ _ D.X _ N _ (fun _ hk => hk) (stdPO_d3 h) rfl
      tieC := fun _ _ _ _ => trivial
      qaOK := fun _ hq => hq
      oneN := hN
      needNA := fun a => le_of_eq_of_le (n1 a) (hA a)
      needNW := fun a => le_of_eq_of_le (n2 a) (hW a)
      needNU := fun a => le_of_eq_of_le (n3 a) (hU a)
      needNO := fun a => le_of_eq_of_le (n4 a) (hO a)
      test₁B := stdPO_d1 h
      test₂B := stdPO_d2 h }

end
end Cb
