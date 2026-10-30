-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/YesFacts.lean: **FOUR CLAUSES OF CoreFacts (Johnson/Desc/Sound/SeamFacts.lean) FROM A YES OF THE PROXIMITY TEST's DECISION AND TWO TESTS ON THE PLAN.** Statements; each proof is K12's files' own lemmas, at the DECISION's yes (their forms and others stand at
a piece over the kind's own record; the ledger's pieces stand over a pair, and a yes of such a piece is a yes of the decision: held_decides, NineAt.lean). NO NEW MATHEMATICS.
  stageJ_of_joh     johOk π r · the plan's first stage is a ⟹ (sgOf a).StageJ (rad (sgOf a)), rad := r at the stage: the first lines of payPub_of_joh.
  comb_of_decide    a yes of the decision ⟹ combineAt behind the beginning: combOk_of_decide · comb_of_ok (Johnson/Desc/K12/Law/Step8.lean).
  lens_of_decide    a yes · π.early · the block's test on the plan ⟹ the layout's k | h are the first stage's: k12_lens · bat_front · first_sizes: the last lines of yes_lens.
  **yes_facts**     the four together, at whatever the record fixes.
Limits. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.K12.Law.BatValsPayAt
import Johnson.Desc.K12.Law.Step8

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker
open OnBytes.Means
open Iop Prob _root_.Run Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.JointK
open H2K.Pub (sgOf johOk)
open H2K.First (Plain)

/-- The facts on codes at the first radius. -/
theorem stageJ_of_joh (p : P12) (r : Fmt.M1.Stage → ℕ) (rad : Sg → ℕ) (hr : ∀ s, rad s = r s.st)
    (hj : johOk p r = true) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : p.nums.stages = a :: rest) : (sgOf a).StageJ (rad (sgOf a)) := by
  unfold H2K.Pub.johOk H2K.Pub.johAll at hj
  rw [hs] at hj
  unfold H2K.Pub.johWalk at hj
  rw [H2K.Pub.ok_append, H2K.Pub.ok_tag, Bool.and_eq_true] at hj
  rw [hr]
  exact H2K.Pub.stageJ_of_L hj.1

/-- A yes of the decision holds combineAt behind the beginning. -/
theorem comb_of_decide (p : P12) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) (G0 : Group) (Ly : GroupLayout)
    (hG : t0.st.groups[t0.g]? = some G0) (hL : t0.st.layout t0.g = some Ly) :
    combineAt (begun t0.st t0.g G0) t0.g ⟨Ly, runRows t0.st G0⟩ = true :=
  comb_of_ok t0 (combOk_of_decide p t0 tE rs gs h) G0 Ly hG hL

/-- A yes of the decision: the layout's k | h are the first stage's. -/
theorem lens_of_decide (π : P12) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts π : Blk').decide t0 rs gs = .ok tE) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t0 a rest G0 Ly D) : Ly.k = (sgOf a).h + (sgOf a).g ∧ Ly.h = (sgOf a).h := by
  obtain ⟨first, rest', e, r, row, L, S', e1, hbat, h1, h2, _, _⟩ := k12_lens π he t0 tE _ _ hp h
  obtain ⟨G1, _, g2, _⟩ := bat_front _ _ _ _ _ _ _ hbat
  obtain ⟨rfl, _⟩ := List.cons.inj (e1.symm.trans hf.1)
  obtain rfl := Option.some.inj (g2.symm.trans hf.2.2.1)
  obtain ⟨_, _, hhk⟩ := first_sizes guardedProximityTestParts π hp first rest' e1
  refine ⟨?_, h2⟩
  show L.k = first.h + (first.k - first.h)
  rw [h1]
  omega

/-- **The four together.** -/
theorem yes_facts (π : P12) (r : Fmt.M1.Stage → ℕ) (rad : Sg → ℕ) (hr : ∀ s, rad s = r s.st)
    (hj : johOk π r = true) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts π : Blk').decide t0 rs gs = .ok tE) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t0 a rest G0 Ly D) :
    (sgOf a).StageJ (rad (sgOf a)) ∧
      combineAt (begun t0.st t0.g G0) t0.g ⟨Ly, runRows t0.st G0⟩ = true ∧
      Ly.k = (sgOf a).h + (sgOf a).g ∧ Ly.h = (sgOf a).h :=
  ⟨stageJ_of_joh π r rad hr hj a rest hf.1, comb_of_decide π t0 tE rs gs h G0 Ly hf.2.1 hf.2.2.1,
    lens_of_decide π he hp t0 tE rs gs h a rest G0 Ly D hf⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.stageJ_of_joh
#print axioms VerifiableInference.Desc.K12.Coin.comb_of_decide
#print axioms VerifiableInference.Desc.K12.Coin.lens_of_decide
#print axioms VerifiableInference.Desc.K12.Coin.yes_facts
