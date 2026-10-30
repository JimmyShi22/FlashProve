-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/OptsWhereLaid.lean: two of the seven named tests of `At.OptsOk`
(Johnson/P5J/OptsOk.lean), in the letters of the law that asks them: `At.whereB` and `At.laidB`.
Definitions and statements with their proofs.

THE TESTS' TEXTS ARE SPELLED OUT (`whereText`, `laidText`): the file that names them stands
outside the ground of this file. `At.whereB Zp = whereText Zp` and `At.laidB Zp = laidText Zp` are
`whereB_is` and `laidB_is` (Johnson/Goal/Skeleton/CondsOfLaid.lean): two lines by rfl.
(Where this and lean/THEOREM.md differ, the page holds.)


  `from_written`: where the first chain's entries are the written ones, the step "M.0.call" of the
    table of stretches is there and 48,270 rounds stand in front of it: by the laws on that table
    (`front_of_base`, `rounds_before_call`, Johnson/Desc/First/Driver/CutFront.lean), `pubBy_cuts`
    and two facts that Lean's kernel has walked (`base_not_before`, `base_not_after`): others' all.
  `three_written`: (W) and (N) at once: the written list has a round at 48,270 + i just where i <
    23.
  `where_written`; `whereB_at_name`: **(Z): NO PIN IS ASKED**: from the scope and `LaidAt` alone:
    the entries are the written ones where the value is laid (`plans_written`).
  `laidB_at_name`: (Z): under hy, an accept of `madePinnedAt`: a call of `laid_in_scope`
    (Johnson/HB/LLHARD/PlanInScope.lean), which gives the layout itself (`LFull`).
Nothing is evaluated here.

Limits. Nothing on soundness.
-/
import Johnson.P5T.EndsWritten
import Johnson.HB.LLHARD.PlanInScope
import Johnson.Desc.K14.Law.StartWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open Johnson.G
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (front_of_base rounds_before_call)
open VerifiableInference.PlanWritten (madePinnedAt plans_written)
open Desc.K14.Law (pubBy_cuts base_not_before base_not_after)

/-- The text of the named test `At.whereB` (Johnson/P5J/OptsOk.lean), to the letter. -/
def whereText (Zp : ProofFile.Pub) : Bool :=
  (VerifiableInference.Desc.K13.fromOf? Zp).isSome &&
    (List.range 3).all fun i => (Zp.plans.1[VerifiableInference.Desc.K13.fromOf Zp + i]?).isSome

/-- The text of the named test `At.laidB` (Johnson/P5J/LettersAt2.lean), to the letter. -/
def laidText (Zp : ProofFile.Pub) : Bool :=
  (VerifiableInference.Desc.K12.Door.laidAtCodes (At.cs Zp) Zp.made.proof.1).isSome

/-- Where the first chain's entries are the written ones, the members' batching begins at round
48,270. -/
theorem from_written {made : ByteArray → ByteArray → ByteArray → Except String OfPlan.Made}
    {st : ProofFile.Starts} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pubBy made st pol lay KL = .ok Z)
    (p1 : Z.plans.1 = dryProofFull.1.map (·.1.entry)) :
    VerifiableInference.Desc.K13.fromOf? Z = some 48270 := by
  have hc := pubBy_cuts h
  rw [p1] at hc
  obtain ⟨front, pl, q, b, e, hN, ht⟩ := front_of_base dryProofFull.1 (·.1.entry) hc 48268
    base_not_before base_not_after
  obtain ⟨a1, a2⟩ := rounds_before_call hN pl q b
  unfold VerifiableInference.Desc.K13.fromOf? ProofFile.Pub.roundsBefore? ProofFile.Pub.roundsBefore
  rw [e, if_pos a1, a2, ht]

/-- The written list has the three rounds from 48,270 on; it has none at 48,293. -/
theorem three_written (i : ℕ) :
    ((dryProofFull.1.map (·.1.entry))[48270 + i]?).isSome = decide (i < 23) := by
  have hl : (dryProofFull.1.map (·.1.entry)).length = 48293 := by
    rw [List.length_map]
    exact congrArg (·.1) dryProofFull_length
  by_cases hi : i < 23
  · rw [List.getElem?_eq_getElem (by rw [hl]; omega), decide_eq_true hi]
    rfl
  · rw [List.getElem?_eq_none (by rw [hl]; omega), decide_eq_false hi]
    rfl

/-- The test accepts wherever the first chain's entries are the written ones. -/
theorem where_written {made : ByteArray → ByteArray → ByteArray → Except String OfPlan.Made}
    {st : ProofFile.Starts} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pubBy made st pol lay KL = .ok Z)
    (p1 : Z.plans.1 = dryProofFull.1.map (·.1.entry)) : whereText Z = true := by
  have f := from_written h p1
  have g : VerifiableInference.Desc.K13.fromOf Z = 48270 := by
    unfold VerifiableInference.Desc.K13.fromOf
    rw [f]
    rfl
  unfold whereText
  rw [f, g, p1, Bool.and_eq_true]
  refine ⟨rfl, List.all_eq_true.2 fun i hi => ?_⟩
  rw [three_written, decide_eq_true]
  have := List.mem_range.1 hi
  omega

section
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **`At.whereB`, in the letters of the law that asks it: NO PREMISE BESIDE THE THREE.** -/
theorem whereB_at_name (hZ : VerifierAndGoals.InScope Z = true) (_hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) : whereText Zp = true := by
  obtain ⟨Z', hZ', p1, _, _⟩ := plans_written hZ (P5T.laid_of_at L)
  obtain rfl : Z' = Zp := Except.ok.inj (hZ'.symm.trans L.pub)
  exact where_written hZ' p1

/-- **`At.laidB`, in the letters of the law that asks it.** hy: an accept of the verifier's test on
the sizes, the lists of rounds and the sendings. -/
theorem laidB_at_name (hZ : VerifierAndGoals.InScope Z = true) (_hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    laidText Zp = true := by
  show (VerifiableInference.Desc.K12.Door.laidAtCodes Zp.first.codes Zp.made.proof.1).isSome = true
  rw [VerifiableInference.Desc.K13.Law.laid_in_scope hZ L.pub hy]
  rfl

end

end P5J

#print axioms P5J.from_written
#print axioms P5J.three_written
#print axioms P5J.where_written
#print axioms P5J.whereB_at_name
#print axioms P5J.laidB_at_name
