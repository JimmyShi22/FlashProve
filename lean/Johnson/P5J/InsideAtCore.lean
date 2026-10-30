-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/InsideAtCore.lean (kind K9): THE FIELDS inSeg · inTot OF WHAT IS LEFT OF A LINK's «REST»
    (`CoreLeft`, Johnson/Desc/First/Link/Law/CoreLeft.lean), AT THE CLOSED CONSTANT's LETTERS, AT
    ALL 25 LINKS, FROM THE HEAD ALONE; AND inRun FROM THE HEAD, «A PART IS THERE» BEHIND THE
    BATCHING AND THE SORT's OWN «EVERY RUN KEEPS insF». Closed facts by
the kernel and theorems: the last join of a row of payers.

THE STONES, EACH ANOTHER FILE's. `inTot_of_promise` | `inRun_of_keeps` (InsideOfPromise.lean |
    InRunOfKeeps.lean under Johnson/Desc/First/Link/Law/) · FoldFacts at the written list:
    `AtMgA.fold_full` (MaskLettersAtMg.lean beside this file; over `atMgR_rch_of_head`) ·
    the closed sentence: `AtMgA.planFits_at` (PlanFitsAtHead.lean) ·
the open ledger's two numbers: `AtMgA.slots_at` and `AtMgA.ns_is`
    (SlotsAtHead.lean) · «a part is there» in front of the batching:
    `part_at_batch_all` (Johnson/LPFE1R/PartAtBatch.lean), carried to these letters as
    `part_at` (Johnson/LPFE1R/HitemsAtConst.lean) carries it.

What is said. h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x; m < 25; z a public part; kAt m := batchAt
    fullLinks At.ps m.
  `threeB`, `three_full` [BY THE KERNEL]: at each m < 25 and i < 3 the list of places has at kAt m +
      i a place of segment m, of piece ≤ 11 + 2 · shift; that number is one of the 75 borders and ≤
      353. `three_off` [NEGATIVE]: at i = 3 the test threeB says no at every m.
  `AtMgA.inside_at`: **i < 3 ⊢ ∀ b, onTR … (kAt m + i) b → ∀ a, atS.get? b.1 = some a → InsideAt
      h.𝔇.cs h.𝔇.ms (h.𝔇.N.group m) a.**
  `AtMgA.inTot_at`: **THE FIELD inTot, TO THE LETTER** (i = 2). `AtMgA.inSeg_at`: **THE FIELD
      inSeg** (i = 0). `AtMgA.inRun_at`: **THE FIELD inRun** (i = 1), under hq and Ahs1.

Limits. AtMgA («the head») is a premise: WITH THE FOURTEEN ENTRY TESTS; its options are paid at the
    top by others. AT THE SECOND HASH FUNCTION. THE FULL SIZE ALONE. «To the letter»: by eye
    against a CoreLeft.lean not held against the shipped one: that file is not imported: the call
    that fills `CoreLeft` is the check. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.InsideOfPromise
import Johnson.P5J.MaskLettersAtMg
import Johnson.P5J.PlanFitsAtHead
import Johnson.P5J.SlotsAtHead
import Johnson.P5J.K09List
import Johnson.LPFE1R.PartAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Model OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit Link Chain)
open VerifiableInference.Desc.First (S ModelPart Numbers FoldFacts shiftAt momentAt)
open VerifiableInference.Desc.LinkJoin (onTR batchAt nsZ insF AtAfter inTot_of_promise
  inSeg_of_promise inRun_of_promise part_at_batch_all)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K9 (atS segAt?)
open VerifiableInference.Desc.K13.Law (LFull)
open _root_.Run _root_.Run.PQ

/-- At link m, i borders behind the batching's own: a place of segment m, early enough; the number
is one of the 75 borders and at most 353. -/
def threeB (m i : ℕ) : Bool :=
  match At.ps[batchAt fullLinks At.ps m + i]? with
  | some p => p.link == some m && decide (p.piece ≤ 11 + 2 * shiftAt fullLinks m) &&
      P5T.bordersW.contains (batchAt fullLinks At.ps m + i) &&
      decide (batchAt fullLinks At.ps m + i ≤ 353)
  | none => false

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **(W) So at all 25 links, at the three borders.** -/
theorem three_full : ((List.range 25).all fun m => (List.range 3).all fun i => threeB m i) = true :=
    by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **(N)** One border further the test says no at every link. -/
theorem three_off : ((List.range 25).any fun m => threeB m 3) = false := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- **InsideAt AT THE THREE BORDERS OF EVERY LINK, FROM THE HEAD ALONE.** -/
theorem AtMgA.inside_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25) {i : ℕ}
    (hi : i < 3) (z : ProofFile.InstPub) :
    ∀ b : S × (Frame.E FrK).Str, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z,
        s))
        (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
        (batchAt fullLinks At.ps m + i) b →
      ∀ a, atS.get? b.1 = some a → InsideAt h.𝔇.cs h.𝔇.ms (h.𝔇.N.group m) a := by
  have hB := List.all_eq_true.1 (List.all_eq_true.1 three_full m (List.mem_range.2 hm)) i
    (List.mem_range.2 hi)
  unfold threeB at hB
  cases hp : At.ps[batchAt fullLinks At.ps m + i]? with
  | none =>
    rw [hp] at hB
    cases hB
  | some p =>
    rw [hp] at hB
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.contains_iff_mem] at hB
    obtain ⟨⟨⟨hl, hpc⟩, hk⟩, h353⟩ := hB
    exact inTot_of_promise (F := FrK) h.fold_full h.𝔇.N (mgAll h.𝔇 mgBase) h.𝔇.ms
      (nsZ Zp Zp.p.X.H.ns) z hp hl hpc (fun b hr => h.slots_at h353 ((z, b.1), b.2) hr)
      (h.ns_is hm) (h.planFits_at hk hp hl hm)

/-- **THE FIELD inTot.** -/
theorem AtMgA.inTot_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25)
    (z : ProofFile.InstPub) :
    ∀ b : S × (Frame.E FrK).Str, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z,
        s))
        (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
        (batchAt fullLinks At.ps m + 1 + 1) b →
      ∀ a, atS.get? b.1 = some a → InsideAt h.𝔇.cs h.𝔇.ms (h.𝔇.N.group m) a :=
  h.inside_at hm (i := 2) (by omega) z

/-- A part is there in front of the batching, at these letters. -/
theorem AtMgA.part_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25)
    (z : ProofFile.InstPub) :
    ∀ b : S × (Frame.E FrK).Str, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z,
        s))
        (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
        (batchAt fullLinks At.ps m) b → (atS.get? b.1).isSome = true := by
  intro b hb
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e : IM.linksW = fullLinks := LPFK9.linksW_full
  have ep : IM.placesW = At.ps := by
    unfold IM.placesW At.ps
    rw [e]
  have H := part_at_batch_all (N := h.𝔇.N) (Mg := mgAll h.𝔇 mgBase) (z := z)
    (Rz := VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z) h.scope h.reads O
    (fun j c hc => list_rchIs h z j c hc) hm (a := b)
  rw [ep, e] at H
  exact H hb

/-- **THE FIELD inSeg.** -/
theorem AtMgA.inSeg_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25)
    (z : ProofFile.InstPub) :
    ∀ b : S × (Frame.E FrK).Str, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z,
        s))
        (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
        (batchAt fullLinks At.ps m) b →
      ∀ y, segAt? b.1 = some y → InsideAt h.𝔇.cs h.𝔇.ms (h.𝔇.N.group m) y := by
  intro b hb y hy
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (h.part_front hm z b hb)
  obtain rfl : a = y :=
    Option.some.inj ((VerifiableInference.Desc.K9.segAt_of_atS b.1 a ha).symm.trans hy)
  exact h.inside_at hm (i := 0) (by omega) z b hb a ha

/-- **THE FIELD inRun**, under the sort's «every run behind the batching keeps insF» and Ahs1. -/
theorem AtMgA.inRun_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25)
    (z : ProofFile.InstPub) (L : Link S ProofFile.Cl)
    (hq : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → insF e₁ = insF e)
    (Ahs1 : ∀ b : S × (Frame.E FrK).Str, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps
        (fun s : S => (z, s)) (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
        (batchAt fullLinks At.ps m + 1) b → (atS.get? b.1).isSome = true) :
    ∀ b : S × (Frame.E FrK).Str, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z,
        s))
        (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z)
        (batchAt fullLinks At.ps m + 1) b →
      ∀ s' a, L.runBehind b.1 = .ok s' → atS.get? s' = some a →
        InsideAt h.𝔇.cs h.𝔇.ms (h.𝔇.N.group m) a :=
  VerifiableInference.Desc.LinkJoin.inRun_of_keeps h.𝔇.cs h.𝔇.ms (h.𝔇.N.group m) L hq _ Ahs1
    (h.inside_at hm (i := 1) (by omega) z)

end P5J

#print axioms P5J.three_full
#print axioms P5J.three_off
#print axioms P5J.AtMgA.inside_at
#print axioms P5J.AtMgA.inTot_at
#print axioms P5J.AtMgA.part_front
#print axioms P5J.AtMgA.inSeg_at
#print axioms P5J.AtMgA.inRun_at
