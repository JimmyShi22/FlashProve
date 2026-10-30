-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverCutFirst.lean: the hypothesis `s₁` of `falls_asks`
(Honest/Law/CoverAsks.lean), that the run has met no fall before the first chain's first round, from
the chain's written cut. `fellBy_start` (Honest/Law/CoverStart.lean) proves `s₁` if no fall stands
at a sub-protocol before the first one that has a round. Where the chain's cut into sub-protocols is
the library's written one (`hcut`, see Honest/Law/CoverCut.lean), which sub-protocols these are is a
closed fact on a written list: none of them stands at a fall's seat (`fallSeat`,
Honest/Law/CoverSeats.lean).

  1  `cut_first_yes`, `cut_first_control`   the closed statement, by `decide +kernel`, and a control
     that rejects
  2  `front_cut`   no sub-protocol before the first round stands at a fall's seat
  3  `fellBy_cut`   `s₁`, at any data of the chain whose walk starts as `fellBy_start` asks

Limits.
  * `hcut` is a hypothesis here. `members_head` (Honest/Law/CoverCutHead.lean) shows where the
    library proves it, under the hypothesis `P5J.AtMg`.
  * `hfs` (every fall stands at a fall's seat) is a hypothesis.
  * The closed statement is decided at one form of the written lists. The full size alone.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverCut
import Johnson.Desc.ProofFile.Honest.Law.CoverStart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open VerifiableInference.PlanWritten (cutOf cutFirstFull toldRounds)

variable {S Cl W Y : Type}

/-! ## 1 The closed statement -/

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- No row before the first row that has a round stands at a fall's seat. -/
theorem cut_first_yes : ((cutFirstFull.takeWhile fun r => r.2.2.1 == 0).all fun r =>
    !fallSeat P5J.At.links r.2.1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- A control: some row of the written cut stands at a fall's seat. -/
theorem cut_first_control : (cutFirstFull.all fun r => !fallSeat P5J.At.links r.2.1) = false := by
  decide +kernel

/-! ## 2 Before the first round -/

/-- No sub-protocol before the first one that has a round stands at a fall's seat. -/
theorem front_cut {all : List (Block S Cl)} (hcut : cutOf all = cutFirstFull) :
    ∀ d ∈ all.takeWhile (fun d => d.rounds.isEmpty), fallSeat P5J.At.links d.place = false := by
  intro d hd
  have e0 : (fun d : Block S Cl => d.rounds.isEmpty) =
      (fun r : String × Place × Nat × Nat × List (Nat × List Oracle) × List (Nat × Nat) =>
        r.2.2.1 == 0) ∘ fun b : Block S Cl =>
          (b.name, b.place, b.rounds.length, b.oracles.length, toldRounds b, b.before) := by
    funext c
    show c.rounds.isEmpty = (c.rounds.length == 0)
    cases c.rounds <;> rfl
  rw [e0] at hd
  have hm : (d.name, d.place, d.rounds.length, d.oracles.length, toldRounds d, d.before) ∈
      (cutOf all).takeWhile fun r => r.2.2.1 == 0 := by
    unfold cutOf
    rw [List.takeWhile_map]
    exact List.mem_map.2 ⟨d, hd, rfl⟩
  rw [hcut] at hm
  have t : (!fallSeat P5J.At.links d.place) = true := List.all_eq_true.1 cut_first_yes _ hm
  simpa using t

/-! ## 3 No fall before the first round -/

/-- The run has met no fall before the chain's first round. `hX`: as `fellBy_start` asks: a start of
`ChainProgress.start`, at some columns handed. -/
theorem fellBy_cut {all : List (Block S Cl)} (hcut : cutOf all = cutFirstFull)
    (fs : List (Fall S)) (hfs : ∀ f ∈ fs, fallSeat P5J.At.links f.place = true)
    (X : ChainAt S Cl W Y)
    (hX : ∀ a s₀, X.start = some a → X.s₀ = some s₀ →
      ∃ (m₀ : Option (Mid W Y)) (front : List OpenedColumn), m₀.isSome = true ∧
        ChainProgress.start X.lay all m₀ (some s₀) front = .ok a)
    (dr : List Fmt.Drawn) : fellBy all fs X 0 dr = false :=
  fellBy_start all fs X hX (fun d hd f hf e => by
    have h1 := hfs f hf
    rw [e, front_cut hcut d hd] at h1
    cases h1) dr

end ProofFile.Honest

#print axioms ProofFile.Honest.cut_first_yes
#print axioms ProofFile.Honest.cut_first_control
#print axioms ProofFile.Honest.front_cut
#print axioms ProofFile.Honest.fellBy_cut
