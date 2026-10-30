-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K9x/LotsAtPure.lean: THE PREMISE `LotsCarry` OF THE ROAD "WHO PAYS K3RanAt"
(RanAtPure.lean) AT THE SEAT THAT IS SEATED (Johnson/Desc/ProofFile/OnlineDescription.lean: `pureSeat o Z`;
its lots: ProofFile/OnlineDescriptionBlocks.lean: `onlineFirstChainBlockTables Z`). Definitions, and theorems with their proofs.

  `QN Z`: the letter Q at a place a: K9's own `QK9 atS p` (CallsAtK9.lean) AT THE NUMBERS p THAT
    K9's LOT READS OFF THE PLAN AT a's LINK (`k9Where (k9Stretches Z) l = some p`).
  `k9MakerIs`: what K9's lot answers at a place is `K9.batch atS p` at these numbers.
  `KindsRun hd Z`: WHAT IS LEFT, ONE FIELD A LOT THAT STATES TYPED RUNS: K3 · K4 · K5 · K6 · K8 ·
    K11: every run of every block that the lot lays steps `CarriesFo S.fork? hd`.
  `makerOfPure`, `hearOfPure`: of the fifteen lots K9's alone gives a maker; these six alone lay
    blocks with typed runs.
  **`lotsCarryAtPure`**: `KindsRun hd Z`, and K9's law at hd, give
    `LotsCarry (CarriesFo S.fork? hd) (QN Z) (pureSeat o Z)`.
  PAID HERE: `k4Runs` (k4C_runsFo, Johnson/Desc/First/K4/CarriesFoK4.lean) · `k11RunsLook`,
    `k11RunsDigits` (run_carries_…, Johnson/Top/H0/MergeLaw/RunCarries.lean).

Limits. A frame's law: no error; nothing on soundness. A FIELD OF `KindsRun` RANGES OVER A LIST THAT
ITS LOT MAKES: where a lot lays nothing the field is idle (a place that then lacks a block makes
`onlineDescriptionFromPublicPart` refuse). The lookups' lot `K3Lot.lot` is ProofFile/Lot/K3.lean's. NO MEMBER.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.K9x.RanAtPure
import Johnson.Desc.First.K9x.CallsAtK9
import Johnson.Desc.First.K4.CarriesFoK4
import Johnson.Top.H0.MergeLaw.RunCarries
import Johnson.Desc.ProofFile.OnlineDescription

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S MakerMono k9_makerMono)
open ProofFile (Pub Lot Ground Cl PureSeat pureSeat onlineFirstChainBlockTables k9Ninth k9Where k9Stretches k9Links)

/-- The letter Q at a place: K9's own, at the numbers that its lot reads off the plan there. -/
def QN (Z : Pub) (a : Place) (s : S) (rs : List Fmt.RoundView) (t : S) (cls : List Cl) (e s' : S) : Prop :=
  ∃ l p, a.link = some l ∧ k9Where (k9Stretches Z) l = some p ∧ QK9 atS p s rs t cls e s'

theorem lookupMap {β : Type} (f : Nat → β) : ∀ (ls : List Nat) (l : Nat) (w : β),
    (ls.map fun l => (l, f l)).lookup l = some w → w = f l
  | [], _, _, h => nomatch h
  | x :: ls, l, w, h => by
    rw [List.map_cons, List.lookup_cons] at h
    split at h
    · rename_i e
      rw [eq_of_beq e]
      exact (Option.some.inj h).symm
    · exact lookupMap f ls l w h

/-- **What K9's lot answers at a place.** -/
theorem k9MakerIs (Z : Pub) (G : Ground) (a : Place) (mk : ProofFile.Gatherer → Block S Cl)
    (h : (k9Ninth Z).batch G a = some mk) :
    ∃ l p, a.link = some l ∧ k9Where (k9Stretches Z) l = some p ∧ mk = fun g => batch atS p g := by
  have h' : (match a.kind, a.link with
    | .K9, some l =>
      ((((k9Links (k9Stretches Z)).map fun l => (l, k9Where (k9Stretches Z) l)).lookup l).bind
        id).bind fun p =>
          if p.piece == a.piece then some fun g => batch atS p g else none
    | _, _ => none) = some mk := h
  split at h'
  · rename_i l _ hl
    obtain ⟨p, hp, h'⟩ := Option.bind_eq_some_iff.1 h'
    obtain ⟨w, hw, e⟩ := Option.bind_eq_some_iff.1 hp
    have ew := lookupMap (k9Where (k9Stretches Z)) _ l w hw
    split at h'
    · exact ⟨l, p, hl, by rw [← ew]; exact e, (Option.some.inj h').symm⟩
    · exact nomatch h'
  · exact nomatch h'

/-- **What is left: one field a lot that states typed runs.** -/
structure KindsRun (hd : S → Option Forest.Heard) (Z : Pub) : Prop where
  k3 : ∀ G, ∀ b ∈ (K3Lot.lot Z).hearC G, b.RunsStep (CarriesFo S.fork? hd)
  k4 : ∀ G, ∀ b ∈ (ProofFile.k4Lot Z).hearC G, b.RunsStep (CarriesFo S.fork? hd)
  k5 : ∀ G, ∀ b ∈ (H2K5.lotN Z).hearC G, b.RunsStep (CarriesFo S.fork? hd)
  k6 : ∀ G, ∀ b ∈ (P4.k6Lot Z).hearC G, b.RunsStep (CarriesFo S.fork? hd)
  k8 : ∀ G, ∀ b ∈ (ProofFile.P1K8.lot Z).hearC G, b.RunsStep (CarriesFo S.fork? hd)
  k11 : ∀ G, ∀ b ∈ (K11.lot Z).hearC G, b.RunsStep (CarriesFo S.fork? hd)

/-- A lot is K9's, or gives no batching's maker. -/
theorem makerOfPure (Z : Pub) (lot : Lot) (hl : lot ∈ onlineFirstChainBlockTables Z) :
    lot = k9Ninth Z ∨ ∀ G a, lot.batch G a = none := by
  simp only [onlineFirstChainBlockTables, ProofFile.p4Pure, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr fun _ _ => rfl

/-- A lot is one of the six, or lays no block with typed runs. -/
theorem hearOfPure (Z : Pub) (lot : Lot) (hl : lot ∈ onlineFirstChainBlockTables Z) :
    lot = K3Lot.lot Z ∨ lot = ProofFile.k4Lot Z ∨ lot = H2K5.lotN Z ∨ lot = P4.k6Lot Z ∨
      lot = ProofFile.P1K8.lot Z ∨ lot = K11.lot Z ∨ ∀ G, lot.hearC G = [] := by
  simp only [onlineFirstChainBlockTables, ProofFile.p4Pure, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr (Or.inl rfl))
    | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr fun _ => rfl)))))

/-- **`LotsCarry` at the seated seat**, general in the reading hd: from K9's law at hd and the six
fields. -/
theorem lotsCarryAtPure (hd : S → Option Forest.Heard) (o : ProofFile.SecondHashFunctionArgument) (Z : Pub)
    (h9 : ∀ p, Calls (CarriesFo S.fork? hd) (QK9 atS p) (batch atS p)) (K : KindsRun hd Z) :
    LotsCarry (CarriesFo S.fork? hd) (QN Z) (pureSeat o Z) where
  calls := fun lot hl G a mk h => by
    rcases makerOfPure Z lot hl with rfl | hn
    · obtain ⟨l, p, ha, hp, rfl⟩ := k9MakerIs Z G a mk h
      intro f s rs gs s' D
      obtain ⟨t, cls, e, r₁, r₂, r₃, q⟩ := h9 p f s rs gs s' D
      exact ⟨t, cls, e, r₁, r₂, r₃, l, p, ha, hp, q⟩
    · rw [hn] at h
      exact nomatch h
  mono := fun lot hl G a mk h => by
    rcases makerOfPure Z lot hl with rfl | hn
    · obtain ⟨l, p, _, _, rfl⟩ := k9MakerIs Z G a mk h
      exact k9_makerMono atS p
    · rw [hn] at h
      exact nomatch h
  face := fun lot hl G a mk h g => by
    rcases makerOfPure Z lot hl with rfl | hn
    · obtain ⟨l, p, _, _, rfl⟩ := k9MakerIs Z G a mk h
      exact runsOfBare _ rfl
    · rw [hn] at h
      exact nomatch h
  runs := fun lot hl G b hb => by
    rcases hearOfPure Z lot hl with rfl | rfl | rfl | rfl | rfl | rfl | hn
    · exact K.k3 G b hb
    · exact K.k4 G b hb
    · exact K.k5 G b hb
    · exact K.k6 G b hb
    · exact K.k8 G b hb
    · exact K.k11 G b hb
    · rw [hn] at hb
      exact nomatch hb

/-! ## The fields that are paid -/

/-- K4's: the law on the typed block (k4C_runsFo, Johnson/Desc/First/K4/CarriesFoK4.lean). -/
theorem k4Runs {hd : S → Option Forest.Heard} (H : OnBytes.Desc.First.K4.KeepsIn hd) (Z : Pub) :
    ∀ G, ∀ b ∈ (ProofFile.k4Lot Z).hearC G, b.RunsStep (CarriesFo S.fork? hd) := by
  intro G b hb
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 hb
  exact runsOfClaims _ _ rfl (OnBytes.Desc.First.K4.k4C_runsFo H { x.2 with k3Runs := true })

/-- K11's, at what the lookup on the calls was heard to return: the law run_carries_look. -/
theorem k11RunsLook (Z : Pub) :
    ∀ G, ∀ b ∈ (K11.lot Z).hearC G, b.RunsStep (CarriesFo S.fork? S.lookHeard?) := by
  intro G b hb
  obtain rfl := List.mem_singleton.1 hb
  intro c hc n s cl s' h
  obtain rfl := List.mem_singleton.1 hc
  exact First.MergeLaw.run_carries_look n s (cl, s') h

/-- K11's, at what the lookup on the digits was heard to return. -/
theorem k11RunsDigits (Z : Pub) :
    ∀ G, ∀ b ∈ (K11.lot Z).hearC G,
      b.RunsStep (CarriesFo S.fork? fun s => s.tl?.bind (·.heard)) := by
  intro G b hb
  obtain rfl := List.mem_singleton.1 hb
  intro c hc n s cl s' h
  obtain rfl := List.mem_singleton.1 hc
  exact First.MergeLaw.run_carries_digits n s (cl, s') h

end VerifiableInference.Desc.K9

#print axioms VerifiableInference.Desc.K9.lookupMap
#print axioms VerifiableInference.Desc.K9.k9MakerIs
#print axioms VerifiableInference.Desc.K9.makerOfPure
#print axioms VerifiableInference.Desc.K9.hearOfPure
#print axioms VerifiableInference.Desc.K9.lotsCarryAtPure
#print axioms VerifiableInference.Desc.K9.k4Runs
#print axioms VerifiableInference.Desc.K9.k11RunsLook
#print axioms VerifiableInference.Desc.K9.k11RunsDigits
