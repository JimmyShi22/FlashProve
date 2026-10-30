--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/StepFits.lean: ROUNDS OF THE SHAPE OF THE OUTPUT HEAD's TABLE PASS Block.step's OWN TESTS: tools for the member of mean1's rowStep (Law/K06HonestStep.lean).
  knownRound | rounds_known   the format knows the name of every round of the kind's table (Fmt.kindOf returns).
  roundFit_one | roundsFit_shaped   rounds shaped as a table says (Law/TapeShape.lean: ShapedAs: scalars and drawn elements alone, in the table's counts), none of whose drawn elements is (0,0,0), at names that the format knows: Block.lean's roundsFit says yes at the table's declared rounds.
  noDigest_shaped   such rounds bear no sealed digest: striking it turns nothing.      groups_none   declared rounds that open no tree and no stored table: the block is owed no column.
WHAT IT IS NOT. Tools. That a prover's rounds have that shape: a premise. Nothing on soundness.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.TapeShape
import Johnson.Desc.Kinds.Law.StepBack

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open Part.MaskedSum (rvOf)
open VerifiableInference.Desc.First (S)

/-- The format knows the round's name. -/
def knownRound (R : Round) : Bool := (Fmt.kindOf R.name).isSome

theorem triple_ne_zero (x : E) (h : OnBytes.isZeroE x = false) : x.triple ≠ (0, 0, 0) := by
  intro e
  have e0 : x.c0 = 0 := congrArg Prod.fst e
  have e1 : x.c1 = 0 := congrArg (fun t => t.2.1) e
  have e2 : x.c2 = 0 := congrArg (fun t => t.2.2) e
  simp [OnBytes.isZeroE, e0, e1, e2] at h

/-- One round passes the step's test on the rounds. -/
theorem roundFit_one (work : Nat) (R : Round) (s d : List E) (hs : s.length = R.sent)
    (hd : d.length = R.drawn) (hk : knownRound R = true)
    (hz : ∀ x ∈ d, OnBytes.isZeroE x = false) (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView)
    (h : roundsFit ds rs = true) :
    roundsFit (({ entry := R.entry work } : Fmt.DeclaredRound) :: ds) (rvOf s d :: rs) = true := by
  obtain ⟨k, hk'⟩ := Option.isSome_iff_exists.mp hk
  have hv : (rvOf s d).vals.map itemOf = List.replicate R.sent Fmt.Item.e := by
    rw [← hs]
    show (s.map fun x => Fmt.ItemValue.e x.triple).map itemOf = _
    rw [List.map_map]
    exact List.eq_replicate_iff.mpr ⟨by simp, fun b hb => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb
      rfl⟩
  have hi : (({ entry := R.entry work } : Fmt.DeclaredRound).items.filter (· != .root))
      = List.replicate R.sent Fmt.Item.e := by
    show ((R.entry work).cut.filter (· != .root)) = _
    unfold Fmt.Entry.cut Round.entry
    simp
  have hnz : drawsMarkedNonzeroHaveNonzeroWords ({ entry := R.entry work } : Fmt.DeclaredRound) (rvOf s d) = true := by
    unfold drawsMarkedNonzeroHaveNonzeroWords
    show ((Fmt.kindOf R.name).any fun k => _) = true
    rw [hk']
    simp only [Option.any_some, List.all_eq_true]
    intro x hx
    have hx2 : x.2 ∈ (rvOf s d).drawn.elems := (List.of_mem_zip hx).2
    obtain ⟨y, hy, e⟩ := List.mem_map.mp (show x.2 ∈ d.map (·.triple) from hx2)
    have := triple_ne_zero y (hz y hy)
    rw [e] at this
    simp [this]
  unfold roundsFit
  rw [hv, hi, hnz, h]
  simp [rvOf, Round.entry, hd]

/-- **The rounds pass.** -/
theorem roundsFit_shaped (work : Nat) (D : List E) (hz : ∀ x ∈ D, OnBytes.isZeroE x = false) :
    ∀ (rs : List Fmt.RoundView) (Rs : List Round), ShapedAs D rs Rs →
      (∀ R ∈ Rs, knownRound R = true) →
      roundsFit (Rs.map fun R => ({ entry := R.entry work } : Fmt.DeclaredRound)) rs = true
  | _, _, .nil, _ => rfl
  | _, _, .cons (a := r) (b := R) (l₁ := rs) (l₂ := Rs) h1 h2, hp => by
    obtain ⟨s, d, rfl, hs, hd, hD⟩ := h1
    exact roundFit_one work R s d hs hd (hp R List.mem_cons_self) (fun x hx => hz x (hD x hx)) _ _
      (roundsFit_shaped work D hz rs Rs h2 fun R' h' => hp R' (List.mem_cons_of_mem _ h'))

/-- Rounds of that shape bear no sealed digest: striking it turns nothing. -/
theorem noDigest_shaped (D : List E) : ∀ (rs : List Fmt.RoundView) (Rs : List Round), ShapedAs D rs Rs →
    rs.map noDigest = rs
  | _, _, .nil => rfl
  | _, _, .cons (a := r) (b := R) (l₁ := rs) (l₂ := Rs) h1 h2 => by
    obtain ⟨s, d, rfl, _, _, _⟩ := h1
    rw [List.map_cons, noDigest_shaped D rs Rs h2]
    rfl

/-- A block whose rounds open no tree and no stored table is owed no column. -/
theorem groups_none (firstTree work : Nat) : ∀ (Rs : List Round) (dr : List Fmt.Drawn),
    groupsOf firstTree (Rs.map fun R => ({ entry := R.entry work } : Fmt.DeclaredRound)) dr = []
  | [], _ => by simp [groupsOf]
  | _ :: _, [] => by simp [groupsOf]
  | R :: Rs, x :: dr => by
    rw [List.map_cons]
    unfold groupsOf
    rw [groups_none firstTree work Rs dr]
    rfl

theorem known_of (n : String) (h : (Fmt.kindOf n).isSome = true) (a b : Nat) (z : Bool) (r : Nat) :
    knownRound { name := n, sent := a, drawn := b, notZero := z, rows := r } = true := h

/-- Every round of the kind's table has a name that the format knows. -/
theorem rounds_known [Sizes] : ∀ R ∈ (rounds : List Round), knownRound R = true := by
  intro R hR
  simp only [rounds, Norm.rounds, FinalNorm.rounds, drawPoint.rounds, drawJoin.rounds,
    sendThenBatch.rounds, level.rounds, sumcheck.rounds, List.mem_append, List.mem_cons,
    List.mem_replicate, List.not_mem_nil, or_false] at hR
  simp only [or_assoc] at hR
  rcases hR with rfl | rfl | h | rfl | ⟨_, rfl⟩ | rfl | rfl | rfl | rfl | rfl | ⟨_, rfl⟩ | rfl | rfl |
    rfl | ⟨_, rfl⟩ | rfl | rfl | rfl | ⟨_, rfl⟩ | rfl | rfl
  · exact known_of "ZERO" (by decide) _ _ _ _
  · exact known_of "BAT-sigma" (by decide) _ _ _ _
  · have hN0 : Norm.lNI = 0 := rfl
    rw [hN0] at h
    simp at h
  · exact known_of "PSC epsilon" (by decide) _ _ _ _
  · exact known_of "PSC round" (by decide) _ _ _ _
  · exact known_of "PSC Y" (by decide) _ _ _ _
  · exact known_of "PSC values" (by decide) _ _ _ _
  · exact known_of "LINE" (by decide) _ _ _ _
  · exact known_of "BAT-sigma" (by decide) _ _ _ _
  · exact known_of "PSC epsilon" (by decide) _ _ _ _
  · exact known_of "PSC round" (by decide) _ _ _ _
  · exact known_of "PSC Y" (by decide) _ _ _ _
  · exact known_of "PSC values" (by decide) _ _ _ _
  · exact known_of "PSC epsilon" (by decide) _ _ _ _
  · exact known_of "PSC round" (by decide) _ _ _ _
  · exact known_of "PSC Y" (by decide) _ _ _ _
  · exact known_of "PSC values" (by decide) _ _ _ _
  · exact known_of "PSC epsilon" (by decide) _ _ _ _
  · exact known_of "PSC round" (by decide) _ _ _ _
  · exact known_of "PSC Y" (by decide) _ _ _ _
  · exact known_of "PSC values" (by decide) _ _ _ _

end VerifiableInference.Desc.Kinds.Head.Law
