-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/TapeShape.lean: THE OUTPUT HEAD's DECISION's TEST "the rounds' shape" RETURNS ON ROUNDS THAT ARE SHAPED AS THE KIND's TABLE OF ROUNDS SAYS. The converse of
Law/SentFits.lean. FOR A TOY OF K06_law.
  ShapedAs D rs Rs   round for round: r is a round of scalars and drawn elements alone (rvOf, Johnson/Desc/Part/MaskedSumHonest.lean: no position, no matrix entry, no digest), with as many
               scalars sent and elements drawn as the table's round says, every drawn element out of the list D. (head_sendsC, Johnson/Desc/Kinds/Law/HeadSends.lean, hands this of its rounds, under the name Shaped, where zt has lt coordinates.)
  plainRound R       the clauses of the strict reading (Johnson/Desc/First/Tape/Tape.lean: roundT) that read the table's round alone: the name's kind is the one asked; rows are
               counted at "BAT-sigma" alone. rounds_plain: every round of Head.lean's table passes.
  tape_returns       ShapedAs D rs Rs, every R of Rs plain, no element of D is (0, 0, 0): tapeT returns on rs at the declared entries of Rs, whatever the bits of work.
WHAT IT IS NOT. Nothing on soundness; nothing on what the rounds hold. That any rounds are ShapedAs: other files' to show.

-/
import Mathlib
import Johnson.Desc.Kinds.HeadKind
import Johnson.Desc.Part.MaskedSumHonest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open Part.MaskedSum (rvOf)
open VerifiableInference.Desc.First.Tape (TapeRule elemsOf roundT tapeT kindAsked)

/-- Round for round as the table says. -/
def ShapedAs (D : List E) (rs : List Fmt.RoundView) (Rs : List Round) : Prop :=
  List.Forall₂ (fun (r : Fmt.RoundView) (R : Round) => ∃ s d, r = rvOf s d ∧ s.length = R.sent ∧
    d.length = R.drawn ∧ ∀ x ∈ d, x ∈ D) rs Rs

/-- The decision's rule of reading. -/
def headRule : TapeRule := { rows := fun e => e.name == "BAT-sigma" }

/-- What the strict reading asks of the table's round alone. -/
def plainRound (R : Round) : Bool :=
  ((R.rows == 0 && R.name != OnBytes.Model.RoundName.batSigma.name) || R.name == "BAT-sigma") &&
    OnBytes.Params.kindOf R.name == some (kindAsked R.name)

theorem elemsOf_of : ∀ s : List E, elemsOf (s.map fun x => Fmt.ItemValue.e x.triple) = some s
  | [] => rfl
  | x :: l => by
    show (elemsOf (l.map fun x => Fmt.ItemValue.e x.triple)).map (E.ofTriple x.triple :: ·) = _
    rw [elemsOf_of l, E.ofTriple_triple]
    rfl

/-- One round. -/
theorem roundT_returns (work : Nat) (R : Round) (s d : List E) (hs : s.length = R.sent)
    (hd : d.length = R.drawn) (hp : plainRound R = true)
    (hz : ∀ x ∈ d, OnBytes.isZeroE x = false) :
    (roundT headRule (rvOf s d) (R.entry work)).isSome = true := by
  unfold plainRound at hp
  rw [Bool.and_eq_true] at hp
  obtain ⟨p1, p2⟩ := hp
  have hall : (((d.map (·.triple)).drop (R.drawn - (if R.notZero then 1 else 0))).all fun x =>
      !OnBytes.isZeroE (E.ofTriple x)) = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop hx)
    rw [E.ofTriple_triple, hz y hy]
    rfl
  unfold roundT
  have he : elemsOf (rvOf s d).vals = some s := elemsOf_of s
  rw [he]
  simp only [rvOf, Round.entry, headRule, List.length_map, hd, hs, beq_self_eq_true,
    List.isEmpty_nil, Bool.and_self, Bool.true_and, Bool.and_true, p1, p2, hall, if_true,
    Option.isSome_some]

/-- **The strict reading returns.** -/
theorem tape_returns (work : Nat) (D : List E) (hz : ∀ x ∈ D, OnBytes.isZeroE x = false) :
    ∀ (rs : List Fmt.RoundView) (Rs : List Round), ShapedAs D rs Rs →
      (∀ R ∈ Rs, plainRound R = true) →
      (tapeT headRule rs (Rs.map fun R => R.entry work)).isSome = true
  | _, _, .nil, _ => rfl
  | _, _, .cons (a := r) (b := R) (l₁ := rs) (l₂ := Rs) h1 h2, hp => by
    obtain ⟨s, d, rfl, hs, hd, hD⟩ := h1
    have a := roundT_returns work R s d hs hd (hp R List.mem_cons_self)
      fun x hx => hz x (hD x hx)
    have b := tape_returns work D hz rs Rs h2 fun R' h' => hp R' (List.mem_cons_of_mem _ h')
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp a
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp b
    show (tapeT headRule (rvOf s d :: rs) (R.entry work :: Rs.map fun R => R.entry work)).isSome
      = true
    unfold tapeT
    rw [hx, ht]
    rfl

/-- The same of a name and a count of rows. -/
def plainName (n : String) (r : Nat) : Bool :=
  ((r == 0 && n != OnBytes.Model.RoundName.batSigma.name) || n == "BAT-sigma") &&
    OnBytes.Params.kindOf n == some (kindAsked n)

theorem plain_of (n : String) (r : Nat) (h : plainName n r = true) (a b : Nat) (z : Bool) :
    plainRound { name := n, sent := a, drawn := b, notZero := z, rows := r } = true := h

theorem plain_bat (r : Nat) : plainName "BAT-sigma" r = true := by
  unfold plainName
  rw [Bool.and_eq_true, Bool.or_eq_true]
  exact ⟨Or.inr (by decide), by decide⟩

/-- Every round of the kind's table passes. -/
theorem rounds_plain [Sizes] : ∀ R ∈ (rounds : List Round), plainRound R = true := by
  intro R hR
  simp only [rounds, Norm.rounds, FinalNorm.rounds, drawPoint.rounds, drawJoin.rounds,
    sendThenBatch.rounds, level.rounds, sumcheck.rounds, List.mem_append, List.mem_cons,
    List.mem_replicate, List.not_mem_nil, or_false] at hR
  simp only [or_assoc] at hR
  rcases hR with rfl | rfl | h | rfl | ⟨_, rfl⟩ | rfl | rfl | rfl | rfl | rfl | ⟨_, rfl⟩ | rfl | rfl |
    rfl | ⟨_, rfl⟩ | rfl | rfl | rfl | ⟨_, rfl⟩ | rfl | rfl
  · exact plain_of "ZERO" 0 (by decide) _ _ _
  · exact plain_of "BAT-sigma" 9 (by decide) _ _ _
  · have hN0 : Norm.lNI = 0 := rfl
    rw [hN0] at h
    simp at h
  · exact plain_of "PSC epsilon" 0 (by decide) _ _ _
  · exact plain_of "PSC round" 0 (by decide) _ _ _
  · exact plain_of "PSC Y" 0 (by decide) _ _ _
  · exact plain_of "PSC values" 0 (by decide) _ _ _
  · exact plain_of "LINE" 0 (by decide) _ _ _
  · exact plain_of "BAT-sigma" (7 * Norm.NI) (plain_bat _) _ _ _
  · exact plain_of "PSC epsilon" 0 (by decide) _ _ _
  · exact plain_of "PSC round" 0 (by decide) _ _ _
  · exact plain_of "PSC Y" 0 (by decide) _ _ _
  · exact plain_of "PSC values" 0 (by decide) _ _ _
  · exact plain_of "PSC epsilon" 0 (by decide) _ _ _
  · exact plain_of "PSC round" 0 (by decide) _ _ _
  · exact plain_of "PSC Y" 0 (by decide) _ _ _
  · exact plain_of "PSC values" 0 (by decide) _ _ _
  · exact plain_of "PSC epsilon" 0 (by decide) _ _ _
  · exact plain_of "PSC round" 0 (by decide) _ _ _
  · exact plain_of "PSC Y" 0 (by decide) _ _ _
  · exact plain_of "PSC values" 0 (by decide) _ _ _

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.tape_returns
#print axioms VerifiableInference.Desc.Kinds.Head.Law.rounds_plain
