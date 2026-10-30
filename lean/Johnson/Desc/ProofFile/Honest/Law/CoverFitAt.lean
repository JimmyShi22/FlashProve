-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverFitAt.lean: THE FIT's MARK OWES NOTHING: ITS PREMISE, MEMBER
BY MEMBER. `fitMark_debt` (Honest/Law/CoverFit.lean) takes hk: every typed message of the member's
own rounds' data shows challenges that its rounds can draw. `drawsFit_typed` (Honest/Law/Due.lean)
says that of a whole list of rounds whose data fit them, under a kit that meets three clauses. Here
the cut: where a chain's data fit its members' rounds in a row, one member's stretch of the data
fits that member's rounds (`kindFits_at`); so hk (`fit_at_member`); at the release's field's kit the
three clauses hold (`kit_two`, Honest/Law/KitTwo.lean): `fit_at_two`; and the mark's debt itself
(`fitMark_zero`).

WHAT THIS IS. Lemmas on lists and on definitions of ours; calls. None of the library's goals.

  `kindFits_at`, `kindFits_get`, `stretch_at`, `stretch_one`, `fit_at_member`, `fit_at_two`,
  `fitMark_zero`

Limits. That a chain's data fit its rounds (at a description's own data: `kinds_of_data`,
Honest/Law/DataKinds.lean, brought to the gated members' rounds by Honest/Law/CoverData.lean), and
that every declared round states no more «never 0» elements than elements, are premises: neither is
shown here of the proof file's description. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverFit
import Johnson.Desc.ProofFile.Honest.Law.Due
import Johnson.Desc.ProofFile.Honest.Law.KitTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)
open _root_.Run (ckP)

variable {S Cl : Type}

/-- **One member's stretch of the chain's data fits that member's rounds.** A: the members in front
of b; B: those behind it. -/
theorem kindFits_at (ds : List RDT) (A B : List (Block S Cl)) (b : Block S Cl)
    (h : List.Forall₂ KindFits ds ((A ++ b :: B).flatMap (·.rounds))) :
    List.Forall₂ KindFits ((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length)
      b.rounds := by
  have h1 := List.forall₂_drop (A.flatMap (·.rounds)).length h
  rw [List.flatMap_append, List.flatMap_cons, List.drop_left' rfl] at h1
  have h2 := List.forall₂_take b.rounds.length h1
  rw [List.take_left' rfl] at h2
  exact h2

/-- Round by round: where data fit rounds in a row, the data at a round's number fit that round. -/
theorem kindFits_get : ∀ {ds : List RDT} {zs : List Fmt.DeclaredRound}, List.Forall₂ KindFits ds zs →
    ∀ (i : Nat) (z : Fmt.DeclaredRound), zs[i]? = some z → ∃ d, ds[i]? = some d ∧ KindFits d z
  | _, _, .nil, _, _, h => by cases h
  | _, _, .cons hd _, 0, z, h => by
    rw [List.getElem?_cons_zero] at h
    cases h
    exact ⟨_, List.getElem?_cons_zero, hd⟩
  | _, _, .cons _ tl, i + 1, z, h => by
    rw [List.getElem?_cons_succ] at h
    obtain ⟨d, h1, h2⟩ := kindFits_get tl i z h
    exact ⟨d, by rw [List.getElem?_cons_succ]; exact h1, h2⟩

/-- **THE CHAIN's OWN STRETCH OF DATA AT A MEMBER, ROUND BY ROUND**: at the number of each declared
round of the member it holds data that bear that round's entry and the kind of its name. The stretch
is the very term that `localDebts_of` (Honest/Law/CoverSplit.lean) and `chainHeld_of`
(Honest/Law/SharesParts.lean) hand a member. -/
theorem stretch_at (ds : List RDT) (A B : List (Block S Cl)) (b : Block S Cl)
    (h : List.Forall₂ KindFits ds ((A ++ b :: B).flatMap (·.rounds))) (i : Nat)
    (z : Fmt.DeclaredRound) (hz : b.rounds[i]? = some z) :
    ∃ d, ((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length)[i]? = some d ∧
      d.entry = z.entry ∧ Fmt.kindOf z.entry.name = some d.kind :=
  kindFits_get (kindFits_at ds A B b h) i z hz

/-- **At a member with one round the stretch is [d].** -/
theorem stretch_one (ds : List RDT) (A B : List (Block S Cl)) (b : Block S Cl)
    (h : List.Forall₂ KindFits ds ((A ++ b :: B).flatMap (·.rounds))) (z : Fmt.DeclaredRound)
    (hb : b.rounds = [z]) :
    ∃ d, (ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length = [d] ∧
      d.entry = z.entry ∧ Fmt.kindOf z.entry.name = some d.kind := by
  have h1 := kindFits_at ds A B b h
  generalize (ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length = l at h1 ⊢
  rw [hb] at h1
  cases h1 with
  | cons hd tl =>
    cases tl
    exact ⟨_, rfl, hd.1, hd.2⟩

/-- **hk, under a kit that meets the three clauses.** -/
theorem fit_at_member (C : CK)
    (hC : ∀ e k (c : C.Ch e k), H2K.Fit.FitsDrawn e k (C.dr e k c) ∧
      (∀ z ∈ (C.dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
      ((C.dr e k c).digest = none ∨ k = .sealed))
    (ds : List RDT) (A B : List (Block S Cl)) (b : Block S Cl)
    (h : List.Forall₂ KindFits ds ((A ++ b :: B).flatMap (·.rounds)))
    (hz : ∀ z ∈ b.rounds, z.entry.drawNZ ≤ z.entry.drawE)
    (ρ : Iop.Rho (uLT C ((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length))) :
    drawsFit b.rounds (drawnT C _ ρ) = true :=
  drawsFit_typed C hC _ _ (kindFits_at ds A B b h) hz ρ

/-- **At the release's field's kit.** -/
theorem fit_at_two (ds : List RDT) (A B : List (Block S Cl)) (b : Block S Cl)
    (h : List.Forall₂ KindFits ds ((A ++ b :: B).flatMap (·.rounds)))
    (hz : ∀ z ∈ b.rounds, z.entry.drawNZ ≤ z.entry.drawE)
    (ρ : Iop.Rho (uLT (ckP .two)
      ((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length))) :
    drawsFit b.rounds (drawnT (ckP .two) _ ρ) = true :=
  fit_at_member (ckP .two) kit_two ds A B b h hz ρ

/-- **So the fit's mark at that member owes nothing.** -/
theorem fitMark_zero (C : CK)
    (hC : ∀ e k (c : C.Ch e k), H2K.Fit.FitsDrawn e k (C.dr e k c) ∧
      (∀ z ∈ (C.dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
      ((C.dr e k c).digest = none ∨ k = .sealed))
    (ds : List RDT) (A B : List (Block S Cl)) (b : Block S Cl)
    (h : List.Forall₂ KindFits ds ((A ++ b :: B).flatMap (·.rounds)))
    (hz : ∀ z ∈ b.rounds, z.entry.drawNZ ≤ z.entry.drawE) (P : List Fmt.Drawn → Prop)
    (q : ℝ≥0∞) :
    MarkDebt C ⟨b.place,
      fun _ own => if drawsFit b.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ ((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length) P q :=
  fitMark_debt C b _ (fit_at_member C hC ds A B b h hz) P q

end ProofFile.Honest

#print axioms ProofFile.Honest.kindFits_at
#print axioms ProofFile.Honest.kindFits_get
#print axioms ProofFile.Honest.stretch_at
#print axioms ProofFile.Honest.stretch_one
#print axioms ProofFile.Honest.fit_at_member
#print axioms ProofFile.Honest.fit_at_two
#print axioms ProofFile.Honest.fitMark_zero
