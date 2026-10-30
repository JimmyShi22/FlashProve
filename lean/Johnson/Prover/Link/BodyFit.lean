-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyFit.lean: AT WHICH ROUND A STAGE STANDS: THE DRAWS FIT THE ROUNDS STILL TO
BE DEALT. bodyAll (Johnson/Prover/Link/BodyAll.lean) reads the draws as one function D of the
round's number and an offset o; the proximity test's frame (Johnson/Desc/K12/Frame.lean) deals the
declared rounds l. FitFrom D l o ties the three: it rides beside the invariant of the induction over
the stages. Definition, statements and proofs.

  FitFrom D l o    for every n: D (o + n) fits the n-th declared round of l, whatever fitting items
                   stand beside it (RoundFits, Johnson/Top/H0/StepLaws/RoundsFit.lean), and its
                   elements' words are below the prime
  FitFrom.drop     it rides: l.drop m at o + m
  roundsFit_of     rounds that drew D (o + n), as many as the first m of l, whose items are of the
                   declared sorts, pass roundsFit at these m declared rounds

Not shown here. That a run's draws are such (ChainRounds.lean: roundFits_run; ViewWords.lean:
ltE_drawnSL). Nothing on a decision, on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.Frame
import Johnson.Top.H0.StepLaws.RoundsFit
import Johnson.Prover.Link.ViewWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- **The draws from the round o on fit the declared rounds l.** -/
def FitFrom (D : ℕ → Fmt.Drawn) (l : Laid) (o : ℕ) : Prop :=
  ∀ n d, l[n]? = some d →
    (∀ vals : List Fmt.ItemValue, vals.map itemOf = d.1.items.filter (· != .root) →
      RoundFits d.1 ⟨vals, D (o + n)⟩) ∧
    ∀ x ∈ (D (o + n)).elems, ltE x = true

theorem FitFrom.drop {D : ℕ → Fmt.Drawn} {l : Laid} {o : ℕ} (h : FitFrom D l o) (m : ℕ) :
    FitFrom D (l.drop m) (o + m) := fun n d hd => by
  rw [List.getElem?_drop] at hd
  rw [Nat.add_assoc]
  exact h (m + n) d hd

/-- Rounds that drew D (o + n) and show items of the declared sorts fit. -/
theorem roundsFit_of {D : ℕ → Fmt.Drawn} : ∀ (l : Laid) (o : ℕ) (rs : List Fmt.RoundView),
    FitFrom D l o → rs.length = l.length →
    (∀ (n : ℕ) (r : Fmt.RoundView), rs[n]? = some r → r.drawn = D (o + n)) →
    (∀ (n : ℕ) (r : Fmt.RoundView) (d : Fmt.DeclaredRound × List Oracle), rs[n]? = some r → l[n]? = some d →
      r.vals.map itemOf = d.1.items.filter (· != .root)) →
    roundsFit (l.map (·.1)) rs = true
  | [], _, [], _, _, _, _ => rfl
  | [], _, _ :: _, _, h, _, _ => by cases h
  | _ :: _, _, [], _, h, _, _ => by cases h
  | d :: l, o, r :: rs, hF, hl, hd, hi => by
    refine (roundsFit_iff _ _).2 (List.Forall₂.cons ?_ ((roundsFit_iff _ _).1
      (roundsFit_of (D := D) l (o + 1) rs ?_ (Nat.succ.inj hl) ?_ ?_)))
    · have e : r = ⟨r.vals, D (o + 0)⟩ := by
        rw [← hd 0 r rfl]
      rw [e]
      exact (hF 0 d rfl).1 r.vals (hi 0 r d rfl rfl)
    · exact hF.drop 1
    · intro n r' h'
      rw [hd (n + 1) r' h']
      congr 1
      omega
    · intro n r' d' h1 h2
      exact hi (n + 1) r' d' h1 h2

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.FitFrom.drop
#print axioms Johnson.Prover.Link.roundsFit_of
