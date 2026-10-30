-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/SharedStand.lean: NOT IN FRONT OF A LAW OVER COINS. A thread of
twelve members walked from its start through its eleven first members at the letter that keeps the
field: a stand at 9, at 10 and at 11, with what the two tests keep and what the run has heard. The
form of the proof file's shared chain, general in the thread: the twin of the key file's
stand_eleven_at_key (K12/AtKey/UOStand.lean in the key's walked pack).

  start_at_letter      the stand at border 0 at the letter, from the invariant there
  paid_of_border       MemberPaid at the letter, from FiveAtBorder
  stand_eleven         the walk

Premises left, each named. F: WalkFacts. P₀: member 0. H: the five at members 1 to 10. R: each
member's rounds at the run's coins and the lists given. u₀: the invariant at the start.

By what. walk_of_paid, step_of_paid (Honest/ThruWalk.lean), paid_of_five (SharedWalk.lean),
saidField_start (Honest/Thread/SaidField.lean).

Limits. A walk of the thread's steps, not a run of the frame. Nothing on completeness, soundness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.SharedWalk
import Johnson.Desc.ProofFile.Honest.Thread.FiveAtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Cl V W X Pb}

/-- **The stand at border 0 at the letter.** The invariant does not read the field opened. -/
theorem start_at_letter {k : Coins Bk} {s : S} {m : Mid W X} {E : Env} (h : Thr T 0 k s m E)
    (hseen : m.seen = []) : ThrS T (SaidField T BaseNil) 0 k s { m with opened := some [] } E :=
  ⟨h, saidField_start T hseen⟩

/-- **What a member pays at the letter, from the five.** -/
theorem paid_of_border {n b : Nat} (F : WalkFacts T n) (hb : b < n)
    (H : FiveAtBorder T (SaidField T BaseNil) (fun _ _ _ => none) b) :
    MemberPaid T (SaidField T BaseNil) b :=
  paid_of_five F hb
    (treesNext_of_playsS T H.plays fun blk _ m ds => AtPublicFiles.Stops.chainStopAt_none _ F.stops [blk] _ _)
    H.plays H.accepted H.behind H.exchange H.ridesPast

/-- **The walk through the first eleven members.** -/
theorem stand_eleven (F : WalkFacts T 12) (P₀ : MemberPaid T (SaidField T BaseNil) 0)
    (H : ∀ b, 1 ≤ b → b ≤ 10 → FiveAtBorder T (SaidField T BaseNil) (fun _ _ _ => none) b)
    {k : Coins Bk} {s₀ : S} {m₀ : Mid W X} {E₀ : Env}
    (start : ThrS T (SaidField T BaseNil) 0 k s₀ m₀ E₀) (ds : Nat → List Fmt.Drawn)
    (R : ∀ j, j < 11 → MemberRuns T k j (ds j)) :
    ∃ (s s' s'' : S) (m m' m'' : Mid W X) (E E' E'' : Env),
      ThrS T (SaidField T BaseNil) 9 k s m E ∧ ThrS T (SaidField T BaseNil) 10 k s' m' E' ∧
      ThrS T (SaidField T BaseNil) 11 k s'' m'' E'' ∧ T.keeps 9 s s' ∧ T.keeps 10 s' s'' ∧
      m''.st.heard =
        m₀.st.heard ++ ((List.range 9).flatMap fun j => ds (0 + j)) ++ ds 9 ++ ds 10 := by
  have hP : ∀ j, j < 9 → MemberPaid T (SaidField T BaseNil) (0 + j) := by
    intro j hj
    rw [Nat.zero_add]
    rcases Nat.eq_zero_or_pos j with rfl | h1
    · exact P₀
    · exact paid_of_border F (by omega) (H j h1 (by omega))
  obtain ⟨s, m, E, u, hh⟩ := walk_of_paid T (SaidField T BaseNil) (n := 12) F.fits 0 k ds start 9
    (by omega) hP (fun j hj => by rw [Nat.zero_add]; exact R j (by omega))
  obtain ⟨s', m', E', u', h', k9, -⟩ := step_of_paid T (SaidField T BaseNil) (n := 12) F.fits
    (by omega) (paid_of_border F (by omega) (H 9 (by omega) (by omega))) (R 9 (by omega)) u
  obtain ⟨s'', m'', E'', u'', h'', k10, -⟩ := step_of_paid T (SaidField T BaseNil) (n := 12) F.fits
    (by omega) (paid_of_border F (by omega) (H 10 (by omega) (by omega))) (R 10 (by omega)) u'
  exact ⟨s, s', s'', m, m', m'', E, E', E'', u, u', u'', k9, k10, by rw [h'', h', hh]⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.start_at_letter
#print axioms ProofFile.Honest.paid_of_border
#print axioms ProofFile.Honest.stand_eleven
