-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/RoundsStretch.lean: the closing of a segment (K10): the description's fold over a list
of members, the state in front of a place (`frontState`, Honest/K10/StAt.lean) and the made-up columns (`zeroCols`,
Honest/K10/StAtZero.lean) read of a chain's rounds just the first stretch that these members take. One definition;
lemmas.

  `roundsDue bs`     the number of rounds that a list of members takes: the sum of the numbers of their declared rounds
  `fold_more`        where the fold returns at a list of rounds, it returns at that list with more rounds behind it: the
                    same state and columns left; the further rounds are left over too
  `fold_stretch`     where the fold returns at a list of rounds, it returns at the list's first `roundsDue` rounds: the
                    same state and columns left, no round left; and what it had left over is the rest of the list
  `zeroCols_stretch`   the made-up columns at a list of rounds are those at its first `roundsDue` rounds
  **`front_same`**   two lists of rounds with one first stretch of `roundsDue` (of the members in front of the place):
                    where `frontState` returns at the one it returns at the other, the same state
  **`zeroCols_same`**   and the made-up columns are one at both

What it is for. A chain's decision folds over the view's rounds, all of them; a part has seen the rounds in front of its
own. With these two lemmas a law at the view's rounds goes over to the rounds seen, once these are known to begin alike
as far as the members in front take rounds.

Limits. That the rounds which a part has seen begin as the view's rounds do is the frame's matter: it is a premise here
(the equation of the two first stretches). The laws speak where the fold returns: that a refusal's word is one at both
lists is not shown. `stAtZero_of_chain` (Honest/K10/Wipe/SeatWipe.lean) calls `front_same`; no file calls
`zeroCols_same`. No property of the protocol is claimed: nothing is said on its soundness, completeness, binding or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.WipeFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Block Place OpenedColumn foldBlocks groupsOf)

variable {σ Cl : Type}

/-- The number of rounds that a list of members takes. -/
def roundsDue : List (Block σ Cl) → Nat
  | [] => 0
  | b :: l => b.rounds.length + roundsDue l

/-- **More rounds behind do no harm.** -/
theorem fold_more (ft : Nat) :
    ∀ (bs : List (Block σ Cl)) (s : σ) (rs : List Fmt.RoundView) (c : List OpenedColumn) (r : σ × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft bs s rs c = .ok r → ∀ e : List Fmt.RoundView,
        foldBlocks ft bs s (rs ++ e) c = .ok (r.1, r.2.1 ++ e, r.2.2)
  | [], s, rs, c, r, h, e => by
    have hr : r = (s, rs, c) := (Except.ok.inj h).symm
    subst hr
    rfl
  | b :: l, s, rs, c, r, h, e => by
    obtain ⟨hl, s', k, hs, hf⟩ := VerifiableInference.Desc.foldBlocks_cons_ok.1 h
    have hle : b.rounds.length ≤ rs.length := by
      rw [List.length_take] at hl
      omega
    have e1 : (rs ++ e).take b.rounds.length = rs.take b.rounds.length := List.take_append_of_le_length hle
    have e2 : (rs ++ e).drop b.rounds.length = rs.drop b.rounds.length ++ e := List.drop_append_of_le_length hle
    refine VerifiableInference.Desc.foldBlocks_cons_ok.2 ⟨by rw [e1]; exact hl, s', k, by rw [e1]; exact hs, ?_⟩
    rw [e2]
    exact fold_more ft l s' _ _ r hf e

/-- **The fold reads no round beyond those that its members take.** -/
theorem fold_stretch (ft : Nat) :
    ∀ (bs : List (Block σ Cl)) (s : σ) (rs : List Fmt.RoundView) (c : List OpenedColumn) (r : σ × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft bs s rs c = .ok r →
        foldBlocks ft bs s (rs.take (roundsDue bs)) c = .ok (r.1, [], r.2.2) ∧ r.2.1 = rs.drop (roundsDue bs)
  | [], s, rs, c, r, h => by
    have hr : r = (s, rs, c) := (Except.ok.inj h).symm
    subst hr
    exact ⟨rfl, rfl⟩
  | b :: l, s, rs, c, r, h => by
    obtain ⟨hl, s', k, hs, hf⟩ := VerifiableInference.Desc.foldBlocks_cons_ok.1 h
    obtain ⟨i1, i2⟩ := fold_stretch ft l s' (rs.drop b.rounds.length) (c.drop k) r hf
    have e1 : (rs.take (b.rounds.length + roundsDue l)).take b.rounds.length = rs.take b.rounds.length := by
      rw [List.take_take, Nat.min_eq_left (Nat.le_add_right _ _)]
    have e2 : (rs.take (b.rounds.length + roundsDue l)).drop b.rounds.length =
        (rs.drop b.rounds.length).take (roundsDue l) := by
      rw [List.drop_take, Nat.add_sub_cancel_left]
    refine ⟨?_, ?_⟩
    · show foldBlocks ft (b :: l) s (rs.take (b.rounds.length + roundsDue l)) c = _
      refine VerifiableInference.Desc.foldBlocks_cons_ok.2 ⟨by rw [e1]; exact hl, s', k, by rw [e1]; exact hs, ?_⟩
      rw [e2]
      exact i1
    · show r.2.1 = rs.drop (b.rounds.length + roundsDue l)
      rw [i2, List.drop_drop]

/-- The made-up columns read no round beyond those that the members take. -/
theorem zeroCols_stretch (ft : Nat) :
    ∀ (bs : List (Block σ Cl)) (rs : List Fmt.RoundView), zeroCols ft bs (rs.take (roundsDue bs)) = zeroCols ft bs rs
  | [], _ => rfl
  | b :: l, rs => by
    have e1 : (rs.take (b.rounds.length + roundsDue l)).take b.rounds.length = rs.take b.rounds.length := by
      rw [List.take_take, Nat.min_eq_left (Nat.le_add_right _ _)]
    have e2 : (rs.take (b.rounds.length + roundsDue l)).drop b.rounds.length =
        (rs.drop b.rounds.length).take (roundsDue l) := by
      rw [List.drop_take, Nat.add_sub_cancel_left]
    show zeroCols ft (b :: l) (rs.take (b.rounds.length + roundsDue l)) = _
    rw [zeroCols_cons, zeroCols_cons, e1, e2, zeroCols_stretch ft l]

/-- **The made-up columns are one at two lists of rounds with one first stretch.** -/
theorem zeroCols_same (ft : Nat) (bs : List (Block σ Cl)) {rs rs' : List Fmt.RoundView}
    (h : rs'.take (roundsDue bs) = rs.take (roundsDue bs)) : zeroCols ft bs rs' = zeroCols ft bs rs := by
  rw [← zeroCols_stretch ft bs rs', h, zeroCols_stretch]

/-- **The state in front of a place is one at two lists of rounds with one first stretch.** -/
theorem front_same (ft : Nat) (bs : List (Block σ Cl)) (a : Place) {s : σ} {rs rs' : List Fmt.RoundView} {c : List OpenedColumn}
    {t : σ}
    (hr : rs'.take (roundsDue (bs.takeWhile (·.place != a))) = rs.take (roundsDue (bs.takeWhile (·.place != a))))
    (h : frontState ft bs s a rs c = .ok t) : frontState ft bs s a rs' c = .ok t := by
  unfold frontState at h ⊢
  split at h
  · cases h
  · rename_i hany
    rw [if_neg hany]
    cases hf : foldBlocks ft (bs.takeWhile (·.place != a)) s rs c with
    | error e => rw [hf] at h; cases h
    | ok r =>
      rw [hf] at h
      have e : r.1 = t := Except.ok.inj h
      have h1 := (fold_stretch ft _ s rs c r hf).1
      rw [← hr] at h1
      have h2 := fold_more ft _ s _ c _ h1 (rs'.drop (roundsDue (bs.takeWhile (·.place != a))))
      rw [List.take_append_drop] at h2
      rw [h2]
      exact congrArg Except.ok e

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.roundsDue
#print axioms ProofFile.Honest.K10.fold_more
#print axioms ProofFile.Honest.K10.fold_stretch
#print axioms ProofFile.Honest.K10.zeroCols_stretch
#print axioms ProofFile.Honest.K10.zeroCols_same
#print axioms ProofFile.Honest.K10.front_same
