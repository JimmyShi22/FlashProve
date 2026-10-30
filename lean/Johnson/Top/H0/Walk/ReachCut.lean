-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/ReachCut.lean: KIND-FREE: «REACHED» (Johnson/Top/H0/Walk/Reach.lean), CUT: ONE
RUN, EVERY EARLIER BORDER: whatever is reached at border k' is the return of a fold at ONE list of
rounds and ONE list of columns, and at these same lists the fold over the first k sub-protocols,
for each k ≤ k', returns a state that is itself reached at k. NO BLOCK IMPORTS THIS FILE.
  Reach.cuts        Reach ft bs start k' a ⟹ ∃ rs cols, the fold over the first k' returns a's
                    state and leaves nothing over ∧ ∀ k ≤ k', ∃ s r c, s is reached at k (at the
                    same public part) ∧ the fold over the first k returns s at rs | cols and
                    leaves r | c over
  fold_raw          an accepting fold over the wrapped sub-protocols («below b»: b behind the test
                    that every word shown is below the prime) is an accepting fold over the
                    sub-protocols themselves, with the same return
  reach_cuts_below  Reach.cuts at the wrapped family, with the folds over the sub-protocols
                    themselves
WHY. A fact that a law asks at EARLIER borders of the same run (the states in front of a segment
and inside it, say) can so be asked at reached states alone; several cuts stand at one run. BY:
Reach.fold · fold_split · reach_of_fold (Walk/Reach.lean) · foldBlocks_cons
(Johnson/Desc/Block.lean) · step_ok_iff · below_yes. No soundness is claimed.

-/
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open VerifiableInference.Desc (Block OpenedColumn foldBlocks foldBlocks_cons)
open VerifiableInference.Desc.Sound

variable {S Cl P : Type}

theorem Reach.cuts {ft : ℕ} {bs : List (Block S Cl)} {start : P → S} {k' : ℕ} {a : P × S}
    (h : Reach ft bs start k' a) :
    ∃ (rs : List Fmt.RoundView) (cols : List OpenedColumn),
      foldBlocks ft (bs.take k') (start a.1) rs cols = .ok (a.2, [], []) ∧
      ∀ k, k ≤ k' → ∃ (s : S) (r : List Fmt.RoundView) (c : List OpenedColumn),
        Reach ft bs start k (a.1, s) ∧
        foldBlocks ft (bs.take k) (start a.1) rs cols = .ok (s, r, c) := by
  obtain ⟨hk', rs, cols, hf⟩ := h.fold
  refine ⟨rs, cols, hf, fun k hk => ?_⟩
  have e : bs.take k' = bs.take k ++ (bs.take k').drop k := by
    have e1 := (List.take_append_drop k (bs.take k')).symm
    rw [List.take_take, Nat.min_eq_left hk] at e1
    exact e1
  rw [e] at hf
  obtain ⟨t, r, c, h1, _⟩ := fold_split ft _ _ _ _ _ _ hf
  exact ⟨t, r, c, reach_of_fold k (Nat.le_trans hk hk') t rs r cols c h1, h1⟩

theorem fold_raw (ft : ℕ) : ∀ (l : List (Block S Cl)) (s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
    foldBlocks ft (l.map below) s rs cols = .ok out → foldBlocks ft l s rs cols = .ok out
  | [], s, rs, cols, out, h => h
  | b :: l, s, rs, cols, out, h => by
    obtain ⟨s', k, hl, hs, h'⟩ := foldBlocks_cons ft (below b) (l.map below) s rs cols out h
    obtain ⟨h1, h2, h3, h4⟩ := (step_ok_iff ft (below b) s s' _ cols k).1 hs
    have hs' : b.step ft s (rs.take b.rounds.length) cols = .ok (s', k) :=
      (step_ok_iff ft b s s' _ cols k).2 ⟨h1, h2, h3, (below_yes b _ _ _ _ h4).2⟩
    have hl' : (rs.take b.rounds.length).length = b.rounds.length := hl
    unfold foldBlocks
    simp only [List.splitAt_eq, hl', ne_eq, not_true_eq_false, if_false, hs']
    exact fold_raw ft l s' _ _ out h'

theorem reach_cuts_below {ft : ℕ} {l : List (Block S Cl)} {start : P → S} {k' : ℕ} {a : P × S}
    (h : Reach ft (l.map below) start k' a) :
    ∃ (rs : List Fmt.RoundView) (cols : List OpenedColumn),
      foldBlocks ft (l.take k') (start a.1) rs cols = .ok (a.2, [], []) ∧
      ∀ k, k ≤ k' → ∃ (s : S) (r : List Fmt.RoundView) (c : List OpenedColumn),
        Reach ft (l.map below) start k (a.1, s) ∧
        foldBlocks ft (l.take k) (start a.1) rs cols = .ok (s, r, c) := by
  obtain ⟨rs, cols, hf, hall⟩ := h.cuts
  rw [← List.map_take] at hf
  refine ⟨rs, cols, fold_raw ft _ _ _ _ _ hf, fun k hk => ?_⟩
  obtain ⟨s, r, c, h1, h2⟩ := hall k hk
  rw [← List.map_take] at h2
  exact ⟨s, r, c, h1, fold_raw ft _ _ _ _ _ h2⟩

end Johnson.Desc.First.Walk.Tied

#print axioms Johnson.Desc.First.Walk.Tied.Reach.cuts
#print axioms Johnson.Desc.First.Walk.Tied.fold_raw
#print axioms Johnson.Desc.First.Walk.Tied.reach_cuts_below
