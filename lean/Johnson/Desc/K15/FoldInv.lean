-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K15/FoldInv.lean: what a yes of the format's own fold over a list of blocks says, block
by block (Johnson/Desc/Block.lean:
foldBlocks · Block.step · roundsFit · groupsOf · regroup). General in the blocks. Small
lemmas by unfolding.
-/
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
variable {S Cl : Type}

/-- The fold's yes at a list with a first block: that block's stretch is whole, its step says yes,
and the fold goes on behind it. -/
theorem foldBlocks_cons (ft : Nat) (b : Block S Cl) (l : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft (b :: l) s rs cols = .ok out) :
    ∃ s' k, (rs.take b.rounds.length).length = b.rounds.length ∧
      b.step ft s (rs.take b.rounds.length) cols = .ok (s', k) ∧
      foldBlocks ft l s' (rs.drop b.rounds.length) (cols.drop k) = .ok out := by
  unfold foldBlocks at h
  simp only [List.splitAt_eq] at h
  split at h
  · cases h
  · rename_i hl
    split at h
    · cases h
    · rename_i s' k hs
      exact ⟨s', k, by simpa using hl, hs, h⟩

theorem foldBlocks_nil (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn) (h : foldBlocks (Cl := Cl) ft [] s rs cols = .ok out) :
    out = (s, rs, cols) := by
  unfold foldBlocks at h
  injection h with h
  exact h.symm

/-- Rounds that read nothing owe no column. -/
theorem groupsOf_none (ft : Nat) : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    (∀ d ∈ ds, d.stored = [] ∧ d.opens = []) → groupsOf ft ds Rs = []
  | [], _, _ => by unfold groupsOf; rfl
  | _ :: _, [], _ => by unfold groupsOf; rfl
  | d :: ds, R :: Rs, h => by
    unfold groupsOf
    rw [(h d (List.mem_cons_self ..)).1, (h d (List.mem_cons_self ..)).2,
      groupsOf_none ft ds Rs fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

/-- A step's yes, whole: the rounds fit; the next columns are, in key, position and width, those
that are read; decide says yes on
the rounds without the sealed digest and the columns in their groups. -/
theorem step_inv (ft : Nat) (b : Block S Cl) (s s' : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (k : Nat)
    (h : b.step ft s rs cols = .ok (s', k)) :
    roundsFit b.rounds rs = true ∧
      k = ((groupsOf ft b.rounds (rs.map (·.drawn))).flatMap id).length ∧
      (cols.take k).map (fun c => (c.1, c.2.1, c.2.2.length)) =
        (groupsOf ft b.rounds (rs.map (·.drawn))).flatMap id ∧
      b.decide s (rs.map noDigest)
        (regroup ((groupsOf ft b.rounds (rs.map (·.drawn))).map (·.length)) (cols.take k)) = .ok
            s' := by
  unfold Block.step need at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i h1 _ _ h2 _ s'' h3
        injection h with h
        injection h with ha hb
        subst ha hb
        split at h1
        · rename_i hf
          split at h2
          · rename_i hc
            exact ⟨hf, rfl, by simpa using hc, h3⟩
          · cases h2
        · cases h1

/-- A step's yes at a block that reads nothing. -/
theorem step_quiet (ft : Nat) (b : Block S Cl) (hb : ∀ d ∈ b.rounds, d.stored = [] ∧ d.opens = [])
    (s s' : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (k : Nat)
        (h : b.step ft s rs cols = .ok (s', k)) :
    roundsFit b.rounds rs = true ∧ k = 0 ∧ b.decide s (rs.map noDigest) [] = .ok s' := by
  obtain ⟨h1, h2, _, h4⟩ := step_inv ft b s s' rs cols k h
  rw [groupsOf_none ft b.rounds _ hb] at h2 h4
  exact ⟨h1, h2, h4⟩

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.foldBlocks_cons
#print axioms VerifiableInference.Desc.step_inv
#print axioms VerifiableInference.Desc.step_quiet
