-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/WipeFold.lean: the closing of a segment (K10): the general half of the tie between the
filler at made-up columns (Honest/K10/StAtZero.lean) and the description's own fold at the true columns. General in the
state's type σ and in a function wipe : σ → σ ("what is left of a state once the fields into which columns' words go are
set to zero"). Five definitions; lemmas.

  `SameShape c c'`   two lists of columns have the same keys, positions and widths, in order
  `AlikeStep wipe r r'`, `AlikeFold wipe r r'`  two outcomes of a step, or of a fold: both refuse with one word, or both
                   return, with states that are one once wiped and the same number (or the same rounds left, and columns
                   left of one shape)
  `Keeps wipe ft b`  the premise, a member at a time: from two states that are one once wiped, at the same rounds and at
                   columns of one shape, the member's step has like outcomes
  `fold_alike`      every member of a list keeps ⊢ the fold over the list has like outcomes
  `zero_shape`      where the fold returns at a list of columns, what it has taken off the list's front has the shape of
                   `zeroCols`
  `fold_take`, `fold_zero`   it reads no column beyond these; and, over members that keep, it returns at `zeroCols` too
  **`front_zero`**   every member in front of the place keeps; `frontState` returns t at columns cols ⊢ it returns at
                   `zeroCols` too, a state that is t once wiped

Limits. `Keeps` is shown of no member here: that is a lemma for each kind of member of the first chain
(Honest/K10/Wipe/). Nothing says what wipe is. No property of the protocol is claimed: nothing is said on its soundness,
completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.StAtZero
import Johnson.Desc.RunLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Block Place OpenedColumn foldBlocks groupsOf)

variable {σ Cl : Type}

/-- A column's key, position and width. -/
def colShape (c : OpenedColumn) : Nat × Nat × Nat := (c.1, c.2.1, c.2.2.length)

/-- Two lists of columns have the same keys, positions and widths, in order. -/
def SameShape (c c' : List OpenedColumn) : Prop := c.map colShape = c'.map colShape

/-- Two outcomes of a member's step are alike. -/
def AlikeStep (wipe : σ → σ) : Except String (σ × Nat) → Except String (σ × Nat) → Prop
  | .ok (t, k), .ok (t', k') => wipe t = wipe t' ∧ k = k'
  | .error e, .error e' => e = e'
  | _, _ => False

/-- Two outcomes of a fold are alike. -/
def AlikeFold (wipe : σ → σ) :
    Except String (σ × List Fmt.RoundView × List OpenedColumn) → Except String (σ × List Fmt.RoundView × List OpenedColumn) → Prop
  | .ok (t, rs, c), .ok (t', rs', c') => wipe t = wipe t' ∧ rs = rs' ∧ SameShape c c'
  | .error e, .error e' => e = e'
  | _, _ => False

/-- **The premise, a member at a time.** -/
def Keeps (wipe : σ → σ) (ft : Nat) (b : Block σ Cl) : Prop :=
  ∀ (s s' : σ) (rs : List Fmt.RoundView) (c c' : List OpenedColumn), wipe s = wipe s' → SameShape c c' →
    AlikeStep wipe (b.step ft s rs c) (b.step ft s' rs c')

theorem SameShape.drop {c c' : List OpenedColumn} (h : SameShape c c') (k : Nat) :
    SameShape (c.drop k) (c'.drop k) := by
  unfold SameShape at h ⊢
  rw [List.map_drop, List.map_drop, h]

/-- **The fold over members that keep.** -/
theorem fold_alike (wipe : σ → σ) (ft : Nat) :
    ∀ (bs : List (Block σ Cl)), (∀ b ∈ bs, Keeps wipe ft b) →
      ∀ (s s' : σ) (rs : List Fmt.RoundView) (c c' : List OpenedColumn), wipe s = wipe s' → SameShape c c' →
        AlikeFold wipe (foldBlocks ft bs s rs c) (foldBlocks ft bs s' rs c')
  | [], _, s, s', rs, c, c', hs, hc => ⟨hs, rfl, hc⟩
  | b :: l, hk, s, s', rs, c, c', hs, hc => by
    have hb := hk b (List.mem_cons.2 (Or.inl rfl)) s s' (rs.splitAt b.rounds.length).1 c c' hs hc
    unfold foldBlocks
    dsimp only
    by_cases hl : (rs.splitAt b.rounds.length).1.length ≠ b.rounds.length
    · rw [if_pos hl, if_pos hl]
      exact rfl
    · rw [if_neg hl, if_neg hl]
      cases h1 : b.step ft s (rs.splitAt b.rounds.length).1 c with
      | error e =>
        cases h2 : b.step ft s' (rs.splitAt b.rounds.length).1 c' with
        | error e' =>
          rw [h1, h2] at hb
          have : e = e' := hb
          rw [this]
          exact rfl
        | ok y => rw [h1, h2] at hb; exact hb.elim
      | ok y =>
        cases h2 : b.step ft s' (rs.splitAt b.rounds.length).1 c' with
        | error e' => rw [h1, h2] at hb; exact hb.elim
        | ok y' =>
          rw [h1, h2] at hb
          obtain ⟨t, k⟩ := y
          obtain ⟨t', k'⟩ := y'
          obtain ⟨ht, rfl⟩ : wipe t = wipe t' ∧ k = k' := hb
          exact fold_alike wipe ft l (fun b' hb' => hk b' (List.mem_cons.2 (Or.inr hb'))) t t' _ _ _ ht
            (hc.drop k)

/-- The made-up columns of a list of shapes have these shapes. -/
theorem zero_map (want : List (Nat × Nat × Nat)) :
    ((want.map fun c => ((c.1, c.2.1, List.replicate c.2.2 0) : OpenedColumn)).map colShape) = want := by
  induction want with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, ih]
    obtain ⟨x, y, w⟩ := a
    simp [colShape]

/-- The made-up columns at a member and the members behind it. -/
theorem zeroCols_cons (ft : Nat) (b : Block σ Cl) (l : List (Block σ Cl)) (rs : List Fmt.RoundView) :
    zeroCols ft (b :: l) rs =
      ((groupsOf ft b.rounds ((rs.take b.rounds.length).map (·.drawn))).flatMap id).map
          (fun c => ((c.1, c.2.1, List.replicate c.2.2 0) : OpenedColumn)) ++
        zeroCols ft l (rs.drop b.rounds.length) := rfl

/-- **Where the fold returns, what it has taken off the front of the columns has the shape of the made-up columns**, and
what it leaves is the rest. -/
theorem zero_shape (ft : Nat) :
    ∀ (bs : List (Block σ Cl)) (s : σ) (rs : List Fmt.RoundView) (c : List OpenedColumn) (r : σ × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft bs s rs c = .ok r →
        SameShape (c.take (zeroCols ft bs rs).length) (zeroCols ft bs rs) ∧
          r.2.2 = c.drop (zeroCols ft bs rs).length
  | [], s, rs, c, r, h => by
    have e : r = (s, rs, c) := (Except.ok.inj h).symm
    subst e
    exact ⟨rfl, rfl⟩
  | b :: l, s, rs, c, r, h => by
    obtain ⟨_, s', k, hs, hf⟩ := VerifiableInference.Desc.foldBlocks_cons_ok.1 h
    obtain ⟨_, h2, _, hk⟩ := VerifiableInference.Desc.Block.step_ok.1 hs
    obtain ⟨i1, i2⟩ := zero_shape ft l s' (rs.drop b.rounds.length) (c.drop k) r hf
    have hlen : (((groupsOf ft b.rounds ((rs.take b.rounds.length).map (·.drawn))).flatMap id).map
        (fun c => ((c.1, c.2.1, List.replicate c.2.2 0) : OpenedColumn))).length = k := by
      rw [List.length_map, hk]
    rw [zeroCols_cons, List.length_append, hlen]
    refine ⟨?_, ?_⟩
    · unfold SameShape at i1 ⊢
      rw [List.take_add, List.map_append, List.map_append, i1, zero_map]
      congr 1
    · rw [i2, List.drop_drop]

/-- **The fold reads no column beyond those that its members are owed.** -/
theorem fold_take (ft : Nat) :
    ∀ (bs : List (Block σ Cl)) (s : σ) (rs : List Fmt.RoundView) (c : List OpenedColumn) (r : σ × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft bs s rs c = .ok r →
        foldBlocks ft bs s rs (c.take (zeroCols ft bs rs).length) = .ok (r.1, r.2.1, [])
  | [], s, rs, c, r, h => by
    have e : r = (s, rs, c) := (Except.ok.inj h).symm
    subst e
    rfl
  | b :: l, s, rs, c, r, h => by
    obtain ⟨hl, s', k, hs, hf⟩ := VerifiableInference.Desc.foldBlocks_cons_ok.1 h
    obtain ⟨h1, h2, h3, hk⟩ := VerifiableInference.Desc.Block.step_ok.1 hs
    have ih := fold_take ft l s' (rs.drop b.rounds.length) (c.drop k) r hf
    have hlen : (((groupsOf ft b.rounds ((rs.take b.rounds.length).map (·.drawn))).flatMap id).map
        (fun c => ((c.1, c.2.1, List.replicate c.2.2 0) : OpenedColumn))).length = k := by
      rw [List.length_map, hk]
    rw [zeroCols_cons, List.length_append, hlen]
    have e1 : (c.take (k + (zeroCols ft l (rs.drop b.rounds.length)).length)).take k = c.take k := by
      rw [List.take_take, Nat.min_eq_left (Nat.le_add_right _ _)]
    have e2 : (c.take (k + (zeroCols ft l (rs.drop b.rounds.length)).length)).drop k =
        (c.drop k).take (zeroCols ft l (rs.drop b.rounds.length)).length := by
      rw [List.drop_take, Nat.add_sub_cancel_left]
    refine VerifiableInference.Desc.foldBlocks_cons_ok.2 ⟨hl, s', k, ?_, ?_⟩
    · exact VerifiableInference.Desc.Block.step_ok.2 ⟨h1, by rw [e1]; exact h2, by rw [e1]; exact h3, hk⟩
    · rw [e2]
      exact ih

/-- **The fold at the made-up columns**, over members that keep: where the fold returns at some columns, it returns at
the made-up ones too, with the same rounds left, no column left, and a state that is the same once wiped. -/
theorem fold_zero (wipe : σ → σ) (ft : Nat) (bs : List (Block σ Cl)) (hk : ∀ b ∈ bs, Keeps wipe ft b)
    {s : σ} {rs : List Fmt.RoundView} {c : List OpenedColumn} {r : σ × List Fmt.RoundView × List OpenedColumn}
    (h : foldBlocks ft bs s rs c = .ok r) :
    ∃ t0, foldBlocks ft bs s rs (zeroCols ft bs rs) = .ok (t0, r.2.1, []) ∧ wipe t0 = wipe r.1 := by
  have h1 := fold_take ft bs s rs c r h
  have h2 := (zero_shape ft bs s rs c r h).1
  have A := fold_alike wipe ft bs hk s s rs _ _ rfl h2
  rw [h1] at A
  cases hz : foldBlocks ft bs s rs (zeroCols ft bs rs) with
  | error e => rw [hz] at A; exact A.elim
  | ok y =>
    rw [hz] at A
    obtain ⟨t0, rs0, c0⟩ := y
    obtain ⟨a1, a2, a3⟩ : wipe r.1 = wipe t0 ∧ r.2.1 = rs0 ∧ SameShape [] c0 := A
    have hc : c0 = [] := by
      unfold SameShape at a3
      exact List.map_eq_nil_iff.1 a3.symm
    subst a2 hc
    exact ⟨t0, rfl, a1.symm⟩

/-- **The state in front of a place, at the made-up columns.** -/
theorem front_zero (wipe : σ → σ) (ft : Nat) (bs : List (Block σ Cl)) (a : Place)
    (hk : ∀ b ∈ bs.takeWhile (·.place != a), Keeps wipe ft b) {s : σ} {rs : List Fmt.RoundView} {c : List OpenedColumn} {t : σ}
    (h : frontState ft bs s a rs c = .ok t) :
    ∃ t0, frontState ft bs s a rs (zeroCols ft (bs.takeWhile (·.place != a)) rs) = .ok t0 ∧
      wipe t0 = wipe t := by
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
      obtain ⟨t0, z1, z2⟩ := fold_zero wipe ft _ hk hf
      rw [z1]
      exact ⟨t0, rfl, by rw [z2, e]⟩

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.colShape
#print axioms ProofFile.Honest.K10.SameShape
#print axioms ProofFile.Honest.K10.AlikeStep
#print axioms ProofFile.Honest.K10.AlikeFold
#print axioms ProofFile.Honest.K10.Keeps
#print axioms ProofFile.Honest.K10.SameShape.drop
#print axioms ProofFile.Honest.K10.fold_alike
#print axioms ProofFile.Honest.K10.zero_map
#print axioms ProofFile.Honest.K10.zeroCols_cons
#print axioms ProofFile.Honest.K10.zero_shape
#print axioms ProofFile.Honest.K10.fold_take
#print axioms ProofFile.Honest.K10.fold_zero
#print axioms ProofFile.Honest.K10.front_zero
