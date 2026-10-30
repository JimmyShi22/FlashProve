-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FoldLiftProof.lean: the proof of `FoldLift` (Johnson/Desc/Sound/SharedRule.lean),
over `foldBlocks`.

Limits: those of Johnson/Desc/Sound/SharedRule.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SharedRule
import Johnson.Desc.Sound.FoldLawBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S S₀ Cl : Type}

theorem map_bind_pair {α β : Type} (D : Except String α) (g : α → β) (n : Nat) :
    ((D.map g) >>= fun s' => pure (s', n)) =
      ((D >>= fun s' => pure (s', n)).map fun x => (g x.1, x.2) : Except String (β × Nat)) := by
  cases D <;> rfl

theorem ite_map {α β : Type} (A B : Bool) (X : Except String α) (Y : Except String β) (f : α → β)
    (e₁ e₂ : String) (h : Y = X.map f) :
    (if A = true then (if B = true then Y else .error e₂) else .error e₁ : Except String β) =
      (if A = true then (if B = true then X else .error e₂) else .error e₁ :
        Except String α).map f := by
  subst h
  cases A <;> cases B <;> rfl

/-- A lifted block's step is the block's step at the part, laid back. -/
theorem step_lift (get : S → S₀) (set : S → S₀ → S) (ft : Nat) (b : Block S₀ Cl) (t : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    (b.lift get set).step ft t rs cols =
      (b.step ft (get t) rs cols).map fun x => (set t x.1, x.2) := by
  simp only [Block.step_eq, Block.lift]
  exact ite_map _ _ _ _ _ _ _ (map_bind_pair _ _ _)

/-- One block of the fold, from any record. -/
theorem foldBlocks_liftCons (get : S → S₀) (set : S → S₀ → S) (ft : Nat) (b : Block S₀ Cl)
    (l : List (Block S Cl)) (l₀ : List (Block S₀ Cl)) (t : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (ih : ∀ s' rs' cols', foldBlocks ft l (set t s') rs' cols' =
      (foldBlocks ft l₀ s' rs' cols').map fun x => (set t x.1, x.2)) :
    foldBlocks ft (b.lift get set :: l) t rs cols =
      (foldBlocks ft (b :: l₀) (get t) rs cols).map fun x => (set t x.1, x.2) := by
  by_cases hl : b.rounds.length ≤ rs.length
  · have hlen : (rs.take b.rounds.length).length = b.rounds.length := by
      rw [List.length_take]
      omega
    have hrs : rs = rs.take b.rounds.length ++ rs.drop b.rounds.length :=
      (List.take_append_drop _ _).symm
    generalize rs.take b.rounds.length = R₁ at hlen hrs
    generalize rs.drop b.rounds.length = R₂ at hrs
    subst hrs
    have hlen' : R₁.length = (b.lift get set).rounds.length := hlen
    have hb := step_lift get set ft b t R₁ cols
    cases hs : b.step ft (get t) R₁ cols with
    | error e =>
      rw [hs] at hb
      rw [foldBlocks_error ft (b.lift get set) l t R₁ R₂ cols hlen' e hb,
        foldBlocks_error ft b l₀ (get t) R₁ R₂ cols hlen e hs]
      rfl
    | ok x =>
      obtain ⟨s', k⟩ := x
      rw [hs] at hb
      rw [foldBlocks_ok ft (b.lift get set) l t R₁ R₂ cols hlen' (set t s') k hb,
        foldBlocks_ok ft b l₀ (get t) R₁ R₂ cols hlen s' k hs]
      exact ih s' R₂ (cols.drop k)
  · have hl' : ¬ (b.lift get set).rounds.length ≤ rs.length := hl
    rw [foldBlocks_short ft (b.lift get set) l t rs cols hl',
      foldBlocks_short ft b l₀ (get t) rs cols hl]
    rfl

/-- The blocks behind the first: from a record that was laid back. -/
theorem foldBlocks_tail (get : S → S₀) (set : S → S₀ → S) (h1 : ∀ t s, get (set t s) = s)
    (h2 : ∀ t s s', set (set t s) s' = set t s') (ft : Nat) (t₀ : S) :
    ∀ (l₀ : List (Block S₀ Cl)) (s : S₀) (rs : List Fmt.RoundView) (cols : List OpenedColumn),
      foldBlocks ft (l₀.map (Block.lift get set)) (set t₀ s) rs cols =
        (foldBlocks ft l₀ s rs cols).map fun x => (set t₀ x.1, x.2)
  | [], _, _, _ => rfl
  | b :: l₀, s, rs, cols => by
    have k := foldBlocks_liftCons get set ft b (l₀.map (Block.lift get set)) l₀ (set t₀ s) rs cols
      (fun s' rs' cols' => by
        simp only [h2]
        exact foldBlocks_tail get set h1 h2 ft t₀ l₀ s' rs' cols')
    rw [h1] at k
    simp only [h2] at k
    exact k

namespace Sound

theorem foldLift : FoldLift := by
  intro S S₀ Cl F name bs back get set h1 h2 t v
  cases bs with
  | nil => rfl
  | cons b bs =>
    have e1 : ((b :: bs).map (Block.lift get set)).isEmpty = false := rfl
    have e2 : (b :: bs).isEmpty = false := rfl
    simp only [foldRun, chainAt_toOption, e1, e2, Bool.false_eq_true, if_false]
    have k := foldBlocks_liftCons get set F.ft b (bs.map (Block.lift get set)) bs t
      (v.rounds ++ back) v.opened (foldBlocks_tail get set h1 h2 F.ft t bs)
    rw [List.map_cons, k]
    cases foldBlocks F.ft (b :: bs) (get t) (v.rounds ++ back) v.opened with
    | error _ => rfl
    | ok x =>
      obtain ⟨s, rs, cols⟩ := x
      cases rs <;> cases cols <;> rfl

end Sound

end VerifiableInference.Desc
