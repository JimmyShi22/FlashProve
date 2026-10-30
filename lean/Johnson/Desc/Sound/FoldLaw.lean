-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FoldLaw.lean: the fold's own law: the fold of a list of blocks (`foldBlocks`) on
rounds and columns in a row is the fold of its first block, then the fold of the rest. One
definition, one statement as a proposition, proofs. It imports Block.lean alone: no Mathlib.

Main names:
  `endOk`: what a chain's end makes of the fold's answer: the record, where nothing is left over.
  `need_bind`, `Block.step_eq`: `Block.step` with its two tests written as two ifs.
  `step_count`: where `Block.step` returns, it has taken as many columns as the block's declared
    rounds read.
  `step_app`: `Block.step` does not look behind the columns that it reads.
  `foldBlocks_error`, `foldBlocks_ok`, `foldBlocks_short`: one block of the fold.
  `chainAt_toOption`: `chainAt` is `endOk` of the fold, but for the words, and nothing at no block.
  `FoldLaw`, `foldLaw`: `endOk` of the fold of b :: bs on ⟨R₁ ++ R₂, c₁ ++ c₂⟩ is `endOk` of the
    fold of [b] on ⟨R₁, c₁⟩, then of bs on ⟨R₂, c₂⟩: as options: a refusal's words are dropped.

Limits: a law on the frame's fold, general in the blocks: it says nothing of what a block decides.
As options: a refusal's words are dropped. `FoldLaw` has no premise that the rest of the list is not
empty: the fold of no block returns; it is `chainAt` that refuses an empty list.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl : Type}

theorem splitAt_app {α : Type} (a b : List α) (n : Nat) (h : a.length = n) :
    (a ++ b).splitAt n = (a, b) := by
  subst h
  simp [List.splitAt_eq]

/-- What a chain's end makes of the fold's answer: the record, where nothing is left over. -/
def endOk : Except String (S × List Fmt.RoundView × List OpenedColumn) → Option S
  | .ok (s, [], []) => some s
  | _ => none

theorem need_bind {α : Type} (nm : String) (c : Bool) (f : Unit → Except String α) :
    (need nm c >>= f) = if c = true then f () else .error nm := by
  cases c <;> rfl

/-- `Block.step`, its two tests as two ifs. -/
theorem Block.step_eq (ft : Nat) (b : Block S Cl) (s : S) (R : List Fmt.RoundView) (c : List OpenedColumn) :
    b.step ft s R c =
      if roundsFit b.rounds R = true then
        if ((c.take ((groupsOf ft b.rounds (R.map (·.drawn))).flatMap id).length).map
            (fun x => (x.1, x.2.1, x.2.2.length)) ==
              (groupsOf ft b.rounds (R.map (·.drawn))).flatMap id) = true then
          b.decide s (R.map noDigest)
            (regroup ((groupsOf ft b.rounds (R.map (·.drawn))).map (·.length))
              (c.take ((groupsOf ft b.rounds (R.map (·.drawn))).flatMap id).length)) >>=
            fun s' => pure (s', ((groupsOf ft b.rounds (R.map (·.drawn))).flatMap id).length)
        else .error "the columns"
      else .error "the rounds" := by
  simp only [Block.step, need_bind]

theorem bind_pair_ok {α : Type} (D : Except String α) (n k : Nat) (x : α)
    (h : (D >>= fun s' => pure (s', n)) = (.ok (x, k) : Except String (α × Nat))) : k = n := by
  cases D with
  | error e =>
    have h' : (Except.error e : Except String (α × Nat)) = .ok (x, k) := h
    cases h'
  | ok y =>
    have h' : (Except.ok (y, n) : Except String (α × Nat)) = .ok (x, k) := h
    cases h'
    rfl

theorem step_count (ft : Nat) (b : Block S Cl) (s : S) (R : List Fmt.RoundView) (c : List OpenedColumn) (s' : S)
    (k : Nat) (h : b.step ft s R c = .ok (s', k)) :
    k = ((b.reads ft (R.map (·.drawn))).flatMap id).length := by
  rw [Block.step_eq] at h
  split at h
  · split at h
    · exact bind_pair_ok _ _ _ _ h
    · cases h
  · cases h

/-- `Block.step` does not look behind the columns that it reads. -/
theorem step_app (ft : Nat) (b : Block S Cl) (s : S) (R : List Fmt.RoundView) (c c' : List OpenedColumn)
    (h : ((b.reads ft (R.map (·.drawn))).flatMap id).length = c.length) :
    b.step ft s R (c ++ c') = b.step ft s R c := by
  have e : ((groupsOf ft b.rounds (R.map (·.drawn))).flatMap id).length = c.length := h
  simp only [Block.step_eq, e, List.take_left, List.take_length]

/-- One block of the fold, where its step refuses. -/
theorem foldBlocks_error (ft : Nat) (b : Block S Cl) (l : List (Block S Cl)) (s : S)
    (R₁ R₂ : List Fmt.RoundView) (c : List OpenedColumn) (h : R₁.length = b.rounds.length) (e : String)
    (hs : b.step ft s R₁ c = .error e) :
    foldBlocks ft (b :: l) s (R₁ ++ R₂) c = .error (b.name ++ ": " ++ e) := by
  simp only [foldBlocks, splitAt_app R₁ R₂ b.rounds.length h, h, ne_eq, not_true_eq_false, if_false,
    hs]

/-- One block of the fold, where its step returns. -/
theorem foldBlocks_ok (ft : Nat) (b : Block S Cl) (l : List (Block S Cl)) (s : S)
    (R₁ R₂ : List Fmt.RoundView) (c : List OpenedColumn) (h : R₁.length = b.rounds.length) (s' : S) (k : Nat)
    (hs : b.step ft s R₁ c = .ok (s', k)) :
    foldBlocks ft (b :: l) s (R₁ ++ R₂) c = foldBlocks ft l s' R₂ (c.drop k) := by
  simp only [foldBlocks, splitAt_app R₁ R₂ b.rounds.length h, h, ne_eq, not_true_eq_false, if_false,
    hs]

/-- One block of the fold, where fewer rounds are left than it declares. -/
theorem foldBlocks_short (ft : Nat) (b : Block S Cl) (l : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : ¬ b.rounds.length ≤ rs.length) :
    foldBlocks ft (b :: l) s rs c = .error (b.name ++ ": the stretch is short") := by
  have hne : (rs.splitAt b.rounds.length).1.length ≠ b.rounds.length := by
    rw [List.splitAt_eq, List.length_take]
    omega
  simp only [foldBlocks, hne, ne_eq, not_false_eq_true, if_true]

/-- `chainAt` is `endOk` of the fold, but for the words; at no block it is nothing. -/
theorem chainAt_toOption (name : String) (ft : Nat) (bs : List (Block S Cl)) (s : S)
    (v : Fmt.View) :
    (chainAt name ft bs s v).toOption =
      if bs.isEmpty = true then none else endOk (foldBlocks ft bs s v.rounds v.opened) := by
  unfold chainAt
  cases hE : bs.isEmpty with
  | true => rfl
  | false =>
  simp only [Bool.false_eq_true, if_false]
  cases foldBlocks ft bs s v.rounds v.opened with
  | error e => rfl
  | ok t =>
    obtain ⟨s', rs, cs⟩ := t
    cases rs with
    | nil =>
      cases cs with
      | nil => rfl
      | cons _ _ => rfl
    | cons _ _ => rfl

/-- **The fold's own law.** -/
def FoldLaw : Prop :=
  ∀ (S Cl : Type) (ft : Nat) (b : Block S Cl) (bs : List (Block S Cl)) (s : S)
    (R₁ R₂ : List Fmt.RoundView) (c₁ c₂ : List OpenedColumn),
    R₁.length = b.rounds.length →
    ((b.reads ft (R₁.map (·.drawn))).flatMap id).length = c₁.length →
    endOk (foldBlocks ft (b :: bs) s (R₁ ++ R₂) (c₁ ++ c₂)) =
      (endOk (foldBlocks ft [b] s R₁ c₁)).bind fun s' => endOk (foldBlocks ft bs s' R₂ c₂)

theorem foldLaw : FoldLaw := by
  intro S Cl ft b bs s R₁ R₂ c₁ c₂ hlen hc
  have ha := step_app ft b s R₁ c₁ c₂ hc
  cases hs : b.step ft s R₁ c₁ with
  | error e =>
    have e1 := foldBlocks_error ft b bs s R₁ R₂ (c₁ ++ c₂) hlen e (ha.trans hs)
    have e2 := foldBlocks_error ft b [] s R₁ [] c₁ hlen e hs
    rw [List.append_nil] at e2
    rw [e1, e2]
    rfl
  | ok x =>
    obtain ⟨s', k⟩ := x
    have hk := (step_count ft b s R₁ c₁ s' k hs).trans hc
    subst hk
    have e1 := foldBlocks_ok ft b bs s R₁ R₂ (c₁ ++ c₂) hlen s' c₁.length (ha.trans hs)
    rw [List.drop_left] at e1
    have e2 := foldBlocks_ok ft b [] s R₁ [] c₁ hlen s' c₁.length hs
    rw [List.append_nil, List.drop_length] at e2
    rw [e1, e2]
    rfl

end VerifiableInference.Desc
