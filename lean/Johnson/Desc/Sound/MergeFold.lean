-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MergeFold.lean: THE FRAME'S FOLD DOES NOT SEE WHETHER TWO NEIGHBOURING BLOCKS ARE
MERGED. Theorems on `foldBlocks` and `chainAt` (Johnson/Desc/Block.lean) and `Block.andThen`;
without Mathlib; no probability in them.

Why. The rule of composition (Johnson/Desc/Sound/ChainRule.lean) takes one law a block. A law that
the library has proved of a whole stretch of places at once (a link's inside) then has no socket.
`Block.andThen` makes two blocks one: the rounds, the oracles and `before` appended; `decide` cuts
the rounds and the groups of columns between the two. So a stretch of several blocks is a `Piece` at
the merged block, and every carriage and rule that lies serves it unturned: IF the chain's own fold,
over the unmerged list, is the fold over the merged one. That is shown here.

Main theorems:
  `Merges.foldCons_iff`: where the fold over a block and a list returns: the block's rounds are
    there, its step returns, and the fold over the list returns behind it.
  `foldBlocks_merge`: **the fold over (p andThen q) :: l returns r just where the fold over p :: q
    :: l does.** By `andThen_step` (the step laws: Johnson/Top/H0/StepLaws/StepLaws.lean).
  `foldBlocks_front`: the like behind a common front. `Merges l m`: m comes of l by merging
    neighbours, any number of times. `Merges.fold`, `Merges.isEmpty`.
  `Merges.chainAt_iff`: where a chain's fold says yes. `Merges.chainAt`: **a chain's fold says yes
    at the same views and leaves the same record whether or not neighbours are merged.**

Silly members: these are equations on the frame's fold: they hold of every block, of one that says
yes to all and of one that says no to all alike: they claim nothing of what a block decides.

Limits: the words of a refusal may part (a merged block refuses under its own name). Nothing on a
merged block's `place`, `planOk`, `claims` or `after`: the fold reads none of them; the tests on the
plan are made on the description's own, unmerged list. IT STANDS ON ANOTHER FILE: StepLaws.lean:
`andThen_step`, an iff with no premise: compiled by Lean.
`andThen` appends `before`: "fixed before the draw" is then said of the
second block's messages at the first block's draws too, which may be false: nothing reads `before`
of a merged block: no test on `before` is to be run on a merged list. `mergeAll` lays one name
at every step: a refusal inside a stretch names none of its blocks. Built over
Block.lean.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Block
import Johnson.Top.H0.StepLaws.StepLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl : Type}

/-- Where the fold over a block and a list returns. -/
theorem Merges.foldCons_iff (ft : Nat) (b : Block S Cl) (l : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn) :
    foldBlocks ft (b :: l) s rs cols = .ok r ↔
      b.rounds.length ≤ rs.length ∧
        ∃ s' k, b.step ft s (rs.take b.rounds.length) cols = .ok (s', k) ∧
          foldBlocks ft l s' (rs.drop b.rounds.length) (cols.drop k) = .ok r := by
  rw [foldBlocks]
  simp only [List.splitAt_eq]
  by_cases hl : b.rounds.length ≤ rs.length
  · have hm : (rs.take b.rounds.length).length = b.rounds.length := by
      rw [List.length_take]; omega
    rw [if_neg (by rw [hm]; exact fun h => h rfl)]
    cases hs : b.step ft s (rs.take b.rounds.length) cols with
    | error e =>
      constructor
      · intro h; cases h
      · rintro ⟨_, s', k, h, _⟩; cases h
    | ok x =>
      obtain ⟨s', k⟩ := x
      constructor
      · intro h; exact ⟨hl, s', k, rfl, h⟩
      · rintro ⟨_, s₁, k₁, h, h'⟩
        cases h
        exact h'
  · have hm : (rs.take b.rounds.length).length ≠ b.rounds.length := by
      rw [List.length_take]; omega
    rw [if_pos hm]
    constructor
    · intro h; cases h
    · rintro ⟨h, _⟩; exact absurd h hl

/-- **THE FOLD DOES NOT SEE WHETHER TWO NEIGHBOURS ARE MERGED.** -/
theorem foldBlocks_merge (ft : Nat) (n : String) (p q : Block S Cl) (l : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn) :
    foldBlocks ft (p.andThen n q :: l) s rs cols = .ok r ↔
      foldBlocks ft (p :: q :: l) s rs cols = .ok r := by
  have hlen : (p.andThen n q).rounds.length = p.rounds.length + q.rounds.length := by
    simp [Block.andThen]
  rw [Merges.foldCons_iff, Merges.foldCons_iff, hlen]
  constructor
  · rintro ⟨hl, s'', k, hs, hf⟩
    obtain ⟨s', k₁, k₂, h₁, h₂, rfl⟩ := (andThen_step n p q ft s s'' _ cols k).1 hs
    rw [List.take_take, Nat.min_eq_left (Nat.le_add_right _ _)] at h₁
    refine ⟨by omega, s', k₁, h₁, ?_⟩
    rw [Merges.foldCons_iff]
    refine ⟨by rw [List.length_drop]; omega, s'', k₂, ?_, ?_⟩
    · rw [List.drop_take] at h₂
      simpa using h₂
    · rw [List.drop_drop, List.drop_drop]
      simpa [Nat.add_comm] using hf
  · rintro ⟨hl, s', k₁, h₁, hf⟩
    rw [Merges.foldCons_iff] at hf
    obtain ⟨hl₂, s'', k₂, h₂, hf⟩ := hf
    rw [List.length_drop] at hl₂
    refine ⟨by omega, s'', k₁ + k₂, (andThen_step n p q ft s s'' _ cols _).2
      ⟨s', k₁, k₂, ?_, ?_, rfl⟩, ?_⟩
    · rw [List.take_take, Nat.min_eq_left (Nat.le_add_right _ _)]
      exact h₁
    · rw [List.drop_take]
      simpa using h₂
    · rw [List.drop_drop, List.drop_drop] at hf
      simpa [Nat.add_comm] using hf

/-- Two lists of blocks at which the fold returns the same stay so behind a common front. -/
theorem foldBlocks_front (ft : Nat) (X Y : List (Block S Cl))
    (h : ∀ s rs cols r, foldBlocks ft X s rs cols = .ok r ↔ foldBlocks ft Y s rs cols = .ok r) :
    ∀ (pre : List (Block S Cl)) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
      (r : S × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft (pre ++ X) s rs cols = .ok r ↔ foldBlocks ft (pre ++ Y) s rs cols = .ok r
  | [], s, rs, cols, r => h s rs cols r
  | b :: pre, s, rs, cols, r => by
    rw [List.cons_append, List.cons_append, Merges.foldCons_iff, Merges.foldCons_iff]
    constructor
    · rintro ⟨hl, s', k, hs, hf⟩
      exact ⟨hl, s', k, hs, (foldBlocks_front ft X Y h pre _ _ _ r).1 hf⟩
    · rintro ⟨hl, s', k, hs, hf⟩
      exact ⟨hl, s', k, hs, (foldBlocks_front ft X Y h pre _ _ _ r).2 hf⟩

/-- **The second list comes of the first by merging neighbours**, any number of times. -/
inductive Merges : List (Block S Cl) → List (Block S Cl) → Prop
  | refl (l : List (Block S Cl)) : Merges l l
  | step (pre : List (Block S Cl)) (n : String) (p q : Block S Cl) (rest m : List (Block S Cl)) :
    Merges (pre ++ p.andThen n q :: rest) m → Merges (pre ++ p :: q :: rest) m

theorem Merges.fold (ft : Nat) {l m : List (Block S Cl)} (h : Merges l m) :
    ∀ s rs cols r, foldBlocks ft l s rs cols = .ok r ↔ foldBlocks ft m s rs cols = .ok r := by
  induction h with
  | refl l => exact fun _ _ _ _ => Iff.rfl
  | step pre n p q rest m _ ih =>
    intro s rs cols r
    exact ((foldBlocks_front ft _ _ (fun s rs cols r =>
      (foldBlocks_merge ft n p q rest s rs cols r).symm) pre s rs cols r)).trans (ih s rs cols r)

theorem Merges.isEmpty {l m : List (Block S Cl)} (h : Merges l m) : l.isEmpty = m.isEmpty := by
  induction h with
  | refl l => rfl
  | step pre n p q rest m _ ih =>
    rw [← ih]
    cases pre <;> rfl

/-- Where a chain's fold says yes. -/
theorem Merges.chainAt_iff (name : String) (ft : Nat) (bs : List (Block S Cl)) (s s' : S)
    (v : Fmt.View) :
    chainAt name ft bs s v = .ok s' ↔
      bs.isEmpty = false ∧ foldBlocks ft bs s v.rounds v.opened = .ok (s', [], []) := by
  unfold chainAt
  by_cases hE : bs.isEmpty = true
  · simp [hE]
  · have hE' : bs.isEmpty = false := by simpa using hE
    simp only [hE', Bool.false_eq_true, if_false, true_and]
    generalize foldBlocks ft bs s v.rounds v.opened = x
    match x with
    | .error e => simp
    | .ok (s₁, [], []) => simp
    | .ok (s₁, [], c :: cs) => simp
    | .ok (s₁, r :: rs, cs) => simp

/-- **A CHAIN'S FOLD SAYS YES AT THE SAME VIEWS, AND LEAVES THE SAME RECORD, WHETHER OR NOT
NEIGHBOURS ARE MERGED.** (The words of a refusal may part.) -/
theorem Merges.chainAt (name : String) (ft : Nat) {l m : List (Block S Cl)} (h : Merges l m)
    (s s' : S) (v : Fmt.View) :
    Desc.chainAt name ft l s v = .ok s' ↔ Desc.chainAt name ft m s v = .ok s' := by
  rw [Merges.chainAt_iff, Merges.chainAt_iff, h.isEmpty, h.fold ft]


end VerifiableInference.Desc
