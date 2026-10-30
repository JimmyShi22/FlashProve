-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Causal.lean: what comes after a list of sub-protocols does not
matter to them. The verifier's own step (`Block.step`), `foldBlocks` over a list of sub-protocols
(both Johnson/Desc/Block.lean) and the decisions along the list (`decides`, Honest/Law/Kept.lean)
are functions of the state before the list, of the list's own rounds and of the columns that these
rounds read. Rounds and columns that come after them are passed on unchanged. So whether, where and
with which message the first so many sub-protocols reject is fixed as soon as their last challenge
is heard and their columns are filled. No prover, no coin and no input occurs in sections 1 to
4; section 5 counts the tables of rounds as played.

  1  `step_take`, `step_more`   one step reads the columns that its rounds read, and no more
  2  `owed`, `owed_cons`   how many columns a list of sub-protocols reads at its rounds' challenges
  3  `foldBlocks_eq`, `foldBlocks_more`   on `foldBlocks`
  4  `decides_more`, `decides_snoc`   the decisions; a list and one sub-protocol after it
  5  `tables_count`   as many tables are played as the rounds declare oracle messages

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl W X : Type}

/-! ## 1 One step -/

theorem step_take (ft : Nat) (b : Block S Cl) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    b.step ft s rs cols = b.step ft s rs (cols.take (b.want ft rs).length) := by
  unfold Block.step Block.want
  simp only [List.take_take, Nat.min_self]

theorem step_more (ft : Nat) (b : Block S Cl) (s : S) (rs : List Fmt.RoundView) (c₁ c₂ : List OpenedColumn)
    (h : (b.want ft rs).length ≤ c₁.length) : b.step ft s rs (c₁ ++ c₂) = b.step ft s rs c₁ := by
  rw [step_take ft b s rs (c₁ ++ c₂), step_take ft b s rs c₁, List.take_append_of_le_length h]

/-! ## 2 How many columns a list of sub-protocols reads -/

/-- The number of columns that a list of sub-protocols reads, at rounds as a view shows them (not
`Owed` of Honest/Owed.lean). -/
def owed (ft : Nat) (l : List (Block S Cl)) (rs : List Fmt.RoundView) : Nat :=
  ((groupsOf ft (l.flatMap (·.rounds)) (rs.map (·.drawn))).flatMap id).length

theorem owed_cons (ft : Nat) (b : Block S Cl) (l : List (Block S Cl)) (rs : List Fmt.RoundView) :
    owed ft (b :: l) rs =
      (b.want ft (rs.take b.rounds.length)).length + owed ft l (rs.drop b.rounds.length) := by
  unfold owed Block.want
  rw [List.flatMap_cons, groupsOf_app, List.flatMap_append, List.length_append, List.map_take,
    List.map_drop]

/-! ## 3 On `foldBlocks` -/

theorem foldBlocks_eq (ft : Nat) (b : Block S Cl) (l : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    foldBlocks ft (b :: l) s rs cols =
      if (rs.take b.rounds.length).length ≠ b.rounds.length then
        .error (b.name ++ ": the stretch is short")
      else
        match b.step ft s (rs.take b.rounds.length) cols with
        | .error e => .error (b.name ++ ": " ++ e)
        | .ok (s', k) => foldBlocks ft l s' (rs.drop b.rounds.length) (cols.drop k) := by
  conv_lhs => unfold foldBlocks
  simp only [List.splitAt_eq]
  rfl

/-- **What comes after a list is passed on unchanged**: `foldBlocks` gives what it gives over the
list's own rounds and the columns that they read, acceptance or rejection, with the same message. -/
theorem foldBlocks_more (ft : Nat) : ∀ (l : List (Block S Cl)) (s : S) (r₁ r₂ : List Fmt.RoundView)
    (c₁ c₂ : List OpenedColumn), r₁.length = (l.flatMap (·.rounds)).length → c₁.length = owed ft l r₁ →
    foldBlocks ft l s (r₁ ++ r₂) (c₁ ++ c₂) =
      (foldBlocks ft l s r₁ c₁).map fun z => (z.1, z.2.1 ++ r₂, z.2.2 ++ c₂)
  | [], s, r₁, r₂, c₁, c₂, _, _ => rfl
  | b :: l, s, r₁, r₂, c₁, c₂, hr, hc => by
    rw [List.flatMap_cons, List.length_append] at hr
    rw [owed_cons] at hc
    have hn : b.rounds.length ≤ r₁.length := by omega
    have hw : (b.want ft (r₁.take b.rounds.length)).length ≤ c₁.length := by omega
    rw [foldBlocks_eq, foldBlocks_eq, List.take_append_of_le_length hn,
      List.drop_append_of_le_length hn, step_more ft b s _ c₁ c₂ hw]
    split
    · rfl
    · cases hs : b.step ft s (r₁.take b.rounds.length) c₁ with
      | error e => rfl
      | ok z =>
        obtain ⟨s', k⟩ := z
        have hk := ((step_iff ft b s s' _ c₁ k).1 hs).2.2
        subst hk
        show foldBlocks ft l s' (r₁.drop b.rounds.length ++ r₂)
          ((c₁ ++ c₂).drop (b.want ft (r₁.take b.rounds.length)).length) =
          (foldBlocks ft l s' (r₁.drop b.rounds.length)
            (c₁.drop (b.want ft (r₁.take b.rounds.length)).length)).map _
        rw [List.drop_append_of_le_length hw]
        exact foldBlocks_more ft l s' _ r₂ _ c₂ (by rw [List.length_drop]; omega)
          (by rw [List.length_drop]; omega)

/-! ## 4 The decisions -/

theorem decides_more (ft : Nat) : ∀ (l : List (Block S Cl)) (s : S) (r₁ r₂ : List Fmt.RoundView)
    (c₁ c₂ : List OpenedColumn), r₁.length = (l.flatMap (·.rounds)).length → c₁.length = owed ft l r₁ →
    decides ft l s (r₁ ++ r₂) (c₁ ++ c₂) = decides ft l s r₁ c₁
  | [], _, _, _, _, _, _, _ => rfl
  | b :: l, s, r₁, r₂, c₁, c₂, hr, hc => by
    rw [List.flatMap_cons, List.length_append] at hr
    rw [owed_cons] at hc
    have hn : b.rounds.length ≤ r₁.length := by omega
    have hw : (b.want ft (r₁.take b.rounds.length)).length ≤ c₁.length := by omega
    rw [decides_cons, decides_cons, List.take_append_of_le_length hn,
      List.drop_append_of_le_length hn, List.drop_append_of_le_length hw]
    have hsh : b.shown ft (r₁.take b.rounds.length) (c₁ ++ c₂) =
        b.shown ft (r₁.take b.rounds.length) c₁ := by
      unfold Block.shown
      rw [List.take_append_of_le_length hw]
    rw [hsh]
    cases b.decide s ((r₁.take b.rounds.length).map noDigest)
      (b.shown ft (r₁.take b.rounds.length) c₁) with
    | error e => rfl
    | ok s' =>
      exact decides_more ft l s' _ r₂ _ c₂ (by rw [List.length_drop]; omega)
        (by rw [List.length_drop]; omega)

/-- **A list and one sub-protocol after it.** -/
theorem decides_snoc (ft : Nat) (l : List (Block S Cl)) (b : Block S Cl) (s : S)
    (r₁ r₂ : List Fmt.RoundView) (c₁ c₂ : List OpenedColumn) (hr : r₁.length = (l.flatMap (·.rounds)).length)
    (hc : c₁.length = owed ft l r₁) (hr₂ : r₂.length = b.rounds.length)
    (hc₂ : c₂.length = (b.want ft r₂).length) :
    decides ft (l ++ [b]) s (r₁ ++ r₂) (c₁ ++ c₂) =
      (decides ft l s r₁ c₁).bind fun s' =>
        b.decide s' (r₂.map noDigest)
          (regroup ((groupsOf ft b.rounds (r₂.map (·.drawn))).map (·.length)) c₂) := by
  have e1 : (r₁ ++ r₂).drop (l.flatMap (·.rounds)).length = r₂ := List.drop_left' hr
  have e2 : ((groupsOf ft (l.flatMap (·.rounds)) ((r₁ ++ r₂).map (·.drawn))).flatMap id).length =
      c₁.length := by
    rw [hc]
    unfold owed
    rw [List.map_append, ← List.append_nil (l.flatMap (·.rounds)), groupsOf_app,
      List.append_nil, List.take_left' (by rw [List.length_map, hr])]
    simp [groupsOf]
  have e3 : (c₁ ++ c₂).drop c₁.length = c₂ := List.drop_left' rfl
  rw [decides_append, decides_more ft l s r₁ r₂ c₁ c₂ hr hc, e1, e2, e3]
  refine congrArg _ (funext fun s' => ?_)
  rw [decides_cons, ← hr₂, List.take_length, List.drop_length]
  unfold Block.shown
  rw [← hc₂, List.take_length]
  cases b.decide s' (r₂.map noDigest)
    (regroup ((groupsOf ft b.rounds (r₂.map (·.drawn))).map (·.length)) c₂) <;> rfl

/-! ## 5 The tables that are played -/

/-- As many tables are played as the rounds declare oracle messages, if each round declares as many
as its entry counts roots. -/
theorem tables_count : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (ps : List Played), Yields ss ds back ps → (∀ s ∈ ss, s.oracles.length = s.decl.entry.roots) →
    (tablesOf ps).length = (ss.flatMap (·.oracles)).length := by
  intro ss
  induction ss with
  | nil =>
    intro ds back ps h _
    cases ds <;> cases ps <;> first | rfl | simp [Yields] at h
  | cons s ss ih =>
    intro ds back ps h ho
    cases ds with
    | nil => simp [Yields] at h
    | cons d ds =>
      cases ps with
      | nil => simp [Yields] at h
      | cons p ps =>
        simp only [Yields] at h
        obtain ⟨⟨-, -, -, ht, hn⟩, h2⟩ := h
        have hp : p.tables.length = s.oracles.length := by
          cases hm : s.move.isSome with
          | true =>
            obtain ⟨-, z, hz, -, htb⟩ := ht hm
            simp only [Sending.fits, Bool.and_eq_true, beq_iff_eq] at hz
            have e := congrArg List.length hz.2
            rw [List.length_map, List.length_map] at e
            rw [htb, List.length_map, e]
          | false =>
            obtain ⟨-, -, htb⟩ := hn hm
            rw [htb, List.length_replicate, ho s List.mem_cons_self]
        have e : tablesOf (p :: ps) = (p.tables.map fun t => t.map fun x => (p.place, x)) ++
            tablesOf ps := by
          unfold tablesOf
          rw [List.flatMap_cons]
        rw [e, List.length_append, List.length_map, hp, List.flatMap_cons, List.length_append,
          ih ds back.tail ps h2 fun s' hs' => ho s' (List.mem_cons_of_mem _ hs')]

end ProofFile.Honest

#print axioms ProofFile.Honest.step_take
#print axioms ProofFile.Honest.step_more
#print axioms ProofFile.Honest.owed_cons
#print axioms ProofFile.Honest.foldBlocks_eq
#print axioms ProofFile.Honest.foldBlocks_more
#print axioms ProofFile.Honest.decides_more
#print axioms ProofFile.Honest.decides_snoc
#print axioms ProofFile.Honest.tables_count
