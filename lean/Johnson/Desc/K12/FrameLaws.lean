-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/FrameLaws.lean: the proximity test (the kind K12): laws of its frame
(Johnson/Desc/K12/Frame.lean), for all parts and all numbers of a place. Theorems; no code.

  stagesFrom_rounds, stagesFrom_oracles   the stages' blocks state, in order, just the rounds and
      the oracle messages that they were dealt: the frame's cut loses none, doubles none and turns
      no order, whatever the stages' numbers are.
  k12_rounds, k12_oracles   where the block's test on the plan says yes, the block's rounds are the
      whole list that the numbers give (`H2U.roundsOfNums`), and its oracle messages are the
      place's.
  andThen_ok, asks_ok   what a yes of two blocks as one, and of a question of the record, holds.
  four_ok, k12_ok   a yes of the test holds the front's yes, then the batching's on the rounds and
      groups that it states, then that the group is the first stage's, then the stages' yes on all
      that lies behind: in that order, each from the record that the one before leaves.
  five_ok, stagesFrom_ok, stagesFrom_last   the like for the stages, both ways: a stage that is not
      the last is the fold, the switch, the batching behind it, whether the next mask has come, then
      the stages from the next on; the last stage is the base case.
What they are for: that the block's rounds are the made plan's stretch is held by runs at two plans;
these say, for every plan, that the frame adds nothing of its own between the rounds' maker and the
block. Nothing on what a part decides. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12
open Fmt.M1 (Stage)

variable {T Cl : Type}

/-- A list cut at a, then at two behind a, is the list. -/
theorem cut3 {α : Type} (l : List α) (k : Nat) :
    l.take (1 + k) ++ (l.drop (1 + k)).take 2 ++ l.drop (k + 3) = l := by
  have h : l.drop (k + 3) = (l.drop (1 + k)).drop 2 := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [h, List.append_assoc, List.take_append_drop, List.take_append_drop]

theorem stagesFrom_rounds (X : Parts T) (p : P12) (rest : List Stage) :
    ∀ (j : Nat) (cur : Stage) (l : Laid),
      (stagesFrom X p j cur rest l : Block T Cl).rounds = l.map (·.1) := by
  induction rest with
  | nil => intro j cur l; simp [stagesFrom, Part.at]
  | cons next rest ih =>
    intro j cur l
    simp only [stagesFrom, Block.andThen, Part.at, asks, ih, List.map_nil, List.append_nil]
    rw [← List.map_append, ← List.map_append, cut3]

theorem stagesFrom_oracles (X : Parts T) (p : P12) (rest : List Stage) :
    ∀ (j : Nat) (cur : Stage) (l : Laid),
      (stagesFrom X p j cur rest l : Block T Cl).oracles = l.map (·.2) := by
  induction rest with
  | nil => intro j cur l; simp [stagesFrom, Part.at]
  | cons next rest ih =>
    intro j cur l
    simp only [stagesFrom, Block.andThen, Part.at, asks, ih, List.map_nil, List.append_nil]
    rw [← List.map_append, ← List.map_append, cut3]

/-- **The block's rounds are the whole list that the numbers give.** -/
theorem k12_rounds (X : Parts T) (p : P12) (h : (proximityTestKind X p : Block T Cl).planOk = true) :
    H2U.roundsOfNums p.nums = some (proximityTestKind X p : Block T Cl).rounds := by
  unfold proximityTestKind at h ⊢
  split at h
  · rename_i first rest rs os hs hr ho
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have hl : p.oracles.length = rs.length := h.1.1.2
    simp only [hr, Block.andThen, Part.at, asks, stagesFrom_rounds, List.map_nil,
      List.nil_append, List.append_nil]
    rw [← List.map_append, List.take_append_drop, List.map_fst_zip (by omega)]
  · simp at h

/-- **The block's oracle messages are the place's.** -/
theorem k12_oracles (X : Parts T) (p : P12) (h : (proximityTestKind X p : Block T Cl).planOk = true) :
    (proximityTestKind X p : Block T Cl).oracles = p.oracles := by
  unfold proximityTestKind at h ⊢
  split at h
  · rename_i first rest rs os hs hr ho
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have hl : p.oracles.length = rs.length := h.1.1.2
    simp only [Block.andThen, Part.at, asks, stagesFrom_oracles, List.map_nil,
      List.nil_append, List.append_nil]
    rw [← List.map_append, List.take_append_drop, List.map_snd_zip (by omega)]
  · simp at h

/-! ## What a yes of the block holds -/

/-- Two blocks as one say yes just where the first says yes on its own rounds and groups and the
second on the rest, from the record that the first leaves. -/
theorem andThen_ok {S : Type} (name : String) (a b : Block S Cl) (s s'' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (a.andThen name b).decide s rs gs = .ok s'' ↔
      ∃ s', a.decide s (rs.take a.rounds.length) (gs.take a.openings) = .ok s' ∧
        b.decide s' (rs.drop a.rounds.length) (gs.drop a.openings) = .ok s'' := by
  simp only [Block.andThen]
  cases h : a.decide s (rs.take a.rounds.length) (gs.take a.openings) with
  | error e => simp [Except.bind]
  | ok s' => simp [Except.bind]

/-- A question of the record says yes just where the answer is yes, and turns nothing. -/
theorem asks_ok (name : String) (place : Place) (ok : T → Bool) (t t' : T) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (asks name place ok : Block T Cl).decide t rs gs = .ok t' ↔ ok t = true ∧ t' = t := by
  simp only [asks, need]
  cases h : ok t with
  | false => simp [Except.map]
  | true => simp [Except.map, eq_comm]

/-- The groups of a block without a round: none. -/
theorem openings_nil {S : Type} (a : Block S Cl) (h : a.rounds = []) : a.openings = 0 := by
  simp [Block.openings, h]

/-- In front of a block, a block without a round adds no round and no group. -/
theorem andThen_left_nil {S : Type} (name : String) (a b : Block S Cl) (h : a.rounds = []) :
    (a.andThen name b).rounds = b.rounds ∧ (a.andThen name b).openings = b.openings := by
  simp [Block.andThen, Block.openings, h]

/-- Behind a block, likewise. -/
theorem andThen_right_nil {S : Type} (name : String) (a b : Block S Cl) (h : b.rounds = []) :
    (a.andThen name b).rounds = a.rounds ∧ (a.andThen name b).openings = a.openings := by
  simp [Block.andThen, Block.openings, h]

/-- Four blocks in a row, of which the first and the third have no round. -/
theorem four_ok {S : Type} (n₁ n₂ n₃ : String) (A B Q R : Block S Cl) (hA : A.rounds = [])
    (hQ : Q.rounds = []) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (((A.andThen n₁ B).andThen n₂ Q).andThen n₃ R).decide s rs gs = .ok s' ↔
      ∃ s₀ s₁ s₂, A.decide s [] [] = .ok s₀ ∧
        B.decide s₀ (rs.take B.rounds.length) (gs.take B.openings) = .ok s₁ ∧
        Q.decide s₁ [] [] = .ok s₂ ∧
        R.decide s₂ (rs.drop B.rounds.length) (gs.drop B.openings) = .ok s' := by
  have e₁ := andThen_left_nil n₁ A B hA
  have e₂ := andThen_right_nil n₂ (A.andThen n₁ B) Q hQ
  simp only [andThen_ok, e₂.1, e₂.2, e₁.1, e₁.2, hA, openings_nil A hA, List.length_nil,
    List.drop_zero, List.take_take, Nat.min_self, List.drop_take_self]
  constructor
  · rintro ⟨s₂, ⟨s₁, ⟨s₀, h0, h1⟩, h2⟩, h3⟩
    exact ⟨s₀, s₁, s₂, h0, h1, h2, h3⟩
  · rintro ⟨s₀, s₁, s₂, h0, h1, h2, h3⟩
    exact ⟨s₂, ⟨s₁, ⟨s₀, h0, h1⟩, h2⟩, h3⟩

/-- The batching's block inside the test: the part at the first of the dealt rounds. -/
def batAt (X : Parts T) (p : P12) (l : Laid) : Block T Cl :=
  (X.bat p ((l.take 1).map (·.1))).at "the batching" p.place (l.take 1)

/-- **A yes of the proximity test holds, in this order**: the front's yes on no round; the
batching's yes, from the record that the front leaves, on the rounds and groups that the batching
states, which come first; that the group as the record then has it is the first stage's; and the
stages' yes, from that same record, on all the rounds and groups behind the batching's. -/
theorem k12_ok (X : Parts T) (p : P12) (t t' : T) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind X p : Block T Cl).decide t rs gs = .ok t') :
    ∃ first rest ds t₀ t₁,
      p.nums.stages = first :: rest ∧ H2U.roundsOfNums p.nums = some ds ∧
      (X.front p).decide t [] [] = .ok t₀ ∧
      (batAt X p (ds.zip p.oracles) : Block T Cl).decide t₀
        (rs.take (batAt X p (ds.zip p.oracles) : Block T Cl).rounds.length)
        (gs.take (batAt X p (ds.zip p.oracles) : Block T Cl).openings) = .ok t₁ ∧
      (X.group t₁).any (firstFits first) = true ∧
      (stagesFrom X p 0 first rest ((ds.zip p.oracles).drop 1) : Block T Cl).decide t₁
        (rs.drop (batAt X p (ds.zip p.oracles) : Block T Cl).rounds.length)
        (gs.drop (batAt X p (ds.zip p.oracles) : Block T Cl).openings) = .ok t' := by
  unfold proximityTestKind at h
  split at h
  · rename_i first rest ds os hs hr ho
    have h' := (four_ok "the front" "the batching" "the test"
      ((X.front p).at "the front" p.place [] : Block T Cl) (batAt X p (ds.zip p.oracles))
      (asks "the group is not the first stage's" p.place fun t =>
        (X.group t).any (firstFits first))
      (stagesFrom X p 0 first rest ((ds.zip p.oracles).drop 1))
      (by simp [Part.at]) (by simp [asks]) t t' rs gs).1 h
    obtain ⟨s₀, s₁, s₂, h0, h1, h2, h3⟩ := h'
    obtain ⟨hf, he⟩ := (asks_ok _ _ _ _ _ _ _).1 h2
    subst he
    exact ⟨first, rest, ds, s₀, _, hs, hr, by simpa [Part.at] using h0, h1, hf, h3⟩
  · simp [asks, need, Except.map] at h

/-- Five blocks in a row, of which the third and the fourth have no round. -/
theorem five_ok {S : Type} (n₁ n₂ n₃ n₄ : String) (A B C Q R : Block S Cl) (hC : C.rounds = [])
    (hQ : Q.rounds = []) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    ((((A.andThen n₁ B).andThen n₂ C).andThen n₃ Q).andThen n₄ R).decide s rs gs = .ok s' ↔
      ∃ s₁ s₂ s₃ s₄,
        A.decide s (rs.take A.rounds.length) (gs.take A.openings) = .ok s₁ ∧
        B.decide s₁ ((rs.drop A.rounds.length).take B.rounds.length)
          ((gs.drop A.openings).take B.openings) = .ok s₂ ∧
        C.decide s₂ [] [] = .ok s₃ ∧ Q.decide s₃ [] [] = .ok s₄ ∧
        R.decide s₄ (rs.drop (A.rounds.length + B.rounds.length))
          (gs.drop (A.openings + B.openings)) = .ok s' := by
  have e₂ := andThen_right_nil n₂ (A.andThen n₁ B) C hC
  have e₃ := andThen_right_nil n₃ ((A.andThen n₁ B).andThen n₂ C) Q hQ
  have r₁ : (A.andThen n₁ B).rounds.length = A.rounds.length + B.rounds.length := by
    simp [Block.andThen]
  have o₁ : (A.andThen n₁ B).openings = A.openings + B.openings := by
    simp only [Block.openings, Block.andThen, List.foldl_append]
    generalize A.rounds.foldl (fun n r => n + r.stored.length + r.opens.length) 0 = a
    induction B.rounds generalizing a with
    | nil => simp
    | cons r l ih =>
      simp only [List.foldl_cons]
      rw [ih, ih (0 + r.stored.length + r.opens.length)]
      omega
  simp only [andThen_ok, e₃.1, e₃.2, e₂.1, e₂.2, r₁, o₁, List.take_take, Nat.min_self,
    List.drop_take_self, List.drop_take, Nat.add_sub_cancel_left,
    Nat.min_eq_left (Nat.le_add_right _ _)]
  constructor
  · rintro ⟨s₄, ⟨s₃, ⟨s₂, ⟨s₁, h1, h2⟩, h3⟩, h4⟩, h5⟩
    exact ⟨s₁, s₂, s₃, s₄, h1, h2, h3, h4, h5⟩
  · rintro ⟨s₁, s₂, s₃, s₄, h1, h2, h3, h4, h5⟩
    exact ⟨s₄, ⟨s₃, ⟨s₂, ⟨s₁, h1, h2⟩, h3⟩, h4⟩, h5⟩

/-- The fold's and the switch's blocks inside the test, at the rounds still to be dealt. -/
def foldAt (X : Parts T) (p : P12) (j : Nat) (cur : Stage) (l : Laid) : Block T Cl :=
  (X.fold p j cur ((l.take (1 + cur.k)).map (·.1))).at "the fold" p.place (l.take (1 + cur.k))

def switchAt (X : Parts T) (p : P12) (j : Nat) (cur next : Stage) (last : Bool) (l : Laid) :
    Block T Cl :=
  (X.switch p j cur next last (((l.drop (1 + cur.k)).take 2).map (·.1))).at "the switch" p.place
    ((l.drop (1 + cur.k)).take 2)

/-- **A yes of the stages from a stage that is not the last holds just this, in this order**: the
fold's yes on the rounds and groups that it states; the switch's on those that it states, which
come next; the yes of the batching behind the switch, on none; that the next mask has come, if the
masks come early; and the yes of the stages from the next stage on, on all that lies behind. -/
theorem stagesFrom_ok (X : Parts T) (p : P12) (j : Nat) (cur next : Stage) (rest : List Stage)
    (l : Laid) (t t' : T) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (stagesFrom X p j cur (next :: rest) l : Block T Cl).decide t rs gs = .ok t' ↔
      ∃ t₁ t₂ t₃,
        (foldAt X p j cur l : Block T Cl).decide t
          (rs.take (foldAt X p j cur l : Block T Cl).rounds.length)
          (gs.take (foldAt X p j cur l : Block T Cl).openings) = .ok t₁ ∧
        (switchAt X p j cur next rest.isEmpty l : Block T Cl).decide t₁
          ((rs.drop (foldAt X p j cur l : Block T Cl).rounds.length).take
            (switchAt X p j cur next rest.isEmpty l : Block T Cl).rounds.length)
          ((gs.drop (foldAt X p j cur l : Block T Cl).openings).take
            (switchAt X p j cur next rest.isEmpty l : Block T Cl).openings) = .ok t₂ ∧
        (X.batBehind p (j + 1) next (((l.drop (1 + cur.k)).take 2).map (·.1))).decide t₂ [] []
          = .ok t₃ ∧
        (!p.early || X.maskCame t₃) = true ∧
        (stagesFrom X p (j + 1) next rest (l.drop (cur.k + 3)) : Block T Cl).decide t₃
          (rs.drop ((foldAt X p j cur l : Block T Cl).rounds.length +
            (switchAt X p j cur next rest.isEmpty l : Block T Cl).rounds.length))
          (gs.drop ((foldAt X p j cur l : Block T Cl).openings +
            (switchAt X p j cur next rest.isEmpty l : Block T Cl).openings)) = .ok t' := by
  have h := five_ok "a stage" "a stage" "a stage" "the stages" (foldAt X p j cur l : Block T Cl)
    (switchAt X p j cur next rest.isEmpty l)
    ((X.batBehind p (j + 1) next (((l.drop (1 + cur.k)).take 2).map (·.1))).at
      "the batching behind the switch" p.place [])
    (asks "the next mask has not come" p.place fun t => !p.early || X.maskCame t)
    (stagesFrom X p (j + 1) next rest (l.drop (cur.k + 3)))
    (by simp [Part.at]) (by simp [asks]) t t' rs gs
  constructor
  · intro h0
    obtain ⟨s₁, s₂, s₃, s₄, h1, h2, h3, h4, h5⟩ := h.1 h0
    obtain ⟨hm, he⟩ := (asks_ok _ _ _ _ _ _ _).1 h4
    subst he
    exact ⟨s₁, s₂, _, h1, h2, by simpa [Part.at] using h3, hm, h5⟩
  · rintro ⟨s₁, s₂, s₃, h1, h2, h3, hm, h5⟩
    exact h.2 ⟨s₁, s₂, s₃, s₃, h1, h2, by simpa [Part.at] using h3,
      (asks_ok _ _ _ _ _ _ _).2 ⟨hm, rfl⟩, h5⟩

/-- At the last stage the stages' yes is the base case's. -/
theorem stagesFrom_last (X : Parts T) (p : P12) (j : Nat) (cur : Stage) (l : Laid) (t : T)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (stagesFrom X p j cur [] l : Block T Cl).decide t rs gs =
      (X.base p j cur (l.map (·.1))).decide t rs gs := by
  simp [stagesFrom, Part.at]

end VerifiableInference.Desc.K12
