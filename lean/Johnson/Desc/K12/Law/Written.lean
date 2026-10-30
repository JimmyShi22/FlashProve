-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Written.lean: from "every dealt column is the written tree's, opening by
opening" to the clauses of `ReadsK` on columns.

Statements and proofs.
Main names:
  `Follows gs src`: every column of group number i is `src i`'s at its position; `src i x` is the
    written column behind opening number i, at x.
  `srcFrom`: the written columns behind the openings of a chain from a stage on, by recursion along
    the chain at the frame's own cuts: as many openings as the stage's fold and switch declare
    belong to the stage's own tree; behind them comes the tree that the switch has written; and so
    on.
  `srcFirst`: the same for the whole test behind the batching: the first stage's openings are the
    trees ts of the group under test, in the book's order, with the written columns `gT t` by the
    book's place.
  `shownFrom_of_follows`, `shownLater_of_follows`, `second_half`: `Follows` gives `ShownFrom`,
    `ShownLater` and "each column of group t is `g t`'s".
Limits: It does not say that any view follows, nor that a view which follows is one on which
`Block.step` says yes. Nothing here is about hiding.
-/
import Johnson.Desc.K12.Law.ReadsK

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- Every column of group number i is src i's at its position. -/
def Follows (gs : Gs) (src : ℕ → ℕ → List UInt64) : Prop :=
  ∀ (i : ℕ) (grp : List (ℕ × List UInt64)), gs[i]? = some grp → ∀ x ∈ grp, x.2 = src i x.1

theorem Follows.drop {gs : Gs} {src : ℕ → ℕ → List UInt64} (h : Follows gs src) (n : ℕ)
    (src' : ℕ → ℕ → List UInt64) (he : ∀ i x, src (n + i) x = src' i x) :
    Follows (gs.drop n) src' := by
  intro i grp hi x hx
  rw [List.getElem?_drop] at hi
  rw [← he]
  exact h _ _ hi x hx

theorem mem_cut {α : Type} (l : List α) (a m : ℕ) (y : α) (h : y ∈ (l.drop a).take m) :
    ∃ i, i < m ∧ l[a + i]? = some y := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 h
  rw [List.getElem?_take] at hi
  split at hi
  · rename_i hlt
    rw [List.getElem?_drop] at hi
    exact ⟨i, hlt, hi⟩
  · cases hi

/-- The written columns behind the openings of a chain from a stage on. d, o: the round that sent
the stage's tree, and its written oracle. -/
def srcFrom : {s : Sg} → (c : Chain s) → (d : PQ.RD) → (wRound d).Orc → c.Bl → Laid → ℕ → ℕ →
    List UInt64
  | _, .last _ _ _ _ _ _ _ => fun d o _ _ _ x => colW d o x
  | s, .step _ _ _ _ _ _ _ dS _ _ _ _ _ _ next => fun d o b l i x =>
    if i < nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)) then colW d o x
    else srcFrom next dS b.2.1.1.1 b.2.2 (l.drop (s.h + s.g + 3))
      (i - (nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)))) x

/-- The written columns behind the openings of the whole test, behind the batching. (At i below the
fold's own openings the subtraction is cut off and ts's first place is read: idle where a fold's cut
opens nothing, which is what the test dealOk asks of the plan.) ts: the places in the book of the
trees that the first switch opens; gT t: the written columns of the tree at the place t. -/
def srcFirst : {s : Sg} → (c : Chain s) → c.Bl → Laid → List ℕ → (ℕ → ℕ → List UInt64) → ℕ → ℕ →
    List UInt64
  | _, .last _ _ _ _ _ _ _ => fun _ _ _ _ _ _ => []
  | s, .step _ _ _ _ _ _ _ dS _ _ _ _ _ _ next => fun b l ts gT i x =>
    if i < nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)) then
      gT (ts.getD (i - nOpen (cutF l (s.h + s.g))) 0) x
    else srcFrom next dS b.2.1.1.1 b.2.2 (l.drop (s.h + s.g + 3))
      (i - (nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)))) x

/-- `Follows` at `srcFrom` gives `ShownFrom`. -/
theorem shownFrom_of_follows : ∀ {s : Sg} (c : Chain s) (d : PQ.RD) (o : (wRound d).Orc) (b : c.Bl)
    (l : Laid) (gs : Gs), Follows gs (srcFrom c d o b l) → ShownFrom c d o b l gs := by
  intro s c
  induction c with
  | last s e dL dB fu fs εb =>
    intro d o b l gs h grp hg x hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hg
    exact h i grp hi x hx
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    intro d o b l gs h
    refine ⟨?_, ?_⟩
    · intro grp hg x hx
      obtain ⟨i, hlt, hi⟩ := mem_cut _ _ _ _ hg
      have h1 := h _ grp hi x hx
      have e1 : srcFrom (Chain.step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next) d o b l
          (nOpen (cutF l (s.h + s.g)) + i) x.1 = colW d o x.1 := by
        show (if _ then _ else _) = _
        rw [if_pos (by omega)]
      rw [h1, e1]
    · refine ih dS b.2.1.1.1 b.2.2 _ _ (h.drop _ _ fun i x => ?_)
      show (if _ then _ else _) = _
      rw [if_neg (by omega), Nat.add_sub_cancel_left]

/-- `Follows` at `srcFirst` gives `ShownLater`. -/
theorem shownLater_of_follows {s : Sg} (c : Chain s) (b : c.Bl) (l : Laid) (ts : List ℕ)
    (gT : ℕ → ℕ → List UInt64) (gs : Gs) (h : Follows gs (srcFirst c b l ts gT)) :
    ShownLater c b l gs := by
  cases c with
  | last s e dL dB fu fs εb => trivial
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next =>
    refine shownFrom_of_follows next dS b.2.1.1.1 b.2.2 _ _ (h.drop _ _ fun i x => ?_)
    show (if _ then _ else _) = _
    rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem forall₂_of_index {α β : Type} (R : α → β → Prop) : ∀ (l : List α) (m : List β),
    l.length = m.length → (∀ (j : ℕ) (a : α) (b : β), l[j]? = some a → m[j]? = some b → R a b) →
    List.Forall₂ R l m
  | [], [], _, _ => List.Forall₂.nil
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | a :: l, b :: m, h, H =>
    List.Forall₂.cons (H 0 a b rfl rfl)
      (forall₂_of_index R l m (Nat.succ.inj h) fun j a' b' h1 h2 => H (j + 1) a' b' h1 h2)

/-- The second half of `GroupsAre`, at the first switch's cut of the groups. -/
theorem second_half {s : Sg} (c : Chain s) (b : c.Bl) (l : Laid) (ts : List ℕ)
    (gT : ℕ → ℕ → List UInt64) (gs : Gs) (h : Follows gs (srcFirst c b l ts gT))
    (hc : c.len ≠ 0) (hlen : ts.length = (grpS l (s.h + s.g) gs).length) :
    List.Forall₂ (fun t (grp : List (ℕ × List UInt64)) => ∀ x ∈ grp, some (gT t x.1) = some x.2) ts
      (grpS l (s.h + s.g) gs) := by
  cases c with
  | last s e dL dB fu fs εb => exact absurd rfl hc
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next =>
    refine forall₂_of_index _ _ _ hlen fun j t grp ht hg x hx => ?_
    unfold grpS at hg
    rw [List.getElem?_take] at hg
    split at hg
    · rename_i hlt
      rw [List.getElem?_drop] at hg
      have h1 := h _ grp hg x hx
      have e1 : srcFirst (Chain.step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next) b l ts gT
          (nOpen (cutF l (s.h + s.g)) + j) x.1 = gT t x.1 := by
        show (if _ then _ else _) = _
        rw [if_pos (by omega), Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD, ht]
        rfl
      rw [h1, e1]
    · cases hg

end H2K.JointK
