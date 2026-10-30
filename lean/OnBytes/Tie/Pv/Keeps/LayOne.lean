-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Keeps/LayOne.lean: the rule that places the oracle messages of one prover's message
in trees (layTrees, OnBytes/Iop/Ground.lean), at a tree that holds one oracle message alone: the
tree's depth and width are those of that message.

Definitions, statements and proofs. layTrees goes through the messages three times: two passes open
the trees and say which message lies in which (OnBytes/Params/Fit/LayPasses.lean has them under
names); a third loop fills each tree's lists of symbols. A last step gives a tree without main
symbols the depth of its mask rows. This file names the third loop's step, follows one message i0
through the three loops, and reads off its tree's shape where no other message lies in that tree.
Main names:
  depth1 codes s, width1 s: the depth and the width of a tree that holds one message of the shape s.
  fillStep, fixShape: the third loop's step; the last step. layTrees_some: layTrees in these names.
  Placed, laid_spec: behind the two passes the message i0 has a tree, of its main rows' depth.
  fill_spec: behind the third loop that tree holds the symbols of i0 alone.
  lay_one: the tree of i0 is one of the trees returned, and has depth1 and width1 of i0's shape.
Limits: nothing on a tree with two messages or more. Of a tree's shape: logN and the sum of the two
widths alone. That layTrees returns is a premise.


-/
import OnBytes.Params.Fit.LayPasses

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Keeps.Fit

open OnBytes
open OnBytes.Params (layStep layPass laidOf)

/-! ## Entries of arrays -/

theorem getD_empty {α : Type} (t : Nat) (d : α) : (#[] : Array α).getD t d = d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.zero_le t)]
  rfl

theorem getD_push {α : Type} (a : Array α) (x d : α) (t : Nat) :
    (a.push x).getD t d = if t = a.size then x else a.getD t d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split <;> rfl

theorem getD_modify {α : Type} (a : Array α) (t : Nat) (f : α → α) (d : α)
    (ht : t < a.size) : (a.modify t f).getD t d = f (a.getD t d) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_modify, if_pos rfl,
    Array.getElem?_eq_getElem ht]
  rfl

theorem getD_modify_ne {α : Type} (a : Array α) (i t : Nat) (f : α → α) (d : α)
    (h : i ≠ t) : (a.modify i f).getD t d = a.getD t d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_modify, if_neg h]

theorem getD_set {α : Type} (a : Array α) (i : Nat) (v d : α) (h : i < a.size) :
    (a.setIfInBounds i v).getD i d = v := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, if_pos rfl, if_pos h]
  rfl

theorem getD_set_ne {α : Type} (a : Array α) (i t : Nat) (v d : α) (h : i ≠ t) :
    (a.setIfInBounds i v).getD t d = a.getD t d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
    if_neg h]

theorem getD_map {α β : Type} (a : Array α) (f : α → β) (t : Nat) (d : α) (e : β)
    (ht : t < a.size) : (a.map f).getD t e = f (a.getD t d) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_eq_getElem ht]
  rfl

/-! ## One message's depth and width -/

/-- The depth of a tree that holds one oracle message of the shape s: that of its main rows' code;
without main symbols that of its mask rows' code; 0 if it has neither. A code's number beyond the
list reads as the default code; Blk.shapeOk refuses such a shape. -/
def depth1 (codes : Codes) (s : OracleShape) : Nat :=
  if s.mainRows * s.mainDeg = 0 then
    (if 0 < s.maskRows then (codes.mask.getD s.maskCode default).logN else 0)
  else (codes.base.getD s.code default).logN

/-- Its width: the base-field elements of all its rows in a column. -/
def width1 (s : OracleShape) : Nat := s.mainRows * s.mainDeg + s.maskRows * 3

/-! ## The third loop and the last step, under names -/

/-- One step of the loop that fills the trees. tree: for each message its tree. -/
def fillStep (codes : Codes) (sent : Array OracleNotice) (tree : Array Nat)
    (s : Array TreeShape × Array Nat × Array Nat) (i : Nat) :
    Option (Array TreeShape × Array Nat × Array Nat) :=
  let n := sent.getD i default
  let at0 := tree.getD i 0
  let zk := (codes.mask.getD n.shape.maskCode default).logN
  let before := (s.1.getD at0 {}).mainSymbols.size
  if 0 < n.shape.maskRows && 0 < s.2.2.getD at0 0 && (s.1.getD at0 {}).logNzk != zk then none
  else
    pure (s.1.modify at0 fun t =>
        { t with
          logNzk := if 0 < n.shape.maskRows then zk else t.logNzk
          mainSymbols := t.mainSymbols.push (n.shape.mainRows * n.shape.mainDeg)
          maskSymbols := t.maskSymbols.push (n.shape.maskRows * 3) },
      s.2.1.push before, s.2.2.modify at0 (· + n.shape.maskRows * 3))

/-- The last step: a tree without main symbols has the depth of its mask rows. -/
def fixShape (t : TreeShape) : TreeShape :=
  if t.mainWidth == 0 then { t with logN := t.logNzk } else t

/-- What layTrees returns, in these names. -/
theorem layTrees_some {codes : Codes} {sent : Array OracleNotice} {T : TreeLay}
    (h : layTrees codes sent = some T) :
    ∃ filled, (List.range sent.size).foldlM (fillStep codes sent (laidOf codes sent).2.2)
        ((laidOf codes sent).1, #[], Array.replicate (laidOf codes sent).1.size 0) = some filled ∧
      T.tree = (laidOf codes sent).2.2 ∧ T.shapes = filled.1.map fixShape := by
  unfold layTrees at h
  dsimp only at h
  obtain ⟨filled, hf, h2⟩ := Option.bind_eq_some_iff.mp h
  split at h2
  · rw [← Option.some.inj h2]
    exact ⟨filled, hf, rfl, rfl⟩
  · cases h2

/-! ## The two passes, at one message -/

section One
variable (codes : Codes) (sent : Array OracleNotice) (i0 : Nat)

/-- No tree has a symbol yet. -/
def Blank (a : Array TreeShape) : Prop :=
  ∀ t, (a.getD t {}).logNzk = 0 ∧ (a.getD t {}).mainSymbols = #[] ∧
    (a.getD t {}).maskSymbols = #[]

theorem blank_push {a : Array TreeShape} (h : Blank a) (x : TreeShape)
    (hx : x.logNzk = 0 ∧ x.mainSymbols = #[] ∧ x.maskSymbols = #[]) : Blank (a.push x) :=
  fun t => by
    rw [getD_push]
    split
    · exact hx
    · exact h t

/-- What every step of a pass keeps. -/
def PInv (s : Array TreeShape × Array Nat × Array Nat) : Prop :=
  Blank s.1 ∧ s.2.2.size = sent.size

/-- The message i0 has a tree; if it has main rows, the tree has their code's depth. -/
def Placed (s : Array TreeShape × Array Nat × Array Nat) : Prop :=
  s.2.2.getD i0 0 < s.1.size ∧ ((sent.getD i0 default).shape.mainRows ≠ 0 →
    (s.1.getD (s.2.2.getD i0 0) {}).logN =
      (codes.base.getD (sent.getD i0 default).shape.code default).logN)

variable {codes sent i0}

theorem layStep_skip {b : Bool} {s : Array TreeShape × Array Nat × Array Nat} {i : Nat}
    (h : (((sent.getD i default).shape.mainRows == 0) != b) = true) :
    layStep codes sent b s i = s := by
  unfold layStep
  dsimp only
  rw [if_pos h]

/-- A step that places its message: in a tree that is there, or in a new one. -/
theorem layStep_act {b : Bool} {s : Array TreeShape × Array Nat × Array Nat} {i : Nat}
    (h : (((sent.getD i default).shape.mainRows == 0) != b) = false) :
    (∃ t, t < s.1.size ∧ (b = false → (s.1.getD t {}).logN =
          (codes.base.getD (sent.getD i default).shape.code default).logN) ∧
        layStep codes sent b s i = (s.1, s.2.1, s.2.2.setIfInBounds i t)) ∨
      layStep codes sent b s i =
        (s.1.push (if b then {} else
            { logN := (codes.base.getD (sent.getD i default).shape.code default).logN }),
          s.2.1.push (sent.getD i default).leafClass, s.2.2.setIfInBounds i s.1.size) := by
  unfold layStep
  dsimp only
  rw [if_neg (by rw [h]; exact Bool.false_ne_true)]
  split
  · next t e =>
    refine Or.inl ⟨t, List.mem_range.1 (List.mem_of_find?_eq_some e), fun hb => ?_, rfl⟩
    have q := List.find?_some e
    simp only [Bool.and_eq_true] at q
    have q2 := q.2
    rw [hb, Bool.false_or] at q2
    exact beq_iff_eq.1 q2
  · exact Or.inr rfl

theorem flag_of_eq {m b : Bool} (h : m = b) : (m != b) = false := by
  subst h
  cases m <;> rfl

theorem flag_of_ne {m b : Bool} (h : m ≠ b) : (m != b) = true := by
  cases m <;> cases b <;> first | rfl | exact absurd rfl h

theorem pinv_step {b : Bool} {s : Array TreeShape × Array Nat × Array Nat} (i : Nat)
    (h : PInv sent s) : PInv sent (layStep codes sent b s i) := by
  by_cases hf : ((sent.getD i default).shape.mainRows == 0) = b
  · rcases layStep_act (codes := codes) (s := s) (flag_of_eq hf) with ⟨t, _, _, e⟩ | e
    · rw [e]
      exact ⟨h.1, by rw [Array.size_setIfInBounds]; exact h.2⟩
    · rw [e]
      refine ⟨blank_push h.1 _ ?_, by rw [Array.size_setIfInBounds]; exact h.2⟩
      split <;> exact ⟨rfl, rfl, rfl⟩
  · rw [layStep_skip (flag_of_ne hf)]
    exact h

theorem placed_other {b : Bool} {s : Array TreeShape × Array Nat × Array Nat} {i : Nat}
    (hi : i ≠ i0) (h : Placed codes sent i0 s) :
    Placed codes sent i0 (layStep codes sent b s i) := by
  by_cases hf : ((sent.getD i default).shape.mainRows == 0) = b
  · rcases layStep_act (codes := codes) (s := s) (flag_of_eq hf) with ⟨t, _, _, e⟩ | e
    · rw [e]
      unfold Placed
      dsimp only
      rw [getD_set_ne _ _ _ _ _ hi]
      exact h
    · rw [e]
      unfold Placed
      dsimp only
      rw [getD_set_ne _ _ _ _ _ hi, Array.size_push, getD_push, if_neg (Nat.ne_of_lt h.1)]
      exact ⟨Nat.lt_succ_of_lt h.1, h.2⟩
  · rw [layStep_skip (flag_of_ne hf)]
    exact h

theorem placed_self {b : Bool} {s : Array TreeShape × Array Nat × Array Nat}
    (hs : i0 < s.2.2.size) (hf : ((sent.getD i0 default).shape.mainRows == 0) = b) :
    Placed codes sent i0 (layStep codes sent b s i0) := by
  have hb : (sent.getD i0 default).shape.mainRows ≠ 0 → b = false := fun hne => by
    cases b with
    | false => rfl
    | true => exact absurd (beq_iff_eq.1 hf) hne
  rcases layStep_act (codes := codes) (s := s) (flag_of_eq hf) with ⟨t, ht, hl, e⟩ | e
  · rw [e]
    unfold Placed
    dsimp only
    rw [getD_set _ _ _ _ hs]
    exact ⟨ht, fun hne => hl (hb hne)⟩
  · rw [e]
    unfold Placed
    dsimp only
    rw [getD_set _ _ _ _ hs, Array.size_push, getD_push, if_pos rfl]
    refine ⟨Nat.lt_succ_self _, fun hne => ?_⟩
    rw [hb hne]
    rfl

/-- A pass. -/
theorem pass_spec (b : Bool) (hi0 : i0 < sent.size)
    (s0 : Array TreeShape × Array Nat × Array Nat) (h0 : PInv sent s0) :
    PInv sent (layPass codes sent b s0) ∧
      ((Placed codes sent i0 s0 ∨ ((sent.getD i0 default).shape.mainRows == 0) = b) →
        Placed codes sent i0 (layPass codes sent b s0)) := by
  have key : ∀ k, PInv sent ((List.range k).foldl (layStep codes sent b) s0) ∧
      ((Placed codes sent i0 s0 ∨
          (((sent.getD i0 default).shape.mainRows == 0) = b ∧ i0 < k)) →
        Placed codes sent i0 ((List.range k).foldl (layStep codes sent b) s0)) := by
    intro k
    induction k with
    | zero =>
      exact ⟨h0, fun q => q.elim id fun r => absurd r.2 (Nat.not_lt_zero _)⟩
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      obtain ⟨p, q⟩ := ih
      refine ⟨pinv_step k p, fun r => ?_⟩
      by_cases e : k = i0
      · subst e
        by_cases hM : ((sent.getD k default).shape.mainRows == 0) = b
        · exact placed_self (by rw [p.2]; exact hi0) hM
        · rw [layStep_skip (flag_of_ne hM)]
          exact q (r.elim Or.inl fun z => absurd z.1 hM)
      · exact placed_other e (q (r.imp id fun z => ⟨z.1, by omega⟩))
  obtain ⟨p, q⟩ := key sent.size
  exact ⟨p, fun r => q (r.imp id fun z => ⟨z, hi0⟩)⟩

/-- Behind the two passes. -/
theorem laid_spec (hi0 : i0 < sent.size) :
    PInv sent (laidOf codes sent) ∧ Placed codes sent i0 (laidOf codes sent) := by
  have h0 : PInv sent ((#[], #[], Array.replicate sent.size 0) :
      Array TreeShape × Array Nat × Array Nat) :=
    ⟨fun t => by
      show ((#[] : Array TreeShape).getD t {}).logNzk = 0 ∧ _ ∧ _
      rw [getD_empty]
      exact ⟨rfl, rfl, rfl⟩, Array.size_replicate⟩
  obtain ⟨p1, q1⟩ := pass_spec (codes := codes) (i0 := i0) false hi0 _ h0
  obtain ⟨p2, q2⟩ := pass_spec (codes := codes) (i0 := i0) true hi0 _ p1
  refine ⟨p2, q2 ?_⟩
  cases hM : ((sent.getD i0 default).shape.mainRows == 0) with
  | false => exact Or.inl (q1 (Or.inr hM))
  | true => exact Or.inr rfl

/-! ## The third loop, at a tree that holds one message -/

variable (codes sent i0)

/-- What the step of i0 makes of its tree. -/
def fillOne (L : TreeShape) : TreeShape :=
  { L with
    logNzk := if 0 < (sent.getD i0 default).shape.maskRows then
      (codes.mask.getD (sent.getD i0 default).shape.maskCode default).logN else L.logNzk
    mainSymbols := L.mainSymbols.push
      ((sent.getD i0 default).shape.mainRows * (sent.getD i0 default).shape.mainDeg)
    maskSymbols := L.maskSymbols.push ((sent.getD i0 default).shape.maskRows * 3) }

variable {codes sent i0}

theorem fill_spec (A0 : Array TreeShape) (p0 w0 tree : Array Nat) (hτ : tree.getD i0 0 < A0.size)
    (uniq : ∀ j, j < sent.size → tree.getD j 0 = tree.getD i0 0 → j = i0) :
    ∀ (k : Nat) (s : Array TreeShape × Array Nat × Array Nat), k ≤ sent.size →
      (List.range k).foldlM (fillStep codes sent tree) (A0, p0, w0) = some s →
      s.1.size = A0.size ∧ s.1.getD (tree.getD i0 0) {} =
        if i0 < k then fillOne codes sent i0 (A0.getD (tree.getD i0 0) {})
        else A0.getD (tree.getD i0 0) {}
  | 0, s, _, h => by
    obtain rfl : (A0, p0, w0) = s := Option.some.inj h
    exact ⟨rfl, by rw [if_neg (Nat.not_lt_zero _)]⟩
  | k + 1, s, hk, h => by
    rw [List.range_succ, List.foldlM_append] at h
    obtain ⟨s0, h0, h1⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨sz, g⟩ := fill_spec A0 p0 w0 tree hτ uniq k s0 (Nat.le_of_succ_le hk) h0
    have h1' : fillStep codes sent tree s0 k = some s := by
      rw [List.foldlM_cons] at h1
      obtain ⟨y1, a1, a2⟩ := Option.bind_eq_some_iff.1 h1
      obtain rfl : y1 = s := Option.some.inj a2
      exact a1
    unfold fillStep at h1'
    dsimp only at h1'
    split at h1'
    · cases h1'
    · obtain rfl := Option.some.inj h1'
      refine ⟨by rw [Array.size_modify]; exact sz, ?_⟩
      by_cases e : k = i0
      · subst e
        rw [getD_modify _ _ _ _ (by rw [sz]; exact hτ), g, if_neg (Nat.lt_irrefl _),
          if_pos (Nat.lt_succ_self _)]
        rfl
      · have ne : tree.getD k 0 ≠ tree.getD i0 0 := fun q => e (uniq k hk q)
        rw [getD_modify_ne _ _ _ _ _ ne, g]
        by_cases l : i0 < k
        · rw [if_pos l, if_pos (Nat.lt_succ_of_lt l)]
        · rw [if_neg l, if_neg (by omega)]

/-- The last step on a tree that was blank before the step of i0. -/
theorem fix_fill (L : TreeShape) (b1 : L.logNzk = 0) (b2 : L.mainSymbols = #[])
    (b3 : L.maskSymbols = #[]) :
    (fixShape (fillOne codes sent i0 L)).logN =
        (if (sent.getD i0 default).shape.mainRows * (sent.getD i0 default).shape.mainDeg = 0 then
          (if 0 < (sent.getD i0 default).shape.maskRows then
            (codes.mask.getD (sent.getD i0 default).shape.maskCode default).logN else 0)
        else L.logN) ∧
      (fixShape (fillOne codes sent i0 L)).mainWidth +
        (fixShape (fillOne codes sent i0 L)).maskWidth = width1 (sent.getD i0 default).shape := by
  have w1 : (fillOne codes sent i0 L).mainWidth =
      (sent.getD i0 default).shape.mainRows * (sent.getD i0 default).shape.mainDeg := by
    unfold fillOne TreeShape.mainWidth
    dsimp only
    rw [b2]
    simp
  have w2 : (fillOne codes sent i0 L).maskWidth = (sent.getD i0 default).shape.maskRows * 3 := by
    unfold fillOne TreeShape.maskWidth
    dsimp only
    rw [b3]
    simp
  have z : (fillOne codes sent i0 L).logNzk =
      if 0 < (sent.getD i0 default).shape.maskRows then
        (codes.mask.getD (sent.getD i0 default).shape.maskCode default).logN else 0 := by
    unfold fillOne
    dsimp only
    rw [b1]
  unfold fixShape
  rw [w1]
  split
  · next q =>
    refine ⟨?_, ?_⟩
    · rw [if_pos (beq_iff_eq.1 q)]
      exact z
    · show (fillOne codes sent i0 L).mainWidth + (fillOne codes sent i0 L).maskWidth = _
      rw [w1, w2]
      rfl
  · next q =>
    refine ⟨?_, ?_⟩
    · rw [if_neg fun y => q (beq_iff_eq.2 y)]
      rfl
    · rw [w1, w2]
      rfl

end One

/-- **A tree that holds one oracle message alone has that message's depth and width.** -/
theorem lay_one {codes : Codes} {sent : Array OracleNotice} {T : TreeLay} {i0 : Nat}
    (h : layTrees codes sent = some T) (hi0 : i0 < sent.size)
    (uniq : ∀ j, j < sent.size → T.tree.getD j 0 = T.tree.getD i0 0 → j = i0) :
    T.tree.getD i0 0 < T.shapes.size ∧
      (T.shapes.getD (T.tree.getD i0 0) {}).logN = depth1 codes (sent.getD i0 default).shape ∧
      (T.shapes.getD (T.tree.getD i0 0) {}).mainWidth +
        (T.shapes.getD (T.tree.getD i0 0) {}).maskWidth = width1 (sent.getD i0 default).shape := by
  obtain ⟨filled, hf, eT, eS⟩ := layTrees_some h
  obtain ⟨pi, pl⟩ := laid_spec (codes := codes) hi0
  rw [eT] at uniq ⊢
  obtain ⟨sz, g⟩ := fill_spec _ _ _ _ pl.1 uniq sent.size filled (Nat.le_refl _) hf
  rw [if_pos hi0] at g
  obtain ⟨b1, b2, b3⟩ := pi.1 ((laidOf codes sent).2.2.getD i0 0)
  obtain ⟨f1, f2⟩ := fix_fill (codes := codes) (sent := sent) (i0 := i0) _ b1 b2 b3
  have hlt : (laidOf codes sent).2.2.getD i0 0 < filled.1.size := by rw [sz]; exact pl.1
  rw [eS, Array.size_map, getD_map _ _ _ {} _ hlt, g]
  refine ⟨hlt, ?_, f2⟩
  rw [f1]
  unfold depth1
  by_cases q : (sent.getD i0 default).shape.mainRows * (sent.getD i0 default).shape.mainDeg = 0
  · rw [if_pos q, if_pos q]
  · rw [if_neg q, if_neg q]
    exact pl.2 fun y => q (by rw [y, Nat.zero_mul])

/-- Every message has a tree among those returned. -/
theorem lay_lt {codes : Codes} {sent : Array OracleNotice} {T : TreeLay} {i0 : Nat}
    (h : layTrees codes sent = some T) (hi0 : i0 < sent.size) :
    T.tree.getD i0 0 < T.shapes.size := by
  obtain ⟨_, pl⟩ := laid_spec (codes := codes) hi0
  obtain ⟨_, _, eT, _⟩ := layTrees_some h
  rw [eT, OnBytes.Params.layTrees_size h]
  exact pl.1

end OnBytes.Tie.Pv.Keeps.Fit
