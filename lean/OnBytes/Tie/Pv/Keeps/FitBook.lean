-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Keeps/FitBook.lean: a property of a statement's oracle messages and the book of trees
together, and that it goes along where a prover's message with oracle messages is entered.

Definitions, statements and proofs, on plain data: no routine is run here.
OnBytes/Slice/BlkSendRun.lean names treesSent and partsLaid, the trees after Blk.receiveOracles as
functions of what was held before. This file says what these functions do to single trees, and
carries the property through them by lay_one (OnBytes/Tie/Pv/Keeps/LayOne.lean). fit_sent is stated
at a statement and a book written out with them; that Blk.receiveOracles leaves these is shown of a
run that is not dry (`receiveOracles_inv`, OnBytes/Slice/BlkSendRun.lean); of a dry run too:
OnBytes/Tie/Pv/Keeps/FitKit.lean [not in this library; so here read: not proved in this library].
Main names:
  FitAt codes os B: (1) the place of an oracle message names a tree that holds the message; (2) a
    tree that holds one message alone has that message's depth and width (depth1, width1); (3) what
    a tree holds are numbers of oracle messages.
  treesSent_size, treesSent_old, treesSent_new; parts_spec: single trees behind the two loops.
  fit_oracles, fit_trees: the property goes along where messages keep their shapes, and where trees
    keep shape and parts.
  fit_sent: it goes along where a prover's message is entered.
Limits: nothing on a tree with two messages or more. Of a tree's shape: logN and the sum of the two
widths alone.


-/
import OnBytes.Tie.Pv.Keeps.LayOne
import OnBytes.Slice.BlkSendRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Keeps.Fit

open OnBytes
open OnBytes.Slice (treesSent partsLaid)

/-- The property. -/
def FitAt (codes : Codes) (os : Array Oracle) (B : TreeBook) : Prop :=
  (∀ (o τ p : Nat), B.place[o]? = some (τ, p) →
    ∃ t : Tree, B.trees[τ]? = some t ∧ o ∈ t.parts.toList) ∧
  (∀ (τ : Nat) (t : Tree) (o : Nat) (x : Oracle), B.trees[τ]? = some t →
    t.parts.toList = [o] → os[o]? = some x →
    t.shape.logN = depth1 codes x.shape ∧
      t.shape.mainWidth + t.shape.maskWidth = width1 x.shape) ∧
  (∀ (τ : Nat) (t : Tree) (o : Nat), B.trees[τ]? = some t → o ∈ t.parts.toList →
    o < os.size)

/-- Nothing has been sent. -/
theorem fit_empty (codes : Codes) : FitAt codes #[] {} := by
  refine ⟨fun o τ p h => ?_, fun τ t o x h => ?_, fun τ t o h => ?_⟩
  · exact absurd (Array.getElem?_eq_some_iff.1 h).1 (Nat.not_lt_zero _)
  · exact absurd (Array.getElem?_eq_some_iff.1 h).1 (Nat.not_lt_zero _)
  · exact absurd (Array.getElem?_eq_some_iff.1 h).1 (Nat.not_lt_zero _)

/-! ## Changes that keep shapes -/

theorem modify_some {α : Type} {a : Array α} {i j : Nat} {f : α → α} {y : α}
    (h : (a.modify i f)[j]? = some y) : ∃ x, a[j]? = some x ∧ (y = x ∨ y = f x) := by
  rw [Array.getElem?_modify] at h
  split at h
  · cases e : a[j]? with
    | none => rw [e] at h; cases h
    | some x =>
      rw [e] at h
      exact ⟨x, rfl, Or.inr (Option.some.inj h).symm⟩
  · exact ⟨y, h, Or.inl rfl⟩

/-- One oracle message is changed and keeps its shape. -/
theorem fit_oracles {codes : Codes} {os : Array Oracle} {B : TreeBook} (o : Nat)
    (f : Oracle → Oracle) (hf : ∀ x, (f x).shape = x.shape) (h : FitAt codes os B) :
    FitAt codes (os.modify o f) B := by
  refine ⟨h.1, fun τ t o' x a b c => ?_, fun τ t o' a b => ?_⟩
  · obtain ⟨x0, e0, q⟩ := modify_some c
    have es : x.shape = x0.shape := by
      rcases q with rfl | rfl
      · rfl
      · exact hf x0
    rw [es]
    exact h.2.1 τ t o' x0 a b e0
  · rw [Array.size_modify]
    exact h.2.2 τ t o' a b

/-- One tree is changed and keeps its shape and what it holds. -/
theorem fit_trees {codes : Codes} {os : Array Oracle} {B : TreeBook} (j : Nat) (f : Tree → Tree)
    (hf : ∀ x, (f x).shape = x.shape ∧ (f x).parts = x.parts) (h : FitAt codes os B) :
    FitAt codes os { B with trees := B.trees.modify j f } := by
  have back : ∀ (τ : Nat) (t : Tree), (B.trees.modify j f)[τ]? = some t →
      ∃ t0 : Tree, B.trees[τ]? = some t0 ∧ t.shape = t0.shape ∧ t.parts = t0.parts :=
    fun τ t a => by
    obtain ⟨t0, e0, q⟩ := modify_some a
    rcases q with rfl | rfl
    · exact ⟨_, e0, rfl, rfl⟩
    · exact ⟨t0, e0, (hf t0).1, (hf t0).2⟩
  refine ⟨fun o τ p a => ?_, fun τ t o x a b c => ?_, fun τ t o a b => ?_⟩
  · obtain ⟨t, e, m⟩ := h.1 o τ p a
    show ∃ t : Tree, (B.trees.modify j f)[τ]? = some t ∧ _
    rw [Array.getElem?_modify]
    split
    · exact ⟨f t, by rw [e]; rfl, by rw [(hf t).2]; exact m⟩
    · exact ⟨t, e, m⟩
  · obtain ⟨t0, e0, s, q⟩ := back τ t a
    rw [s]
    exact h.2.1 τ t0 o x e0 (by rw [← q]; exact b) c
  · obtain ⟨t0, e0, _, q⟩ := back τ t a
    exact h.2.2 τ t0 o e0 (by rw [← q]; exact b)

/-! ## The trees of a prover's message -/

theorem treesSent_size (first : Nat) : ∀ (l : List TreeShape) (r : Nat) (A : Array Tree),
    (treesSent first l r A).size = A.size + l.length
  | [], _, _ => rfl
  | s :: l, r, A => by
    show (treesSent first l (r + 1) (A.push _)).size = _
    rw [treesSent_size first l, Array.size_push, List.length_cons]
    omega

theorem treesSent_old (first : Nat) : ∀ (l : List TreeShape) (r : Nat) (A : Array Tree) (i : Nat),
    i < A.size → (treesSent first l r A)[i]? = A[i]?
  | [], _, _, _, _ => rfl
  | s :: l, r, A, i, h => by
    show (treesSent first l (r + 1) (A.push _))[i]? = _
    rw [treesSent_old first l _ _ i (by rw [Array.size_push]; omega), Array.getElem?_push,
      if_neg (by omega)]

theorem treesSent_new (first : Nat) : ∀ (l : List TreeShape) (r : Nat) (A : Array Tree) (τ : Nat)
    (s' : TreeShape), l[τ]? = some s' →
    ∃ t : Tree, (treesSent first l r A)[A.size + τ]? = some t ∧ t.shape = s' ∧ t.parts = #[]
  | [], _, _, _, _, h => by cases h
  | s :: l, r, A, 0, s', h => by
    obtain rfl : s = s' := Option.some.inj h
    refine ⟨{ shape := s, number := first + r, src := .own r }, ?_, rfl, rfl⟩
    show (treesSent first l (r + 1) (A.push _))[A.size + 0]? = _
    rw [treesSent_old first l _ _ _ (by rw [Array.size_push]; omega), Array.getElem?_push,
      if_pos (Nat.add_zero _)]
  | s :: l, r, A, τ + 1, s', h => by
    obtain ⟨t, a, b, c⟩ := treesSent_new first l (r + 1)
      (A.push { shape := s, number := first + r, src := .own r }) τ s' h
    refine ⟨t, ?_, b, c⟩
    rw [Array.size_push, show A.size + 1 + τ = A.size + (τ + 1) by omega] at a
    exact a

/-! ## The messages as parts of their trees -/

/-- One turn of the loop that enters the messages as parts. -/
def partStep (sent : Array OracleNotice) (lay : TreeLay) (n0 base : Nat) (trees : Array Tree)
    (i : Nat) : Array Tree :=
  trees.modify (base + lay.tree.getD i 0) fun x => { x with
    parts := x.parts.push (n0 + i)
    oneList := x.oneList || (sent.getD i default).shape.answers == 0 }

theorem partStep_size (sent : Array OracleNotice) (lay : TreeLay) (n0 base : Nat)
    (T : Array Tree) (i : Nat) : (partStep sent lay n0 base T i).size = T.size := by
  unfold partStep
  rw [Array.size_modify]

theorem partStep_ne (sent : Array OracleNotice) (lay : TreeLay) (n0 base : Nat) (T : Array Tree)
    (i j : Nat) (h : base + lay.tree.getD i 0 ≠ j) :
    (partStep sent lay n0 base T i)[j]? = T[j]? := by
  unfold partStep
  rw [Array.getElem?_modify, if_neg h]

theorem partStep_eq (sent : Array OracleNotice) (lay : TreeLay) (n0 base : Nat) (T : Array Tree)
    (i : Nat) (t : Tree) (h : T[base + lay.tree.getD i 0]? = some t) :
    (partStep sent lay n0 base T i)[base + lay.tree.getD i 0]? = some { t with
      parts := t.parts.push (n0 + i)
      oneList := t.oneList || (sent.getD i default).shape.answers == 0 } := by
  unfold partStep
  rw [Array.getElem?_modify, if_pos rfl, h]
  rfl

theorem parts_spec (sent : Array OracleNotice) (lay : TreeLay) (n0 base : Nat) (T1 : Array Tree) :
    ∀ k, ((List.range k).foldl (partStep sent lay n0 base) T1).size = T1.size ∧
      (∀ i, i < base → ((List.range k).foldl (partStep sent lay n0 base) T1)[i]? = T1[i]?) ∧
      ∀ (τ : Nat) (t1 : Tree), T1[base + τ]? = some t1 →
        ∃ t2 : Tree,
          ((List.range k).foldl (partStep sent lay n0 base) T1)[base + τ]? = some t2 ∧
          t2.shape = t1.shape ∧ ∀ o, o ∈ t2.parts.toList ↔
            (o ∈ t1.parts.toList ∨ ∃ j, j < k ∧ lay.tree.getD j 0 = τ ∧ o = n0 + j) := by
  intro k
  induction k with
  | zero =>
    exact ⟨rfl, fun _ _ => rfl, fun τ t1 h => ⟨t1, h, rfl, fun o =>
      ⟨Or.inl, fun q => q.elim id fun ⟨j, hj, _⟩ => absurd hj (Nat.not_lt_zero _)⟩⟩⟩
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨sz, old, new⟩ := ih
    refine ⟨?_, fun i hi => ?_, fun τ t1 h => ?_⟩
    · rw [partStep_size]
      exact sz
    · rw [partStep_ne _ _ _ _ _ _ _ (by omega)]
      exact old i hi
    · obtain ⟨t2, a, s, m⟩ := new τ t1 h
      by_cases e : lay.tree.getD k 0 = τ
      · subst e
        refine ⟨_, partStep_eq _ _ _ _ _ _ _ a, s, fun o => ?_⟩
        show o ∈ (t2.parts.push (n0 + k)).toList ↔ _
        rw [Array.toList_push, List.mem_append, List.mem_singleton, m o]
        constructor
        · rintro ((q | ⟨j, hj, e1, e2⟩) | q)
          · exact Or.inl q
          · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, e1, e2⟩
          · exact Or.inr ⟨k, Nat.lt_succ_self k, rfl, q⟩
        · rintro (q | ⟨j, hj, e1, e2⟩)
          · exact Or.inl (Or.inl q)
          · by_cases ejk : j = k
            · subst ejk
              exact Or.inr e2
            · exact Or.inl (Or.inr ⟨j, by omega, e1, e2⟩)
      · rw [partStep_ne _ _ _ _ _ _ _ (by omega)]
        refine ⟨t2, a, s, fun o => ?_⟩
        rw [m o]
        constructor
        · rintro (q | ⟨j, hj, e1, e2⟩)
          · exact Or.inl q
          · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, e1, e2⟩
        · rintro (q | ⟨j, hj, e1, e2⟩)
          · exact Or.inl q
          · by_cases ejk : j = k
            · subst ejk
              exact absurd e1 e
            · exact Or.inr ⟨j, by omega, e1, e2⟩

/-! ## A prover's message is entered -/

/-- **The property goes along where a prover's message with oracle messages is entered.** -/
theorem fit_sent {codes : Codes} {os : Array Oracle} {B : TreeBook} (sent : Array OracleNotice)
    (lay : TreeLay) (first r : Nat) (hl : layTrees codes sent = some lay)
    (hs : os.size = B.place.size) (h : FitAt codes os B) :
    FitAt codes (os ++ sent.map fun n => { shape := n.shape })
      { trees := partsLaid sent lay os.size B.trees.size
          (treesSent first lay.shapes.toList r B.trees)
        place := B.place ++ (Array.range sent.size).map fun i =>
          (B.trees.size + lay.tree.getD i 0, lay.part.getD i 0) } := by
  obtain ⟨sz, old, new⟩ := parts_spec sent lay os.size B.trees.size
    (treesSent first lay.shapes.toList r B.trees) sent.size
  have eP : partsLaid sent lay os.size B.trees.size (treesSent first lay.shapes.toList r B.trees) =
      (List.range sent.size).foldl (partStep sent lay os.size B.trees.size)
        (treesSent first lay.shapes.toList r B.trees) := rfl
  -- a tree of the new book: an old one, or one of the message's
  have split : ∀ (τ' : Nat) (t : Tree), (partsLaid sent lay os.size B.trees.size
      (treesSent first lay.shapes.toList r B.trees))[τ']? = some t →
      (τ' < B.trees.size ∧ B.trees[τ']? = some t) ∨
      ∃ τ, τ' = B.trees.size + τ ∧ t.shape = lay.shapes.getD τ {} ∧
        ∀ o, o ∈ t.parts.toList ↔
          ∃ j, j < sent.size ∧ lay.tree.getD j 0 = τ ∧ o = os.size + j := by
    intro τ' t a
    rw [eP] at a
    by_cases lt : τ' < B.trees.size
    · rw [old τ' lt, treesSent_old first _ _ _ _ lt] at a
      exact Or.inl ⟨lt, a⟩
    · obtain ⟨τ, rfl⟩ : ∃ τ, τ' = B.trees.size + τ := ⟨τ' - B.trees.size, by omega⟩
      have b : B.trees.size + τ < B.trees.size + lay.shapes.toList.length := by
        rw [← treesSent_size first _ r, ← sz]
        exact (Array.getElem?_eq_some_iff.1 a).1
      have b' : τ < lay.shapes.size := by
        rw [Array.length_toList] at b
        omega
      obtain ⟨t1, a1, s1, p1⟩ :=
        treesSent_new first lay.shapes.toList r B.trees τ lay.shapes[τ]
          (by rw [Array.getElem?_toList, Array.getElem?_eq_getElem b'])
      obtain ⟨t2, a2, s2, m2⟩ := new τ t1 a1
      rw [a] at a2
      obtain rfl : t = t2 := Option.some.inj a2
      refine Or.inr ⟨τ, rfl, ?_, fun o => ?_⟩
      · rw [s2, s1, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem b']
        rfl
      · rw [m2 o, p1]
        exact ⟨fun q => q.elim (fun z => by cases z) id, Or.inr⟩
  refine ⟨fun o τ' p a => ?_, fun τ' t o x a b c => ?_, fun τ' t o a b => ?_⟩
  · -- the places
    have a' : (B.place ++ (Array.range sent.size).map fun i =>
        (B.trees.size + lay.tree.getD i 0, lay.part.getD i 0))[o]? = some (τ', p) := a
    show ∃ t : Tree, (partsLaid sent lay os.size B.trees.size
      (treesSent first lay.shapes.toList r B.trees))[τ']? = some t ∧ _
    by_cases lt : o < B.place.size
    · rw [Array.getElem?_append_left lt] at a'
      obtain ⟨t, e, m⟩ := h.1 o τ' p a'
      have lt' := (Array.getElem?_eq_some_iff.1 e).1
      exact ⟨t, by rw [eP, old τ' lt', treesSent_old first _ _ _ _ lt']; exact e, m⟩
    · rw [Array.getElem?_append_right (Nat.le_of_not_lt lt), Array.getElem?_map] at a'
      obtain ⟨i, hi, e⟩ := Option.map_eq_some_iff.1 a'
      obtain ⟨hi', ei⟩ := Array.getElem?_eq_some_iff.1 hi
      rw [Array.size_range] at hi'
      rw [Array.getElem_range] at ei
      subst ei
      obtain rfl : B.trees.size + lay.tree.getD (o - B.place.size) 0 = τ' :=
        congrArg Prod.fst e
      have b' := lay_lt hl hi'
      obtain ⟨t1, a1, _, _⟩ := treesSent_new first lay.shapes.toList r B.trees
        (lay.tree.getD (o - B.place.size) 0) lay.shapes[lay.tree.getD (o - B.place.size) 0]
        (by rw [Array.getElem?_toList, Array.getElem?_eq_getElem b'])
      obtain ⟨t2, a2, _, m2⟩ := new _ t1 a1
      refine ⟨t2, by rw [eP]; exact a2, (m2 o).2 (Or.inr ⟨o - B.place.size, hi', rfl, ?_⟩)⟩
      omega
  · -- a tree with one part
    have c' : (os ++ sent.map fun n => ({ shape := n.shape } : Oracle))[o]? = some x := c
    rcases split τ' t a with ⟨_, e⟩ | ⟨τ, rfl, s, m⟩
    · have lo := h.2.2 τ' t o e (by rw [b]; exact List.mem_singleton.2 rfl)
      rw [Array.getElem?_append_left lo] at c'
      exact h.2.1 τ' t o x e b c'
    · obtain ⟨j, hj, ej, rfl⟩ := (m o).1 (by rw [b]; exact List.mem_singleton.2 rfl)
      have uniq : ∀ j', j' < sent.size → lay.tree.getD j' 0 = lay.tree.getD j 0 → j' = j := by
        intro j' hj' e'
        have q := (m (os.size + j')).2 ⟨j', hj', e'.trans ej, rfl⟩
        rw [b, List.mem_singleton] at q
        omega
      obtain ⟨_, d1, d2⟩ := lay_one hl hj uniq
      rw [Array.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
        Array.getElem?_map, Array.getElem?_eq_getElem hj] at c'
      obtain rfl := Option.some.inj c'
      have eg : sent.getD j default = sent[j] := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
        rfl
      rw [eg, ej] at d1 d2
      rw [s]
      exact ⟨d1, d2⟩
  · -- parts are numbers of oracle messages
    show o < (os ++ sent.map fun n => ({ shape := n.shape } : Oracle)).size
    rw [Array.size_append, Array.size_map]
    rcases split τ' t a with ⟨_, e⟩ | ⟨τ, _, _, m⟩
    · exact Nat.lt_of_lt_of_le (h.2.2 τ' t o e b) (Nat.le_add_right _ _)
    · obtain ⟨j, hj, _, rfl⟩ := (m o).1 b
      omega

end OnBytes.Tie.Pv.Keeps.Fit
