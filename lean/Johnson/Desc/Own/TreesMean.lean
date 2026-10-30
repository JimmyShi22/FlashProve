-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Own/TreesMean.lean: what Johnson/Desc/Own/Trees.lean's treesCan checks, as a
proposition on the messages, proved in both directions.

In words: no mask rows of two lengths meet in one tree, and none are longer than their tree's main
rows. Statements and proofs. No block imports this file.
Main names:
  `TreesFit codes sent`: the two facts. For messages i, j to which treeOf gives one tree: if both
    have mask rows, these have one length; if i has mask rows and j has main symbols, the mask rows
    of i are not longer than the main rows of j.
  `treesCan_iff`: treesCan codes sent = true ↔ TreesFit codes sent. Its halves: `treesFit_of_can`
    (what a yes gives) and `can_of_treesFit` (the test asks nothing more).
  `treeOf_lt`: every message's tree is one of the trees. `treeOf_mainLen`: the tree of a message
    with main rows has that message's main length. `treeOf_fresh`: the trees that treeOf opens hold
    no symbol yet.
  `treesMade_gives`: where treesMade gives the lay: lay.tree is treeOf's; every message's tree is
    one of lay.shapes; every message with mask rows lies in a tree whose recorded mask length
    (logNzk) is the message's own and which holds mask symbols; and every tree of lay.shapes holds
    no mask symbols or has logNzk ≤ logN. `treesCan_gives`: treesCan's yes gives such a lay.
  `treesCan_oneLength`, `treesCan_notLonger`, `treesMade_mainLen`: the facts one by one, on the
    lay.
  `FillInv`, `FillMore` with `.start`, `.step`, `.fold`: what holds of the state of the laying,
    message by message. `fill_total`: under the first fact every message can be laid.
    `passStep_inv`, `pass_inv`, `passStep_len`, `pass_len`, `pass_fresh`: the like for the two
    passes of treeOf.
Limits: Which messages share a tree (treeOf) is taken as it is: nothing is said on whether that is
the right way to share. A message whose main rows have the degree 0 has no main symbols and counts
as one without main rows in the second fact. Nothing on soundness.

-/
import Johnson.Desc.Own.Trees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own

/-- An entry of an array of which one entry has been changed. -/
theorem getD_modify {α : Type} (a : Array α) (i j : Nat) (f : α → α) (d : α) :
    (a.modify i f).getD j d = if i = j ∧ j < a.size then f (a.getD j d) else a.getD j d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < a.size
    · simp [hi]
    · simp [hi]
  · simp [hij]

/-- The number of mask rows of message number i. -/
def maskRowsAt (sent : Array OnBytes.OracleNotice) (i : Nat) : Nat :=
  (sent.getD i default).shape.maskRows

/-- The logarithm of the length of a mask row of message number i. -/
def maskLenAt (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (i : Nat) : Nat :=
  (codes.mask.getD (sent.getD i default).shape.maskCode default).logN

/-- What holds of the state of the laying once the messages «done» are laid, among m trees: the two
arrays have an entry a tree; a tree into which a message with mask rows has come holds mask symbols
(by the count beside the trees, and by the tree's own list); and its mask length is that
message's. -/
structure FillInv (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (tree : Array Nat)
    (m : Nat) (done : List Nat) (s : Array OnBytes.TreeShape × Array Nat × Array Nat) : Prop where
  szT : s.1.size = m
  szW : s.2.2.size = m
  wide : ∀ i ∈ done, 0 < maskRowsAt sent i → tree.getD i 0 < m → 0 < s.2.2.getD (tree.getD i 0) 0
  len : ∀ i ∈ done, 0 < maskRowsAt sent i → tree.getD i 0 < m →
    (s.1.getD (tree.getD i 0) {}).logNzk = maskLenAt codes sent i
  sym : ∀ i ∈ done, 0 < maskRowsAt sent i → tree.getD i 0 < m →
    0 < (s.1.getD (tree.getD i 0) {}).maskWidth

/-- One message more. -/
theorem FillInv.step {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice} {tree : Array Nat}
    {m : Nat} {done : List Nat} {s s' : Array OnBytes.TreeShape × Array Nat × Array Nat} {k : Nat}
    (I : FillInv codes sent tree m done s) (h : fillStep codes sent tree s k = some s') :
    FillInv codes sent tree m (k :: done) s' := by
  unfold fillStep at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hc
    have hs := Option.some.inj h
    subst hs
    have hc' : ¬ (0 < maskRowsAt sent k ∧ 0 < s.2.2.getD (tree.getD k 0) 0 ∧
        (s.1.getD (tree.getD k 0) {}).logNzk ≠ maskLenAt codes sent k) := by
      intro q
      apply hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
      exact ⟨⟨q.1, q.2.1⟩, q.2.2⟩
    refine ⟨by simp [I.szT], by simp [I.szW], ?_, ?_, ?_⟩
    · intro i hi hm ht
      show 0 < (s.2.2.modify (tree.getD k 0) _).getD (tree.getD i 0) 0
      rw [getD_modify]
      rcases List.mem_cons.1 hi with rfl | hi
      · rw [if_pos ⟨rfl, by rw [I.szW]; exact ht⟩]
        have : 0 < maskRowsAt sent i := hm
        unfold maskRowsAt at this
        omega
      · have := I.wide i hi hm ht
        split <;> omega
    · intro i hi hm ht
      show ((s.1.modify (tree.getD k 0) _).getD (tree.getD i 0) {}).logNzk = _
      rw [getD_modify]
      rcases List.mem_cons.1 hi with rfl | hi
      · rw [if_pos ⟨rfl, by rw [I.szT]; exact ht⟩]
        show (if 0 < maskRowsAt sent i then maskLenAt codes sent i else _) = _
        rw [if_pos hm]
      · have hl := I.len i hi hm ht
        by_cases hk : tree.getD k 0 = tree.getD i 0 ∧ tree.getD i 0 < s.1.size
        · rw [if_pos hk]
          show (if 0 < maskRowsAt sent k then maskLenAt codes sent k
            else (s.1.getD (tree.getD i 0) {}).logNzk) = _
          by_cases hmk : 0 < maskRowsAt sent k
          · rw [if_pos hmk]
            have hw := I.wide i hi hm ht
            rw [← hk.1] at hw hl
            by_cases he : (s.1.getD (tree.getD k 0) {}).logNzk = maskLenAt codes sent k
            · rw [← he, hl]
            · exact absurd ⟨hmk, hw, he⟩ hc'
          · rw [if_neg hmk, hl]
        · rw [if_neg hk, hl]
    · intro i hi hm ht
      show 0 < ((s.1.modify (tree.getD k 0) _).getD (tree.getD i 0) {}).maskWidth
      rw [getD_modify]
      rcases List.mem_cons.1 hi with rfl | hi
      · rw [if_pos ⟨rfl, by rw [I.szT]; exact ht⟩]
        have : 0 < maskRowsAt sent i := hm
        unfold maskRowsAt at this
        simp only [OnBytes.TreeShape.maskWidth, Array.foldl_push]
        omega
      · have hw := I.sym i hi hm ht
        split
        · simp only [OnBytes.TreeShape.maskWidth, Array.foldl_push] at hw ⊢
          omega
        · exact hw

/-- All messages of a list. -/
theorem FillInv.fold {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice} {tree : Array Nat}
    {m : Nat} : ∀ (l done : List Nat) (s s' : Array OnBytes.TreeShape × Array Nat × Array Nat),
    FillInv codes sent tree m done s → l.foldlM (fillStep codes sent tree) s = some s' →
    FillInv codes sent tree m (l.reverse ++ done) s'
  | [], done, s, s', I, h => by
    cases h
    exact I
  | k :: l, done, s, s', I, h => by
    rw [List.foldlM_cons] at h
    cases hk : fillStep codes sent tree s k with
    | none => rw [hk] at h; cases h
    | some s1 =>
      rw [hk] at h
      have := FillInv.fold l (k :: done) s1 s' (I.step hk) h
      rw [List.reverse_cons, List.append_assoc]
      exact this

/-- In front of the first message. -/
theorem FillInv.start (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (tree : Array Nat)
    (a : Array OnBytes.TreeShape) :
    FillInv codes sent tree a.size [] (a, #[], Array.replicate a.size 0) where
  szT := rfl
  szW := by simp
  wide := fun _ hi => by cases hi
  len := fun _ hi => by cases hi
  sym := fun _ hi => by cases hi

/-- The last step keeps each tree's mask symbols. -/
theorem getD_closed_width (a : Array OnBytes.TreeShape) (t : Nat) (ht : t < a.size) :
    ((a.map fun t => if t.mainWidth == 0 then { t with logN := t.logNzk } else t).getD t
      {}).maskWidth = (a.getD t {}).maskWidth := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_eq_getElem ht]
  show (if a[t].mainWidth == 0 then _ else _ : OnBytes.TreeShape).maskWidth = a[t].maskWidth
  split <;> rfl

/-- The last step keeps each tree's mask length. -/
theorem getD_closed (a : Array OnBytes.TreeShape) (t : Nat) (ht : t < a.size) :
    ((a.map fun t => if t.mainWidth == 0 then { t with logN := t.logNzk } else t).getD t
      {}).logNzk = (a.getD t {}).logNzk := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_eq_getElem ht]
  show (if a[t].mainWidth == 0 then _ else _ : OnBytes.TreeShape).logNzk = a[t].logNzk
  split <;> rfl

/-! ## Every message's tree is one of the trees -/

/-- An entry of an array of which one entry has been set. -/
theorem getD_setIfInBounds {α : Type} (a : Array α) (i j : Nat) (v d : α) :
    (a.setIfInBounds i v).getD j d = if i = j ∧ j < a.size then v else a.getD j d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < a.size
    · simp [hi]
    · simp [hi]
  · simp [hij]

/-- The step of treeOfPass, under a name. -/
def passStep (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (maskOnly : Bool)
    (s : Array OnBytes.TreeShape × Array Nat × Array Nat) (i : Nat) :
    Array OnBytes.TreeShape × Array Nat × Array Nat :=
  if ((sent.getD i default).shape.mainRows == 0) != maskOnly then s
  else
    match (List.range s.1.size).find? (fun t =>
      s.2.1.getD t (2 ^ 32 - 1) == (sent.getD i default).leafClass &&
        (maskOnly || (s.1.getD t {}).logN ==
          (codes.base.getD (sent.getD i default).shape.code default).logN)) with
    | some t => (s.1, s.2.1, s.2.2.setIfInBounds i t)
    | none =>
      (s.1.push (if maskOnly then {}
          else { logN := (codes.base.getD (sent.getD i default).shape.code default).logN }),
        s.2.1.push (sent.getD i default).leafClass, s.2.2.setIfInBounds i s.1.size)

theorem treeOfPass_eq (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (maskOnly : Bool)
    (s : Array OnBytes.TreeShape × Array Nat × Array Nat) :
    treeOfPass codes sent maskOnly s =
      (List.range sent.size).foldl (passStep codes sent maskOnly) s :=
  rfl

/-- One step: the list of trees keeps its length n; whoever had a tree has one; and message i has
one if the pass is its own. -/
theorem passStep_inv (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (maskOnly : Bool)
    (n : Nat) (s : Array OnBytes.TreeShape × Array Nat × Array Nat) (i : Nat) (A : Nat → Prop)
    (hsz : s.2.2.size = n) (hi : i < n) (hA : ∀ j, A j → s.2.2.getD j 0 < s.1.size) :
    (passStep codes sent maskOnly s i).2.2.size = n ∧
    (∀ j, A j ∨ (j = i ∧ ((sent.getD i default).shape.mainRows == 0) = maskOnly) →
      (passStep codes sent maskOnly s i).2.2.getD j 0 <
        (passStep codes sent maskOnly s i).1.size) := by
  unfold passStep
  split
  · rename_i hne
    refine ⟨hsz, fun j hj => ?_⟩
    rcases hj with hj | ⟨_, hk⟩
    · exact hA j hj
    · rw [hk] at hne
      simp at hne
  · split
    · rename_i t ht
      have htl : t < s.1.size := List.mem_range.1 (List.mem_of_find?_eq_some ht)
      refine ⟨by simp [hsz], fun j hj => ?_⟩
      show (s.2.2.setIfInBounds i t).getD j 0 < s.1.size
      rw [getD_setIfInBounds]
      split
      · exact htl
      · rename_i hn
        rcases hj with hj | ⟨rfl, _⟩
        · exact hA j hj
        · exact absurd ⟨rfl, by rw [hsz]; exact hi⟩ hn
    · refine ⟨by simp [hsz], fun j hj => ?_⟩
      show (s.2.2.setIfInBounds i s.1.size).getD j 0 < (s.1.push _).size
      rw [getD_setIfInBounds, Array.size_push]
      split
      · omega
      · rename_i hn
        rcases hj with hj | ⟨rfl, _⟩
        · have := hA j hj
          omega
        · exact absurd ⟨rfl, by rw [hsz]; exact hi⟩ hn

/-- A whole pass over a list of numbers below n. -/
theorem pass_inv (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (maskOnly : Bool)
    (n : Nat) : ∀ (l : List Nat) (s : Array OnBytes.TreeShape × Array Nat × Array Nat)
    (A : Nat → Prop), (∀ i ∈ l, i < n) → s.2.2.size = n → (∀ j, A j → s.2.2.getD j 0 < s.1.size) →
    (l.foldl (passStep codes sent maskOnly) s).2.2.size = n ∧
    (∀ j, A j ∨ (j ∈ l ∧ ((sent.getD j default).shape.mainRows == 0) = maskOnly) →
      (l.foldl (passStep codes sent maskOnly) s).2.2.getD j 0 <
        (l.foldl (passStep codes sent maskOnly) s).1.size)
  | [], s, A, _, hsz, hA => ⟨hsz, fun j hj => by
      rcases hj with hj | ⟨hj, _⟩
      · exact hA j hj
      · cases hj⟩
  | i :: l, s, A, hl, hsz, hA => by
    obtain ⟨h1, h2⟩ :=
      passStep_inv codes sent maskOnly n s i A hsz (hl i (List.mem_cons_self ..)) hA
    obtain ⟨h3, h4⟩ := pass_inv codes sent maskOnly n l (passStep codes sent maskOnly s i) _
      (fun k hk => hl k (List.mem_cons_of_mem _ hk)) h1 h2
    refine ⟨h3, fun j hj => h4 j ?_⟩
    rcases hj with hj | ⟨hj, hk⟩
    · exact .inl (.inl hj)
    · rcases List.mem_cons.1 hj with rfl | hj
      · exact .inl (.inr ⟨rfl, hk⟩)
      · exact .inr ⟨hj, hk⟩

/-- Every message's tree is one of the trees. -/
theorem treeOf_lt (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (i : Nat)
    (hi : i < sent.size) : (treeOf codes sent).2.2.getD i 0 < (treeOf codes sent).1.size := by
  unfold treeOf
  rw [treeOfPass_eq, treeOfPass_eq]
  obtain ⟨h1, h2⟩ := pass_inv codes sent false sent.size (List.range sent.size)
    (#[], #[], Array.replicate sent.size 0) (fun _ => False) (fun _ h => List.mem_range.1 h)
    (by simp) (fun _ h => h.elim)
  obtain ⟨_, h4⟩ := pass_inv codes sent true sent.size (List.range sent.size) _ _
    (fun _ h => List.mem_range.1 h) h1 h2
  refine h4 i ?_
  cases hk : ((sent.getD i default).shape.mainRows == 0)
  · exact .inl (.inr ⟨List.mem_range.2 hi, rfl⟩)
  · exact .inr ⟨List.mem_range.2 hi, rfl⟩

/-! ## What a yes checks -/

/-- What the trees that are laid are like. Where treesMade gives the lay: each message's tree is the
one that treeOf names, and it is one of the trees; (1) every message with mask rows lies in a tree
whose mask length is its own; (2) no tree holds mask symbols that are longer than the tree. -/
theorem treesMade_gives {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    {lay : OnBytes.TreeLay} (h : treesMade codes sent = some lay) :
    lay.tree = (treeOf codes sent).2.2 ∧
    (∀ i, i < sent.size → lay.tree.getD i 0 < lay.shapes.size) ∧
    (∀ i, i < sent.size → 0 < maskRowsAt sent i →
      (lay.shapes.getD (lay.tree.getD i 0) {}).logNzk = maskLenAt codes sent i ∧
      0 < (lay.shapes.getD (lay.tree.getD i 0) {}).maskWidth) ∧
    (∀ t ∈ lay.shapes.toList, t.maskWidth = 0 ∨ t.logNzk ≤ t.logN) := by
  unfold treesMade at h
  split at h
  · cases h
  · rename_i filled hf
    have I := FillInv.fold (codes := codes) (sent := sent) (tree := (treeOf codes sent).2.2)
      (m := (treeOf codes sent).1.size) (List.range sent.size) [] _ filled
      (FillInv.start codes sent _ _) hf
    unfold closeTrees at h
    dsimp only at h
    split at h
    · rename_i hall
      have hl := Option.some.inj h
      subst hl
      have hlt : ∀ i, i < sent.size → (treeOf codes sent).2.2.getD i 0 < filled.1.size :=
        fun i hi => by rw [I.szT]; exact treeOf_lt codes sent i hi
      refine ⟨rfl, fun i hi => by simpa using hlt i hi, fun i hi hm => ?_, fun t ht => ?_⟩
      · dsimp only
        rw [getD_closed _ _ (hlt i hi), getD_closed_width _ _ (hlt i hi)]
        exact ⟨I.len i (by simp [hi]) hm (treeOf_lt codes sent i hi),
          I.sym i (by simp [hi]) hm (treeOf_lt codes sent i hi)⟩
      · have := (Array.all_eq_true_iff_forall_mem.1 hall) t (Array.mem_toList_iff.1 ht)
        simpa using this
    · cases h

/-- What treesCan's yes checks: the trees are laid, and they are as treesMade_gives says. -/
theorem treesCan_gives {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    (h : treesCan codes sent = true) :
    ∃ lay, treesMade codes sent = some lay ∧ lay.tree = (treeOf codes sent).2.2 ∧
      (∀ i, i < sent.size → lay.tree.getD i 0 < lay.shapes.size) ∧
      (∀ i, i < sent.size → 0 < maskRowsAt sent i →
        (lay.shapes.getD (lay.tree.getD i 0) {}).logNzk = maskLenAt codes sent i ∧
        0 < (lay.shapes.getD (lay.tree.getD i 0) {}).maskWidth) ∧
      (∀ t ∈ lay.shapes.toList, t.maskWidth = 0 ∨ t.logNzk ≤ t.logN) := by
  obtain ⟨lay, hl⟩ := Option.isSome_iff_exists.1 h
  exact ⟨lay, hl, treesMade_gives hl⟩

/-- No mask rows of two lengths meet in one tree: behind treesCan's yes, two messages with mask rows
that treeOf puts into one tree have mask rows of one length. -/
theorem treesCan_oneLength {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    (h : treesCan codes sent = true) (i j : Nat) (hi : i < sent.size) (hj : j < sent.size)
    (hmi : 0 < maskRowsAt sent i) (hmj : 0 < maskRowsAt sent j)
    (hij : (treeOf codes sent).2.2.getD i 0 = (treeOf codes sent).2.2.getD j 0) :
    maskLenAt codes sent i = maskLenAt codes sent j := by
  obtain ⟨lay, _, e, _, h1, _⟩ := treesCan_gives h
  have a := (h1 i hi hmi).1
  have b := (h1 j hj hmj).1
  rw [e] at a b
  rw [← a, ← b, hij]

/-- And none are longer than their tree: behind treesCan's yes, the mask rows of a message are not
longer than the tree in which it lies. (A tree's length is that of its main rows; a tree without
main symbols has its mask rows' length.) -/
theorem treesCan_notLonger {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    {lay : OnBytes.TreeLay} (h : treesMade codes sent = some lay) (i : Nat) (hi : i < sent.size)
    (hm : 0 < maskRowsAt sent i) :
    maskLenAt codes sent i ≤ (lay.shapes.getD (lay.tree.getD i 0) {}).logN := by
  obtain ⟨_, h0, h1, h2⟩ := treesMade_gives h
  obtain ⟨a, b⟩ := h1 i hi hm
  have hmem : lay.shapes.getD (lay.tree.getD i 0) {} ∈ lay.shapes.toList := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (h0 i hi)]
    exact Array.mem_toList_iff.2 (Array.getElem_mem _)
  rcases h2 _ hmem with q | q
  · omega
  · omega

/-! ## The converse: the test asks nothing more -/

/-- The number of main symbols of message number i in a column. -/
def mainSymsAt (sent : Array OnBytes.OracleNotice) (i : Nat) : Nat :=
  (sent.getD i default).shape.mainRows * (sent.getD i default).shape.mainDeg

/-- An entry of an array to which an entry has been added. -/
theorem getD_push {α : Type} (a : Array α) (x d : α) (t : Nat) :
    (a.push x).getD t d = if t = a.size then x else a.getD t d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split <;> rfl

/-- A pass opens trees that hold no symbol yet. -/
theorem passStep_fresh (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (maskOnly : Bool)
    (s : Array OnBytes.TreeShape × Array Nat × Array Nat) (i : Nat)
    (h : ∀ t, (s.1.getD t {}).mainWidth = 0 ∧ (s.1.getD t {}).maskWidth = 0) :
    ∀ t, ((passStep codes sent maskOnly s i).1.getD t {}).mainWidth = 0 ∧
      ((passStep codes sent maskOnly s i).1.getD t {}).maskWidth = 0 := by
  unfold passStep
  split
  · exact h
  · split
    · exact h
    · intro t
      show ((s.1.push _).getD t {}).mainWidth = 0 ∧ ((s.1.push _).getD t {}).maskWidth = 0
      rw [getD_push]
      split
      · cases maskOnly <;> exact ⟨rfl, rfl⟩
      · exact h t

theorem pass_fresh (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (maskOnly : Bool) :
    ∀ (l : List Nat) (s : Array OnBytes.TreeShape × Array Nat × Array Nat),
    (∀ t, (s.1.getD t {}).mainWidth = 0 ∧ (s.1.getD t {}).maskWidth = 0) →
    ∀ t, ((l.foldl (passStep codes sent maskOnly) s).1.getD t {}).mainWidth = 0 ∧
      ((l.foldl (passStep codes sent maskOnly) s).1.getD t {}).maskWidth = 0
  | [], _, h => h
  | i :: l, s, h => pass_fresh codes sent maskOnly l _ (passStep_fresh codes sent maskOnly s i h)

/-- The trees that treeOf opens hold no symbol yet. -/
theorem treeOf_fresh (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (t : Nat) :
    ((treeOf codes sent).1.getD t {}).mainWidth = 0 ∧
      ((treeOf codes sent).1.getD t {}).maskWidth = 0 := by
  unfold treeOf
  rw [treeOfPass_eq, treeOfPass_eq]
  exact pass_fresh codes sent true _ _ (pass_fresh codes sent false _ _ (fun _ => ⟨rfl, rfl⟩)) t

/-- More of what holds of the state of the laying: a tree holds symbols of a kind ONLY IF a message
with such symbols has come into it; a message with main symbols leaves main symbols; no tree's
length is turned. a0: the trees in front of the laying. -/
structure FillMore (sent : Array OnBytes.OracleNotice) (tree : Array Nat) (m : Nat)
    (a0 : Array OnBytes.TreeShape) (done : List Nat)
    (s : Array OnBytes.TreeShape × Array Nat × Array Nat) : Prop where
  wideOnly : ∀ t, 0 < s.2.2.getD t 0 → ∃ i ∈ done, tree.getD i 0 = t ∧ 0 < maskRowsAt sent i
  symOnly : ∀ t, 0 < (s.1.getD t {}).maskWidth →
    ∃ i ∈ done, tree.getD i 0 = t ∧ 0 < maskRowsAt sent i
  mainPos : ∀ j ∈ done, 0 < mainSymsAt sent j → tree.getD j 0 < m →
    0 < (s.1.getD (tree.getD j 0) {}).mainWidth
  mainOnly : ∀ t, 0 < (s.1.getD t {}).mainWidth →
    ∃ j ∈ done, tree.getD j 0 = t ∧ 0 < mainSymsAt sent j
  keepN : ∀ t, (s.1.getD t {}).logN = (a0.getD t {}).logN

theorem FillMore.step {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice} {tree : Array Nat}
    {m : Nat} {a0 : Array OnBytes.TreeShape} {done : List Nat}
    {s s' : Array OnBytes.TreeShape × Array Nat × Array Nat} {k : Nat}
    (I : FillInv codes sent tree m done s) (J : FillMore sent tree m a0 done s)
    (h : fillStep codes sent tree s k = some s') : FillMore sent tree m a0 (k :: done) s' := by
  unfold fillStep at h
  dsimp only at h
  split at h
  · cases h
  · have hs := Option.some.inj h
    subst hs
    have up : ∀ {p : Nat → Prop}, (∃ i ∈ done, p i) → ∃ i ∈ k :: done, p i :=
      fun ⟨i, hi, hp⟩ => ⟨i, List.mem_cons_of_mem _ hi, hp⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      have ht' : 0 < (s.2.2.modify (tree.getD k 0) _).getD t 0 := ht
      rw [getD_modify] at ht'
      split at ht'
      · rename_i hk
        by_cases h0 : 0 < s.2.2.getD t 0
        · exact up (J.wideOnly t h0)
        · refine ⟨k, List.mem_cons_self .., hk.1, ?_⟩
          unfold maskRowsAt
          omega
      · exact up (J.wideOnly t ht')
    · intro t ht
      have ht' : 0 < ((s.1.modify (tree.getD k 0) _).getD t {}).maskWidth := ht
      rw [getD_modify] at ht'
      split at ht'
      · rename_i hk
        by_cases h0 : 0 < (s.1.getD t {}).maskWidth
        · exact up (J.symOnly t h0)
        · refine ⟨k, List.mem_cons_self .., hk.1, ?_⟩
          simp only [OnBytes.TreeShape.maskWidth, Array.foldl_push] at ht' h0
          unfold maskRowsAt
          omega
      · exact up (J.symOnly t ht')
    · intro j hj hm ht
      show 0 < ((s.1.modify (tree.getD k 0) _).getD (tree.getD j 0) {}).mainWidth
      rw [getD_modify]
      rcases List.mem_cons.1 hj with rfl | hj
      · rw [if_pos ⟨rfl, by rw [I.szT]; exact ht⟩]
        have : 0 < mainSymsAt sent j := hm
        unfold mainSymsAt at this
        simp only [OnBytes.TreeShape.mainWidth, Array.foldl_push]
        omega
      · have hw := J.mainPos j hj hm ht
        split
        · simp only [OnBytes.TreeShape.mainWidth, Array.foldl_push] at hw ⊢
          omega
        · exact hw
    · intro t ht
      have ht' : 0 < ((s.1.modify (tree.getD k 0) _).getD t {}).mainWidth := ht
      rw [getD_modify] at ht'
      split at ht'
      · rename_i hk
        by_cases h0 : 0 < (s.1.getD t {}).mainWidth
        · exact up (J.mainOnly t h0)
        · refine ⟨k, List.mem_cons_self .., hk.1, ?_⟩
          simp only [OnBytes.TreeShape.mainWidth, Array.foldl_push] at ht' h0
          unfold mainSymsAt
          omega
      · exact up (J.mainOnly t ht')
    · intro t
      show ((s.1.modify (tree.getD k 0) _).getD t {}).logN = _
      rw [getD_modify]
      split
      · exact J.keepN t
      · exact J.keepN t

/-- The logarithm of the length of a main row of message number i. -/
def mainLenAt (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (i : Nat) : Nat :=
  (codes.base.getD (sent.getD i default).shape.code default).logN

/-- One step of a pass keeps, and in the first pass gives: the tree of a message with main rows has
that message's main length. A: messages with main rows that have their tree. -/
theorem passStep_len (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (maskOnly : Bool)
    (n : Nat) (s : Array OnBytes.TreeShape × Array Nat × Array Nat) (i : Nat) (A : Nat → Prop)
    (hsz : s.2.2.size = n) (hi : i < n)
    (hAk : ∀ j, A j → ((sent.getD j default).shape.mainRows == 0) = false)
    (hA : ∀ j, A j → s.2.2.getD j 0 < s.1.size ∧
      (s.1.getD (s.2.2.getD j 0) {}).logN = mainLenAt codes sent j) :
    ∀ j, A j ∨ (j = i ∧ ((sent.getD i default).shape.mainRows == 0) = false ∧ maskOnly = false) →
      (passStep codes sent maskOnly s i).2.2.getD j 0 < (passStep codes sent maskOnly s i).1.size ∧
      ((passStep codes sent maskOnly s i).1.getD ((passStep codes sent maskOnly s i).2.2.getD j 0)
        {}).logN = mainLenAt codes sent j := by
  intro j hj
  have hkj : ((sent.getD j default).shape.mainRows == 0) = false := by
    rcases hj with hj | ⟨rfl, hk, _⟩
    · exact hAk j hj
    · exact hk
  unfold passStep
  split
  · rename_i hne
    rcases hj with hj | ⟨rfl, hk, hm⟩
    · exact hA j hj
    · rw [hk, hm] at hne
      simp at hne
  · rename_i hne
    have hkind : ((sent.getD i default).shape.mainRows == 0) = maskOnly := by
      cases h1 : ((sent.getD i default).shape.mainRows == 0) <;> cases maskOnly <;> simp_all
    split
    · rename_i t ht
      have htl : t < s.1.size := List.mem_range.1 (List.mem_of_find?_eq_some ht)
      show (s.2.2.setIfInBounds i t).getD j 0 < s.1.size ∧
        (s.1.getD ((s.2.2.setIfInBounds i t).getD j 0) {}).logN = _
      rw [getD_setIfInBounds]
      by_cases hij : i = j ∧ j < s.2.2.size
      · rw [if_pos hij]
        obtain ⟨rfl, _⟩ := hij
        have hm : maskOnly = false := by rw [← hkind, hkj]
        have hp := List.find?_some ht
        rw [hm] at hp
        simp only [Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hp
        exact ⟨htl, hp.2⟩
      · rw [if_neg hij]
        rcases hj with hj | ⟨rfl, _, _⟩
        · exact hA j hj
        · exact absurd ⟨rfl, by rw [hsz]; exact hi⟩ hij
    · show (s.2.2.setIfInBounds i s.1.size).getD j 0 < (s.1.push _).size ∧
        ((s.1.push _).getD ((s.2.2.setIfInBounds i s.1.size).getD j 0) {}).logN = _
      rw [getD_setIfInBounds, Array.size_push]
      by_cases hij : i = j ∧ j < s.2.2.size
      · rw [if_pos hij, getD_push, if_pos rfl]
        obtain ⟨rfl, _⟩ := hij
        have hm : maskOnly = false := by rw [← hkind, hkj]
        rw [hm]
        exact ⟨by omega, rfl⟩
      · rw [if_neg hij]
        rcases hj with hj | ⟨rfl, _, _⟩
        · obtain ⟨a, b⟩ := hA j hj
          rw [getD_push, if_neg (by omega)]
          exact ⟨by omega, b⟩
        · exact absurd ⟨rfl, by rw [hsz]; exact hi⟩ hij

theorem pass_len (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (maskOnly : Bool)
    (n : Nat) : ∀ (l : List Nat) (s : Array OnBytes.TreeShape × Array Nat × Array Nat)
    (A : Nat → Prop), (∀ i ∈ l, i < n) → s.2.2.size = n →
    (∀ j, A j → ((sent.getD j default).shape.mainRows == 0) = false) →
    (∀ j, A j → s.2.2.getD j 0 < s.1.size ∧
      (s.1.getD (s.2.2.getD j 0) {}).logN = mainLenAt codes sent j) →
    ∀ j, A j ∨ (j ∈ l ∧ ((sent.getD j default).shape.mainRows == 0) = false ∧ maskOnly = false) →
      (l.foldl (passStep codes sent maskOnly) s).2.2.getD j 0 <
        (l.foldl (passStep codes sent maskOnly) s).1.size ∧
      ((l.foldl (passStep codes sent maskOnly) s).1.getD
        ((l.foldl (passStep codes sent maskOnly) s).2.2.getD j 0) {}).logN = mainLenAt codes sent j
  | [], s, A, _, _, _, hA => fun j hj => by
      rcases hj with hj | ⟨hj, _⟩
      · exact hA j hj
      · cases hj
  | i :: l, s, A, hl, hsz, hAk, hA => fun j hj => by
    have hi := hl i (List.mem_cons_self ..)
    have h1 := (passStep_inv codes sent maskOnly n s i (fun _ => False) hsz hi
      (fun _ h => h.elim)).1
    refine pass_len codes sent maskOnly n l (passStep codes sent maskOnly s i)
      (fun j => A j ∨ (j = i ∧ ((sent.getD i default).shape.mainRows == 0) = false ∧
        maskOnly = false))
      (fun k hk => hl k (List.mem_cons_of_mem _ hk)) h1 ?_
      (passStep_len codes sent maskOnly n s i A hsz hi hAk hA) j ?_
    · intro j hj
      rcases hj with hj | ⟨rfl, hk, _⟩
      · exact hAk j hj
      · exact hk
    · rcases hj with hj | ⟨hj, hk, hm⟩
      · exact .inl (.inl hj)
      · rcases List.mem_cons.1 hj with rfl | hj
        · exact .inl (.inr ⟨rfl, hk, hm⟩)
        · exact .inr ⟨hj, hk, hm⟩

/-- The tree of a message with main rows has that message's main length. -/
theorem treeOf_mainLen (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (i : Nat)
    (hi : i < sent.size) (hk : ((sent.getD i default).shape.mainRows == 0) = false) :
    ((treeOf codes sent).1.getD ((treeOf codes sent).2.2.getD i 0) {}).logN =
      mainLenAt codes sent i := by
  unfold treeOf
  rw [treeOfPass_eq, treeOfPass_eq]
  have hr : ∀ k ∈ List.range sent.size, k < sent.size := fun _ h => List.mem_range.1 h
  have h1 := pass_len codes sent false sent.size (List.range sent.size)
    (#[], #[], Array.replicate sent.size 0) (fun _ => False) hr (by simp) (fun _ h => h.elim)
    (fun _ h => h.elim)
  have hs := (pass_inv codes sent false sent.size (List.range sent.size)
    (#[], #[], Array.replicate sent.size 0) (fun _ => False) hr (by simp) (fun _ h => h.elim)).1
  exact (pass_len codes sent true sent.size (List.range sent.size) _ _ hr hs
    (fun j hj => by
      rcases hj with hj | ⟨_, hk, _⟩
      · exact hj.elim
      · exact hk) h1 i (.inl (.inr ⟨List.mem_range.2 hi, hk, rfl⟩))).2

theorem FillMore.start (sent : Array OnBytes.OracleNotice) (tree : Array Nat)
    (a : Array OnBytes.TreeShape)
    (hf : ∀ t, (a.getD t {}).mainWidth = 0 ∧ (a.getD t {}).maskWidth = 0) :
    FillMore sent tree a.size a [] (a, #[], Array.replicate a.size 0) where
  wideOnly := fun t ht => by
    have h0 : (Array.replicate a.size 0).getD t 0 = 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl
    have ht' : 0 < (Array.replicate a.size 0).getD t 0 := ht
    omega
  symOnly := fun t ht => by
    have := (hf t).2
    have ht' : 0 < (a.getD t {}).maskWidth := ht
    omega
  mainPos := fun _ hj => by cases hj
  mainOnly := fun t ht => by
    have := (hf t).1
    have ht' : 0 < (a.getD t {}).mainWidth := ht
    omega
  keepN := fun _ => rfl

theorem FillMore.fold {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice} {tree : Array Nat}
    {m : Nat} {a0 : Array OnBytes.TreeShape} :
    ∀ (l done : List Nat) (s s' : Array OnBytes.TreeShape × Array Nat × Array Nat),
    FillInv codes sent tree m done s → FillMore sent tree m a0 done s →
    l.foldlM (fillStep codes sent tree) s = some s' →
    FillMore sent tree m a0 (l.reverse ++ done) s'
  | [], done, s, s', _, J, h => by
    cases h
    exact J
  | k :: l, done, s, s', I, J, h => by
    rw [List.foldlM_cons] at h
    cases hk : fillStep codes sent tree s k with
    | none => rw [hk] at h; cases h
    | some s1 =>
      rw [hk] at h
      have := FillMore.fold l (k :: done) s1 s' (I.step hk) (J.step I hk) h
      rw [List.reverse_cons, List.append_assoc]
      exact this

/-- What the last step does to a tree's length. -/
theorem getD_closed_logN (a : Array OnBytes.TreeShape) (t : Nat) (ht : t < a.size) :
    ((a.map fun t => if t.mainWidth == 0 then { t with logN := t.logNzk } else t).getD t
      {}).logN =
      if (a.getD t {}).mainWidth = 0 then (a.getD t {}).logNzk else (a.getD t {}).logN := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_eq_getElem ht]
  show (if a[t].mainWidth == 0 then _ else _ : OnBytes.TreeShape).logN =
    if a[t].mainWidth = 0 then a[t].logNzk else a[t].logN
  by_cases h : a[t].mainWidth = 0
  · simp [h]
  · simp [h]

/-- A message with main symbols has main rows. -/
theorem hasMain_of_syms {sent : Array OnBytes.OracleNotice} {j : Nat} (h : 0 < mainSymsAt sent j) :
    ((sent.getD j default).shape.mainRows == 0) = false := by
  unfold mainSymsAt at h
  have : (sent.getD j default).shape.mainRows ≠ 0 := fun q => by rw [q] at h; omega
  simpa using this

/-- The tree in which a message with main symbols lies has that message's main length. -/
theorem treesMade_mainLen {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    {lay : OnBytes.TreeLay} (h : treesMade codes sent = some lay) (j : Nat) (hj : j < sent.size)
    (hm : 0 < mainSymsAt sent j) :
    (lay.shapes.getD (lay.tree.getD j 0) {}).logN = mainLenAt codes sent j := by
  unfold treesMade at h
  split at h
  · cases h
  · rename_i filled hf
    have I0 := FillInv.start codes sent (treeOf codes sent).2.2 (treeOf codes sent).1
    have I := FillInv.fold (List.range sent.size) [] _ filled I0 hf
    have J := FillMore.fold (List.range sent.size) [] _ filled I0
      (FillMore.start sent (treeOf codes sent).2.2 (treeOf codes sent).1 (treeOf_fresh codes sent))
      hf
    unfold closeTrees at h
    dsimp only at h
    split at h
    · have hl := Option.some.inj h
      subst hl
      have hlt := treeOf_lt codes sent j hj
      dsimp only
      rw [getD_closed_logN _ _ (by rw [I.szT]; exact hlt)]
      have hp := J.mainPos j (by simp [hj]) hm hlt
      rw [if_neg (by omega), J.keepN]
      exact treeOf_mainLen codes sent j hj (hasMain_of_syms hm)
    · cases h

/-- What treesCan checks: no mask rows of two lengths meet in one tree, and none are longer than
their tree's main rows. i, j: messages; «one tree»: treeOf gives both the same number. -/
def TreesFit (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) : Prop :=
  (∀ i j, i < sent.size → j < sent.size → 0 < maskRowsAt sent i → 0 < maskRowsAt sent j →
    (treeOf codes sent).2.2.getD i 0 = (treeOf codes sent).2.2.getD j 0 →
    maskLenAt codes sent i = maskLenAt codes sent j) ∧
  (∀ i j, i < sent.size → j < sent.size → 0 < maskRowsAt sent i → 0 < mainSymsAt sent j →
    (treeOf codes sent).2.2.getD i 0 = (treeOf codes sent).2.2.getD j 0 →
    maskLenAt codes sent i ≤ mainLenAt codes sent j)

/-- A yes gives the two facts. -/
theorem treesFit_of_can {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    (h : treesCan codes sent = true) : TreesFit codes sent := by
  refine ⟨fun i j hi hj hmi hmj hij => treesCan_oneLength h i j hi hj hmi hmj hij,
    fun i j hi hj hmi hmj hij => ?_⟩
  obtain ⟨lay, hl, e, _⟩ := treesCan_gives h
  have a := treesCan_notLonger hl i hi hmi
  have b := treesMade_mainLen hl j hj hmj
  rw [e] at a b
  rw [hij, b] at a
  exact a

/-- Where the test of fillStep does not strike, it gives something. -/
theorem fillStep_some (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (tree : Array Nat)
    (s : Array OnBytes.TreeShape × Array Nat × Array Nat) (k : Nat)
    (h : ¬ (0 < maskRowsAt sent k ∧ 0 < s.2.2.getD (tree.getD k 0) 0 ∧
      (s.1.getD (tree.getD k 0) {}).logNzk ≠ maskLenAt codes sent k)) :
    ∃ s', fillStep codes sent tree s k = some s' := by
  unfold fillStep
  dsimp only
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
    exact absurd ⟨hc.1.1, hc.1.2, hc.2⟩ h
  · exact ⟨_, rfl⟩

/-- Under the first fact every message can be laid. -/
theorem fill_total {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice} {tree : Array Nat}
    {m : Nat} {a0 : Array OnBytes.TreeShape} (htr : ∀ i, i < sent.size → tree.getD i 0 < m)
    (h1 : ∀ i j, i < sent.size → j < sent.size → 0 < maskRowsAt sent i → 0 < maskRowsAt sent j →
      tree.getD i 0 = tree.getD j 0 → maskLenAt codes sent i = maskLenAt codes sent j) :
    ∀ (l done : List Nat) (s : Array OnBytes.TreeShape × Array Nat × Array Nat),
    (∀ i ∈ done, i < sent.size) → (∀ k ∈ l, k < sent.size) →
    FillInv codes sent tree m done s → FillMore sent tree m a0 done s →
    ∃ s', l.foldlM (fillStep codes sent tree) s = some s'
  | [], _, s, _, _, _, _ => ⟨s, rfl⟩
  | k :: l, done, s, hd, hl, I, J => by
    have hk := hl k (List.mem_cons_self ..)
    obtain ⟨s1, hs1⟩ := fillStep_some codes sent tree s k (by
      rintro ⟨hm, hw, hne⟩
      obtain ⟨i, hi, hti, hmi⟩ := J.wideOnly _ hw
      have a := I.len i hi hmi (htr i (hd i hi))
      rw [hti] at a
      exact hne (a.trans (h1 i k (hd i hi) hk hmi hm hti)))
    obtain ⟨s', hs'⟩ := fill_total htr h1 l (k :: done) s1
      (fun i hi => by
        rcases List.mem_cons.1 hi with rfl | hi
        · exact hk
        · exact hd i hi)
      (fun q hq => hl q (List.mem_cons_of_mem _ hq)) (I.step hs1) (J.step I hs1)
    exact ⟨s', by rw [List.foldlM_cons, hs1]; exact hs'⟩

/-- The two facts give a yes: the test asks nothing more. -/
theorem can_of_treesFit {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    (h : TreesFit codes sent) : treesCan codes sent = true := by
  have I0 := FillInv.start codes sent (treeOf codes sent).2.2 (treeOf codes sent).1
  have J0 := FillMore.start sent (treeOf codes sent).2.2 (treeOf codes sent).1
    (treeOf_fresh codes sent)
  obtain ⟨filled, hf⟩ := fill_total (treeOf_lt codes sent) h.1 (List.range sent.size) [] _
    (fun _ hi => by cases hi) (fun _ hk => List.mem_range.1 hk) I0 J0
  have I := FillInv.fold (List.range sent.size) [] _ filled I0 hf
  have J := FillMore.fold (List.range sent.size) [] _ filled I0 J0 hf
  have hin : ∀ i, i ∈ (List.range sent.size).reverse ++ [] → i < sent.size := fun i hi => by
    simpa using hi
  unfold treesCan treesMade
  rw [hf]
  show (closeTrees _ filled).isSome = true
  unfold closeTrees
  dsimp only
  rw [if_pos]
  · rfl
  · rw [Array.all_eq_true_iff_forall_mem]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Array.mem_map.1 hx
    obtain ⟨t, ht, rfl⟩ := Array.mem_iff_getElem.1 hy
    have hg : filled.1.getD t {} = filled.1[t] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht]
      rfl
    by_cases hw : filled.1[t].mainWidth = 0
    · simp [hw]
    · by_cases hz : filled.1[t].maskWidth = 0
      · simp [hw, hz]
      · obtain ⟨i, hi, hti, hmi⟩ := J.symOnly t (by rw [hg]; omega)
        obtain ⟨j, hj, htj, hmj⟩ := J.mainOnly t (by rw [hg]; omega)
        have a := I.len i hi hmi (treeOf_lt codes sent i (hin i hi))
        have b := treeOf_mainLen codes sent j (hin j hj) (hasMain_of_syms hmj)
        have c := J.keepN t
        rw [hti, hg] at a
        rw [htj] at b
        rw [hg, b] at c
        have d := h.2 i j (hin i hi) (hin j hj) hmi hmj (hti.trans htj.symm)
        simp only [hw, beq_iff_eq, if_false, Bool.or_eq_true, decide_eq_true_eq]
        right
        omega

/-- What treesCan checks, no less and no more. -/
theorem treesCan_iff (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) :
    treesCan codes sent = true ↔ TreesFit codes sent :=
  ⟨treesFit_of_can, can_of_treesFit⟩

end VerifiableInference.Desc.Own

#print axioms VerifiableInference.Desc.Own.treeOf_lt
#print axioms VerifiableInference.Desc.Own.treesCan_gives
#print axioms VerifiableInference.Desc.Own.treesCan_oneLength
#print axioms VerifiableInference.Desc.Own.treesCan_notLonger
#print axioms VerifiableInference.Desc.Own.treeOf_mainLen
#print axioms VerifiableInference.Desc.Own.treesCan_iff
