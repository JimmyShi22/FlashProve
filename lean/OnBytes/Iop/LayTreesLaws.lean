-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Iop/LayTreesLaws.lean: two laws on the verifier's layout of a prover's message in trees
(layTrees, OnBytes/Iop/Ground.lean).

What is proved. Let layTrees cs sent = some L, and let i be the number of an oracle message of sent.
 - layTrees_main: if message i has main rows and its mainDeg is not 0, then the logN of its tree in
   L is the logN of the message's main code.
 - layTrees_mask: if message i has mask rows, then the logNzk of its tree in L is the logN of the
   message's mask code, and it is at most the tree's logN.
Of cs and sent the laws ask only that layTrees gives a layout.

How. layTrees is two placing passes, a filling loop and a last touch. The first section repeats the
bodies of the loops as definitions; layTrees_eq says, by unfolding alone, that layTrees is made of
them. Behind the passes every message has a tree, which has the length of the message's main rows if
there are any (laid_placed). The filling loop keeps a tree's logN. Once message i has entered its
tree, the tree has main symbols if the message has, so the last touch leaves its logN. If the
message has mask rows, the tree has their length from then on, since a later message with mask rows
of another length makes the loop fail (fillStep_inv); and the tree has mask symbols, so the closing
test of layTrees compares its two lengths.

Main definitions: TreeLay.treeOf; in LayTreesLaws: passStep, laid, enter, fillStep, settle, Placed,
FillInv.
Main theorems: layTrees_main, layTrees_mask; in LayTreesLaws: layTrees_eq, laid_placed,
fillStep_inv, layTrees_core.

What is not claimed. Nothing on soundness. Not that layTrees gives a layout for any cs and sent.
Nothing on L.part, on the widths that a tree lists (mainSymbols, maskSymbols), on which messages
share a tree or on the number of trees. Nothing on a number i that is not below sent.size. A code
is read as layTrees reads it, with Array.getD: where a message names a code that cs does not have,
the laws speak of the default code, whose logN is 0. Whether the codes exist is another test
(Blk.shapeOk). A message with main rows whose mainDeg is 0 is outside layTrees_main: it adds no
main symbol, so the last touch may overwrite its tree's logN. No layout at a real file's messages
is shown here.
-/
import OnBytes.Iop.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes

namespace LayTreesLaws

/-! ### The steps of layTrees, by name -/

/-- The state of each of the three loops of layTrees: three arrays. -/
abbrev State := Array TreeShape × Array Nat × Array Nat

/-- One step of a placing pass of layTrees: message i finds its tree or opens one. The state: the
trees, their classes, each message's tree. -/
def passStep (codes : Codes) (sent : Array OracleNotice) (maskOnly : Bool) (s : State) (i : Nat) :
    State :=
  let n := sent.getD i default
  if (n.shape.mainRows == 0) != maskOnly then s
  else
    let logN := (codes.base.getD n.shape.code default).logN
    let fits (t : Nat) : Bool :=
      s.2.1.getD t noId == n.leafClass && (maskOnly || (s.1.getD t {}).logN == logN)
    match (List.range s.1.size).find? fits with
    | some t => (s.1, s.2.1, s.2.2.setIfInBounds i t)
    | none =>
      (s.1.push (if maskOnly then {} else { logN := logN }), s.2.1.push n.leafClass,
        s.2.2.setIfInBounds i s.1.size)

/-- The state behind both placing passes of layTrees. -/
def laid (codes : Codes) (sent : Array OracleNotice) : State :=
  (List.range sent.size).foldl (passStep codes sent true)
    ((List.range sent.size).foldl (passStep codes sent false)
      (#[], #[], Array.replicate sent.size 0))

/-- A message of shape sh, whose mask code has the length 2^zk, enters its widths in the tree t. -/
def enter (sh : OracleShape) (zk : Nat) (t : TreeShape) : TreeShape :=
  { t with
    logNzk := if 0 < sh.maskRows then zk else t.logNzk
    mainSymbols := t.mainSymbols.push (sh.mainRows * sh.mainDeg)
    maskSymbols := t.maskSymbols.push (sh.maskRows * 3) }

/-- One step of the filling loop of layTrees: message i enters its widths in its tree. The state:
the trees, each message's place in its tree, each tree's width of mask symbols so far. -/
def fillStep (codes : Codes) (sent : Array OracleNotice) (tree : Array Nat) (s : State) (i : Nat) :
    Option State :=
  let n := sent.getD i default
  let at0 := tree.getD i 0
  let zk := (codes.mask.getD n.shape.maskCode default).logN
  let before := (s.1.getD at0 {}).mainSymbols.size
  if 0 < n.shape.maskRows && 0 < s.2.2.getD at0 0 && (s.1.getD at0 {}).logNzk != zk then none
  else
    some (s.1.modify at0 (enter n.shape zk), s.2.1.push before,
      s.2.2.modify at0 (· + n.shape.maskRows * 3))

/-- The last touch of layTrees: a tree without main symbols takes its mask rows' length. -/
def settle (t : TreeShape) : TreeShape :=
  if t.mainWidth == 0 then { t with logN := t.logNzk } else t

/-- layTrees, written with the named steps. -/
theorem layTrees_eq (codes : Codes) (sent : Array OracleNotice) :
    layTrees codes sent =
      ((List.range sent.size).foldlM (fillStep codes sent (laid codes sent).2.2)
        ((laid codes sent).1, #[], Array.replicate (laid codes sent).1.size 0)).bind fun filled =>
        if (filled.1.map settle).all fun t => t.maskWidth == 0 || t.logNzk ≤ t.logN then
          some { tree := (laid codes sent).2.2, part := filled.2.1, shapes := filled.1.map settle }
        else none :=
  rfl

/-! ### Loops over List.range -/

/-- A property that every step carries on holds behind a loop over List.range. -/
theorem foldl_range_inv {σ : Type} (f : σ → Nat → σ) (P : Nat → σ → Prop) (n : Nat) (s0 : σ)
    (h0 : P 0 s0) (hs : ∀ k s, k < n → P k s → P (k + 1) (f s k)) :
    P n ((List.range n).foldl f s0) := by
  induction n with
  | zero => simpa using h0
  | succ m ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact hs m _ (Nat.lt_succ_self m) (ih fun k s hk => hs k s (Nat.lt_succ_of_lt hk))

/-- The same for a loop whose steps can fail, if the loop has not failed. -/
theorem foldlM_range_inv {σ : Type} (f : σ → Nat → Option σ) (P : Nat → σ → Prop) (n : Nat)
    (s0 r : σ) (h : (List.range n).foldlM f s0 = some r) (h0 : P 0 s0)
    (hs : ∀ k s s', k < n → P k s → f s k = some s' → P (k + 1) s') : P n r := by
  induction n generalizing r with
  | zero =>
    simp at h
    exact h ▸ h0
  | succ m ih =>
    rw [List.range_succ, List.foldlM_append] at h
    cases hm : (List.range m).foldlM f s0 with
    | none => simp [hm] at h
    | some s =>
      simp [hm] at h
      exact hs m s r (Nat.lt_succ_self m)
        (ih s hm fun k s s' hk => hs k s s' (Nat.lt_succ_of_lt hk)) h

/-! ### The placing passes -/

/-- Message j has a tree, and if it has main rows, the tree has their length. -/
def Placed (codes : Codes) (sent : Array OracleNotice) (s : State) (j : Nat) : Prop :=
  ∃ T, s.1[s.2.2.getD j 0]? = some T ∧ (0 < (sent.getD j default).shape.mainRows →
    T.logN = (codes.base.getD (sent.getD j default).shape.code default).logN)

/-- A step keeps the number of messages. -/
theorem passStep_size (codes : Codes) (sent : Array OracleNotice) (b : Bool) (s : State)
    (k : Nat) : (passStep codes sent b s k).2.2.size = s.2.2.size := by
  simp only [passStep]
  split
  · rfl
  · split <;> simp

/-- A step leaves the tree of every other message as it is. -/
theorem passStep_keeps (codes : Codes) (sent : Array OracleNotice) (b : Bool) (s : State)
    (j k : Nat) (hjk : j ≠ k) (T : TreeShape) (h : s.1[s.2.2.getD j 0]? = some T) :
    (passStep codes sent b s k).1[(passStep codes sent b s k).2.2.getD j 0]? = some T := by
  have hkj : k ≠ j := fun e => hjk e.symm
  simp only [Array.getD_eq_getD_getElem?] at h
  simp only [passStep]
  split
  · simpa using h
  · split
    · simpa [Array.getElem?_setIfInBounds, hkj] using h
    · have hlt := (Array.getElem?_eq_some_iff.1 h).1
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, hkj, if_false]
      rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hlt)]
      exact h

/-- A step of the other pass changes nothing. -/
theorem passStep_skip (codes : Codes) (sent : Array OracleNotice) (b : Bool) (s : State) (k : Nat)
    (hk : ((sent.getD k default).shape.mainRows == 0) ≠ b) : passStep codes sent b s k = s := by
  simp only [passStep]
  rw [if_pos]
  simpa using hk

/-- A step of its own pass places its message. -/
theorem passStep_places (codes : Codes) (sent : Array OracleNotice) (b : Bool) (s : State)
    (k : Nat) (hk : ((sent.getD k default).shape.mainRows == 0) = b) (hsz : k < s.2.2.size) :
    Placed codes sent (passStep codes sent b s k) k := by
  have hb : 0 < (sent.getD k default).shape.mainRows → b = false := by
    intro hpos
    rw [← hk]
    exact beq_eq_false_iff_ne.2 (Nat.ne_of_gt hpos)
  simp only [Placed, passStep]
  rw [if_neg (by rw [hk]; simp)]
  split
  · rename_i t ht
    have hfit := List.find?_some ht
    have hmem := List.mem_range.1 (List.mem_of_find?_eq_some ht)
    refine ⟨s.1[t], ?_, ?_⟩
    · simp [hsz, hmem]
    · intro hpos
      simp [hb hpos, hmem] at hfit
      simpa using hfit.2
  · refine ⟨if b then {} else
      { logN := (codes.base.getD (sent.getD k default).shape.code default).logN }, ?_, ?_⟩
    · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, if_pos hsz, if_true,
        Option.getD_some, Array.getElem?_push_size]
    · intro hpos
      simp [hb hpos]

/-- Behind a pass every message of the pass is placed, and so is every message that was. -/
theorem pass_inv (codes : Codes) (sent : Array OracleNotice) (b : Bool) (D : Nat → Prop)
    (s0 : State) (hsz : s0.2.2.size = sent.size) (h0 : ∀ j, D j → Placed codes sent s0 j) :
    ((List.range sent.size).foldl (passStep codes sent b) s0).2.2.size = sent.size ∧
      ∀ j, D j ∨ (j < sent.size ∧ ((sent.getD j default).shape.mainRows == 0) = b) →
        Placed codes sent ((List.range sent.size).foldl (passStep codes sent b) s0) j := by
  refine foldl_range_inv (passStep codes sent b)
    (fun k s => s.2.2.size = sent.size ∧
      ∀ j, D j ∨ (j < k ∧ ((sent.getD j default).shape.mainRows == 0) = b) →
        Placed codes sent s j)
    sent.size s0 ⟨hsz, ?_⟩ ?_
  · intro j hj
    rcases hj with hj | hj
    · exact h0 j hj
    · exact absurd hj.1 (Nat.not_lt_zero j)
  · intro k s hk ⟨hs, hp⟩
    refine ⟨by rw [passStep_size, hs], ?_⟩
    intro j hj
    by_cases hb : ((sent.getD k default).shape.mainRows == 0) = b
    · by_cases hjk : j = k
      · subst hjk
        exact passStep_places codes sent b s j hb (by omega)
      · have hj' : D j ∨ (j < k ∧ ((sent.getD j default).shape.mainRows == 0) = b) := by
          rcases hj with hj | hj
          · exact Or.inl hj
          · exact Or.inr ⟨by omega, hj.2⟩
        obtain ⟨T, hT, hl⟩ := hp j hj'
        exact ⟨T, passStep_keeps codes sent b s j k hjk T hT, hl⟩
    · rw [passStep_skip codes sent b s k hb]
      apply hp j
      rcases hj with hj | hj
      · exact Or.inl hj
      · have hjk : j ≠ k := fun e => hb (e ▸ hj.2)
        exact Or.inr ⟨by omega, hj.2⟩

/-- Behind both passes every message is placed. -/
theorem laid_placed (codes : Codes) (sent : Array OracleNotice) (j : Nat) (hj : j < sent.size) :
    Placed codes sent (laid codes sent) j := by
  have h1 := pass_inv codes sent false (fun _ => False) (#[], #[], Array.replicate sent.size 0)
    (by simp) (fun _ h => h.elim)
  have h2 := pass_inv codes sent true
    (fun j => j < sent.size ∧ ((sent.getD j default).shape.mainRows == 0) = false) _ h1.1
    (fun j h => h1.2 j (Or.inr h))
  apply h2.2 j
  by_cases hb : ((sent.getD j default).shape.mainRows == 0) = true
  · exact Or.inr ⟨hj, hb⟩
  · exact Or.inl ⟨hj, eq_false_of_ne_true hb⟩

/-! ### The filling loop -/

/-- What the filling loop keeps of tree t, the tree of message i, before step k. The tree exists and
has the length l0. Once message i has entered: the tree has main symbols if the message has; if the
message has mask rows, the tree has their length, has mask symbols, and its counted width of mask
symbols is not 0. -/
def FillInv (codes : Codes) (sent : Array OracleNotice) (i t l0 k : Nat) (s : State) : Prop :=
  ∃ T w, s.1[t]? = some T ∧ s.2.2[t]? = some w ∧ T.logN = l0 ∧ (i < k →
    (0 < (sent.getD i default).shape.mainRows * (sent.getD i default).shape.mainDeg →
      0 < T.mainWidth) ∧
    (0 < (sent.getD i default).shape.maskRows →
      T.logNzk = (codes.mask.getD (sent.getD i default).shape.maskCode default).logN ∧
        0 < T.maskWidth ∧ 0 < w))

/-- A step of the filling loop that does not fail carries FillInv on. -/
theorem fillStep_inv (codes : Codes) (sent : Array OracleNotice) (tree : Array Nat)
    (i t l0 k : Nat) (s s' : State) (htree : tree.getD i 0 = t)
    (hI : FillInv codes sent i t l0 k s) (hs : fillStep codes sent tree s k = some s') :
    FillInv codes sent i t l0 (k + 1) s' := by
  obtain ⟨T, w, hT, hw, hl, hdone⟩ := hI
  simp only [fillStep] at hs
  generalize hak : tree.getD k 0 = a at hs
  split at hs
  · cases hs
  · rename_i hc
    cases hs
    by_cases ht : a = t
    · subst ht
      have hc' : 0 < (sent.getD k default).shape.maskRows → 0 < w → T.logNzk =
          (codes.mask.getD (sent.getD k default).shape.maskCode default).logN := by
        intro h1 h2
        simp [hT, hw, h2] at hc
        simpa using hc (by simpa using h1)
      refine ⟨enter (sent.getD k default).shape
        (codes.mask.getD (sent.getD k default).shape.maskCode default).logN T,
        w + (sent.getD k default).shape.maskRows * 3, ?a, ?b, ?c, ?d⟩
      case a =>
        rw [Array.getElem?_modify, if_pos rfl, hT]
        rfl
      case b =>
        rw [Array.getElem?_modify, if_pos rfl, hw]
        rfl
      case c => exact hl
      case d =>
        intro hik
        by_cases hek : i = k
        · subst hek
          refine ⟨fun h => ?_, fun h => ⟨?_, ?_, ?_⟩⟩
          · simp only [enter, TreeShape.mainWidth, Array.foldl_push]
            omega
          · simp only [enter, if_pos h]
          · simp only [enter, TreeShape.maskWidth, Array.foldl_push]
            omega
          · omega
        · obtain ⟨h1, h2⟩ := hdone (by omega)
          refine ⟨fun h => ?_, fun h => ?_⟩
          · have h3 := h1 h
            simp only [enter, TreeShape.mainWidth, Array.foldl_push] at h3 ⊢
            omega
          · obtain ⟨e1, e2, e3⟩ := h2 h
            refine ⟨?_, ?_, by omega⟩
            · show (if 0 < _ then _ else T.logNzk) = _
              split
              · rename_i hz
                rw [← hc' hz e3]
                exact e1
              · exact e1
            · simp only [enter, TreeShape.maskWidth, Array.foldl_push] at e2 ⊢
              omega
    · have hne : i ≠ k := fun e => ht (by rw [← hak, ← htree, e])
      refine ⟨T, w, ?_, ?_, hl, fun hik => hdone (by omega)⟩
      · rw [Array.getElem?_modify, if_neg ht]
        exact hT
      · rw [Array.getElem?_modify, if_neg ht]
        exact hw

/-! ### The whole -/

/-- What layTrees, where it gives a layout, has made of the tree of message i. -/
theorem layTrees_core (cs : Codes) (sent : Array OracleNotice) (L : TreeLay)
    (h : layTrees cs sent = some L) (i : Nat) (hi : i < sent.size) :
    ∃ T, L.shapes.getD (L.tree.getD i 0) default = settle T ∧
      (0 < (sent.getD i default).shape.mainRows →
        T.logN = (cs.base.getD (sent.getD i default).shape.code default).logN) ∧
      (0 < (sent.getD i default).shape.mainRows * (sent.getD i default).shape.mainDeg →
        0 < T.mainWidth) ∧
      (0 < (sent.getD i default).shape.maskRows →
        T.logNzk = (cs.mask.getD (sent.getD i default).shape.maskCode default).logN ∧
          0 < T.maskWidth) ∧
      ((settle T).maskWidth = 0 ∨ (settle T).logNzk ≤ (settle T).logN) := by
  rw [layTrees_eq] at h
  cases hf : (List.range sent.size).foldlM (fillStep cs sent (laid cs sent).2.2)
      ((laid cs sent).1, #[], Array.replicate (laid cs sent).1.size 0) with
  | none =>
    rw [hf] at h
    cases h
  | some filled =>
    rw [hf, Option.bind_some] at h
    split at h
    · rename_i hall
      cases h
      obtain ⟨T0, hT0, hl0⟩ := laid_placed cs sent i hi
      have hlt := (Array.getElem?_eq_some_iff.1 hT0).1
      obtain ⟨T, w, hT, -, hl, hdone⟩ := foldlM_range_inv _
        (FillInv cs sent i ((laid cs sent).2.2.getD i 0) T0.logN) sent.size _ filled hf
        ⟨T0, 0, hT0, by rw [Array.getElem?_replicate, if_pos hlt], rfl,
          fun h => absurd h (Nat.not_lt_zero i)⟩
        (fun k s s' _ hI hs => fillStep_inv cs sent _ i _ _ k s s' rfl hI hs)
      obtain ⟨h1, h2⟩ := hdone hi
      refine ⟨T, ?_, fun h => hl.trans (hl0 h), h1, fun h => ⟨(h2 h).1, (h2 h).2.1⟩, ?_⟩
      · show (filled.1.map settle).getD ((laid cs sent).2.2.getD i 0) default = settle T
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, hT]
        rfl
      · have hmem : settle T ∈ filled.1.map settle :=
          Array.mem_map.2 ⟨T, Array.mem_of_getElem? hT, rfl⟩
        simpa using Array.all_eq_true_iff_forall_mem.1 hall _ hmem
    · cases h

end LayTreesLaws

/-- The tree of message number i of a prover's message. -/
def TreeLay.treeOf (L : TreeLay) (i : Nat) : TreeShape := L.shapes.getD (L.tree.getD i 0) default

/-- Where `layTrees` gives a layout: a message with main rows whose mainDeg is not 0 lies in a tree
whose logN is that of its main code. -/
theorem layTrees_main (cs : Codes) (sent : Array OracleNotice) (L : TreeLay)
    (h : layTrees cs sent = some L) (i : Nat) (hi : i < sent.size)
    (hm : 0 < (sent.getD i default).shape.mainRows)
    (hd : 0 < (sent.getD i default).shape.mainDeg) :
    (L.treeOf i).logN = (cs.base.getD (sent.getD i default).shape.code default).logN := by
  obtain ⟨T, hT, h1, h2, -, -⟩ := LayTreesLaws.layTrees_core cs sent L h i hi
  have hw := h2 (Nat.mul_pos hm hd)
  rw [TreeLay.treeOf, hT, ← h1 hm, LayTreesLaws.settle, if_neg]
  simp
  omega

/-- A message with mask rows lies in a tree whose mask rows have the length of its mask code, and
that length is at most the tree's. -/
theorem layTrees_mask (cs : Codes) (sent : Array OracleNotice) (L : TreeLay)
    (h : layTrees cs sent = some L) (i : Nat) (hi : i < sent.size)
    (hz : 0 < (sent.getD i default).shape.maskRows) :
    (L.treeOf i).logNzk = (cs.mask.getD (sent.getD i default).shape.maskCode default).logN ∧
      (L.treeOf i).logNzk ≤ (L.treeOf i).logN := by
  obtain ⟨T, hT, -, -, h3, h4⟩ := LayTreesLaws.layTrees_core cs sent L h i hi
  obtain ⟨e, hw⟩ := h3 hz
  have hzk : (LayTreesLaws.settle T).logNzk = T.logNzk := by
    unfold LayTreesLaws.settle
    split <;> rfl
  have hmw : (LayTreesLaws.settle T).maskWidth = T.maskWidth := by
    unfold LayTreesLaws.settle
    split <;> rfl
  rw [TreeLay.treeOf, hT]
  refine ⟨hzk.trans e, ?_⟩
  rcases h4 with h4 | h4
  · omega
  · exact h4

end OnBytes
