-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/OpenDomProofs.lean: the proofs of the statements of Run/OpenDom.lean.

The statements, both under the hypotheses told in Run/OpenDom.lean, the head, 3, and both at two
hash functions that agree on the hash function's domain (`Fmt.hDom`):
  the reader of a Merkle opening (`Fmt.readOpeningW`) gives the same;
  the lenient reader with the reader of openings as a parameter (`cutWhole`; its fold over rounds
    is `cutFold`), at two readers of openings, gives the same.
The domain: the calls at which `hDom` is true: a number of the format's table; a tree and an index
that the table allows under that number; bytes within the bound on their length; a start of the
fixed length, all zero under a number that takes no start; and, under a leaf's number, bytes laid
out as a leaf (`hDom`, Fmt/Rules23.lean; `leafOK`, Fmt/Rules23.lean). (`Fmt.formatHash` and
`Fmt.HO Fmt.oracle` agree on the domain, and beyond it no agreement of the two is stated in Run/ or
Fmt/.)

Main names (statements and hypotheses: Run/OpenDom.lean):
  `open_dom`: the reader of a Merkle opening (`Fmt.readOpeningW`) at two hash functions that agree
    on the domain.
  `fold_dom`: the lenient reader with the reader of openings as a parameter (`cutWhole`), at two
    such readers.
The domain is `Fmt.hDom`; the fold over rounds of `cutWhole` is `cutFold`. What is not claimed:
Run/OpenDom.lean, the head, 4.

The steps. The walk up a tree for two ways of combining that agree on "good" values and keep them
good (`walkLone_dom`, `walkLevel_dom`, `walk_dom`: generic in the values' type); leaves and
vertices in the domain (`domLeaf`, `domVertex`; `size_colBytes`, `size_leafBytes`); `leavesW_dom`;
`rdOpening_parts` (lengths of what the reader without a hash hands out; on lemmas of
Run/Toy1TieTree.lean, Run/WalkTieProofs.lean); `readOpeningW_dom`. Then the fold: `cutStep_dom2`,
`cutFold_dom2`, `startChainW_run`, `cutChain_dom2`, `cutWhole_dom2`.

Notation:
  `G`: the predicate that says which of the walk's values are "good" (`α → Prop`);
  `166`: the number under which the format hashes an inner vertex (`Fmt.vertexW`, Fmt/Rules7.lean);
  `smallSh sb sh`: the bounds on a tree's shape that the hash's domain asks (Run/OpenDom.lean);
  `smallB S b`: the sizes of description and file that the hash's domain asks (Run/LaxDom.lean);
  `OpsW`: a reader of the openings after one draw of positions (Run/ParseLax.lean).

Terms: lean/GLOSSARY.md: domain (of the hash).
-/
import Run.OpenDom
import Run.LaxDomProofs
import Run.Toy1TieTree
import Fmt.Rules1Laws

set_option autoImplicit false

namespace Run
open _root_.Fmt (hDom dlen)

/-! ### The walk, at two ways of combining that agree on good values -/

section
variable {α : Type} (G : α → Prop) (cb' cb : Nat → Nat → α → α → Id α)
  (hc : ∀ d i x y, G x → G y → cb' d i x y = cb d i x y)
  (hg : ∀ d i x y, G x → G y → G (cb d i x y))

abbrev WalkSt (α : Type) : Type := List α × List (Nat × Nat × α)

include hc hg in
theorem walkLone_dom (d i : Nat) (x : α) (s : WalkSt α) (hx : G x) (hs : ∀ v ∈ s.1, G v) :
    _root_.Fmt.walkLoneW (m := Id) cb' _root_.Fmt.takeGiven d i x s =
      _root_.Fmt.walkLoneW (m := Id) cb _root_.Fmt.takeGiven d i x s ∧
    ∀ r, _root_.Fmt.walkLoneW (m := Id) cb _root_.Fmt.takeGiven d i x s = some r →
      G r.1.2 ∧ ∀ v ∈ r.2.1, G v := by
  obtain ⟨g, lg⟩ := s
  cases g with
  | nil => exact ⟨rfl, fun r e => by cases e⟩
  | cons y g =>
    have hy : G y := hs y (List.mem_cons_self ..)
    have hg' : ∀ v ∈ g, G v := fun v hv => hs v (List.mem_cons_of_mem _ hv)
    unfold _root_.Fmt.walkLoneW _root_.Fmt.takeGiven
    by_cases he : (i % 2 == 0) = true
    · simp only [he, if_true, idb, idp]
      refine ⟨by rw [hc _ _ _ _ hx hy], fun r e => ?_⟩
      cases e
      exact ⟨hg _ _ _ _ hx hy, hg'⟩
    · simp only [he, idb, idp]
      refine ⟨by simp only [Bool.false_eq_true, if_false]; rw [hc _ _ _ _ hy hx], fun r e => ?_⟩
      simp only [Bool.false_eq_true, if_false] at e
      cases e
      exact ⟨hg _ _ _ _ hy hx, hg'⟩


include hc hg in
theorem walkLevel_dom (d : Nat) :
    ∀ (l : List (Nat × α)) (s : WalkSt α), (∀ v ∈ l, G v.2) → (∀ v ∈ s.1, G v) →
      _root_.Fmt.walkLevelW (m := Id) cb' _root_.Fmt.takeGiven d l s =
        _root_.Fmt.walkLevelW (m := Id) cb _root_.Fmt.takeGiven d l s ∧
      ∀ r, _root_.Fmt.walkLevelW (m := Id) cb _root_.Fmt.takeGiven d l s = some r →
        (∀ v ∈ r.1, G v.2) ∧ ∀ v ∈ r.2.1, G v
  | [], s, _, hs => by
    refine ⟨rfl, fun r e => ?_⟩
    have e' : r = ([], s) := (Option.some.inj e).symm
    subst e'
    exact ⟨fun v hv => absurd hv (List.not_mem_nil), hs⟩
  | [(i, x)], s, hl, hs => by
    obtain ⟨e1, e2⟩ := walkLone_dom G cb' cb hc hg d i x s (hl (i, x) (List.mem_cons_self ..)) hs
    simp only [_root_.Fmt.walkLevelW, idb, idp, e1]
    refine ⟨trivial, fun r e => ?_⟩
    cases hw : _root_.Fmt.walkLoneW (m := Id) cb _root_.Fmt.takeGiven d i x s with
    | none => rw [hw] at e; cases e
    | some q =>
      rw [hw] at e
      cases e
      obtain ⟨a, b⟩ := e2 q hw
      exact ⟨fun v hv => by rw [List.mem_singleton] at hv; exact hv ▸ a, b⟩
  | (i, x) :: (i', x') :: rest, s, hl, hs => by
    have hx : G x := hl (i, x) (List.mem_cons_self ..)
    have hx' : G x' := hl (i', x') (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hrest : ∀ v ∈ rest, G v.2 := fun v hv =>
      hl v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv))
    have htl : ∀ v ∈ (i', x') :: rest, G v.2 := fun v hv => hl v (List.mem_cons_of_mem _ hv)
    unfold _root_.Fmt.walkLevelW
    split
    · obtain ⟨e1, e2⟩ := walkLevel_dom d rest s hrest hs
      simp only [idb, idp, e1, hc _ _ _ _ hx hx']
      refine ⟨trivial, fun r e => ?_⟩
      cases hw : _root_.Fmt.walkLevelW (m := Id) cb _root_.Fmt.takeGiven d rest s with
      | none => rw [hw] at e; cases e
      | some q =>
        rw [hw] at e
        cases e
        obtain ⟨a, b⟩ := e2 q hw
        refine ⟨fun v hv => ?_, b⟩
        rcases List.mem_cons.1 hv with rfl | hv
        · exact hg _ _ _ _ hx hx'
        · exact a v hv
    · obtain ⟨e1, e2⟩ := walkLone_dom G cb' cb hc hg d i x s hx hs
      simp only [idb, e1]
      cases hw : _root_.Fmt.walkLoneW (m := Id) cb _root_.Fmt.takeGiven d i x s with
      | none => exact ⟨rfl, fun r e => by cases e⟩
      | some q =>
        obtain ⟨a, b⟩ := e2 q hw
        obtain ⟨f1, f2⟩ := walkLevel_dom d ((i', x') :: rest) q.2 htl b
        simp only [idp, f1]
        refine ⟨trivial, fun r e => ?_⟩
        cases hv2 : _root_.Fmt.walkLevelW
            (m := Id) cb _root_.Fmt.takeGiven d ((i', x') :: rest) q.2 with
        | none => rw [hv2] at e; cases e
        | some t =>
          rw [hv2] at e
          cases e
          obtain ⟨a', b'⟩ := f2 t hv2
          refine ⟨fun v hv => ?_, b'⟩
          rcases List.mem_cons.1 hv with rfl | hv
          · exact a
          · exact a' v hv

include hc hg in
theorem walk_dom :
    ∀ (d : Nat) (now : List (Nat × α)) (s : WalkSt α) (met : List (Nat × Nat × α)),
      (∀ v ∈ now, G v.2) → (∀ v ∈ s.1, G v) →
      _root_.Fmt.walkW (m := Id) cb' _root_.Fmt.takeGiven d now s met =
        _root_.Fmt.walkW (m := Id) cb _root_.Fmt.takeGiven d now s met
  | 0, now, s, met, _, _ => by
    rcases now with _ | ⟨v, _ | ⟨w, l⟩⟩ <;> rfl
  | d + 1, now, s, met, hn, hs => by
    obtain ⟨e1, e2⟩ := walkLevel_dom G cb' cb hc hg (d + 1) now s hn hs
    simp only [_root_.Fmt.walkW, idb, e1]
    cases hw : _root_.Fmt.walkLevelW (m := Id) cb _root_.Fmt.takeGiven (d + 1) now s with
    | none => rfl
    | some q =>
      obtain ⟨a, b⟩ := e2 q hw
      exact walk_dom d q.1 q.2 _ a b

end

/-! ### Leaves and vertices in the hash's domain -/

theorem size_colBytes : ∀ col : List UInt64, (_root_.Fmt.colBytes col).size = 8 * col.length
  | [] => rfl
  | x :: l => by
    have ih := size_colBytes l
    unfold _root_.Fmt.colBytes at ih ⊢
    rw [List.map_cons, _root_.Fmt.cat_cons, ByteArray.size_append, ih,
      _root_.Fmt.size_u64, List.length_cons]
    omega

theorem size_leafBytes (col : List UInt64) (salt : ByteArray) :
    (_root_.Fmt.leafBytes col salt).size ≤ 8 * col.length + 128 + salt.size := by
  unfold _root_.Fmt.leafBytes _root_.Fmt.fillLen
  rw [ByteArray.size_append, ByteArray.size_append, size_colBytes, _root_.Fmt.size_zeros]
  split <;> omega

theorem size_leafBytes' (col : List UInt64) (salt : ByteArray) :
    (_root_.Fmt.leafBytes col salt).size =
      8 * col.length + _root_.Fmt.fillLen col.length salt.size + salt.size := by
  unfold _root_.Fmt.leafBytes
  rw [ByteArray.size_append, ByteArray.size_append, size_colBytes, _root_.Fmt.size_zeros]

/-- Under the hypotheses below, a leaf as `Fmt.leafW` spells it, under the number `Fmt.leafNo st`,
lies in the hash's domain: its label's place holds the tree's number, the number of the column's
words and the number of the salt's words. -/
theorem domLeaf (st : Bool) (tree idx : Nat) (start : ByteArray) (col : List UInt64)
    (salt : ByteArray) (ht : tree < 2 ^ 16) (hi : idx < 2 ^ 63) (hs : start.size = 32)
    (hW1 : 1 ≤ col.length) (hW : col.length < 2 ^ 24)
    (hsalt : _root_.Fmt.saltLenOK salt.size = true) (h0 : (!st || tree == 0) = true) :
    hDom (_root_.Fmt.leafNo st) (_root_.Fmt.leafPlace tree col.length (salt.size / 8))
        idx start (_root_.Fmt.leafBytes col salt) = true := by
  simp only [_root_.Fmt.saltLenOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsalt
  have h8 : 8 * (salt.size / 8) = salt.size := by omega
  have hb : (_root_.Fmt.leafBytes col salt).size ≤ 2 ^ 32 - 144 := by
    have := size_leafBytes col salt; omega
  have hlt : _root_.Fmt.leafPlace tree col.length (salt.size / 8) < 2 ^ 48 :=
    _root_.Fmt.leafPlace_lt _ _ _ ht hW (by omega)
  have hok : ∀ n, (!(n == 173 || n == 174) || tree == 0) = true →
      _root_.Fmt.leafOK n (_root_.Fmt.leafPlace tree col.length (salt.size / 8))
          (_root_.Fmt.leafBytes col salt) = true := by
    intro n hn
    unfold _root_.Fmt.leafOK
    rw [_root_.Fmt.placeW_leafPlace _ _ _ ht hW, _root_.Fmt.placeS_leafPlace _ _ _ ht hW,
      _root_.Fmt.placeTree_leafPlace _ _ _ ht, h8, hn]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_true]
    refine Or.inr ⟨⟨⟨⟨hW1, by omega⟩, by omega⟩, size_leafBytes' col salt⟩, ?_⟩
    have := _root_.Fmt.extract_mid (_root_.Fmt.colBytes col)
      (_root_.Fmt.zeroBytes (_root_.Fmt.fillLen col.length salt.size)) salt
    rw [size_colBytes, _root_.Fmt.size_zeros] at this
    exact congrArg ByteArray.data this
  simp only [hDom, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true]
  cases st
  · refine ⟨⟨⟨⟨⟨⟨⟨by decide, hlt⟩, Or.inl (by decide)⟩, ?_⟩, hb⟩, hs⟩, Or.inl (by decide)⟩,
      hok 164 rfl⟩
    simp only [_root_.Fmt.idxOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
    exact ⟨⟨hi, Or.inl (by decide)⟩, Or.inl (by decide)⟩
  · refine ⟨⟨⟨⟨⟨⟨⟨by decide, hlt⟩, Or.inl (by decide)⟩, ?_⟩, hb⟩, hs⟩, Or.inl (by decide)⟩,
      hok 174 h0⟩
    simp only [_root_.Fmt.idxOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
    exact ⟨⟨hi, Or.inl (by decide)⟩, Or.inl (by decide)⟩

theorem domVertex (cfg l r : ByteArray) (hc : cfg.size = 32) (hl : l.size = 32) (hr : r.size = 32) :
    hDom 166 0 0 cfg (l ++ r) = true := by
  simp only [hDom, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
    ByteArray.size_append, hl, hr]
  exact ⟨⟨⟨⟨⟨⟨⟨by decide, by decide⟩, Or.inr trivial⟩, by decide⟩, by decide⟩, hc⟩,
      Or.inl (by decide)⟩,
    _root_.Fmt.leafOK_other _ _ _ rfl⟩

section
variable (h h' : HId) (ha : ∀ n t i s b, hDom n t i s b = true → h' n t i s b = h n t i s b)
  (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = dlen n)

include ha hz in
theorem leavesW_dom (sh : _root_.Fmt.Shape) (start : ByteArray) (ht : sh.tree < 2 ^ 16)
    (h0 : (!sh.stored || sh.tree == 0) = true) (hs : start.size = 32) :
    ∀ (xs : List Nat) (cs : List (List UInt64 × ByteArray)), (∀ x ∈ xs, 2 ^ sh.a + x < 2 ^ 63) →
      (∀ c ∈ cs, 1 ≤ c.1.length ∧ c.1.length < 2 ^ 24 ∧ _root_.Fmt.saltLenOK c.2.size = true) →
      _root_.Fmt.leavesW (m := Id) h' sh start xs cs =
        _root_.Fmt.leavesW (m := Id) h sh start xs cs ∧
      ∀ v ∈ Id.run (_root_.Fmt.leavesW (m := Id) h sh start xs cs), v.2.size = 32
  | [], _, _, _ => ⟨rfl, fun v hv => absurd hv (List.not_mem_nil)⟩
  | _ :: _, [], _, _ => ⟨rfl, fun v hv => absurd hv (List.not_mem_nil)⟩
  | x :: xs, (col, salt) :: cs, hx, hc => by
    obtain ⟨e1, e2⟩ := leavesW_dom sh start ht h0 hs xs cs
      (fun y hy => hx y (List.mem_cons_of_mem _ hy))
      (fun c hc' => hc c (List.mem_cons_of_mem _ hc'))
    simp only [_root_.Fmt.leavesW, _root_.Fmt.leafW, idb, idp, e1]
    rw [ha _ _ _ _ _
        (domLeaf sh.stored sh.tree _ start col salt ht (hx x (List.mem_cons_self ..)) hs
          (hc (col, salt) (List.mem_cons_self ..)).1 (hc (col, salt) (List.mem_cons_self ..)).2.1
          (hc (col, salt) (List.mem_cons_self ..)).2.2 h0)]
    refine ⟨rfl, fun v hv => ?_⟩
    rcases List.mem_cons.1 hv with rfl | hv
    · show ByteArray.size (h _ _ _ _ _) = 32
      rw [hz]
      cases sh.stored <;> rfl
    · exact e2 v hv

/-- What the reader without a hash (`Fmt.rdOpening`) hands out: columns of W words, salts of the
given length, digests of 32 bytes. -/
theorem rdOpening_parts (f : _root_.Fmt.Fld) (sb : Nat) (sh : _root_.Fmt.Shape) (xs : List Nat)
    (b : ByteArray) (i : Nat) (cs : List (List UInt64 × ByteArray)) (given : List ByteArray)
    (next : Nat) (ep : _root_.Fmt.rdOpening f sb sh xs b i = some ((cs, given), next)) :
    (∀ c ∈ cs, c.1.length = sh.W ∧ c.2.size = sb) ∧ ∀ d ∈ given, d.size = 32 := by
  unfold _root_.Fmt.rdOpening _root_.Fmt.rdPair at ep
  split at ep
  · rename_i cs' j e1
    split at ep
    · rename_i g' k e2
      simp only [Option.some.injEq, Prod.mk.injEq] at ep
      obtain ⟨⟨rfl, rfl⟩, -⟩ := ep
      refine ⟨TieTree.rdMany_all _ (fun c => c.1.length = sh.W ∧ c.2.size = sb) ?_ _ _ _ _ _ e1,
        TieTree.rdMany_all _ (fun d => d.size = 32)
          (fun b i x j hx => TieTree.rdBytes_size 32 b i x j hx) _ _ _ _ _ e2⟩
      intro b' i' x j' hx
      unfold _root_.Fmt.rdPair at hx
      split at hx
      · rename_i col j1 e3
        split at hx
        · rename_i st j2 e4
          simp only [Option.some.injEq, Prod.mk.injEq] at hx
          rw [← hx.1]
          exact ⟨WalkTie.rdMany_length _ _ _ _ _ _ e3, TieTree.rdBytes_size _ _ _ _ _ e4⟩
        · cases hx
      · cases hx
    · cases ep
  · cases ep

include ha hz in
/-- An opening, read and hashed, at two hashes that agree on the domain. (not all hypotheses are
named here: see the statement below) -/
theorem readOpeningW_dom (cfg : ByteArray) (f : _root_.Fmt.Fld) (sb : Nat) (sh : _root_.Fmt.Shape)
    (start : ByteArray) (xs : List Nat) (b : ByteArray) (i : Nat) (hc : cfg.size = 32)
    (hs : start.size = 32) (hsh : smallSh sb sh = true) :
    _root_.Fmt.readOpeningW (m := Id) h' cfg f sb sh start xs b i =
      _root_.Fmt.readOpeningW (m := Id) h cfg f sb sh start xs b i := by
  simp only [smallSh, Bool.and_eq_true, decide_eq_true_eq] at hsh
  obtain ⟨hsh, h0⟩ := hsh
  unfold _root_.Fmt.readOpeningW
  split
  · rename_i hok
    have hl : _root_.Fmt.listOK sh.a xs = true := (Bool.and_eq_true _ _ ▸ hok : _ ∧ _).1
    have hsl : _root_.Fmt.saltLenOK sb = true := (Bool.and_eq_true _ _ ▸ hok : _ ∧ _).2
    obtain ⟨-, -, hb⟩ := WalkTie.listOK_spec sh.a xs hl
    cases ep : _root_.Fmt.rdOpening f sb sh xs b i with
    | none => rfl
    | some r =>
      obtain ⟨⟨cs, given⟩, next⟩ := r
      obtain ⟨p1, p2⟩ := rdOpening_parts f sb sh xs b i cs given next ep
      have h2 : (2 : Nat) ^ sh.a ≤ 2 ^ 48 := Nat.pow_le_pow_right (by decide) hsh.1.1.2
      obtain ⟨e1, e2⟩ := leavesW_dom
        h h' ha hz sh start hsh.1.1.1 h0 hs xs cs (fun x hx => by have := hb x hx; omega)
        (fun c hc' => by have q := p1 c hc'; rw [q.1, q.2]; exact ⟨hsh.1.2, hsh.2, hsl⟩)
      simp only [idb, idp, e1]
      exact congrArg _
        (walk_dom (fun v : ByteArray => v.size = 32)
          (fun _ _ l r => _root_.Fmt.vertexW (m := Id) h' cfg l r)
          (fun _ _ l r => _root_.Fmt.vertexW (m := Id) h cfg l r)
          (fun _ _ x y hx hy => ha _ _ _ _ _ (domVertex cfg x y hc hx hy))
          (fun _ _ x y _ _ => hz _ _ _ _ _) sh.a _ (given, []) [] e2 p2)
  · rfl


/-! ### The lenient fold with two readers of openings that agree at the arguments that the
statements name -/

include ha in
theorem cutStep_dom2 (ops' ops : OpsW Id) (P : _root_.Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) (s : _root_.Fmt.St) (r : _root_.Fmt.Round) (hi : s.chain.round + 1 < 2 ^ 63)
    (hb : b.size + 16 ≤ 2 ^ 32 - 144)
    (he : ∀ roots poss i, ops' run roots poss r.opens i = ops run roots poss r.opens i) :
    cutStep (m := Id) h' ops' P run b s r = cutStep (m := Id) h ops P run b s r := by
  unfold cutStep
  cases hs : _root_.Fmt.slice b s.pos r.entry.msg with
  | none => rfl
  | some msg =>
    dsimp only
    cases _root_.Fmt.whole (_root_.Fmt.readItems P.field r.items) msg with
    | none => rfl
    | some vals =>
      dsimp only
      cases _root_.Fmt.readNonce P r.entry.work b (s.pos + r.entry.msg) with
      | none => rfl
      | some ni =>
        dsimp only
        rw [laxQueryW_dom h h' ha s.chain msg r.kind r.entry.work ni.1 _ hi
            (by have := slice_size b _ _ msg hs; omega)]
        simp only [he]

include ha in
theorem cutFold_dom2 (ops' ops : OpsW Id) (P : _root_.Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) (hb : b.size + 16 ≤ 2 ^ 32 - 144) :
    ∀ (rs : List _root_.Fmt.Round) (s : _root_.Fmt.St), s.chain.round + rs.length < 2 ^ 63 →
      (∀ r ∈ rs, ∀ roots poss i, ops' run roots poss r.opens i = ops run roots poss r.opens i) →
      cutFold (m := Id) h' ops' P run b rs s = cutFold (m := Id) h ops P run b rs s
  | [], _, _, _ => rfl
  | r :: rs, s, hi, he => by
    have hi' : s.chain.round + 1 < 2 ^ 63 := by simp only [List.length_cons] at hi; omega
    simp only [cutFold, idb]
    rw [cutStep_dom2 h h' ha ops' ops P run b s r hi' hb (he r (List.mem_cons_self ..))]
    cases hc : cutStep (m := Id) h ops P run b s r with
    | none => rfl
    | some s' =>
      dsimp only
      exact cutFold_dom2 ops' ops P run b hb rs s'
        (by rw [cutStep_round h ops P run b s s' r hc]; simp only [List.length_cons] at hi; omega)
        (fun r' hr' => he r' (List.mem_cons_of_mem _ hr'))

include hz in
/-- If the answers of h have their length (hz) and `Fmt.startChainW` hands out a chain's head at h
(e), then that head's run's value, if it has one, has 32 bytes. -/
theorem startChainW_run (lab : Nat) (pd statement : ByteArray) (rnd : Option ByteArray)
    (hd : _root_.Fmt.ChainHead)
    (e : _root_.Fmt.startChainW (m := Id) h lab pd statement rnd = some hd) :
    ∀ x, hd.run = some x → x.size = 32 := by
  unfold _root_.Fmt.startChainW at e
  split at e
  · cases rnd with
    | none =>
      simp only [idb, idp] at e
      cases e
      intro x hx
      cases hx
    | some b =>
      dsimp only at e
      split at e
      · simp only [_root_.Fmt.runValueW, idb] at e
        split at e
        · simp only [idp] at e
          cases e
          intro x hx
          cases hx
          exact hz _ _ _ _ _
        · cases e
      · cases e
  · cases e

include ha hz in
theorem cutChain_dom2 (ops' ops : ByteArray → OpsW Id) (S : _root_.Fmt.Spec) (b : ByteArray)
    (i : Nat) (hS : smallB S b = true)
    (he : ∀ run : Option ByteArray, (∀ x, run = some x → x.size = 32) →
      ∀ r ∈ S.rounds,
        ∀ roots poss j, ops' b run roots poss r.opens j = ops b run roots poss r.opens j) :
    cutChain (m := Id) h' ops' S b i = cutChain (m := Id) h ops S b i := by
  simp only [smallB, Bool.and_eq_true, decide_eq_true_eq] at hS
  unfold cutChain
  split
  · rfl
  · dsimp only
    split
    · rfl
    · simp only [_root_.Fmt.paramsDigestW, idb]
      rw [ha _ _ _ _ _ (dom0 169 1 S.params (by decide) (by decide) (by decide) hS.1.1.1),
        startChainW_dom h h' ha hz S.label _ S.statement _ (hz _ _ _ _ _) hS.1.1.2]
      cases hh : _root_.Fmt.startChainW
          (m := Id) h S.label (h 169 0 1 _root_.Fmt.zero32 S.params) S.statement _ with
      | none => rfl
      | some hd =>
        dsimp only
        rw [cutFold_dom2 h h' ha (ops' b) (ops b) S.plan hd.run b hS.1.2 S.rounds _
            (by simpa using hS.2) (he hd.run (startChainW_run h hz _ _ _ _ hd hh))]

include ha hz in
theorem cutWhole_dom2 (ops' ops : ByteArray → OpsW Id) (S : _root_.Fmt.Spec)
    (b : ByteArray) (hS : smallB S b = true)
    (he : ∀ run : Option ByteArray, (∀ x, run = some x → x.size = 32) →
      ∀ r ∈ S.rounds,
        ∀ roots poss j, ops' b run roots poss r.opens j = ops b run roots poss r.opens j) :
    cutWhole (m := Id) h' ops' S b = cutWhole (m := Id) h ops S b := by
  unfold cutWhole
  rw [cutChain_dom2 h h' ha hz ops' ops S b 0 hS he]

end

theorem open_dom : Spec.open_dom := fun h h' ha hz cfg f sb sh start xs b i hc hs hsh =>
  readOpeningW_dom h h' ha hz cfg f sb sh start xs b i hc hs hsh

theorem fold_dom : Spec.fold_dom := fun h h' ha hz ops' ops S b hS he =>
  cutWhole_dom2 h h' ha hz ops' ops S b hS he

end Run
