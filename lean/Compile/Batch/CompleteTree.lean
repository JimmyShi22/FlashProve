-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteTree.lean: the Merkle trees of the honest compiled prover pass the verifier's
checks.

The trees of the compiled prover (Compile/Batch/TokTree.lean) against the checks of the compiled
verifier (Compile/Batch/Verifier.lean), for fixed oracle functions, each under the hypotheses of its
statement. The statements on the prover's programs are postconditions (`Tri`, Compile/EraseKit.lean)
of programs with tokens, relative to the store of the tokens' strings; those on the verifier's
checks say what these return (`EvalsTo`, Compile/MerkleRom.lean) (words of this library:
lean/GLOSSARY.md).

  Part 1  digests as tokens (`IsDig`, `dv`); `pairUp`, `levelsM` over such tokens
  Part 2  `commitT`, `openT` against `runCheck`
  Part 3  `reqT` against `reqCheck`
  Part 4  `commitE`, `openE` against `runCheck`

Notation: `lam`, `K`: natural numbers; a `Dig lam` (Iop/Wire.lean): a hash block (a digest or a
chaining value): lam bits; `L`: an `BatchProtocol I X` (Iop/Batch.lean): the five algorithms (I, D, Test,
Link, Batch), with the honest sides; `sMT`: a natural number: the length of the salt of a leaf
(Compile/Batch/Verifier.lean); `leafE sMT b blind`: Compile/Batch/TokTree.lean; the handle of a
leaf: an `Option (Tok × Tok)`; `saltVal`: the string of its first token, or the empty string for a
leaf without salt; `reqT depthReq cs` (Compile/Batch/TokTree.lean): the request tree over the slot
values cs.
-/
import Compile.Batch.TokTree
import Compile.EraseKit
import Compile.MerkleRom

noncomputable section

namespace Compile.Batch.Cmpl
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (f : Fam (spec lam K L))

/-! ## Part 1. Digests as tokens -/

theorem digD_ofFn (d : Dig lam) : digD lam (List.ofFn d) = d := by
  funext i
  simp [digD, List.getD_eq_getElem?_getD]

/-- the digest for which a token stands -/
def dv (lam : ℕ) (vs : List Bits) (t : Tok) : Dig lam := digD lam (vs.getD t [])

/-- the token points into the store, and its string is a digest -/
def IsDig (lam : ℕ) (vs : List Bits) (t : Tok) : Prop :=
  t < vs.length ∧ vs.getD t [] = List.ofFn (dv lam vs t)

theorem IsDig.mono {vs vs' : List Bits} (h : vs <+: vs') {t : Tok} (ht : IsDig lam vs t) :
    IsDig lam vs' t := by
  have e := getD_of_prefix h ht.1
  refine ⟨lt_of_lt_of_le ht.1 h.length_le, ?_⟩
  unfold dv
  rw [e]
  exact ht.2

theorem dv_of_prefix {vs vs' : List Bits} (h : vs <+: vs') {t : Tok} (ht : t < vs.length) :
    dv lam vs' t = dv lam vs t := by
  unfold dv
  rw [getD_of_prefix h ht]

theorem isDig_concat (vs : List Bits) (d : Dig lam) :
    IsDig lam (vs ++ [List.ofFn d]) vs.length ∧ dv lam (vs ++ [List.ofFn d]) vs.length = d := by
  have e : dv lam (vs ++ [List.ofFn d]) vs.length = d := by
    unfold dv
    rw [getD_concat_length, digD_ofFn]
  exact ⟨⟨by simp, by rw [e, getD_concat_length]⟩, e⟩

theorem map_dv_of_prefix {vs vs' : List Bits} (h : vs <+: vs')
    {l : List Tok} (hl : ∀ t ∈ l, IsDig lam vs t) :
    l.map (dv lam vs') = l.map (dv lam vs) :=
  List.map_congr_left fun t ht => dv_of_prefix h (hl t ht).1

section Lists
variable {f} {nd : Tok → Tok → St lam K L Tok} {hN : Dig lam → Dig lam → Dig lam}
  (hnd : ∀ a b vs, IsDig lam vs a → IsDig lam vs b →
    Tri f (nd a b) vs fun d vs' => IsDig lam vs' d ∧ dv lam vs' d = hN (dv lam vs a) (dv lam vs b))
include hnd

/-- one level up, over tokens of digests (under `hnd`): the digests are those of `pairUpF` -/
theorem tri_pairUpT :
    ∀ (n : ℕ) (l : List Tok), l.length ≤ n →
      ∀ vs : List Bits, (∀ t ∈ l, IsDig lam vs t) →
        Tri f (pairUp nd l) vs fun o vs' =>
          (∀ t ∈ o, IsDig lam vs' t) ∧ o.map (dv lam vs') = pairUpF hN (l.map (dv lam vs))
  | _, [], _, _, _ => tri_pure_iff.2 ⟨fun _ h => (by cases h), rfl⟩
  | _, [a], _, _, h => tri_pure_iff.2 ⟨h, rfl⟩
  | 0, _ :: _ :: _, hn, _, _ => by simp at hn
  | n + 1, a :: b :: t, hn, vs, h => by
      refine Tri.bind (hnd a b vs (h a (by simp)) (h b (by simp))).with_prefix fun c vs1 hc => ?_
      refine Tri.bind
        (tri_pairUpT n t (by simp at hn; omega) vs1 fun u hu =>
          (h u (by simp [hu])).mono hc.2).with_prefix
        fun r vs2 hr => tri_pure_iff.2 ⟨?_, ?_⟩
      · intro u hu
        rcases List.mem_cons.1 hu with rfl | hu
        · exact hc.1.1.mono hr.2
        · exact hr.1.1 u hu
      · rw [List.map_cons, hr.1.2, dv_of_prefix hr.2 hc.1.1.1, hc.1.2, List.map_cons, List.map_cons,
          pairUpF_cons₂, map_dv_of_prefix hc.2 fun u hu => h u (by simp [hu])]

/-- all levels, over tokens -/
theorem tri_levelsT : ∀ (d : ℕ) (l : List Tok) (vs : List Bits), (∀ t ∈ l, IsDig lam vs t) →
    Tri f (levelsM nd d l) vs fun lv vs' =>
      (∀ lvl ∈ lv, ∀ t ∈ lvl, IsDig lam vs' t) ∧
      lv.map (List.map (dv lam vs')) = levelsF hN d (l.map (dv lam vs))
  | 0, l, vs, h =>
    tri_pure_iff.2 ⟨fun lvl hl t ht => by rw [List.mem_singleton.1 hl] at ht; exact h t ht, rfl⟩
  | d + 1, l, vs, h => by
      refine Tri.bind (tri_pairUpT hnd l.length l le_rfl vs h).with_prefix fun u vs1 hu => ?_
      refine Tri.bind (tri_levelsT d u vs1 hu.1.1).with_prefix fun r vs2 hr =>
        tri_pure_iff.2 ⟨?_, ?_⟩
      · intro lvl hl t ht
        rcases List.mem_cons.1 hl with rfl | hl
        · exact (h t ht).mono (hu.2.trans hr.2)
        · exact hr.1.1 lvl hl t ht
      · rw [List.map_cons, hr.1.2, hu.1.2, levelsF_succ, map_dv_of_prefix (hu.2.trans hr.2) h]

end Lists

/-! ### Reading a path and the root off levels of tokens -/

section Read
variable {A B : Type} [Inhabited A] [Inhabited B] (g : A → B) (hN : B → B → B)

theorem getD_map_of_lt {l : List A} {n : ℕ} (h : n < l.length) :
    (l.map g).getD n default = g (l.getD n default) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- Under the hypotheses below: the path that is read off levels of tokens stands for the path that
is read off the levels of digests. -/
theorem pathOf_map :
    ∀ (d : ℕ) (lv : List (List A)) (l : List B) (j : ℕ), l.length = 2 ^ d → j < 2 ^ d →
      lv.map (List.map g) = levelsF hN d l → (pathOf lv j).map g = pathOf (levelsF hN d l) j
  | 0, lv, l, j, _, _, h => by
      rw [levelsF_zero] at h ⊢
      match lv, h with
      | [_], _ => rfl
  | d + 1, lv, l, j, hl, hj, h => by
      obtain ⟨ls, hls⟩ := exists_levelsF_eq_cons hN d (pairUpF hN l)
      rw [levelsF_succ, hls] at h ⊢
      match lv, h with
      | l0 :: l1 :: rest, h =>
        simp only [List.map_cons, List.cons.injEq] at h
        obtain ⟨h0, h1, h2⟩ := h
        have hl2 : l.length = 2 * 2 ^ d := by rw [hl, pow_succ, Nat.mul_comm]
        have hj2 : j / 2 < 2 ^ d :=
          Nat.div_lt_of_lt_mul (by rw [pow_succ, Nat.mul_comm] at hj; exact hj)
        have ih := pathOf_map d (l1 :: rest) (pairUpF hN l) (j / 2) (length_pairUpF hN _ l hl2) hj2
          (by rw [hls, List.map_cons, h1, h2])
        rw [hls] at ih
        rw [pathOf_cons₂, pathOf_cons₂, List.map_cons, ih, ← h0]
        congr 1
        refine (getD_map_of_lt g ?_).symm
        have hlen : l0.length = 2 * 2 ^ d := by rw [← hl2, ← h0, List.length_map]
        rw [pow_succ] at hj
        split <;> omega

theorem rootOf_map : ∀ (d : ℕ) (lv : List (List A)) (l : List B), l.length = 2 ^ d →
    lv.map (List.map g) = levelsF hN d l → g (rootOf lv) = rootOf (levelsF hN d l)
  | 0, lv, l, hl, h => by
      rw [levelsF_zero] at h ⊢
      match lv, h with
      | [l0], h =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
        subst h
        match l0, hl with
        | [a], _ => rfl
        | [], hl => simp at hl
        | _ :: _ :: _, hl => simp at hl
  | d + 1, lv, l, hl, h => by
      obtain ⟨ls, hls⟩ := exists_levelsF_eq_cons hN d (pairUpF hN l)
      rw [levelsF_succ, hls] at h ⊢
      match lv, h with
      | l0 :: l1 :: rest, h =>
        simp only [List.map_cons, List.cons.injEq] at h
        obtain ⟨-, h1, h2⟩ := h
        have hl2 : l.length = 2 * 2 ^ d := by rw [hl, pow_succ, Nat.mul_comm]
        have ih := rootOf_map d (l1 :: rest) (pairUpF hN l)
          (length_pairUpF hN _ l hl2) (by rw [hls, List.map_cons, h1, h2])
        rw [hls] at ih
        rw [rootOf_cons₂, rootOf_cons₂, ih]

omit [Inhabited B] in
/-- Under the hypotheses below: the root that is read off the levels is an entry of a level. -/
theorem rootOf_mem : ∀ (d : ℕ) (lv : List (List A)) (l : List B), l.length = 2 ^ d →
    lv.map (List.map g) = levelsF hN d l → ∃ lvl ∈ lv, rootOf lv ∈ lvl
  | 0, lv, l, hl, h => by
      rw [levelsF_zero] at h
      match lv, h with
      | [l0], h =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
        subst h
        match l0, hl with
        | [a], _ => exact ⟨[a], List.mem_singleton.2 rfl, List.mem_singleton.2 rfl⟩
        | [], hl => simp at hl
        | _ :: _ :: _, hl => simp at hl
  | d + 1, lv, l, hl, h => by
      obtain ⟨ls, hls⟩ := exists_levelsF_eq_cons hN d (pairUpF hN l)
      rw [levelsF_succ, hls] at h
      match lv, h with
      | l0 :: l1 :: rest, h =>
        simp only [List.map_cons, List.cons.injEq] at h
        obtain ⟨-, h1, h2⟩ := h
        have hl2 : l.length = 2 * 2 ^ d := by rw [hl, pow_succ, Nat.mul_comm]
        obtain ⟨lvl, hm, hr⟩ := rootOf_mem d (l1 :: rest) (pairUpF hN l)
          (length_pairUpF hN _ l hl2) (by rw [hls, List.map_cons, h1, h2])
        exact ⟨lvl, List.mem_cons_of_mem _ hm, by rw [rootOf_cons₂]; exact hr⟩

end Read

/-! ## Part 2. Token trees over prover messages -/

/-- the two Merkle functions for trees over oracles, for the fixed oracle functions -/
def leafFB (y : LeafIn L) : Dig lam := f OracleName.leaf y
@[inherit_doc leafFB] def nodeFB (a b : Dig lam) : Dig lam := f OracleName.node (List.ofFn a, List.ofFn b)

theorem tri_leafT (sMT : ℕ) (b : Body L) (vs : List Bits) :
    Tri f (leafT (lam := lam) (K := K) sMT b) vs fun o vs' =>
      (o.1 < vs'.length ∧ (vs'.getD o.1 []).length = sMT) ∧
      IsDig lam vs' o.2 ∧
      dv lam vs' o.2 = leafFB f ⟨b, vs'.getD o.1 []⟩ := by
  unfold leafT
  refine tri_fresh_iff.2 fun r => tri_marked_iff.2 (tri_pure_iff.2 ?_)
  set vs1 := vs ++ [List.ofFn fun i : Fin sMT => r.val.testBit i] with hvs1
  have hd := isDig_concat vs1 (f OracleName.leaf (⟨b, vs1.getD vs.length []⟩ : LeafIn L))
  have hg : ∀ x : Bits, (vs1 ++ [x]).getD vs.length [] = vs1.getD vs.length [] := fun x =>
    getD_of_prefix (List.prefix_append _ _) (by simp [hvs1])
  refine ⟨⟨by simp [hvs1], ?_⟩, hd.1, ?_⟩
  · show ((vs1 ++ [_]).getD vs.length []).length = sMT
    rw [hg, hvs1, getD_concat_length, List.length_ofFn]
  · show dv lam (vs1 ++ [_]) vs1.length = leafFB f ⟨b, (vs1 ++ [_]).getD vs.length []⟩
    rw [hg]
    exact hd.2

theorem tri_nodeT (a b : Tok) (vs : List Bits) (ha : IsDig lam vs a) (hb : IsDig lam vs b) :
    Tri f (nodeT (lam := lam) (K := K) (L := L) a b) vs fun d vs' =>
      IsDig lam vs' d ∧ dv lam vs' d = nodeFB f (dv lam vs a) (dv lam vs b) := by
  unfold nodeT
  refine tri_marked_iff.2 (tri_pure_iff.2 ?_)
  have hd := isDig_concat vs (f OracleName.node ((vs.getD a [], vs.getD b []) : Bits × Bits))
  refine ⟨hd.1, hd.2.trans ?_⟩
  unfold nodeFB
  rw [← ha.2, ← hb.2]

theorem tri_leavesT (sMT : ℕ) : ∀ (l : List (Body L)) (vs : List Bits),
    Tri f (leavesT (lam := lam) (K := K) sMT l) vs fun o vs' =>
      o.2.length = l.length ∧
      (∀ s ∈ o.2, s < vs'.length ∧ (vs'.getD s []).length = sMT) ∧
      (∀ t ∈ o.1, IsDig lam vs' t) ∧
      o.1.map (dv lam vs') = List.zipWith (fun b s => leafFB f ⟨b, vs'.getD s []⟩) l o.2
  | [], _ => tri_pure_iff.2 ⟨rfl, fun _ h => (by cases h), fun _ h => (by cases h), rfl⟩
  | b :: t, vs => by
      refine Tri.bind (tri_leafT f sMT b vs) fun x vs1 hx => ?_
      refine Tri.bind (tri_leavesT sMT t vs1).with_prefix fun r vs2 hr => tri_pure_iff.2 ?_
      obtain ⟨⟨h1, h2, h3, h4⟩, hp⟩ := hr
      have hs : vs2.getD x.1 [] = vs1.getD x.1 [] := getD_of_prefix hp hx.1.1
      refine ⟨by simp [h1], ?_, ?_, ?_⟩
      · intro s hs'
        rcases List.mem_cons.1 hs' with rfl | hs'
        · exact ⟨lt_of_lt_of_le hx.1.1 hp.length_le, by rw [hs]; exact hx.1.2⟩
        · exact h2 s hs'
      · intro u hu
        rcases List.mem_cons.1 hu with rfl | hu
        · exact hx.2.1.mono hp
        · exact h3 u hu
      · rw [List.map_cons, List.zipWith_cons_cons, h4, dv_of_prefix hp hx.2.1.1, hx.2.2, hs]

/-- What the prover keeps of a token tree is correct, relative to a store: a salt of sMT bits for
each of the 2^d leaves; all tokens of the levels stand for digests; these are the levels over the
digests of the leaves, each hashed with its salt. -/
def TTreeOK (sMT : ℕ) (vs : List Bits) (t : TTree) (d : ℕ) (leaf : ℕ → Body L) : Prop :=
  t.salts.length = 2 ^ d ∧ (∀ s ∈ t.salts, s < vs.length ∧ (vs.getD s []).length = sMT) ∧
    (∀ lvl ∈ t.levels, ∀ u ∈ lvl, IsDig lam vs u) ∧
    t.levels.map (List.map (dv lam vs)) = levelsF (nodeFB f) d
      ((List.range (2 ^ d)).map fun j => leafFB f ⟨leaf j, vs.getD (t.salts.getD j 0) []⟩)

theorem getD_mem_of_lt {l : List Tok} {j : ℕ} (h : j < l.length) : l.getD j 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

variable {f}

theorem TTreeOK.mono {sMT : ℕ} {vs vs' : List Bits} (hp : vs <+: vs') {t : TTree} {d : ℕ}
    {leaf : ℕ → Body L} (h : TTreeOK f sMT vs t d leaf) : TTreeOK f sMT vs' t d leaf := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1,
    fun s hs =>
      ⟨lt_of_lt_of_le (h2 s hs).1 hp.length_le,
        by rw [getD_of_prefix hp (h2 s hs).1]; exact (h2 s hs).2⟩,
    fun lvl hl u hu => (h3 lvl hl u hu).mono hp,
    ?_⟩
  have e1 : t.levels.map (List.map (dv lam vs')) = t.levels.map (List.map (dv lam vs)) :=
    List.map_congr_left fun lvl hl => map_dv_of_prefix hp (h3 lvl hl)
  rw [e1, h4]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  rw [getD_of_prefix hp (h2 _ (getD_mem_of_lt (by rw [h1]; exact List.mem_range.1 hj))).1]

theorem TTreeOK.isDig_root {sMT : ℕ} {vs : List Bits} {t : TTree} {d : ℕ}
    {leaf : ℕ → Body L} (h : TTreeOK f sMT vs t d leaf) :
    IsDig lam vs t.root := by
  obtain ⟨lvl, hm, hr⟩ := rootOf_mem (dv lam vs) (nodeFB f) d t.levels _ (by simp) h.2.2.2
  exact h.2.2.1 lvl hm _ hr

variable (f)

theorem zipWith_range {A B C : Type} (g : A → B → C) (n : ℕ) (leaf : ℕ → A) (l : List B)
    (d : B) (hl : l.length = n) :
    List.zipWith g ((List.range n).map leaf) l =
      (List.range n).map fun j => g (leaf j) (l.getD j d) := by
  refine List.ext_getElem (by simp [hl]) fun j h1 h2 => ?_
  have hj : j < l.length := by simpa [hl] using h1
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem tri_commitT (sMT d : ℕ) (leaf : ℕ → Body L) (vs : List Bits) :
    Tri f (commitT (lam := lam) (K := K) sMT d leaf) vs fun t vs' =>
      TTreeOK f sMT vs' t d leaf := by
  refine Tri.bind (tri_leavesT f sMT _ vs) fun x vs1 hx => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hx
  refine Tri.bind (tri_levelsT (tri_nodeT f) d x.1 vs1 h3).with_prefix fun lv vs2 hlv =>
    tri_pure_iff.2 ?_
  obtain ⟨⟨h5, h6⟩, hp⟩ := hlv
  have hl : x.2.length = 2 ^ d := by simpa using h1
  refine ⟨hl,
    fun s hs =>
      ⟨lt_of_lt_of_le (h2 s hs).1 hp.length_le,
        by rw [getD_of_prefix hp (h2 s hs).1]; exact (h2 s hs).2⟩,
    h5, ?_⟩
  show lv.map (List.map (dv lam vs2)) = _
  rw [h6, h4, zipWith_range _ _ leaf x.2 0 hl]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  rw [getD_of_prefix hp (h2 _ (getD_mem_of_lt (by rw [hl]; exact List.mem_range.1 hj))).1]

theorem tri_openT {σ : Type} (t : TTree) (j : ℕ) (a : σ) (vs : List Bits) :
    Tri f (openT (lam := lam) (K := K) (L := L) t j a) vs fun o vs' =>
      o = ⟨a, vs.getD (t.salts.getD j 0) [], (pathOf t.levels j).map (dv lam vs)⟩ ∧ vs' = vs := by
  unfold openT
  refine tri_reveal_iff.2 (tri_pure_iff.2 ⟨?_, rfl⟩)
  simp only [List.map_cons, List.headD_cons, List.tail_cons, List.map_append]
  congr 1
  rw [List.take_left' (by simp), List.map_map]
  rfl

theorem tri_showT (t : Tok) (vs : List Bits) :
    Tri f (showT (lam := lam) (K := K) (L := L) t) vs fun o vs' => o = dv lam vs t ∧ vs' = vs :=
  tri_reveal_iff.2 (tri_pure_iff.2 ⟨rfl, rfl⟩)

/-- Honest openings pass: over 2^d leaf digests, of which number j is the digest of x, the check for
leaf j with the path and the root read off the levels is well formed and accepts. -/
theorem runCheck_honest (d : ℕ) (digs : List (Dig lam)) (hl : digs.length = 2 ^ d) (j : ℕ)
    (hj : j < 2 ^ d) (x : LeafIn L) (hx : leafFB f x = digs.getD j default) :
    Check.wellFormed
        (⟨x, j, pathOf (levelsF (nodeFB f) d digs) j,
          rootOf (levelsF (nodeFB f) d digs), d⟩ : Check lam L) = true ∧
    EvalsTo f (runCheck (K := K)
        (⟨x, j, pathOf (levelsF (nodeFB f) d digs) j,
          rootOf (levelsF (nodeFB f) d digs), d⟩ : Check lam L)) true := by
  refine ⟨by simp [Check.wellFormed, length_pathOf_levelsF, hj], ?_⟩
  have h2 : climbF (nodeFB f) (pathOf (levelsF (nodeFB f) d digs) j) j (f OracleName.leaf x) =
      rootOf (levelsF (nodeFB f) d digs) := by
    have h3 : f OracleName.leaf x = digs.getD j default := hx
    rw [h3]
    exact climbF_pathOf (nodeFB f) d digs j hl hj
  show EvalsTo f ((askTypedOracle (L := L) (K := K) OracleName.leaf x) >>= fun dd =>
    (climbM (hashTreeNode (L := L) (K := K)) (pathOf (levelsF (nodeFB f) d digs) j) j dd) >>= fun r =>
      pure (decide (r = rootOf (levelsF (nodeFB f) d digs)))) true
  refine (evaluates_eager f).bind (evalsTo_ask f OracleName.leaf x) ((evaluates_eager f).bind
            ((evaluates_eager f).climbM (qN := hashTreeNode (L := L) (K := K)) (hN := nodeFB f)
              (fun a b => evalsTo_ask f OracleName.node (List.ofFn a, List.ofFn b)) _ j _) ?_)
  rw [h2, decide_eq_true rfl]
  exact (evaluates_eager f).pure true

/-- Under `TTreeOK`, for j < 2^d: the check of an honest opening in a token tree accepts. -/
theorem check_of_ttreeOK {sMT : ℕ} {vs : List Bits} {t : TTree} {d : ℕ} {leaf : ℕ → Body L}
    (h : TTreeOK f sMT vs t d leaf) {j : ℕ} (hj : j < 2 ^ d) :
    Check.wellFormed
        (⟨⟨leaf j, vs.getD (t.salts.getD j 0) []⟩, j, (pathOf t.levels j).map (dv lam vs),
          dv lam vs t.root, d⟩ : Check lam L) = true ∧
    EvalsTo f (runCheck (K := K)
        (⟨⟨leaf j, vs.getD (t.salts.getD j 0) []⟩, j, (pathOf t.levels j).map (dv lam vs),
          dv lam vs t.root, d⟩ : Check lam L)) true := by
  obtain ⟨-, -, -, h4⟩ := h
  have hlen : ((List.range (2 ^ d)).map fun j =>
        leafFB f ⟨leaf j, vs.getD (t.salts.getD j 0) []⟩).length = 2 ^ d := by simp
  rw [pathOf_map (dv lam vs) (nodeFB f) d t.levels _ j hlen hj h4]
  have hr : dv lam vs t.root = _ := rootOf_map (dv lam vs) (nodeFB f) d t.levels _ hlen h4
  rw [hr]
  exact runCheck_honest f d _ hlen j hj _ (by simp [List.getD_eq_getElem?_getD, hj])

/-! ## Part 3. Request trees -/

/-- the two Merkle functions for request trees -/
def rleafFB (c : Dig lam) : Dig lam := f OracleName.rleaf (List.ofFn c)
@[inherit_doc rleafFB] def rnodeFB (a b : Dig lam) : Dig lam :=
  f OracleName.rnode (List.ofFn a, List.ofFn b)

theorem tri_rleafT (c : Tok) (vs : List Bits) (hc : IsDig lam vs c) :
    Tri f (rleafT (lam := lam) (K := K) (L := L) c) vs fun d vs' =>
      IsDig lam vs' d ∧ dv lam vs' d = rleafFB f (dv lam vs c) := by
  unfold rleafT
  refine tri_marked_iff.2 (tri_pure_iff.2 ?_)
  have hd := isDig_concat vs (f OracleName.rleaf (vs.getD c [] : Bits))
  refine ⟨hd.1, hd.2.trans ?_⟩
  unfold rleafFB
  rw [← hc.2]

theorem tri_rnodeT (a b : Tok) (vs : List Bits) (ha : IsDig lam vs a) (hb : IsDig lam vs b) :
    Tri f (rnodeT (lam := lam) (K := K) (L := L) a b) vs fun d vs' =>
      IsDig lam vs' d ∧ dv lam vs' d = rnodeFB f (dv lam vs a) (dv lam vs b) := by
  unfold rnodeT
  refine tri_marked_iff.2 (tri_pure_iff.2 ?_)
  have hd := isDig_concat vs (f OracleName.rnode ((vs.getD a [], vs.getD b []) : Bits × Bits))
  refine ⟨hd.1, hd.2.trans ?_⟩
  unfold rnodeFB
  rw [← ha.2, ← hb.2]

theorem tri_rleavesT : ∀ (cs : List Tok) (vs : List Bits), (∀ c ∈ cs, IsDig lam vs c) →
    Tri f (rleavesT (lam := lam) (K := K) (L := L) cs) vs fun o vs' =>
      (∀ t ∈ o, IsDig lam vs' t) ∧ o.map (dv lam vs') = cs.map fun c => rleafFB f (dv lam vs c)
  | [], _, _ => tri_pure_iff.2 ⟨fun _ h => (by cases h), rfl⟩
  | c :: t, vs, h => by
      refine Tri.bind (tri_rleafT f c vs (h c (by simp))).with_prefix fun d vs1 hd => ?_
      refine Tri.bind (tri_rleavesT t vs1 fun u hu => (h u (by simp [hu])).mono hd.2).with_prefix
        fun r vs2 hr => tri_pure_iff.2 ⟨?_, ?_⟩
      · intro u hu
        rcases List.mem_cons.1 hu with rfl | hu
        · exact hd.1.1.mono hr.2
        · exact hr.1.1 u hu
      · rw [List.map_cons, List.map_cons, hr.1.2, dv_of_prefix hr.2 hd.1.1.1, hd.1.2]
        congr 1
        exact List.map_congr_left fun u hu => by rw [dv_of_prefix hd.2 (h u (by simp [hu])).1]

/-- The request tree is correct, relative to a store: its tokens stand for the levels over the
digests of the slot values cv. -/
def ReqOK (vs : List Bits) (rq : TTree) (depthReq : ℕ) (cv : List (Dig lam)) : Prop :=
  (∀ lvl ∈ rq.levels, ∀ u ∈ lvl, IsDig lam vs u) ∧
    rq.levels.map (List.map (dv lam vs)) = levelsF (rnodeFB f) depthReq (cv.map (rleafFB f))

variable {f} in
theorem ReqOK.mono {vs vs' : List Bits} (hp : vs <+: vs') {rq : TTree} {depthReq : ℕ}
    {cv : List (Dig lam)} (h : ReqOK f vs rq depthReq cv) : ReqOK f vs' rq depthReq cv :=
  ⟨fun lvl hl u hu => (h.1 lvl hl u hu).mono hp, by
    rw [← h.2]
    exact List.map_congr_left fun lvl hl => map_dv_of_prefix hp (h.1 lvl hl)⟩

variable {f} in
theorem ReqOK.isDig_root {vs : List Bits} {rq : TTree} {depthReq : ℕ} {cv : List (Dig lam)}
    (h : ReqOK f vs rq depthReq cv) (hl : cv.length = 2 ^ depthReq) : IsDig lam vs rq.root := by
  obtain ⟨lvl, hm, hr⟩ :=
    rootOf_mem (dv lam vs) (rnodeFB f) depthReq rq.levels _ (by simpa using hl) h.2
  exact h.1 lvl hm _ hr

theorem tri_reqT (depthReq : ℕ) (cs : List Tok) (vs : List Bits) (h : ∀ c ∈ cs, IsDig lam vs c) :
    Tri f (reqT (lam := lam) (K := K) (L := L) depthReq cs) vs fun rq vs' =>
      ReqOK f vs' rq depthReq (cs.map (dv lam vs)) := by
  refine Tri.bind (tri_rleavesT f cs vs h) fun ls vs1 hls => ?_
  refine Tri.bind (tri_levelsT (tri_rnodeT f) depthReq ls vs1 hls.1) fun lv vs2 hlv =>
    tri_pure_iff.2 ⟨hlv.1, ?_⟩
  show lv.map (List.map (dv lam vs2)) = _
  rw [hlv.2, hls.2, List.map_map]
  rfl

/-- Under the hypotheses below: the check in an honest request tree accepts. -/
theorem reqCheck_honest {vs : List Bits} {rq : TTree} {depthReq : ℕ}
    {cv : List (Dig lam)} (h : ReqOK f vs rq depthReq cv) (hl : cv.length = 2 ^ depthReq)
    {j : ℕ} (hj : j < 2 ^ depthReq) :
    EvalsTo f (reqCheck (L := L) (K := K) depthReq (dv lam vs rq.root) j
        ((pathOf rq.levels j).map (dv lam vs)) (cv.getD j default)) true := by
  have hlen : (cv.map (rleafFB f)).length = 2 ^ depthReq := by simpa using hl
  rw [pathOf_map (dv lam vs) (rnodeFB f) depthReq rq.levels _ j hlen hj h.2]
  have hr : dv lam vs rq.root = _ :=
    rootOf_map (dv lam vs) (rnodeFB f) depthReq rq.levels _ hlen h.2
  rw [hr]
  unfold reqCheck
  rw [if_pos ⟨length_pathOf_levelsF _ _ _ _, hj⟩]
  have h2 : climbF (rnodeFB f) (pathOf (levelsF (rnodeFB f) depthReq (cv.map (rleafFB f))) j) j
        (f OracleName.rleaf (List.ofFn (cv.getD j default))) =
      rootOf (levelsF (rnodeFB f) depthReq (cv.map (rleafFB f))) := by
    have h3 : f OracleName.rleaf (List.ofFn (cv.getD j default)) = (cv.map (rleafFB f)).getD j default :=
      (getD_map_of_lt (rleafFB f) (by rw [hl]; exact hj)).symm
    rw [h3]
    exact climbF_pathOf (rnodeFB f) depthReq _ j hlen hj
  refine (evaluates_eager f).bind (evalsTo_ask f OracleName.rleaf (List.ofFn (cv.getD j default)))
    ((evaluates_eager f).bind
      ((evaluates_eager f).climbM (qN := rnodeV (L := L) (K := K)) (hN := rnodeFB f)
        (fun a b => evalsTo_ask f OracleName.rnode (List.ofFn a, List.ofFn b)) _ j _) ?_)
  rw [h2, decide_eq_true rfl]
  exact (evaluates_eager f).pure true

/-! ## Part 4. Trees over encoded indices -/

/-- the salt for which the handle of a leaf stands: the string of its first token, or the empty
string for a leaf without salt -/
def saltVal (vs : List Bits) : Option (Tok × Tok) → Bits
  | some (s, _) => vs.getD s []
  | none => []

/-- the first token of the handle of a leaf (its salt's) points into the store -/
def tokOK (vs : List Bits) : Option (Tok × Tok) → Prop
  | some (s, _) => s < vs.length
  | none => True

theorem tokOK.mono {vs vs' : List Bits} (h : vs <+: vs') :
    ∀ {tk : Option (Tok × Tok)}, tokOK vs tk → tokOK vs' tk
  | some (_, _), ht => lt_of_lt_of_le ht h.length_le
  | none, _ => trivial

theorem saltVal_of_prefix {vs vs' : List Bits} (h : vs <+: vs') :
    ∀ {tk : Option (Tok × Tok)}, tokOK vs tk → saltVal vs' tk = saltVal vs tk
  | some (_, _), ht => getD_of_prefix h ht
  | none, _ => rfl

theorem tri_leafE (sMT : ℕ) (b : Body L) (blind : Bool) (vs : List Bits) :
    Tri f (leafE (lam := lam) (K := K) sMT b blind) vs fun o vs' =>
      o.1 = leafFB f ⟨b, saltVal vs' o.2⟩ ∧
      tokOK vs' o.2 ∧
      (blind = true → (saltVal vs' o.2).length = sMT) := by
  unfold leafE
  cases blind with
  | true =>
    simp only [if_true]
    refine Tri.bind (tri_leafT f sMT b vs) fun x vs1 hx => ?_
    refine Tri.bind (tri_showT f x.2 vs1) fun d vs2 hd => tri_pure_iff.2 ?_
    obtain ⟨rfl, rfl⟩ := hd
    exact ⟨hx.2.2, hx.1.1, fun _ => hx.1.2⟩
  | false =>
    simp only [Bool.false_eq_true, if_false]
    exact tri_plain_iff.2 (tri_pure_iff.2 ⟨rfl, trivial, fun h => by cases h⟩)

theorem tri_leavesE (sMT : ℕ) : ∀ (l : List (Body L × Bool)) (vs : List Bits),
    Tri f (leavesE (lam := lam) (K := K) sMT l) vs fun o vs' =>
      o.2.length = l.length ∧ (∀ tk ∈ o.2, tokOK vs' tk) ∧
        o.1 = List.zipWith (fun x tk => leafFB f ⟨x.1, saltVal vs' tk⟩) l o.2 ∧
        ∀ j x, l[j]? = some x → x.2 = true → (saltVal vs' (o.2.getD j none)).length = sMT
  | [], _ => tri_pure_iff.2 ⟨rfl, fun _ h => (by cases h), rfl, fun _ _ h => (by simp at h)⟩
  | (b, bl) :: t, vs => by
      refine Tri.bind (tri_leafE f sMT b bl vs) fun x vs1 hx => ?_
      refine Tri.bind (tri_leavesE sMT t vs1).with_prefix fun r vs2 hr => tri_pure_iff.2 ?_
      obtain ⟨⟨h1, h2, h3, h4⟩, hp⟩ := hr
      refine ⟨by simp [h1], ?_, ?_, ?_⟩
      · intro tk htk
        rcases List.mem_cons.1 htk with rfl | htk
        · exact hx.2.1.mono hp
        · exact h2 tk htk
      · show x.1 :: r.1 = _
        rw [List.zipWith_cons_cons, ← h3, saltVal_of_prefix hp hx.2.1, ← hx.1]
      · intro j y hy hy2
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
          subst hy
          show (saltVal vs2 x.2).length = sMT
          rw [saltVal_of_prefix hp hx.2.1]
          exact hx.2.2 hy2
        | succ j =>
          simp only [List.getElem?_cons_succ] at hy
          exact h4 j y hy hy2

/-- "Returns a and leaves the store as it is" is closed under `pure` and `bind` (`Evaluates`,
Compile/MerkleList.lean). -/
theorem evaluates_step :
    Evaluates (St lam K L) (fun {_} x a => ∀ vs, Tri f x vs fun o vs' => o = a ∧ vs' = vs) where
  pure a := fun _ => tri_pure_iff.2 ⟨rfl, rfl⟩
  bind := fun hx hg vs => Tri.bind (hx vs) fun a vs' h => by
    obtain ⟨rfl, rfl⟩ := h
    exact hg vs'

theorem tri_levelsE (d : ℕ) (l : List (Dig lam)) (vs : List Bits) :
    Tri f (levelsM (nodeE (K := K) (L := L)) d l) vs fun o vs' =>
      o = levelsF (nodeFB f) d l ∧ vs' = vs :=
  (evaluates_step f).levelsM (qN := nodeE (K := K) (L := L)) (hN := nodeFB f)
    (fun _ _ _ => tri_plain_iff.2 (tri_pure_iff.2 ⟨rfl, rfl⟩)) d l vs

/-- What the prover keeps of a tree over an encoded index is correct, relative to a store. -/
def TreeOK (sMT : ℕ) (vs : List Bits) (t : TreeH lam) (d : ℕ) (leaf : ℕ → Body L × Bool) : Prop :=
  t.salts.length = 2 ^ d ∧
  (∀ tk ∈ t.salts, tokOK vs tk) ∧
  (∀ j, j < 2 ^ d → (leaf j).2 = true → (saltVal vs (t.salts.getD j none)).length = sMT) ∧
  t.levels =
    levelsF (nodeFB f) d
      ((List.range (2 ^ d)).map fun j => leafFB f ⟨(leaf j).1, saltVal vs (t.salts.getD j none)⟩)

theorem tokOK_getD {vs : List Bits} {tks : List (Option (Tok × Tok))}
    (h : ∀ tk ∈ tks, tokOK vs tk) (j : ℕ) : tokOK vs (tks.getD j none) := by
  rw [List.getD_eq_getElem?_getD]
  by_cases hj : j < tks.length
  · rw [List.getElem?_eq_getElem hj]; exact h _ (List.getElem_mem hj)
  · rw [List.getElem?_eq_none (not_lt.1 hj)]; trivial

variable {f} in
theorem TreeOK.mono {sMT : ℕ} {vs vs' : List Bits} (hp : vs <+: vs') {t : TreeH lam} {d : ℕ}
    {leaf : ℕ → Body L × Bool} (h : TreeOK f sMT vs t d leaf) : TreeOK f sMT vs' t d leaf := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1,
    fun tk htk => (h2 tk htk).mono hp,
    fun j hj hb => by rw [saltVal_of_prefix hp (tokOK_getD h2 j)]; exact h3 j hj hb,
    ?_⟩
  rw [h4]
  congr 1
  exact List.map_congr_left fun j _ => by rw [saltVal_of_prefix hp (tokOK_getD h2 j)]

theorem tri_commitE (sMT d : ℕ) (leaf : ℕ → Body L × Bool) (vs : List Bits) :
    Tri f (commitE (lam := lam) (K := K) sMT d leaf) vs fun t vs' => TreeOK f sMT vs' t d leaf := by
  refine Tri.bind (tri_leavesE f sMT _ vs) fun x vs1 hx => ?_
  refine Tri.bind (tri_levelsE f d x.1 vs1) fun lv vs2 hlv => tri_pure_iff.2 ?_
  obtain ⟨rfl, rfl⟩ := hlv
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have hl : x.2.length = 2 ^ d := by simpa using h1
  refine ⟨hl, h2, fun j hj hb => h4 j (leaf j) (by simp [hj]) hb, ?_⟩
  show levelsF (nodeFB f) d x.1 = _
  rw [h3, zipWith_range _ _ leaf x.2 none hl]

theorem tri_openE {σ : Type} (t : TreeH lam) (j : ℕ) (a : σ) (vs : List Bits) :
    Tri f (openE (K := K) (L := L) t j a) vs fun o vs' =>
      o = ⟨a, saltVal vs (t.salts.getD j none), pathOf t.levels j⟩ ∧ vs' = vs := by
  unfold openE
  cases t.salts.getD j none with
  | none => exact tri_pure_iff.2 ⟨rfl, rfl⟩
  | some ss => exact tri_reveal_iff.2 (tri_pure_iff.2 ⟨rfl, rfl⟩)

/-- Under `TreeOK`, for j < 2^d: the check of an honest opening in a tree over an encoded index
accepts. -/
theorem check_of_treeOK {sMT : ℕ} {vs : List Bits} {t : TreeH lam} {d : ℕ}
    {leaf : ℕ → Body L × Bool} (h : TreeOK f sMT vs t d leaf) {j : ℕ} (hj : j < 2 ^ d) :
    Check.wellFormed
        (⟨⟨(leaf j).1, saltVal vs (t.salts.getD j none)⟩, j, pathOf t.levels j,
          t.root, d⟩ : Check lam L) = true ∧
    EvalsTo f (runCheck (K := K)
        (⟨⟨(leaf j).1, saltVal vs (t.salts.getD j none)⟩, j, pathOf t.levels j,
          t.root, d⟩ : Check lam L)) true := by
  obtain ⟨-, -, -, h4⟩ := h
  have hr : t.root = rootOf t.levels := rfl
  rw [hr, h4]
  exact runCheck_honest f d _ (by simp) j hj _ (by simp [List.getD_eq_getElem?_getD, hj])

end Compile.Batch.Cmpl
