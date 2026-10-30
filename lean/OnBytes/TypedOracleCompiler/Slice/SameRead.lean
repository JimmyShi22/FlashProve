-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/SameRead.lean: what the sibling's extractor reads off a log under a root is a walk
of one look.

Fifteen declarations of OnBytes/Slice/SameRead.lean said again over the sibling of the library's
soundness road (OnBytes/TypedOracleCompiler/). The text is cut by program (the opened namespaces; `Batch.` written
`TypedOracleCompiler.Compile.Batch.`); no proof turns. NOT said again: `OneBlock` (OnBytes/TypedOracleCompiler/Run/PageXJoin.lean
has it); `entryOf`, `singleTr_eq`, `entryOf_at`, `inv_iff_code`, which are general in the family of
oracles and are opened from OnBytes.Slice. LEFT OUT: `SameRead` and its three laws (two
implementations of one family): two parts are compared by their looks' walks
(OnBytes/Slice/WalksO.lean: `sameRaw_of_walks`), which serves across two families too; that two
looks agree is then owed in that lemma's own form; over the sibling:
OnBytes/TypedOracleCompiler/Slice/LooksAgree.lean (`looks_of_stored`); for the entry's part of the sibling beside
the library's: TieLooks.lean, TieRaw.lean.

Main definition: `lookOf m`: how a bit string is read as a vertex or as a leaf through the
implementation m.
Main theorems: `lookOf_node`, `lookOf_leaf`; `preimage_eq_walk`, `extLeaf_eq_walk`: the leaf that
the sibling's `extLeaf` finds in the log read through m is the leaf that the look's walk finds in
the log itself.

What is not claimed. What the head of OnBytes/Slice/SameRead.lean does not claim. No implementation
is given here. A look does not open a leaf's body. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.SameRead
import OnBytes.TypedOracleCompiler.Run.PageXJoin
import OnBytes.TypedOracleCompiler.Compile.Batch.Local

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop MeasureTheory
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal
open OnBytes.Slice (Look firstAt logAns NoClash entryOf singleTr_eq entryOf_at inv_iff_code
  findSome_filterMap)
open TypedOracleCompiler.Run (OneBlock)

section
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The view of vertices sees no entry at another oracle. -/
theorem pairM_node_ne {o : TypedOracleCompiler.Compile.Batch.OracleName} (ho : o ≠ TypedOracleCompiler.Compile.Batch.OracleName.node) (q :
                                                    (typedOracleFamily lam K L).Dom o)
    (r : (typedOracleFamily lam K L).Rng o) : (pairM lam K L).node ⟨o, q, r⟩ = none := by
  cases o <;> first | rfl | exact absurd rfl ho

/-- The view of leaves sees no entry at another oracle. -/
theorem pairM_leaf_ne {o : TypedOracleCompiler.Compile.Batch.OracleName} (ho : o ≠ TypedOracleCompiler.Compile.Batch.OracleName.leaf) (q :
                                                    (typedOracleFamily lam K L).Dom o)
    (r : (typedOracleFamily lam K L).Rng o) : (pairM lam K L).leaf ⟨o, q, r⟩ = none := by
  cases o <;> first | rfl | exact absurd rfl ho

/-- Through m an entry of the log is seen as a vertex on the two digests x with the answer c if and
only if its string is m's string of that vertex query and its answer is c. -/
theorem node_hit (m : OracleCoding (typedOracleFamily lam K L) lam) (hm : OneBlock m) (e : QA (rom lam)) (c : Dig lam)
    (x : Dig lam × Dig lam) :
    (entryOf m e).bind (Merkle.hit (pairM lam K L).node c) = some x ↔
      (∃ j, e.2.1 = m.code TypedOracleCompiler.Compile.Batch.OracleName.node
          (List.ofFn x.1, List.ofFn x.2) j) ∧ e.2.2 = c := by
  obtain ⟨u, s, r⟩ := e
  cases u
  rcases hd : m.dec s with ⟨o, q, j⟩
  have hs : s = m.code o q j := by
    have h1 := m.code_dec s
    rw [hd] at h1
    exact h1.symm
  rw [entryOf_at m s r o q j hd]
  by_cases ho : o = TypedOracleCompiler.Compile.Batch.OracleName.node
  · subst ho
    rw [if_pos hm.node1]
    show (Merkle.hit (pairM lam K L).node c
      ⟨TypedOracleCompiler.Compile.Batch.OracleName.node, q,
          (m.rng TypedOracleCompiler.Compile.Batch.OracleName.node).symm fun _ => r⟩) = some x ↔ _
    unfold Merkle.hit
    show ((nodeView q ((m.rng TypedOracleCompiler.Compile.Batch.OracleName.node).symm (fun _ => r) : Dig lam)).bind
      fun qa => if qa.2 = c then some qa.1 else none) = some x ↔ _
    rw [hm.rngNode]
    constructor
    · intro h
      obtain ⟨qa, hqa, hif⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨⟨a, b⟩, c'⟩ := qa
      obtain ⟨h1, h2, h3⟩ := nodeView_eq_some hqa
      split at hif
      · rename_i hc
        have hx := Option.some.inj hif
        subst hx
        refine ⟨⟨j, ?_⟩, h3.trans hc⟩
        show s = _
        rw [hs]
        congr 1
        exact Prod.ext (TypedOracleCompiler.Compile.Batch.eq_ofFn_of_digOf h1)
            (TypedOracleCompiler.Compile.Batch.eq_ofFn_of_digOf h2)
      · cases hif
    · rintro ⟨⟨j', hj'⟩, hc⟩
      have hj2 : s = m.code TypedOracleCompiler.Compile.Batch.OracleName.node (List.ofFn x.1, List.ofFn x.2) j' := hj'
      have h1 := m.dec_code TypedOracleCompiler.Compile.Batch.OracleName.node (List.ofFn x.1, List.ofFn x.2) j'
      rw [← hj2, hd] at h1
      obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.1 h1
      have h3 : q = (List.ofFn x.1, List.ofFn x.2) := (Prod.mk.inj (eq_of_heq h2)).1
      have hc' : r = c := hc
      rw [h3]
      unfold nodeView
      simp only [TypedOracleCompiler.Compile.Batch.digOf_ofFn, Option.bind_some, hc', if_true]
  · have hn : (if m.blocks o = 1 then some (⟨o, q, (m.rng o).symm fun _ => r⟩ : QA (typedOracleFamily lam K L))
        else none).bind (Merkle.hit (pairM lam K L).node c) = none := by
      split
      · show Merkle.hit (pairM lam K L).node c _ = none
        unfold Merkle.hit
        rw [pairM_node_ne ho]
        rfl
      · rfl
    rw [hn]
    constructor
    · intro h
      cases h
    · rintro ⟨⟨j', hj'⟩, -⟩
      have hj2 : s = m.code TypedOracleCompiler.Compile.Batch.OracleName.node (List.ofFn x.1, List.ofFn x.2) j' := hj'
      have h1 := m.dec_code TypedOracleCompiler.Compile.Batch.OracleName.node (List.ofFn x.1, List.ofFn x.2) j'
      rw [← hj2, hd] at h1
      exact absurd (Sigma.mk.inj_iff.1 h1).1 ho

/-- Through m an entry of the log is seen as the leaf query q with the answer c if and only if its
string is m's string of that leaf query and its answer is c. -/
theorem leaf_hit (m : OracleCoding (typedOracleFamily lam K L) lam) (hm : OneBlock m) (e : QA (rom lam)) (c : Dig lam)
    (x : LeafIn L) :
    (entryOf m e).bind (Merkle.hit (pairM lam K L).leaf c) = some x ↔
      (∃ j, e.2.1 = m.code TypedOracleCompiler.Compile.Batch.OracleName.leaf x j) ∧ e.2.2 = c := by
  obtain ⟨u, s, r⟩ := e
  cases u
  rcases hd : m.dec s with ⟨o, q, j⟩
  have hs : s = m.code o q j := by
    have h1 := m.code_dec s
    rw [hd] at h1
    exact h1.symm
  rw [entryOf_at m s r o q j hd]
  by_cases ho : o = TypedOracleCompiler.Compile.Batch.OracleName.leaf
  · subst ho
    rw [if_pos hm.leaf1]
    show (Merkle.hit (pairM lam K L).leaf c
      ⟨TypedOracleCompiler.Compile.Batch.OracleName.leaf, q,
          (m.rng TypedOracleCompiler.Compile.Batch.OracleName.leaf).symm fun _ => r⟩) = some x ↔ _
    unfold Merkle.hit
    show ((some ((q : LeafIn L), ((m.rng TypedOracleCompiler.Compile.Batch.OracleName.leaf).symm
        (fun _ => r) : Dig lam))).bind
      fun qa : LeafIn L × Dig lam => if qa.2 = c then some qa.1 else none) = some x ↔ _
    rw [hm.rngLeaf]
    simp only [Option.bind_some]
    constructor
    · intro h
      split at h
      · rename_i hc
        have hx := Option.some.inj h
        subst hx
        exact ⟨⟨j, hs⟩, hc⟩
      · cases h
    · rintro ⟨⟨j', hj'⟩, hc⟩
      have hj2 : s = m.code TypedOracleCompiler.Compile.Batch.OracleName.leaf x j' := hj'
      have h1 := m.dec_code TypedOracleCompiler.Compile.Batch.OracleName.leaf x j'
      rw [← hj2, hd] at h1
      obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.1 h1
      have h3 : q = x := (Prod.mk.inj (eq_of_heq h2)).1
      have hc' : r = c := hc
      exact (if_pos hc').trans (congrArg some h3)
  · have hn : (if m.blocks o = 1 then some (⟨o, q, (m.rng o).symm fun _ => r⟩ : QA (typedOracleFamily lam K L))
        else none).bind (Merkle.hit (pairM lam K L).leaf c) = none := by
      split
      · show Merkle.hit (pairM lam K L).leaf c _ = none
        unfold Merkle.hit
        rw [pairM_leaf_ne ho]
        rfl
      · rfl
    rw [hn]
    constructor
    · intro h
      cases h
    · rintro ⟨⟨j', hj'⟩, -⟩
      have hj2 : s = m.code TypedOracleCompiler.Compile.Batch.OracleName.leaf x j' := hj'
      have h1 := m.dec_code TypedOracleCompiler.Compile.Batch.OracleName.leaf x j'
      rw [← hj2, hd] at h1
      exact absurd (Sigma.mk.inj_iff.1 h1).1 ho

end

/-! ## The bridge: the extractor's walk is a walk in the log -/

section
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The two digests in a typed query, if it is a vertex query on two strings of lam bits. -/
def nodeOf : (o : TypedOracleCompiler.Compile.Batch.OracleName) → (typedOracleFamily lam K L).Dom o → Option (Dig lam × Dig lam)
  | .node, q => match TypedOracleCompiler.Compile.Batch.digOf (lam := lam) q.1, TypedOracleCompiler.Compile.Batch.digOf
      (lam := lam) q.2 with
    | some a, some b => some (a, b)
    | _, _ => none
  | _, _ => none

/-- The leaf query in a typed query, if it is one. -/
def leafOf : (o : TypedOracleCompiler.Compile.Batch.OracleName) → (typedOracleFamily lam K L).Dom o → Option (LeafIn L)
  | .leaf, q => some q
  | _, _ => none

/-- A typed query at another oracle is no vertex query. -/
theorem nodeOf_ne {o : TypedOracleCompiler.Compile.Batch.OracleName} (ho : o ≠ TypedOracleCompiler.Compile.Batch.OracleName.node) (q :
                                                    (typedOracleFamily lam K L).Dom o) :
    nodeOf o q = none := by
  cases o <;> first | rfl | exact absurd rfl ho

/-- A typed query at another oracle is no leaf query. -/
theorem leafOf_ne {o : TypedOracleCompiler.Compile.Batch.OracleName} (ho : o ≠ TypedOracleCompiler.Compile.Batch.OracleName.leaf) (q :
                                                    (typedOracleFamily lam K L).Dom o) :
    leafOf o q = none := by
  cases o <;> first | rfl | exact absurd rfl ho

/-- How a bit string is read through m. -/
def lookOf (m : OracleCoding (typedOracleFamily lam K L) lam) : Look lam (LeafIn L) where
  node := fun s => nodeOf (m.inv s).1 (m.inv s).2.1
  leaf := fun s => leafOf (m.inv s).1 (m.inv s).2.1

/-- A string is read as the vertex on the two digests x if and only if it stands for a block of the
vertex query on them. -/
theorem lookOf_node (m : OracleCoding (typedOracleFamily lam K L) lam) (s : List Bool) (x : Dig lam × Dig lam) :
    (lookOf m).node s = some x ↔
      ∃ k, m.inv s = ⟨TypedOracleCompiler.Compile.Batch.OracleName.node, ((List.ofFn x.1, List.ofFn x.2), k)⟩ := by
  show nodeOf (m.inv s).1 (m.inv s).2.1 = some x ↔ _
  rcases m.inv s with ⟨o, q, k⟩
  constructor
  · intro h
    have h0 : nodeOf o q = some x := h
    by_cases ho : o = TypedOracleCompiler.Compile.Batch.OracleName.node
    swap
    · rw [nodeOf_ne ho] at h0
      cases h0
    subst ho
    have h' : (match TypedOracleCompiler.Compile.Batch.digOf (lam := lam) q.1, TypedOracleCompiler.Compile.Batch.digOf
        (lam := lam) q.2 with
      | some a, some b => some (a, b)
      | _, _ => none) = some x := h0
    cases h1 : TypedOracleCompiler.Compile.Batch.digOf (lam := lam) q.1 with
    | none => rw [h1] at h'; cases h'
    | some a =>
      cases h2 : TypedOracleCompiler.Compile.Batch.digOf (lam := lam) q.2 with
      | none => rw [h1, h2] at h'; cases h'
      | some b =>
        rw [h1, h2] at h'
        have hx : (a, b) = x := Option.some.inj h'
        subst hx
        refine ⟨k, ?_⟩
        have hq : q = (List.ofFn a, List.ofFn b) :=
          Prod.ext (TypedOracleCompiler.Compile.Batch.eq_ofFn_of_digOf h1) (TypedOracleCompiler.Compile.Batch.eq_ofFn_of_digOf h2)
        rw [hq]
  · rintro ⟨k', h⟩
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 h
    have h3 : q = (List.ofFn x.1, List.ofFn x.2) := (Prod.mk.inj (eq_of_heq h2)).1
    rw [h3]
    show (match TypedOracleCompiler.Compile.Batch.digOf (lam := lam) (List.ofFn x.1), TypedOracleCompiler.Compile.Batch.digOf
        (lam := lam) (List.ofFn x.2)
      with
      | some a, some b => some (a, b)
      | _, _ => none) = some x
    rw [TypedOracleCompiler.Compile.Batch.digOf_ofFn, TypedOracleCompiler.Compile.Batch.digOf_ofFn]

/-- A string is read as the leaf query q if and only if it stands for a block of q. -/
theorem lookOf_leaf (m : OracleCoding (typedOracleFamily lam K L) lam) (s : List Bool) (x : LeafIn L) :
    (lookOf m).leaf s = some x ↔ ∃ k, m.inv s = ⟨TypedOracleCompiler.Compile.Batch.OracleName.leaf, (x, k)⟩ := by
  show leafOf (m.inv s).1 (m.inv s).2.1 = some x ↔ _
  rcases m.inv s with ⟨o, q, k⟩
  constructor
  · intro h
    have h0 : leafOf o q = some x := h
    by_cases ho : o = TypedOracleCompiler.Compile.Batch.OracleName.leaf
    swap
    · rw [leafOf_ne ho] at h0
      cases h0
    subst ho
    have hq : q = x := Option.some.inj h0
    rw [hq]
    exact ⟨k, rfl⟩
  · rintro ⟨k', h⟩
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 h
    have h3 : q = x := (Prod.mk.inj (eq_of_heq h2)).1
    rw [h3]
    rfl

/-- The first vertex with a given answer that the extractor sees through m is the first that
`lookOf m` reads in the log. -/
theorem firstPre_node (m : OracleCoding (typedOracleFamily lam K L) lam) (hm : OneBlock m) (σ : Trace (rom lam))
    (c : Dig lam) :
    Merkle.firstPre (pairM lam K L).node (singleTr m σ) c = firstAt (lookOf m).node σ c := by
  unfold Merkle.firstPre firstAt
  rw [singleTr_eq, findSome_filterMap]
  refine congrArg (fun f => List.findSome? f σ) (funext fun e => Option.ext fun x => ?_)
  rw [node_hit m hm]
  have e1 := (inv_iff_code m e.2.1 TypedOracleCompiler.Compile.Batch.OracleName.node
      (List.ofFn x.1, List.ofFn x.2)).symm.trans
    (lookOf_node m e.2.1 x).symm
  by_cases hc : logAns e = c
  · rw [if_pos hc]
    exact ⟨fun h => e1.1 h.1, fun h => ⟨e1.2 h, hc⟩⟩
  · rw [if_neg hc]
    exact ⟨fun h => absurd h.2 hc, fun h => by cases h⟩

/-- The like for leaves. -/
theorem firstPre_leaf (m : OracleCoding (typedOracleFamily lam K L) lam) (hm : OneBlock m) (σ : Trace (rom lam))
    (c : Dig lam) :
    Merkle.firstPre (pairM lam K L).leaf (singleTr m σ) c = firstAt (lookOf m).leaf σ c := by
  unfold Merkle.firstPre firstAt
  rw [singleTr_eq, findSome_filterMap]
  refine congrArg (fun f => List.findSome? f σ) (funext fun e => Option.ext fun x => ?_)
  rw [leaf_hit m hm]
  have e1 := (inv_iff_code m e.2.1 TypedOracleCompiler.Compile.Batch.OracleName.leaf x).symm.trans
      (lookOf_leaf m e.2.1 x).symm
  by_cases hc : logAns e = c
  · rw [if_pos hc]
    exact ⟨fun h => e1.1 h.1, fun h => ⟨e1.2 h, hc⟩⟩
  · rw [if_neg hc]
    exact ⟨fun h => absurd h.2 hc, fun h => by cases h⟩

/-- The extractor's walk through m is the walk of `lookOf m` in the log. -/
theorem preimage_eq_walk (m : OracleCoding (typedOracleFamily lam K L) lam) (hm : OneBlock m) (σ : Trace (rom lam)) :
    ∀ {t : Merkle.Shape} (p : t.Pos) (c : Dig lam),
      (pairM lam K L).preimage (singleTr m σ) p c = (lookOf m).walk σ p c
  | _, .here, c => firstPre_leaf m hm σ c
  | _, .left p, c => by
    simp only [Merkle.OraclePair.preimage, Look.walk, firstPre_node m hm σ c]
    exact congrArg _ (funext fun q => preimage_eq_walk m hm σ p q.1)
  | _, .right p, c => by
    simp only [Merkle.OraclePair.preimage, Look.walk, firstPre_node m hm σ c]
    exact congrArg _ (funext fun q => preimage_eq_walk m hm σ p q.2)

/-- The bridge. Under `OneBlock m`, the leaf query that the extractor
(`TypedOracleCompiler.Compile.Batch.extLeaf`) finds through m at place j of the tree of depth d under the digest cm
is what the walk of `lookOf m` finds in the log itself. No condition on the log. -/
theorem extLeaf_eq_walk (m : OracleCoding (typedOracleFamily lam K L) lam) (hm : OneBlock m) (σ : Trace (rom lam))
    (d : ℕ) (cm : Dig lam) (j : ℕ) :
    TypedOracleCompiler.Compile.Batch.extLeaf (singleTr m σ) d cm j = (lookOf m).walk σ (posOf d j) cm :=
  preimage_eq_walk m hm σ _ cm

end

end TypedOracleCompiler.Slice
