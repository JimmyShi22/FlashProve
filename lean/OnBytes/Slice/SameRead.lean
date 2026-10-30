-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SameRead.lean: what the library's extractor finds in a log of queries to one oracle,
through an implementation of an interface's typed oracles, is a walk in that log; so two
implementations give one reading under one root off one log in which no two strings have one answer,
for any two readings of a leaf query that agree on strings.

OnBytes/Slice/Look.lean has walks in a log of queries to one oracle, for any way of reading a bit
string as a vertex or a leaf (`Look`), and shows that two such ways that agree find the same
(`walk_same`). The bounds of OnBytes/Slice/OneWorld.lean and OneWorldJ.lean speak of what the
library's extractor finds through an implementation m (`Rom.singleTr m`, `Compile.Batch.extLeaf`).
This file is the bridge for the library's compiler.

A reading takes the place j in the tree and a leaf query, and gives a value of a type Sg or nothing.
The agreement of two sides is said on bit strings, through the implementations' inverse maps, so
that no symbol of either interface and no index of a block occurs in it.

Main definitions.
 `OneBlock m`   a leaf's and a vertex's answer is one block, taken as it is.
 `lookOf m`     how a bit string is read through m: as a vertex, if it stands for a vertex query on
                two strings of lam bits; as a leaf, if it stands for a leaf query.
 `SameRead sym₁ sym₂ m₁ m₂`   a bit string stands for a vertex query on two given digests through m₁
                if and only if it does through m₂; and it stands through m₁ for a leaf query that
                `sym₁ j` reads as x if and only if it stands through m₂ for one that `sym₂ j` reads
                as x.
Main theorems.
 `node_hit`, `leaf_hit`   how an entry of the log is seen through m.
 `extLeaf_eq_walk`       THE BRIDGE: under `OneBlock m`, the leaf query that the extractor finds
                         through m at place j of the tree of depth d under a digest is what the walk
                         of `lookOf m` finds in the log itself.
 `extLeaf_sameRead`      under `OneBlock` of both and `SameRead`, off a log in which no two strings
                         have one answer (`NoClash`, OnBytes/Slice/OneLog.lean), what the one
                         reading makes of the leaf query found at place j of the tree of depth d
                         under a digest is what the other makes of the one found through the other
                         implementation.

What is not claimed. That any two implementations and readings meet `SameRead` (an instance:
OnBytes/Slice/SameStored.lean, SameStoredAt.lean). What the readings leave out (where both give
nothing) may differ between the two sides. Nothing on any protocol, language, checker or hash
function; no probability.

-/
import OnBytes.Slice.Look

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Compile Compile.Batch

/-! ## One entry of the log, through an implementation -/

section
variable {lam : ℕ}

/-- What `Rom.singleTr m` makes of one entry of the log. -/
noncomputable def entryOf {S : OSpec} (m : OracleCoding S lam) (e : QA (rom lam)) : Option (QA S) :=
  if m.blocks (m.dec e.2.1).1 = 1 then
    some ⟨(m.dec e.2.1).1, (m.dec e.2.1).2.1, (m.rng (m.dec e.2.1).1).symm fun _ => e.2.2⟩
  else none

/-- `Rom.singleTr m` applies `entryOf m` along the log and keeps what it returns. -/
theorem singleTr_eq {S : OSpec} (m : OracleCoding S lam) (σ : Trace (rom lam)) :
    singleTr m σ = σ.filterMap (entryOf m) := rfl

/-- The entry at a string that stands for block j of the typed point (o, q). -/
theorem entryOf_at {S : OSpec} (m : OracleCoding S lam) (s : List Bool) (r : Fin lam → Bool) (o : S.ι)
    (q : S.Dom o) (j : Fin (m.blocks o)) (h : m.dec s = ⟨o, q, j⟩) :
    entryOf m ⟨(), s, r⟩ =
      if m.blocks o = 1 then some ⟨o, q, (m.rng o).symm fun _ => r⟩ else none := by
  unfold entryOf
  simp only []
  rw [h]

end

section
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-- In m a leaf's and a vertex's answer is one block, and the typed answer is that block as it
is. -/
structure OneBlock (m : OracleCoding (spec lam K L) lam) : Prop where
  /-- a leaf's answer is one block -/
  leaf1 : m.blocks Batch.OracleName.leaf = 1
  /-- a vertex's answer is one block -/
  node1 : m.blocks Batch.OracleName.node = 1
  /-- a leaf's answer is the oracle's answer, as it is -/
  rngLeaf : ∀ r : Fin lam → Bool, ((m.rng Batch.OracleName.leaf).symm (fun _ => r) : Dig lam) = r
  /-- a vertex's answer is the oracle's answer, as it is -/
  rngNode : ∀ r : Fin lam → Bool, ((m.rng Batch.OracleName.node).symm (fun _ => r) : Dig lam) = r

/-- The view of vertices sees no entry at another oracle. -/
theorem pairM_node_ne {o : Batch.OracleName} (ho : o ≠ Batch.OracleName.node) (q : (spec lam K L).Dom o)
    (r : (spec lam K L).Rng o) : (pairM lam K L).node ⟨o, q, r⟩ = none := by
  cases o <;> first | rfl | exact absurd rfl ho

/-- The view of leaves sees no entry at another oracle. -/
theorem pairM_leaf_ne {o : Batch.OracleName} (ho : o ≠ Batch.OracleName.leaf) (q : (spec lam K L).Dom o)
    (r : (spec lam K L).Rng o) : (pairM lam K L).leaf ⟨o, q, r⟩ = none := by
  cases o <;> first | rfl | exact absurd rfl ho

/-- Through m an entry of the log is seen as a vertex on the two digests x with the answer c if and
only if its string is m's string of that vertex query and its answer is c. -/
theorem node_hit (m : OracleCoding (spec lam K L) lam) (hm : OneBlock m) (e : QA (rom lam)) (c : Dig lam)
    (x : Dig lam × Dig lam) :
    (entryOf m e).bind (Merkle.hit (pairM lam K L).node c) = some x ↔
      (∃ j, e.2.1 = m.code Batch.OracleName.node (List.ofFn x.1, List.ofFn x.2) j) ∧ e.2.2 = c := by
  obtain ⟨u, s, r⟩ := e
  cases u
  rcases hd : m.dec s with ⟨o, q, j⟩
  have hs : s = m.code o q j := by
    have h1 := m.code_dec s
    rw [hd] at h1
    exact h1.symm
  rw [entryOf_at m s r o q j hd]
  by_cases ho : o = Batch.OracleName.node
  · subst ho
    rw [if_pos hm.node1]
    show (Merkle.hit (pairM lam K L).node c
      ⟨Batch.OracleName.node, q, (m.rng Batch.OracleName.node).symm fun _ => r⟩) = some x ↔ _
    unfold Merkle.hit
    show ((nodeView q ((m.rng Batch.OracleName.node).symm (fun _ => r) : Dig lam)).bind
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
        exact Prod.ext (Batch.eq_ofFn_of_digOf h1) (Batch.eq_ofFn_of_digOf h2)
      · cases hif
    · rintro ⟨⟨j', hj'⟩, hc⟩
      have hj2 : s = m.code Batch.OracleName.node (List.ofFn x.1, List.ofFn x.2) j' := hj'
      have h1 := m.dec_code Batch.OracleName.node (List.ofFn x.1, List.ofFn x.2) j'
      rw [← hj2, hd] at h1
      obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.1 h1
      have h3 : q = (List.ofFn x.1, List.ofFn x.2) := (Prod.mk.inj (eq_of_heq h2)).1
      have hc' : r = c := hc
      rw [h3]
      unfold nodeView
      simp only [Batch.digOf_ofFn, Option.bind_some, hc', if_true]
  · have hn : (if m.blocks o = 1 then some (⟨o, q, (m.rng o).symm fun _ => r⟩ : QA (spec lam K L))
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
      have hj2 : s = m.code Batch.OracleName.node (List.ofFn x.1, List.ofFn x.2) j' := hj'
      have h1 := m.dec_code Batch.OracleName.node (List.ofFn x.1, List.ofFn x.2) j'
      rw [← hj2, hd] at h1
      exact absurd (Sigma.mk.inj_iff.1 h1).1 ho

/-- Through m an entry of the log is seen as the leaf query q with the answer c if and only if its
string is m's string of that leaf query and its answer is c. -/
theorem leaf_hit (m : OracleCoding (spec lam K L) lam) (hm : OneBlock m) (e : QA (rom lam)) (c : Dig lam)
    (x : LeafIn L) :
    (entryOf m e).bind (Merkle.hit (pairM lam K L).leaf c) = some x ↔
      (∃ j, e.2.1 = m.code Batch.OracleName.leaf x j) ∧ e.2.2 = c := by
  obtain ⟨u, s, r⟩ := e
  cases u
  rcases hd : m.dec s with ⟨o, q, j⟩
  have hs : s = m.code o q j := by
    have h1 := m.code_dec s
    rw [hd] at h1
    exact h1.symm
  rw [entryOf_at m s r o q j hd]
  by_cases ho : o = Batch.OracleName.leaf
  · subst ho
    rw [if_pos hm.leaf1]
    show (Merkle.hit (pairM lam K L).leaf c
      ⟨Batch.OracleName.leaf, q, (m.rng Batch.OracleName.leaf).symm fun _ => r⟩) = some x ↔ _
    unfold Merkle.hit
    show ((some ((q : LeafIn L), ((m.rng Batch.OracleName.leaf).symm (fun _ => r) : Dig lam))).bind
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
      have hj2 : s = m.code Batch.OracleName.leaf x j' := hj'
      have h1 := m.dec_code Batch.OracleName.leaf x j'
      rw [← hj2, hd] at h1
      obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.1 h1
      have h3 : q = x := (Prod.mk.inj (eq_of_heq h2)).1
      have hc' : r = c := hc
      exact (if_pos hc').trans (congrArg some h3)
  · have hn : (if m.blocks o = 1 then some (⟨o, q, (m.rng o).symm fun _ => r⟩ : QA (spec lam K L))
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
      have hj2 : s = m.code Batch.OracleName.leaf x j' := hj'
      have h1 := m.dec_code Batch.OracleName.leaf x j'
      rw [← hj2, hd] at h1
      exact absurd (Sigma.mk.inj_iff.1 h1).1 ho

end

/-! ## The bridge: the extractor's walk is a walk in the log -/

/-- A bit string stands for some block of the typed point (o, q) if and only if it is the string of
one of that point's blocks. -/
theorem inv_iff_code {S : OSpec} {lam : ℕ} (m : OracleCoding S lam) (s : List Bool) (o : S.ι)
    (q : S.Dom o) : (∃ k, m.inv s = ⟨o, (q, k)⟩) ↔ ∃ k, s = m.code o q k := by
  constructor
  · rintro ⟨k, h⟩
    have h1 := m.code_inv s
    rw [h] at h1
    exact ⟨k, h1.symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, m.inv_code ⟨o, (q, k)⟩⟩

section
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-- The two digests in a typed query, if it is a vertex query on two strings of lam bits. -/
def nodeOf : (o : Batch.OracleName) → (spec lam K L).Dom o → Option (Dig lam × Dig lam)
  | .node, q => match Batch.digOf (lam := lam) q.1, Batch.digOf (lam := lam) q.2 with
    | some a, some b => some (a, b)
    | _, _ => none
  | _, _ => none

/-- The leaf query in a typed query, if it is one. -/
def leafOf : (o : Batch.OracleName) → (spec lam K L).Dom o → Option (LeafIn L)
  | .leaf, q => some q
  | _, _ => none

/-- A typed query at another oracle is no vertex query. -/
theorem nodeOf_ne {o : Batch.OracleName} (ho : o ≠ Batch.OracleName.node) (q : (spec lam K L).Dom o) :
    nodeOf o q = none := by
  cases o <;> first | rfl | exact absurd rfl ho

/-- A typed query at another oracle is no leaf query. -/
theorem leafOf_ne {o : Batch.OracleName} (ho : o ≠ Batch.OracleName.leaf) (q : (spec lam K L).Dom o) :
    leafOf o q = none := by
  cases o <;> first | rfl | exact absurd rfl ho

/-- **How a bit string is read through m.** -/
def lookOf (m : OracleCoding (spec lam K L) lam) : Look lam (LeafIn L) where
  node := fun s => nodeOf (m.inv s).1 (m.inv s).2.1
  leaf := fun s => leafOf (m.inv s).1 (m.inv s).2.1

/-- A string is read as the vertex on the two digests x if and only if it stands for a block of the
vertex query on them. -/
theorem lookOf_node (m : OracleCoding (spec lam K L) lam) (s : List Bool) (x : Dig lam × Dig lam) :
    (lookOf m).node s = some x ↔
      ∃ k, m.inv s = ⟨Batch.OracleName.node, ((List.ofFn x.1, List.ofFn x.2), k)⟩ := by
  show nodeOf (m.inv s).1 (m.inv s).2.1 = some x ↔ _
  rcases m.inv s with ⟨o, q, k⟩
  constructor
  · intro h
    have h0 : nodeOf o q = some x := h
    by_cases ho : o = Batch.OracleName.node
    swap
    · rw [nodeOf_ne ho] at h0
      cases h0
    subst ho
    have h' : (match Batch.digOf (lam := lam) q.1, Batch.digOf (lam := lam) q.2 with
      | some a, some b => some (a, b)
      | _, _ => none) = some x := h0
    cases h1 : Batch.digOf (lam := lam) q.1 with
    | none => rw [h1] at h'; cases h'
    | some a =>
      cases h2 : Batch.digOf (lam := lam) q.2 with
      | none => rw [h1, h2] at h'; cases h'
      | some b =>
        rw [h1, h2] at h'
        have hx : (a, b) = x := Option.some.inj h'
        subst hx
        refine ⟨k, ?_⟩
        have hq : q = (List.ofFn a, List.ofFn b) :=
          Prod.ext (Batch.eq_ofFn_of_digOf h1) (Batch.eq_ofFn_of_digOf h2)
        rw [hq]
  · rintro ⟨k', h⟩
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 h
    have h3 : q = (List.ofFn x.1, List.ofFn x.2) := (Prod.mk.inj (eq_of_heq h2)).1
    rw [h3]
    show (match Batch.digOf (lam := lam) (List.ofFn x.1), Batch.digOf (lam := lam) (List.ofFn x.2)
      with
      | some a, some b => some (a, b)
      | _, _ => none) = some x
    rw [Batch.digOf_ofFn, Batch.digOf_ofFn]

/-- A string is read as the leaf query q if and only if it stands for a block of q. -/
theorem lookOf_leaf (m : OracleCoding (spec lam K L) lam) (s : List Bool) (x : LeafIn L) :
    (lookOf m).leaf s = some x ↔ ∃ k, m.inv s = ⟨Batch.OracleName.leaf, (x, k)⟩ := by
  show leafOf (m.inv s).1 (m.inv s).2.1 = some x ↔ _
  rcases m.inv s with ⟨o, q, k⟩
  constructor
  · intro h
    have h0 : leafOf o q = some x := h
    by_cases ho : o = Batch.OracleName.leaf
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
theorem firstPre_node (m : OracleCoding (spec lam K L) lam) (hm : OneBlock m) (σ : Trace (rom lam))
    (c : Dig lam) :
    Merkle.firstPre (pairM lam K L).node (singleTr m σ) c = firstAt (lookOf m).node σ c := by
  unfold Merkle.firstPre firstAt
  rw [singleTr_eq, findSome_filterMap]
  refine congrArg (fun f => List.findSome? f σ) (funext fun e => Option.ext fun x => ?_)
  rw [node_hit m hm]
  have e1 := (inv_iff_code m e.2.1 Batch.OracleName.node (List.ofFn x.1, List.ofFn x.2)).symm.trans
    (lookOf_node m e.2.1 x).symm
  by_cases hc : logAns e = c
  · rw [if_pos hc]
    exact ⟨fun h => e1.1 h.1, fun h => ⟨e1.2 h, hc⟩⟩
  · rw [if_neg hc]
    exact ⟨fun h => absurd h.2 hc, fun h => by cases h⟩

/-- The like for leaves. -/
theorem firstPre_leaf (m : OracleCoding (spec lam K L) lam) (hm : OneBlock m) (σ : Trace (rom lam))
    (c : Dig lam) :
    Merkle.firstPre (pairM lam K L).leaf (singleTr m σ) c = firstAt (lookOf m).leaf σ c := by
  unfold Merkle.firstPre firstAt
  rw [singleTr_eq, findSome_filterMap]
  refine congrArg (fun f => List.findSome? f σ) (funext fun e => Option.ext fun x => ?_)
  rw [leaf_hit m hm]
  have e1 := (inv_iff_code m e.2.1 Batch.OracleName.leaf x).symm.trans (lookOf_leaf m e.2.1 x).symm
  by_cases hc : logAns e = c
  · rw [if_pos hc]
    exact ⟨fun h => e1.1 h.1, fun h => ⟨e1.2 h, hc⟩⟩
  · rw [if_neg hc]
    exact ⟨fun h => absurd h.2 hc, fun h => by cases h⟩

/-- The extractor's walk through m is the walk of `lookOf m` in the log. -/
theorem preimage_eq_walk (m : OracleCoding (spec lam K L) lam) (hm : OneBlock m) (σ : Trace (rom lam)) :
    ∀ {t : Merkle.Shape} (p : t.Pos) (c : Dig lam),
      (pairM lam K L).preimage (singleTr m σ) p c = (lookOf m).walk σ p c
  | _, .here, c => firstPre_leaf m hm σ c
  | _, .left p, c => by
    simp only [Merkle.OraclePair.preimage, Look.walk, firstPre_node m hm σ c]
    exact congrArg _ (funext fun q => preimage_eq_walk m hm σ p q.1)
  | _, .right p, c => by
    simp only [Merkle.OraclePair.preimage, Look.walk, firstPre_node m hm σ c]
    exact congrArg _ (funext fun q => preimage_eq_walk m hm σ p q.2)

/-- **The bridge.** Under `OneBlock m`, the leaf query that the library's extractor finds through m
at place j of the tree of depth d under the digest cm is what the walk of `lookOf m` finds in the
log itself. No condition on the log. -/
theorem extLeaf_eq_walk (m : OracleCoding (spec lam K L) lam) (hm : OneBlock m) (σ : Trace (rom lam))
    (d : ℕ) (cm : Dig lam) (j : ℕ) :
    Batch.extLeaf (singleTr m σ) d cm j = (lookOf m).walk σ (posOf d j) cm :=
  preimage_eq_walk m hm σ _ cm

end

/-! ## Two implementations, any two readings -/

variable {I₁ X₁ I₂ X₂ : Type} {lam K₁ K₂ : ℕ} {L₁ : BatchProtocol I₁ X₁} {L₂ : BatchProtocol I₂ X₂} {Sg : Type}

/-- **The two implementations agree, on bit strings, as to vertices on two digests and as to what
the two readings make of leaf queries.** j is the place in the tree, handed to both readings. That
answers are one block, taken as they are, is asked apart (`OneBlock`). -/
structure SameRead (sym₁ : ℕ → LeafIn L₁ → Option Sg) (sym₂ : ℕ → LeafIn L₂ → Option Sg)
    (m₁ : OracleCoding (spec lam K₁ L₁) lam) (m₂ : OracleCoding (spec lam K₂ L₂) lam) : Prop where
  /-- both read the same strings as the vertex query on a and b -/
  node : ∀ (s : List Bool) (a b : Dig lam),
    (∃ k, m₁.inv s = ⟨Batch.OracleName.node, ((List.ofFn a, List.ofFn b), k)⟩) ↔
      ∃ k, m₂.inv s = ⟨Batch.OracleName.node, ((List.ofFn a, List.ofFn b), k)⟩
  /-- both read the same strings as a leaf query of which the reading at j makes x -/
  leaf : ∀ (s : List Bool) (j : ℕ) (x : Sg),
    (∃ q k, m₁.inv s = ⟨Batch.OracleName.leaf, (q, k)⟩ ∧ sym₁ j q = some x) ↔
      ∃ q k, m₂.inv s = ⟨Batch.OracleName.leaf, (q, k)⟩ ∧ sym₂ j q = some x

variable {sym₁ : ℕ → LeafIn L₁ → Option Sg} {sym₂ : ℕ → LeafIn L₂ → Option Sg}
  {m₁ : OracleCoding (spec lam K₁ L₁) lam} {m₂ : OracleCoding (spec lam K₂ L₂) lam}

/-- Under `SameRead` the two looks read the same strings as the same vertices. -/
theorem SameRead.look_node (h : SameRead sym₁ sym₂ m₁ m₂) (s : List Bool) :
    (lookOf m₁).node s = (lookOf m₂).node s :=
  Option.ext fun x => by rw [lookOf_node, lookOf_node, h.node]

/-- Under `SameRead`, string by string, what the one reading makes of the first look's leaf is what
the other makes of the second's. -/
theorem SameRead.look_leaf (h : SameRead sym₁ sym₂ m₁ m₂) (j : ℕ) (s : List Bool) :
    ((lookOf m₁).leaf s).bind (sym₁ j) = ((lookOf m₂).leaf s).bind (sym₂ j) := by
  refine Option.ext fun x => ?_
  have e₁ : ((lookOf m₁).leaf s).bind (sym₁ j) = some x ↔
      ∃ q k, m₁.inv s = ⟨Batch.OracleName.leaf, (q, k)⟩ ∧ sym₁ j q = some x := by
    rw [Option.bind_eq_some_iff]
    constructor
    · rintro ⟨q, hq, hs⟩
      obtain ⟨k, hk⟩ := (lookOf_leaf m₁ s q).1 hq
      exact ⟨q, k, hk, hs⟩
    · rintro ⟨q, k, hk, hs⟩
      exact ⟨q, (lookOf_leaf m₁ s q).2 ⟨k, hk⟩, hs⟩
  have e₂ : ((lookOf m₂).leaf s).bind (sym₂ j) = some x ↔
      ∃ q k, m₂.inv s = ⟨Batch.OracleName.leaf, (q, k)⟩ ∧ sym₂ j q = some x := by
    rw [Option.bind_eq_some_iff]
    constructor
    · rintro ⟨q, hq, hs⟩
      obtain ⟨k, hk⟩ := (lookOf_leaf m₂ s q).1 hq
      exact ⟨q, k, hk, hs⟩
    · rintro ⟨q, k, hk, hs⟩
      exact ⟨q, (lookOf_leaf m₂ s q).2 ⟨k, hk⟩, hs⟩
  rw [e₁, e₂, h.leaf]

/-- **Two implementations that agree on strings give one reading.** Off a log in which no two
strings have one answer: what `sym₁ j` makes of the leaf query that is found through m₁ at place j
of the tree of depth d under the digest cm is what `sym₂ j` makes of the one found through m₂; where
the one reading gives nothing, so does the other; the leaf queries that are found may differ. Asked:
`OneBlock` of both, `SameRead`, `NoClash`. The readings are free. No probability. -/
theorem extLeaf_sameRead (h₁ : OneBlock m₁) (h₂ : OneBlock m₂) (h : SameRead sym₁ sym₂ m₁ m₂)
    (σ : Trace (rom lam)) (hσ : NoClash σ) (d j : ℕ) (cm : Dig lam) :
    (Batch.extLeaf (singleTr m₁ σ) d cm j).bind (sym₁ j) =
      (Batch.extLeaf (singleTr m₂ σ) d cm j).bind (sym₂ j) := by
  rw [extLeaf_eq_walk m₁ h₁, extLeaf_eq_walk m₂ h₂]
  exact walk_same _ _ _ _ h.look_node (h.look_leaf j) σ hσ _ cm

end OnBytes.Slice
