-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/WalksTree.lean: the walks of the forests that the compiled verifier makes of the
typing of a whole file say yes, stretch by stretch, under named premises.

Each forest at a stretch is one tree of the stretch (OnBytes/Maker/ForestsAt.lean). Its walk says
yes if its checks are read off one consistent table of vertices
(OnBytes/TypedOracleCompiler/Joined/WalkTable.lean, `walk_of_table`). The table is that of the tree's openings in
the file (`vertexOf` at `recOf`, OnBytes/Maker/WalksAt.lean). Of the four conditions, the one on the
paths is shown in OnBytes/Maker/WalksAt.lean; consistency and the top are shown here from
OnBytes/Maker/RecNodes.lean; the one on the leaves is a premise.

  `WalkOwes g h cfg W r`   what is owed for all trees of the file: two openings of one tree hold one
        value at each vertex (`OneTable`); each opening is what the reader of an opening has handed
        out; g's node hash is the format's vertex hash (`NodeIs`); each value in a record has 32
        bytes.
  `RootsRead`   for a stretch: the root that the wire records and the roots as yielded give to a
        position is the digest of the root to which the reader's walk led, in each opening of the
        position's tree.
  `LeavesRead`  for a stretch: g's leaf hash of the symbol and the salt of the opening at a position
        that is read is the table's entry at the bottom, at the position's leaf.
  `isTree_listed`   each check of a forest that is a tree stands at a leaf that an opening of that
        tree in the file lists, and that opening has the tree's shape.
  `isTree_meets`, `isTree_root`   `FromTable`'s conditions meets and root.
  `isTree_yes`      **the walk of a forest that is a tree says yes.**
  `walks_lo`, `walks_sh`   **all forests of a stretch of local, or of shared, rounds.**

None of `WalkOwes`, `RootsRead`, `LeavesRead` is shown here. OnBytes/Maker/ReadWalks.lean has the
second field of `WalkOwes` for a chain that was read, and the first for openings with one root,
below the root.

Not claimed. Nothing on soundness (index binding included), what a root fixes, opening-form binding,
no two openings of a commitment, correctness of extraction or whatever else names a committer or a prover.

-/
import OnBytes.Maker.RecNodes

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening)
open _root_.Run _root_.Run.PQ

/-- What is owed for all trees of the file. -/
structure WalkOwes {I X : Type} {K' : ℕ} {L : BatchProtocolWithLeafBody I X} (g : Fam (typedOracleFamily 256 K' L))
    (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) (cfg : ByteArray) (W : Three.Whole)
    (r : Proof.TailRead) : Prop where
  one : ∀ j, OneTable W r j
  walked : ∀ j z, (j, z) ∈ ownRowsW W r → Walked h cfg z
  node : NodeIs g h cfg
  size : ∀ j, ∀ u ∈ recOf W r j, u.2.2.size = 32

/-- The root of a position's tree is the digest of the root to which the reader's walk led. -/
def RootsRead {K' : ℕ} (W : Three.Whole) (r : Proof.TailRead) (C : CK) (ds : List RDT) (base : ℕ)
    {A : RoundSplits (uLT C ds)} (Wr : RoundsQueryLayout 256 K' (uLT C ds) A) (R : RootsOfChain 256 (uLT C ds)) : Prop :=
  ∀ q d c z, treeOf (uLT C ds) A Wr R q = some (d, c) →
    (base + treeAt C ds q, z) ∈ ownRowsW W r → bytesToDig z.2.2.root = c

/-- g's leaf hash at an opening that is read is the table's entry at the bottom. -/
def LeavesRead {I X : Type} {K' : ℕ} {L : BatchProtocolWithLeafBody I X} (g : Fam (typedOracleFamily 256 K' L)) (W : Three.Whole)
    (r : Proof.TailRead) (C : CK) (ds : List RDT) (base : ℕ)
    (tabs : List (ℕ × List (ℕ × Row3)))
    (emb : (p : OPos (uLT C ds)) → OSym (uLT C ds) p → Body L) (rd : OPos (uLT C ds) → Bool) :
    Prop :=
  ∀ q op sh, rd q = true → opensT C ds base tabs q = some op →
    treeShT ds (treeAt C ds q) = some sh →
    g OracleName.leaf ⟨emb q op.sym, op.salt⟩ =
      vertexOf sh.a (recOf W r (base + treeAt C ds q)) 0 (leafAt C ds q)

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {a : ℕ} {W : Three.Whole} {sb : ℕ} {r : Proof.TailRead}
  {tabs : List (ℕ × List (ℕ × Row3))} {K' : ℕ} {C : CK} {ds : List RDT} {base : ℕ}
  {A : RoundSplits (uLT C ds)} {Wr : RoundsQueryLayout 256 K' (uLT C ds) A}
  {emb : (p : OPos (uLT C ds)) → OSym (uLT C ds) p → Body L} {R : RootsOfChain 256 (uLT C ds)}
  {rd : OPos (uLT C ds) → Bool} {T : Forest 256 L} {n : ℕ} {sh : Fmt.Shape} {c : Dig 256}

/-- Each check of a forest that is a tree stands at a leaf that an opening of that tree lists. -/
theorem isTree_listed (hrow : TabsRow W sb r tabs) (htabs : TabsHold W sb r tabs)
    (hshape : shapesFit a W = true)
    (hsh : ∀ q, (WholeD.of a W).shape (base + treeAt C ds q) = treeShT ds (treeAt C ds q))
    (H : IsTree C ds Wr emb R rd (opensT C ds base tabs) T n sh c) :
    ∀ x ∈ T.idx, ∃ z q, (base + n, z) ∈ ownRowsW W r ∧ z.1 = sh ∧ x ∈ z.2.1 ∧ x < 2 ^ sh.a ∧
      posAtST C ds n x = some q := by
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  obtain ⟨e0, q, op, hq, -, hop, -⟩ := H.checks e he
  have hpl := place_posAtST C ds n e.2.j q hq
  have hn : treeAt C ds q = n := congrArg Prod.fst hpl
  have hl' : leafAt C ds q = e.2.j := congrArg Prod.snd hpl
  obtain ⟨tab, col, ht, hl, -⟩ := opensT_some C ds base tabs q op hop
  obtain ⟨z, run, s0, hz, hli, -, -, -, -⟩ := hrow _ _ _ _ _ _ ht hl
  obtain ⟨t, ht', e1, hok⟩ := htabs.row _ z hz
  have hT : treeShT ds (treeAt C ds q) = some z.1 := by
    rw [← hsh q, e1]
    exact shapesFit_at hshape ht'
  rw [hn] at hT hz
  obtain rfl : z.1 = sh := Option.some.inj (hT.symm.trans H.shape)
  have hmem : e.2.j ∈ z.2.1 := by
    rw [← hl']
    exact (List.of_mem_zip (listed_col hli)).1
  rw [e0, Nat.zero_mul, Nat.zero_add]
  exact ⟨z, q, hz, rfl, hmem, (TieTree.ok_list (asOpenB z) _ _ hok).2.1 _ hmem, hq⟩

variable (g : Fam (typedOracleFamily 256 K' L)) (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray)
  (cfg : ByteArray)

theorem isTree_meets (hrow : TabsRow W sb r tabs) (htabs : TabsHold W sb r tabs)
    (hshape : shapesFit a W = true)
    (hsh : ∀ q, (WholeD.of a W).shape (base + treeAt C ds q) = treeShT ds (treeAt C ds q))
    (O : WalkOwes g h cfg W r) (H : IsTree C ds Wr emb R rd (opensT C ds base tabs) T n sh c) :
    ∀ m < T.depth,
      Meets (nodeAt g) (vertexOf sh.a (recOf W r (base + n))) m (Octopus.upN m T.idx) := by
  intro m hm i hi
  obtain ⟨x, hx, rfl⟩ := mem_upN m T.idx i hi
  obtain ⟨z, -, hz, rfl, hxz, -, -⟩ := isTree_listed hrow htabs hshape hsh H x hx
  exact rec_meets g h cfg (O.one _) hz (O.walked _ z hz) O.node (O.size _) x hxz m (H.depth ▸ hm)

theorem isTree_root (hrow : TabsRow W sb r tabs) (htabs : TabsHold W sb r tabs)
    (hshape : shapesFit a W = true)
    (hsh : ∀ q, (WholeD.of a W).shape (base + treeAt C ds q) = treeShT ds (treeAt C ds q))
    (O : WalkOwes g h cfg W r) (hrt : RootsRead W r C ds base Wr R)
    (H : IsTree C ds Wr emb R rd (opensT C ds base tabs) T n sh c) :
    ∀ m ∈ Octopus.upN T.depth T.idx,
      vertexOf sh.a (recOf W r (base + n)) T.depth m = T.treeRoot m := by
  intro m hm
  obtain ⟨x, hx, rfl⟩ := mem_upN T.depth T.idx m hm
  obtain ⟨z, q, hz, rfl, -, hlt, hq⟩ := isTree_listed hrow htabs hshape hsh H x hx
  have hn : treeAt C ds q = n := congrArg Prod.fst (place_posAtST C ds n x q hq)
  rw [H.depth, Nat.div_eq_of_lt hlt, H.root, rec_root h cfg (O.one _) hz (O.walked _ z hz)]
  exact hrt q _ c z (H.tree x q hq) (by rw [hn]; exact hz)

/-- **The walk of a forest that is a tree of the stretch says yes.** -/
theorem isTree_yes (hrow : TabsRow W sb r tabs) (htabs : TabsHold W sb r tabs)
    (hshape : shapesFit a W = true)
    (hsh : ∀ q, (WholeD.of a W).shape (base + treeAt C ds q) = treeShT ds (treeAt C ds q))
    (O : WalkOwes g h cfg W r) (hrt : RootsRead W r C ds base Wr R)
    (hlf : LeavesRead g W r C ds base tabs emb rd)
    (H : IsTree C ds Wr emb R rd (opensT C ds base tabs) T n sh c) :
    walkP g T T.reads = true := by
  refine isTree_walk g hrow htabs hshape hsh (O.one _) H (fun e he => ?_)
    (isTree_meets g h cfg hrow htabs hshape hsh O H)
    (isTree_root g h cfg hrow htabs hshape hsh O hrt H)
  obtain ⟨e0, q, op, hq, hr, hop, he2⟩ := H.checks e he
  have hpl := place_posAtST C ds n e.2.j q hq
  have hn : treeAt C ds q = n := congrArg Prod.fst hpl
  have hl' : leafAt C ds q = e.2.j := congrArg Prod.snd hpl
  have key := hlf q op sh hr hop (by rw [hn]; exact H.shape)
  rw [hn, hl'] at key
  rw [e0, Nat.zero_mul, Nat.zero_add, ← key, he2]

end

/-! ## All forests of a stretch -/

section Stretch
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {a : ℕ} {W : Three.Whole} {sb : ℕ} {r : Proof.TailRead}
  {tabs : List (ℕ × List (ℕ × Row3))} (C : CK) (K : ℕ)
  (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (ds : List RDT) (base : ℕ)
  (g : Fam (typedOracleFamily 256 (K + 1) L)) (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray)
  (cfg : ByteArray)

/-- **All forests of a stretch of local rounds.** -/
theorem walks_lo (hrow : TabsRow W sb r tabs) (htabs : TabsHold W sb r tabs)
    (hshape : shapesFit a W = true)
    (hsh : ∀ q, (WholeD.of a W).shape (base + treeAt C ds q) = treeShT ds (treeAt C ds q))
    (O : WalkOwes g h cfg W r)
    (emb : (p : OPos (uLT C ds)) → OSym (uLT C ds) p → Body L) (R : RootsOfChain 256 (uLT C ds))
    (rd : OPos (uLT C ds) → Bool)
    (hrt : RootsRead W r C ds base (wiresLo C K chal ds) R)
    (hlf : LeavesRead g W r C ds base tabs emb rd) (Fs : List (Forest 256 L))
    (hF : forestsB (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds) emb R rd
      (opensT C ds base tabs) = some Fs) :
    ∀ T ∈ Fs, walkP g T T.reads = true := fun T hT => by
  obtain ⟨n, sh, c, H⟩ := forests_lo C K chal ds emb R rd _ Fs hF T hT
  exact isTree_yes g h cfg hrow htabs hshape hsh O hrt hlf H

/-- **All forests of a stretch of shared rounds.** -/
theorem walks_sh (hrow : TabsRow W sb r tabs) (htabs : TabsHold W sb r tabs)
    (hshape : shapesFit a W = true)
    (hsh : ∀ q, (WholeD.of a W).shape (base + treeAt C ds q) = treeShT ds (treeAt C ds q))
    (O : WalkOwes g h cfg W r)
    (emb : (p : OPos (uLT C ds)) → OSym (uLT C ds) p → Body L) (R : RootsOfChain 256 (uLT C ds))
    (rd : OPos (uLT C ds) → Bool)
    (hrt : RootsRead W r C ds base (wiresSh C K chal ds) R)
    (hlf : LeavesRead g W r C ds base tabs emb rd) (Fs : List (Forest 256 L))
    (hF : forestsB (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds) emb
      R rd (opensT C ds base tabs) = some Fs) :
    ∀ T ∈ Fs, walkP g T T.reads = true := fun T hT => by
  obtain ⟨n, sh, c, H⟩ := forests_sh C K chal ds emb R rd _ Fs hF T hT
  exact isTree_yes g h cfg hrow htabs hshape hsh O hrt hlf H

end Stretch

end OnBytes.Maker
