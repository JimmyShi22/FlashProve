-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/WalksOf.lean: the walks of all forests say yes at a value of the typing of a whole
file; what is owed is gathered in one record on the reading and one on the oracle functions.

OnBytes/Maker/WalksFile.lean and OnBytes/Maker/WalkExt.lean have the four fields `walk₁`, `walk₂`,
`walk₃`, `walkE` of `AfterRuns` (OnBytes/TypedOracleCompiler/Joined/K/Left.lean) under `WalkOwes`, `ExtOwes`,
`RootsRead`, `LeavesRead` and two premises on the stored table. OnBytes/Maker/RootsOfTrees.lean pays
`RootsRead`, OnBytes/Maker/LeavesOf.lean cuts the premises on the leaves in two. Here what is left
is sorted by whose matter it is.

  `ReadOwes h cfg W r`   **what is owed of the file as read**, for the trees of the rounds and for
        the stored table: two openings of one tree hold one value at each vertex; each opening is
        what the reader of an opening has handed out, at the digest cfg in the vertices' hashes;
        each value in a record has 32 bytes; the opened leaves' hashes stand in the records, at the
        sender's run's value, for the stored table at cfg; each opening of a tree has walked
        to the root that the tree's sender sent; W counts the first two chains' trees as the chains
        have roots; each sender's run's value has 32 bytes.
  `CodeOwes .. g h embS embE cfg sb`   **what the walks owe of the oracle functions g**, together
        with the ways embS, embE in which symbols are written into bodies: the node hash
        (`NodeIs`), the leaf hash at each of the three stretches (`LeafIs`) and at the stored table
        (`LeafIsE`).
  `walks_of`   **the four fields**, from the two records, the three chains' values under g, the test
        `shapesFit`, and: the digest of the root to which each opening of a stored table has walked
        is the first of the commitments cms.

One digest cfg stands everywhere: it is the letter cfg of `typeFile` (with which a stored leaf's
typed salt begins), the start of the stored leaves' hashes, and the digest in all vertices' hashes.
A typed query to the node oracle holds no such digest, so under one g `NodeIs` can hold at one cfg
alone: where one g is to serve a key file and a proof file, the two must have one cfg.

`CodeOwes` is a debt on the pair of g and the ways of writing: at ways that forget a symbol's tree,
leaf or column it cannot be met (the head of OnBytes/Maker/LeavesOf.lean). It is all that the WALKS
owe of g; the other fields of `AfterRuns` owe more of g: that the verifier's messages give the draws
as read, and the first chain's seal. The two records must stand at one hash h.

Neither record is shown here. Who shows them: `ReadOwes`, and the premise on the stored tables'
roots, from a reading of the whole file: `readOwes_of_read`, `hroot_of_read`
(OnBytes/Maker/Page/ReadOwed.lean); `hroot_of_read` asks besides that the first of cms is the digest
of the root in item 0 of the second chain's statement. `CodeOwes`: at the family of a page
`codeOwes_gJ` (OnBytes/Maker/Page/CodeAt.lean); at any g that meets a law on the leaf oracle and
`NodeIs`, `codeOwes_rows` (OnBytes/Maker/Page/CodeRows.lean).

To be minded. A leaf query of a stored table holds the position and the column, not the table. So
`LeafIsE` asks one answer of g for all stored tables of one width and one length of a salt: at data
with two such tables of two shapes it can be met only by a collision of h, and `walks_of` then says
nothing (the head of OnBytes/Maker/LeavesOf.lean). Both laws that show `CodeOwes` ask that all
stored tables have the mark, the tree 0, one depth and one length of a salt (`StoredFitE`,
OnBytes/Maker/Page/CodeAt.lean): so two of one width have one shape.
Not claimed. The fields `sealAt` and `accept` of `AfterRuns`: nothing here ties the value of either
chain's seal. That the typing returns a value. Nothing on soundness (index binding included), what a
root fixes, opening-form binding, no two openings of a commitment, correctness of extraction or
whatever else names a committer or a prover.

-/
import OnBytes.Maker.LeavesOf
import OnBytes.Maker.RootsOfTrees

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening Tag)
open _root_.Run _root_.Run.PQ

/-- **What is owed of the file as read.** -/
structure ReadOwes (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) (cfg : ByteArray)
    (W : Three.Whole) (r : Proof.TailRead) : Prop where
  one : ∀ j, OneTable W r j
  walked : ∀ j z, (j, z) ∈ ownRowsW W r → Walked h cfg z
  size : ∀ z ∈ ownRowsW W r, ∀ u ∈ z.2.2.2.seen, u.2.2.size = 32
  seen : LeavesSeen h W r
  tree : ∀ j z, (j, z) ∈ ownRowsW W r → ∃ start, TreeAt W r j z.2.2.root start
  n₁ : W.t₁ = r.first.roots.length
  n₂ : W.t₂ = r.shared.roots.length
  run32 : ∀ j run, runOfTree W r j = some run → run.size = 32
  oneE : OneTableE W r
  walkedE : ∀ t z, (t, z) ∈ storedRowsW W r → Walked h cfg z
  sizeE : ∀ y ∈ storedRowsW W r, ∀ u ∈ y.2.2.2.seen, u.2.2.size = 32
  seenE : LeavesSeenE h cfg W r

section File
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (a : ℕ) (W : Three.Whole)
  {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool) {I X : Type} {L : BatchProtocolWithLeafBody I X}
  (g : Fam (typedOracleFamily 256 (K + 1) L)) (hh : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray)
  (embS : (p : OPos (chainsOf C (WholeD.of a W) tF tJ t3).sh) →
    OSym (chainsOf C (WholeD.of a W) tF tJ t3).sh p → Body L) (embE : SgX → Body L)

/-- **What is owed of the oracle functions.** -/
structure CodeOwes (cfg : ByteArray) (sb : ℕ) : Prop where
  node : NodeIs g hh cfg
  leaf₁ : LeafIs g hh sb C (WholeD.of a W).ds₁ fun p => symb₁ embS (.inr p)
  leaf₂ : LeafIs g hh sb C (WholeD.of a W).ds₂ fun p => symb₂ embS (.inr p)
  leaf₃ : LeafIs g hh sb C (WholeD.of a W).ds₃ fun p => symb₃ embS (.inr p)
  leafE : LeafIsE g hh cfg embE W

variable {t : Tag}
  {embP : PlainPart (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ t3).ann →
    PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t)} {xin : Xi → Option X} {cms : List (Dig 256)}

/-- **The walks of all forests say yes at a value of `typeFile`.** -/
theorem walks_of (sb : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) (salt : ByteArray)
    (path : List ByteArray) (r : Proof.TailRead)
    (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch)
    (h : typeFile C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r = some π) (x : Xi)
    (a' : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₁)
    (b' : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₂)
    (e' : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₃)
    (h₁ : (run₁ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
      (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π).det g = some a')
    (h₂ : (run₂ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
      (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π a').det g = some b')
    (h₃ : (run₃ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
      (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π a' b').det g =
      some e')
    (hshape : shapesFit a W = true) (RO : ReadOwes hh cfg W r)
    (CO : CodeOwes C K a W tF tJ t3 g hh embS embE cfg sb)
    (hroot : ∀ t z, (t, z) ∈ storedRowsW W r → bytesToDig z.2.2.root = cms.getD 0 default) :
      (∀ Fs, forestsB _ (chainsOf C (WholeD.of a W) tF tJ t3).A₁
          (wire₁ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run)) (symb₁ embS) a'.2.1
          (rd₁ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
            (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x π a' b' e')
          (op₁ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) π) = some Fs →
        ∀ T ∈ Fs, walkP g T T.reads = true) ∧
      (∀ Fs, forestsB _ (chainsOf C (WholeD.of a W) tF tJ t3).A₂
          (wire₂ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run)) (symb₂ embS) b'.2.1
          (rd₂ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
            (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x π a' b' e')
          (op₂ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) π) = some Fs →
        ∀ T ∈ Fs, walkP g T T.reads = true) ∧
      (∀ Fs, forestsB _ (chainsOf C (WholeD.of a W) tF tJ t3).A₃
          (wire₃ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run)) (symb₃ embS) e'.2.1
          (rd₃ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
            (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x π a' b' e')
          (op₃ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) π) = some Fs →
        ∀ T ∈ Fs, walkP g T T.reads = true) ∧
      ∀ Fe, forestExt (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).ext embE cms
          (readE (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
            (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x (glue a' b' e').1) π.ext =
          some Fe →
        ∀ T ∈ Fe, walkP g T T.reads = true := by
  obtain ⟨tabs, etab, ht, hE, hx, -, -, -⟩ :=
    typeFile_opens C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r π h
  have O : WalkOwes g hh cfg W r :=
    ⟨RO.one, RO.walked, CO.node, fun j u hu => by
      obtain ⟨y, hy, hu'⟩ := List.mem_flatMap.1 hu
      exact RO.size y (List.mem_filter.1 hy).1 u hu'⟩
  have OE : ExtOwes g hh cfg W r :=
    ⟨RO.oneE, RO.walkedE, CO.node, fun u hu => by
      obtain ⟨y, hy, hu'⟩ := List.mem_flatMap.1 hu
      exact RO.sizeE y hy u hu'⟩
  obtain ⟨hr₁, hr₂, hr₃⟩ := rootsRead_typeFile C K chal a W tF tJ t3 silent run g sb cfg pF pJ p3
    salt path r π h x a' b' e' h₁ h₂ h₃ RO.n₁ RO.n₂ RO.tree
  obtain ⟨w1, w2, w3⟩ := walks_typeFile C K chal a W tF tJ t3 silent run g hh cfg embS sb cfg pF pJ
    p3 salt path r π h x a' b' e' hshape O hr₁ hr₂ hr₃
    (fun tabs' ht' => leavesRead_of g hh C _ 0 _ _ (tabsWFull_row ht') (tabsWFull_holds ht') hshape
      (shape₁ C (WholeD.of a W)) RO.one RO.run32 CO.leaf₁ RO.seen)
    (fun tabs' ht' => leavesRead_of g hh C _ _ _ _ (tabsWFull_row ht') (tabsWFull_holds ht') hshape
      (shape₂ C (WholeD.of a W)) RO.one RO.run32 CO.leaf₂ RO.seen)
    (fun tabs' ht' => leavesRead_of g hh C _ _ _ _ (tabsWFull_row ht') (tabsWFull_holds ht') hshape
      (shape₃ C (WholeD.of a W)) RO.one RO.run32 CO.leaf₃ RO.seen)
  refine ⟨w1, w2, w3, walkE_typeFile C K chal a W tF tJ t3 silent run g hh cfg embE sb cfg pF pJ p3
    salt path r π h x cms (glue a' b' e').1 OE hroot fun p op _ hop => ?_⟩
  rw [hx] at hop
  exact hleaf_of g hh embE (extTabWFull_row hE) (extTabWFull_holds hE) RO.oneE CO.leafE RO.seenE p
    op hop

end File

end OnBytes.Maker
