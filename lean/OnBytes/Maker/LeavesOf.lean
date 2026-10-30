-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/LeavesOf.lean: the premises on the leaves of OnBytes/Maker/WalksTree.lean and
OnBytes/Maker/WalkExt.lean, each cut into a half on the oracle functions and a half on the reading.

These files take: g's leaf hash of the symbol and the salt of an opening that is read is the entry,
at the bottom, of the tree's table of vertices (`LeavesRead`; for the stored table `hleaf`). Two
matters are in that. How a typed query to the leaf oracle is spelled as a hash call: that is a
matter of g. And that the reader's record of vertices holds, at an opened leaf, the format's hash
of the column and the salt as read: that is a matter of the reading. Here they are two premises.

`leafHash h sh start x col s0` (OnBytes/Maker/ReadLeaf.lean) is the format's hash of a leaf, with
the hash h as a letter.

  `LeafIs g h sb C ds emb`   **the half on g**, for a stretch: at a position q of a tree of the
        shape sh, a column of sh.W words that types to the symbol y, a start of 32 bytes and a salt
        of sb bytes: g's leaf hash of the body of y and the typed salt (the start, then the salt) is
        the digest of `leafHash` at q's leaf.
  `LeavesSeen h W r`   **the half on the reading**: each opening of a tree in the file holds, in its
        record, at each listed place, at the bottom level, `leafHash` of the column and the salt
        that are listed there, at the run's value of the tree's sender.
  `leavesRead_of`     **`LeavesRead` from the two.**
  `LeafIsE`, `LeavesSeenE`, `hleaf_of`   the same for the stored table; the start is the digest cfg.
        `LeafIsE` speaks of the stored tables of the data's rounds, of no reading, and of symbols
        that hold their own place.
  `storedW_mem`        a stored table that the file opens is one of these.

`LeafIs` and `LeafIsE` are premises on g AND on the way emb in which symbols are written into
bodies. The right side holds the tree, the leaf and the column. So at a way of writing that forgets
one of these they ask two answers of g at one query, and cannot be met but for a collision of the
hash.
`LeafIsE` speaks of every stored table of the data, and a stored table's symbol holds place and
column alone: so two stored tables of one width and one length of a salt must have one shape.

The other premises of `leavesRead_of`: `TabsRow`, `TabsHold` (both follow where the tables return a
value), the test `shapesFit`, `OneTable`, and that each sender's run's value has 32 bytes.

Not claimed. `LeafIs`, `LeafIsE`, `LeavesSeen`, `LeavesSeenE`. Nothing on soundness
(index binding included), what a root fixes, opening-form binding, no two openings of a commitment,
correctness of extraction or whatever else names a committer or a prover.

-/
import OnBytes.Maker.WalkExt
import OnBytes.Maker.ReadLeaf

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening)
open _root_.Run _root_.Run.PQ _root_.Run.WalkTie

variable {I X : Type} {L : BatchProtocolWithLeafBody I X}

/-! ## The trees of the rounds -/

/-- **The half on g.** -/
def LeafIs {K' : ℕ} (g : Fam (typedOracleFamily 256 K' L))
    (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) (sb : ℕ) (C : CK) (ds : List RDT)
    (emb : (p : OPos (uLT C ds)) → OSym (uLT C ds) p → Body L) : Prop :=
  ∀ q sh col y start s0, treeShT ds (treeAt C ds q) = some sh → col.length = sh.W →
    symT' C ds q col = some y → start.size = 32 → s0.size = sb →
    g OracleName.leaf ⟨emb q y, leafSalt start s0⟩ =
      bytesToDig (leafHash h sh start (leafAt C ds q) col s0)

/-- **The half on the reading.** -/
def LeavesSeen (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) (W : Three.Whole)
    (r : Proof.TailRead) : Prop :=
  ∀ j z, (j, z) ∈ ownRowsW W r → ∃ start, runOfTree W r j = some start ∧
    ∀ x col salt, (x, col, salt) ∈ listed z →
      seenAt z.2.2.seen z.1.a x = some (leafHash h z.1 start x col salt)

/-- **`LeavesRead` from the two halves.** -/
theorem leavesRead_of {K' : ℕ} (g : Fam (typedOracleFamily 256 K' L))
    (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) {a : ℕ} {W : Three.Whole} {sb : ℕ}
    {r : Proof.TailRead} {tabs : List (ℕ × List (ℕ × Row3))} (C : CK) (ds : List RDT) (base : ℕ)
    (emb : (p : OPos (uLT C ds)) → OSym (uLT C ds) p → Body L) (rd : OPos (uLT C ds) → Bool)
    (hrow : TabsRow W sb r tabs) (htabs : TabsHold W sb r tabs) (hshape : shapesFit a W = true)
    (hsh : ∀ q, (WholeD.of a W).shape (base + treeAt C ds q) = treeShT ds (treeAt C ds q))
    (hone : ∀ j, OneTable W r j) (hrun : ∀ j run, runOfTree W r j = some run → run.size = 32)
    (hg : LeafIs g h sb C ds emb) (hs : LeavesSeen h W r) :
    LeavesRead g W r C ds base tabs emb rd := by
  intro q op sh _ hop hT
  obtain ⟨z, run, s0, col, hz, hli, hy, hr, hs0, hsalt, -, hT'⟩ :=
    opensT_row hrow htabs hshape C ds base hsh q op hop
  obtain rfl : z.1 = sh := Option.some.inj (hT'.symm.trans hT)
  obtain ⟨t, -, e1, hok⟩ := htabs.row _ z hz
  have hcol : col.length = z.1.W := by
    rw [e1]
    exact (TieTree.ok_list (asOpenB z) _ _ hok).2.2 col (List.of_mem_zip (listed_col hli)).2
  have hlt : leafAt C ds q < 2 ^ z.1.a :=
    (TieTree.ok_list (asOpenB z) _ _ hok).2.1 _ (List.of_mem_zip (listed_col hli)).1
  obtain ⟨start, hst, hseen⟩ := hs _ z hz
  obtain rfl : start = run := Option.some.inj (hst.symm.trans hr)
  have hv := hseen _ col s0 hli
  have hdp : z.1.a ≠ 0 ∨ leafAt C ds q = 0 := by
    by_cases e : z.1.a = 0
    · right
      rw [e] at hlt
      omega
    · exact Or.inl e
  rw [hsalt, hg q z.1 col op.sym start s0 hT hcol hy (hrun _ _ hr) hs0]
  exact (vertexOf_some (by rw [Nat.sub_zero]; exact seenAt_rec (hone _) hz hdp hv)).symm

/-! ## The stored table -/

/-- The half on g, for the stored tables of the data's rounds: at a place x of the table, a column
of its width and a salt of its length. The symbol holds its own place. -/
def LeafIsE {K' : ℕ} (g : Fam (typedOracleFamily 256 K' L))
    (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) (cfg : ByteArray) (emb : SgX → Body L)
    (W : Three.Whole) : Prop :=
  ∀ d ∈ W.ds₁ ++ (W.ds₂ ++ W.ds₃), ∀ t ∈ d.stored, ∀ x col s0, x < 2 ^ t.sh.a →
    col.length = t.sh.W → s0.size = t.salt →
    g OracleName.leaf ⟨emb (x, col), leafSalt cfg s0⟩ = bytesToDig (leafHash h t.sh cfg x col s0)

/-- A stored table that the file opens is a stored table of a round of the data. -/
theorem storedW_mem {W : Three.Whole} {r : Proof.TailRead} {t : Fmt.Stored} {z : Opened}
    (hz : (t, z) ∈ storedRowsW W r) : ∃ d ∈ W.ds₁ ++ (W.ds₂ ++ W.ds₃), t ∈ d.stored := by
  have key : ∀ (ds : List Three.RDL) (o : Fmt.ChainOut), (t, z) ∈ storedRows ds o →
      ∃ d ∈ ds, t ∈ d.stored := fun ds o hm => by
    obtain ⟨u, hu, hq⟩ := List.mem_flatMap.1 hm
    exact ⟨u.1, (List.of_mem_zip hu).1, (List.of_mem_zip hq).1⟩
  rcases List.mem_append.1 hz with h1 | h1
  · obtain ⟨d, hd, ht⟩ := key _ _ h1
    exact ⟨d, List.mem_append_left _ hd, ht⟩
  · rcases List.mem_append.1 h1 with h2 | h2
    · obtain ⟨d, hd, ht⟩ := key _ _ h2
      exact ⟨d, List.mem_append_right _ (List.mem_append_left _ hd), ht⟩
    · obtain ⟨d, hd, ht⟩ := key _ _ h2
      exact ⟨d, List.mem_append_right _ (List.mem_append_right _ hd), ht⟩

/-- The half on the reading, for the stored table: the start is cfg. -/
def LeavesSeenE (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) (cfg : ByteArray)
    (W : Three.Whole) (r : Proof.TailRead) : Prop :=
  ∀ t z, (t, z) ∈ storedRowsW W r → ∀ x col salt, (x, col, salt) ∈ listed z →
    seenAt z.2.2.seen z.1.a x = some (leafHash h z.1 cfg x col salt)

/-- **The stored table's premise on the leaves from the two halves.** -/
theorem hleaf_of {K' : ℕ} (g : Fam (typedOracleFamily 256 K' L))
    (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) {a : ℕ} {cfg : ByteArray}
    {W : Three.Whole} {r : Proof.TailRead} {etab : List (ℕ × Row3)} (emb : SgX → Body L)
    (hrow : ExtRow cfg W r etab) (hext : ExtHolds a W r etab) (hone : OneTableE W r)
    (hg : LeafIsE g h cfg emb W) (hs : LeavesSeenE h cfg W r)
    (p : (oneExternalString (2 ^ a) SgX).Pos) (op : Opening 256 SgX)
    (hop : atT (fun c => some (p.val, c)) etab p.val = some op) :
    g OracleName.leaf ⟨emb op.sym, op.salt⟩ = vertexOf a (recE W r) 0 p.val := by
  obtain ⟨t, z, s0, col, hz, hli, hsym, hs0, hsalt, -, e1, e2⟩ := ext_row hrow hext p op hop
  obtain ⟨-, -, -, hok⟩ := hext.row t z hz
  have hcol : col.length = t.sh.W :=
    (TieTree.ok_list (asOpenB z) _ _ hok).2.2 col (List.of_mem_zip (listed_col hli)).2
  have hv := hs t z hz _ col s0 hli
  have ea : z.1.a = a := by rw [e1, e2]
  have hlt : p.val < 2 ^ z.1.a :=
    (TieTree.ok_list (asOpenB z) _ _ hok).2.1 _ (List.of_mem_zip (listed_col hli)).1
  have hdp : z.1.a ≠ 0 ∨ p.val = 0 := by
    by_cases e : z.1.a = 0
    · right
      rw [e] at hlt
      omega
    · exact Or.inl e
  have hv' := seenAt_recE hone hz hdp hv
  rw [ea] at hv'
  obtain ⟨d, hd, ht⟩ := storedW_mem hz
  rw [hsym, hsalt, hg d hd t ht p.val col s0 (e1 ▸ hlt) hcol hs0, ← e1]
  exact (vertexOf_some (by rw [Nat.sub_zero]; exact hv')).symm

end OnBytes.Maker
