-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/WalkExt.lean: the walk of the stored table's forest says yes at a value of the typing
of a whole file, under named premises.

OnBytes/TypedOracleCompiler/Joined/K/Left.lean asks, among what is left for a yes of a file's verifier, that the
walk of each forest of the external strings ends, under the oracle functions g, in its roots (the
field `walkE` of `AfterRuns`). A file of OnBytes/Maker/ has one external string, the stored table,
and its wire record (`weOne`, OnBytes/Maker/Wire.lean) has all its checks walked together: one
forest of one tree. As for the trees of the rounds (OnBytes/Maker/WalksTree.lean), the walk says
yes because the checks are read off one consistent table of vertices: the records of all openings
of a stored table in the file, in a row.

  `recE W r`         the records of vertices of all openings of stored tables in the file, in a row.
  `OneTableE`, `seenAt_recE`   as `OneTable`, `seenAt_rec` (OnBytes/Maker/WalksAt.lean).
  `ExtOwes g h cfg W r`   what is owed: two openings hold one value at each vertex; each opening is
                     what the reader of an opening has handed out; g's node hash is the format's
                     vertex hash; each value in a record has 32 bytes.
  `walkE_table`      **the walk says yes**, at the look-ups in a table with `ExtRow` and `ExtHolds`.
  `walkE_typeFile`   **the field `walkE` at a value of `typeFile`.**

The premises, none shown here. `ExtOwes`. `hroot`: the digest of the root to which the reader's walk
led, in each opening of a stored table, is the first of the commitments cms. `hleaf`: g's leaf hash
of the symbol and the salt of an opening that is read is the table's entry at the bottom.
Who shows them: `walks_of` (OnBytes/Maker/WalksOf.lean) makes `ExtOwes` of its two records
`ReadOwes` and `CodeOwes`; `hleaf_of` (OnBytes/Maker/LeavesOf.lean) has `hleaf`; `readOwes_of_read`
and `hroot_of_read` (OnBytes/Maker/Page/ReadOwed.lean) have `ReadOwes` and `hroot` from a reading of
the whole file. Two debts are not paid by the reading alone: that `typeFile` returns π
(`typeFile_of_readKey`, `typeFile_of_readProof`, OnBytes/Maker/TypeFileOfRead.lean, have it under
`SameTwice`; `returns_or_collides`, OnBytes/Maker/Page/ReturnsOrCollide.lean, has it or
`CollidesIn`), and `CodeOwes`, which is on g.

A warning. Two digests are letters here: cfg, with which `typeFile` begins a stored leaf's typed
salt, and cfg', which stands in the vertices' hashes (`NodeIs`, `Walked`). At a real file they are
one digest: the shipped reader lays one digest as the stored leaves' start and in the vertices'
hashes. Nothing in these premises asks it. OnBytes/Maker/WalksOf.lean has the law with one letter
(`walks_of`): that is the one to quote.
Not claimed. That the typing returns a value. Nothing on soundness (index binding included), what a
root fixes, opening-form binding, no two openings of a commitment, correctness of extraction or
whatever else names a committer or a prover.

-/
import OnBytes.Maker.WalksFile

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening)
open _root_.Run _root_.Run.PQ

variable {I X : Type} {L : BatchProtocolWithLeafBody I X}

/-! ## The table of the stored table -/

/-- The records of vertices of all openings of stored tables in the file, in a row. -/
def recE (W : Three.Whole) (r : Proof.TailRead) : List (ℕ × ℕ × ByteArray) :=
  (storedRowsW W r).flatMap (·.2.2.2.seen)

theorem mem_recE {W : Three.Whole} {r : Proof.TailRead} {t : Fmt.Stored} {z : Opened}
    (hz : (t, z) ∈ storedRowsW W r) {u : ℕ × ℕ × ByteArray} (hu : u ∈ z.2.2.seen) :
    u ∈ recE W r :=
  List.mem_flatMap.2 ⟨(t, z), hz, hu⟩

/-- **A hypothesis on a file as read**: two openings of stored tables hold one value at each vertex
below the top, and at the top's first place. -/
def OneTableE (W : Three.Whole) (r : Proof.TailRead) : Prop :=
  ∀ y ∈ storedRowsW W r, ∀ y' ∈ storedRowsW W r, ∀ d p v v', (d ≠ 0 ∨ p = 0) →
    seenAt y.2.2.2.seen d p = some v → seenAt y'.2.2.2.seen d p = some v' → v = v'

theorem seenAt_recE {W : Three.Whole} {r : Proof.TailRead} {t : Fmt.Stored} {z : Opened}
    (hone : OneTableE W r) (hz : (t, z) ∈ storedRowsW W r) {d p : ℕ} {v : ByteArray}
    (hdp : d ≠ 0 ∨ p = 0) (h : seenAt z.2.2.seen d p = some v) :
    seenAt (recE W r) d p = some v := by
  unfold recE
  exact seenAt_flat (fun y : Fmt.Stored × Opened => y.2.2.2.seen) d p v (storedRowsW W r)
    ⟨(t, z), hz, h⟩ fun y hy v' hv' => hone y hy (t, z) hz d p v' v hdp hv' h

/-- What is owed for the stored table. -/
structure ExtOwes {K' : ℕ} (g : Fam (typedOracleFamily 256 K' L))
    (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) (cfg : ByteArray) (W : Three.Whole)
    (r : Proof.TailRead) : Prop where
  one : OneTableE W r
  walked : ∀ t z, (t, z) ∈ storedRowsW W r → Walked h cfg z
  node : NodeIs g h cfg
  size : ∀ u ∈ recE W r, u.2.2.size = 32

section Walk
variable {K' : ℕ} (g : Fam (typedOracleFamily 256 K' L)) (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray)
  (cfg : ByteArray) {a : ℕ} {cfgS : ByteArray} {W : Three.Whole} {r : Proof.TailRead}
  {etab : List (ℕ × Row3)}

/-- **The walk of the stored table's forest says yes.** -/
theorem walkE_table (hrow : ExtRow cfgS W r etab) (hext : ExtHolds a W r etab)
    (O : ExtOwes g h cfg W r) (emb : SgX → Body L) (cms : List (Dig 256))
    (rd : (oneExternalString (2 ^ a) SgX).Pos → Bool)
    (hroot : ∀ t z, (t, z) ∈ storedRowsW W r → bytesToDig z.2.2.root = cms.getD 0 default)
    (hleaf : ∀ p op, rd p = true → atT (fun c => some (p.val, c)) etab p.val = some op →
      g OracleName.leaf ⟨emb op.sym, op.salt⟩ = vertexOf a (recE W r) 0 p.val)
    (Fe : List (Forest 256 L))
    (hF : forestExt (weOne a) emb cms rd (fun p => atT (fun c => some (p.val, c)) etab p.val) =
      some Fe) :
    ∀ T ∈ Fe, walkP g T T.reads = true := by
  intro T hT
  obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.1 hF
  obtain rfl : T = ⟨a, fun t => cms.getD t default, cs⟩ := List.mem_singleton.1 hT
  have anat : ∀ e ∈ cs, ∃ (p : (oneExternalString (2 ^ a) SgX).Pos) (op : Opening 256 SgX) (t : Fmt.Stored)
      (z : Opened), rd p = true ∧ atT (fun c => some (p.val, c)) etab p.val = some op ∧
      e = (0, ⟨⟨emb op.sym, op.salt⟩, p.val, op.path, cms.getD 0 default, a⟩) ∧
      (t, z) ∈ storedRowsW W r ∧ p.val ∈ z.2.1 ∧ z.1.a = a ∧
      pathFrom a z.2.2.seen p.val = some op.path := by
    intro e he
    obtain ⟨p, op, -, hr, hg, rfl⟩ := inv_checksExtW (weOne a) emb cms rd _ _ cs hcs e he
    have hg' := hg
    unfold atT at hg'
    cases hl : etab.lookup p.val with
    | none => rw [hl] at hg'; cases hg'
    | some row =>
      obtain ⟨c, s, pt⟩ := row
      rw [hl] at hg'
      obtain rfl : (⟨(p.val, c), s, pt⟩ : Opening 256 SgX) = op := Option.some.inj hg'
      obtain ⟨t, z, s0, hz, hli, -, -, hp⟩ := hrow _ _ _ _ hl
      obtain ⟨e1, e2, -, -⟩ := hext.row t z hz
      have ea : z.1.a = a := by rw [e1, e2]
      exact ⟨p, _, t, z, hr, hg, rfl, hz, (List.of_mem_zip (listed_col hli)).1, ea, ea ▸ hp⟩
  have idx : ∀ x ∈ Forest.idx (⟨a, fun t => cms.getD t default, cs⟩ : Forest 256 L),
      ∃ t z, (t, z) ∈ storedRowsW W r ∧ x ∈ z.2.1 ∧ z.1.a = a := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    obtain ⟨p, op, t, z, -, -, rfl, hz, hm, ea, -⟩ := anat e he
    exact ⟨t, z, hz, by simpa using hm, ea⟩
  refine walk_of_table (V := vertexOf a (recE W r)) ⟨fun e he => ?_, fun e he => ?_,
    fun m hm i hi => ?_, fun m hm => ?_⟩
  · obtain ⟨p, op, t, z, hr, hg, rfl, -, -, -, -⟩ := anat e he
    show g OracleName.leaf ⟨emb op.sym, op.salt⟩ = vertexOf a (recE W r) 0 (0 * 2 ^ a + p.val)
    rw [Nat.zero_mul, Nat.zero_add]
    exact hleaf p op hr hg
  · obtain ⟨p, op, t, z, -, -, rfl, hz, -, -, hp⟩ := anat e he
    show op.path = tpath (vertexOf a (recE W r)) a 0 (0 * 2 ^ a + p.val)
    rw [Nat.zero_mul, Nat.zero_add,
      pathFrom_eq (pathFrom_mono (fun d q v hd hv => seenAt_recE O.one hz (Or.inl hd) hv) hp),
      tpath_vertexOf]
  · obtain ⟨x, hx, rfl⟩ := mem_upN m _ i hi
    obtain ⟨t, z, hz, hxz, rfl⟩ := idx x hx
    have hW := O.walked t z hz
    have hm' : m < z.1.a := hm
    obtain ⟨l, rr, a1, a2, a3⟩ := walked_step h cfg hW x hxz m hm'
    have hlow : z.1.a - m ≠ 0 := by omega
    have htop : z.1.a - (m + 1) ≠ 0 ∨ x / 2 ^ m / 2 = 0 := by
      by_cases e : m + 1 = z.1.a
      · right
        have hlt : x < 2 ^ (m + 1) := by rw [e]; exact walked_lt h cfg hW x hxz
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
        exact Nat.div_eq_of_lt hlt
      · left
        omega
    rw [vertexOf_some (seenAt_recE O.one hz (Or.inl hlow) a1),
      vertexOf_some (seenAt_recE O.one hz (Or.inl hlow) a2),
      vertexOf_some (seenAt_recE O.one hz htop a3),
      O.node l rr (O.size _ (mem_recE hz (seenAt_mem a1))) (O.size _ (mem_recE hz (seenAt_mem a2)))]
  · obtain ⟨x, hx, rfl⟩ := mem_upN _ _ m hm
    obtain ⟨t, z, hz, hxz, rfl⟩ := idx x hx
    have hW := O.walked t z hz
    show vertexOf z.1.a (recE W r) z.1.a (x / 2 ^ z.1.a) = cms.getD (x / 2 ^ z.1.a) default
    rw [Nat.div_eq_of_lt (walked_lt h cfg hW x hxz), ← hroot t z hz]
    exact vertexOf_some (by
      rw [Nat.sub_self]
      exact seenAt_recE O.one hz (Or.inr rfl) (walked_nodes h cfg hW).2)

end Walk

section File
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (a : ℕ) (W : Three.Whole)
  {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool) (g : Fam (typedOracleFamily 256 (K + 1) L))
  (hh : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) (cfg' : ByteArray) (embE : SgX → Body L)

/-- **The walk of the stored table's forest, at a value of `typeFile`.** ρ: the verifier's messages
that the three chains have yielded. -/
theorem walkE_typeFile (sb : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) (salt : ByteArray)
    (path : List ByteArray) (r : Proof.TailRead)
    (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch)
    (h : typeFile C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r = some π) (x : Xi)
    (cms : List (Dig 256)) (ρ : Rho (chainsOf C (WholeD.of a W) tF tJ t3).sh)
    (O : ExtOwes g hh cfg' W r)
    (hroot : ∀ t z, (t, z) ∈ storedRowsW W r → bytesToDig z.2.2.root = cms.getD 0 default)
    (hleaf : ∀ p op, readE (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
        (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x ρ p = true → π.ext p = some op →
      g OracleName.leaf ⟨embE op.sym, op.salt⟩ = vertexOf a (recE W r) 0 p.val) :
    ∀ Fe, forestExt (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).ext embE cms
        (readE (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x ρ) π.ext = some Fe →
      ∀ T ∈ Fe, walkP g T T.reads = true := by
  obtain ⟨tabs, etab, -, hE, hx, -, -, -⟩ :=
    typeFile_opens C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r π h
  intro Fe hF
  rw [hx] at hF hleaf
  exact walkE_table g hh cfg' (extTabWFull_row hE) (extTabWFull_holds hE) O embE cms _ hroot hleaf
    Fe hF

end File

end OnBytes.Maker
