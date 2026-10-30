-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TypingAt.lean: what a value of the typing of a whole file (`typeFile`,
OnBytes/Maker/TypeFile.lean) is made of, said once for all who go on from it.

The reading r is the three chains as the reader returns them, each round with its openings. (The
shipped program hands the first chain on without its openings, `ChainRead.light`,
OnBytes/Chain/Session.lean; at that lighter record `typeFile` returns nothing wherever the first
chain opens a tree. What is said here is said of the reading before that step.)

  `typeFile_opens`   at a value π: the tables with whole paths have values tabs and etab; π's
                     openings of the stored table are the look-ups in etab; π's openings at each
                     chain's rounds (`op₁`, `op₂`, `op₃`, OnBytes/TypedOracleCompiler/Joined/YesByCuts.lean) are
                     none at the silent round and `opensT` at the stretch, at tabs.
  `opensT_row`       an opening that `opensT` lays at a position, from ONE opening z of the file: z
                     is an opening of the position's tree and lists, at the position's leaf, a
                     column and a salt; the symbol is that column typed; the salt is the sender's
                     run's value and then that salt; the path is read off z's record of vertices,
                     in the form of OnBytes/TypedOracleCompiler/Joined/WalkTable.lean's `tpath`; and z's shape is
                     the shape of the position's tree in the rounds' data.
  `ext_row`          the same for a look-up in the stored table's table.

What is known of the premise that `typeFile` returns a value. At a value of the program's reader it
returns, under the test `okAt`, one number of bytes of a salt in the three plans, and the hypothesis
`SameTwice`: `typeFile_of_readKey`, `typeFile_of_readProof` (OnBytes/Maker/TypeFileOfRead.lean).
The test `typeReturns` (OnBytes/Maker/TypeTest.lean) equals
`(typeFile ..).isSome` (`typeFile_isSome`, OnBytes/Maker/TypeTestLaws.lean). cfg is a letter of
`typeFile` that nothing here ties to the description under which r was read.

Not claimed. Nothing on hashes; nothing on soundness.


-/
import OnBytes.Maker.OpenedWhole
import OnBytes.Maker.TypingFlags
import OnBytes.Maker.TypingPath
import OnBytes.Maker.TablesRow

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening Tag)
open _root_.Run _root_.Run.PQ

/-! ## An opening at a position, from one opening of the file -/

/-- **An opening that `opensT` lays, from one opening of the file.** -/
theorem opensT_row {a : ℕ} {W : Three.Whole} {sb : ℕ} {r : Proof.TailRead}
    {tabs : List (ℕ × List (ℕ × Row3))} (hrow : TabsRow W sb r tabs)
    (htabs : TabsHold W sb r tabs) (hshape : shapesFit a W = true) (C : CK) (ds : List RDT)
    (base : ℕ)
    (hsh : ∀ q, (WholeD.of a W).shape (base + treeAt C ds q) = treeShT ds (treeAt C ds q))
    (q : OPos (uLT C ds)) (op : Opening 256 (OSym (uLT C ds) q))
    (h : opensT C ds base tabs q = some op) :
    ∃ z run s0 c, (base + treeAt C ds q, z) ∈ ownRowsW W r ∧
      (leafAt C ds q, c, s0) ∈ listed z ∧ symT' C ds q c = some op.sym ∧
      runOfTree W r (base + treeAt C ds q) = some run ∧ s0.size = sb ∧
      op.salt = leafSalt run s0 ∧
      op.path = tpath (vertexOf z.1.a z.2.2.seen) z.1.a 0 (leafAt C ds q) ∧
      treeShT ds (treeAt C ds q) = some z.1 := by
  obtain ⟨tab, c, ht, hl, hy⟩ := opensT_some C ds base tabs q op h
  obtain ⟨z, run, s0, hz, hli, hr, hs0, hs, hp⟩ := hrow _ _ _ _ _ _ ht hl
  obtain ⟨t, ht', e1, -⟩ := htabs.row _ z hz
  refine ⟨z, run, s0, c, hz, hli, hy, hr, hs0, hs, ?_, ?_⟩
  · rw [pathFrom_eq hp, tpath_vertexOf]
  · rw [← hsh q, e1]
    exact shapesFit_at hshape ht'

/-- The same for a look-up in the stored table's table. -/
theorem ext_row {a : ℕ} {cfg : ByteArray} {W : Three.Whole} {r : Proof.TailRead}
    {etab : List (ℕ × Row3)} (hrow : ExtRow cfg W r etab) (hext : ExtHolds a W r etab)
    (p : (oneExternalString (2 ^ a) SgX).Pos) (op : Opening 256 SgX)
    (h : atT (fun c => some (p.val, c)) etab p.val = some op) :
    ∃ t z s0 c, (t, z) ∈ storedRowsW W r ∧ (p.val, c, s0) ∈ listed z ∧ op.sym = (p.val, c) ∧
      s0.size = t.salt ∧ op.salt = leafSalt cfg s0 ∧
      op.path = tpath (vertexOf a z.2.2.seen) a 0 p.val ∧ z.1 = t.sh ∧ t.sh.a = a := by
  unfold atT at h
  cases hl : etab.lookup p.val with
  | none => rw [hl] at h; cases h
  | some row =>
    obtain ⟨c, s, pt⟩ := row
    rw [hl] at h
    obtain rfl : (⟨(p.val, c), s, pt⟩ : Opening 256 SgX) = op := Option.some.inj h
    obtain ⟨t, z, s0, hz, hli, hs0, hs, hp⟩ := hrow _ _ _ _ hl
    obtain ⟨e1, e2, -, -⟩ := hext.row t z hz
    have ea : z.1.a = a := by rw [e1, e2]
    refine ⟨t, z, s0, c, hz, hli, rfl, hs0, hs, ?_, e1, e2⟩
    show pt = _
    rw [pathFrom_eq hp, ea, tpath_vertexOf]

/-! ## A value of the typing -/

section File
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (a : ℕ) (W : Three.Whole)
  {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool)

/-- **What a value of `typeFile` is made of.** -/
theorem typeFile_opens (sb : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) (salt : ByteArray)
    (path : List ByteArray) (r : Proof.TailRead)
    (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch)
    (h : typeFile C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r = some π) :
    ∃ tabs etab, tabsWFull W sb r = some tabs ∧ extTabWFull a cfg W r = some etab ∧
      π.ext = (fun p => atT (fun c => some (p.val, c)) etab p.val) ∧
      op₁ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) π =
        behind tF (opensT C (WholeD.of a W).ds₁ 0 tabs) ∧
      op₂ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) π =
        behind tJ (opensT C (WholeD.of a W).ds₂ (WholeD.of a W).t₁ tabs) ∧
      op₃ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) π =
        behind t3 (opensT C (WholeD.of a W).ds₃ ((WholeD.of a W).t₁ + (WholeD.of a W).t₂)
          tabs) := by
  obtain ⟨tabs, ext, ht, he, h'⟩ :=
    typeFile_some C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r π h
  obtain ⟨etab, hE, rfl⟩ := Option.map_eq_some_iff.1 he
  obtain ⟨pl₁, pl₂, pl₃, -, -, -, -, ho⟩ :=
    toBPrfW_parts C (WholeD.of a W) tF tJ t3 pF pJ p3 tabs silent run _ salt path r π h'
  refine ⟨tabs, etab, ht, hE,
    toBPrfW_ext C (WholeD.of a W) tF tJ t3 silent run pF pJ p3 tabs _ salt path r π h', ?_, ?_, ?_⟩
  · unfold op₁
    rw [ho]
    exact funext fun p => opensL_app _ _ p
  · unfold op₂
    rw [ho]
    unfold opensA
    rw [opensR_app]
    exact funext fun p => opensL_app _ _ p
  · unfold op₃
    rw [ho]
    unfold opensA
    rw [opensR_app, opensR_app]
    rfl

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} (g : Fam (typedOracleFamily 256 (K + 1) L)) {t : Tag}
  {embP : PlainPart (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ t3).ann →
    PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t)} {xin : Xi → Option X} {cms : List (Dig 256)}

end File

end OnBytes.Maker
