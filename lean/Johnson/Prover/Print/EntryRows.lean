-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/EntryRows.lean: the maker of what the verifier is handed for the entry file
(`laidOf`, Johnson/PV/EntryInOf.lean), at bytes that were written (`wrLeaf`,
Johnson/Prover/Print/LeafBytes.lean; `wrSeeds`, OnBytes/Prover/Print/Bytes.lean): it does not
refuse, all four of its judged rows say yes, and what it lays is the written file's chain and
tables.

Main names (namespace `Johnson.Prover.Print`).
  `laidOf_wr`       at every parsed leaf file L with `LeafP.WF` and every list of seeds that the
                    reader takes: if the configuration's digest has 32 bytes, both tables have
                    2^v * s answers, there are s seeds of lg coordinates and as many rounds as are
                    asked, then `laidOf` gives a value whose rows all say yes, and whose fields are
                    L's
  `rows_entryOf`    the same at the parsed leaf file of a typed proof string (`entryOf`,
                    Johnson/Prover/Print/Entry.lean), with the number of the data's rounds

Limits. The rows entryIn 1 to 4 alone: the two rows that hold the leaf file against the parsed key
file (`tieRows`, Johnson/PV/EntryInKey.lean) are not spoken of. The record that is laid is said as
`recOne` of the written answers and seeds; nothing says that it is any committer's. No prover, no
oracle, no verifier.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Print.Entry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Print
open _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (View CK XO)
open _root_.Run (bytesToDig)
open OnBytes.Flat (linkSkeletonOfRoundData)
open PV.EntryInOf (LeafP Laid laidOf chainOut tabOwn tabStored)
open OnBytes.Prover.Print (wrSeeds okSeed readSeeds_wrSeeds)

/-- **The maker takes what was written, and all its rows say yes.** -/
theorem laidOf_wr :
  ∀ (v lg s rounds : ℕ) (c : ByteArray) (L : LeafP)
    (sd : List (List _root_.Fmt.Ext × _root_.Fmt.Ext)),
  L.WF → sd.length < 2 ^ 64 → (∀ y ∈ sd, okSeed y) → c.size = 32 →
  L.answers.length = 2 ^ v * s → L.answers0.length = 2 ^ v * s →
  sd.length = s → (∀ y ∈ sd, y.1.length = lg) → L.rounds.length = rounds →
  ∃ m : Laid v lg s, laidOf v lg s rounds c (wrLeaf L) (wrSeeds sd) = .ok m ∧ m.ok = true ∧
    m.L = L ∧ m.cm' = bytesToDig L.root ∧
    m.rcd' = OnBytes.K.recOne v lg s ⟨L.root, L.answers.map OnBytes.E.ofTriple⟩
      (sd.map fun y => (y.1.map OnBytes.E.ofTriple, OnBytes.E.ofTriple y.2)) ∧
    m.cfg = c ∧ m.o = chainOut L ∧ m.tab = tabOwn L ∧ m.tx = tabStored L := by
  intro v lg s rounds c L sd hL h1 h2 hc ha ha0 hs hlg hr
  have key : ∀ r, r = laidOf v lg s rounds c (wrLeaf L) (wrSeeds sd) →
      ∃ m : Laid v lg s, r = .ok m ∧ m.ok = true ∧ m.L = L ∧ m.cm' = bytesToDig L.root ∧
        m.rcd' = OnBytes.K.recOne v lg s ⟨L.root, L.answers.map OnBytes.E.ofTriple⟩
          (sd.map fun y => (y.1.map OnBytes.E.ofTriple, OnBytes.E.ofTriple y.2)) ∧
        m.cfg = c ∧ m.o = chainOut L ∧ m.tab = tabOwn L ∧ m.tx = tabStored L := by
    intro r e
    unfold laidOf at e
    rw [rdLeaf_wrLeaf L hL, readSeeds_wrSeeds sd h1 h2] at e
    refine ⟨_, e, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    simp only [Laid.ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq,
      List.all_eq_true]
    refine ⟨⟨⟨⟨⟨hL.root0, hL.root⟩, hL.run⟩, hc⟩, ?_⟩, ⟨ha, ha0⟩, ⟨hs, hlg⟩, hr⟩
    intro x hx d hd
    rcases List.mem_append.1 hx with hx | hx
    · rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨t, ht, hxt⟩ := List.mem_flatMap.1 hx
        exact ((hL.trees t ht).2.2 x hxt).path d hd
      · exact (hL.stored0 x hx).path d hd
    · exact (hL.stored1 x hx).path d hd
  exact key _ rfl

section
variable (C : CK) (ds : List PQ.RD) (a : ℕ) (xs : List XO) {X : Type} (dec : X → View → Bool)

/-- **The same at the parsed leaf file of a typed proof string.** -/
theorem rows_entryOf :
  ∀ (v lg s : ℕ) (cfg root0 : ByteArray) (answers0 : List (UInt64 × UInt64 × UInt64))
    (root : ByteArray) (answers : List (UInt64 × UInt64 × UInt64))
    (π : OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up) (sd : List (List _root_.Fmt.Ext × _root_.Fmt.Ext)),
  RootsFitL ds → PrintableL C ds a xs dec cfg π →
  SizesL C ds a xs dec root0 answers0 root answers π →
  sd.length < 2 ^ 64 → (∀ y ∈ sd, okSeed y) →
  answers.length = 2 ^ v * s → answers0.length = 2 ^ v * s →
  sd.length = s → (∀ y ∈ sd, y.1.length = lg) →
  ∃ m : Laid v lg s,
    laidOf v lg s ds.length cfg (wrLeaf (entryOf C ds a xs dec root0 answers0 root answers π))
      (wrSeeds sd) = .ok m ∧ m.ok = true ∧
    m.L = entryOf C ds a xs dec root0 answers0 root answers π ∧ m.cm' = bytesToDig root ∧
    m.rcd' = OnBytes.K.recOne v lg s ⟨root, answers.map OnBytes.E.ofTriple⟩
      (sd.map fun y => (y.1.map OnBytes.E.ofTriple, OnBytes.E.ofTriple y.2)) ∧
    m.cfg = cfg ∧ m.o = chainOut (entryOf C ds a xs dec root0 answers0 root answers π) ∧
    m.tab = tabOwn (entryOf C ds a xs dec root0 answers0 root answers π) ∧
    m.tx = tabStored (entryOf C ds a xs dec root0 answers0 root answers π) :=
  fun v lg s cfg root0 answers0 root answers π sd hf hp hz h1 h2 ha ha0 hs hlg =>
    laidOf_wr v lg s ds.length cfg _ sd
      (wf_entryOf C ds a xs dec cfg root0 answers0 root answers π hf hp hz) h1 h2 hp.cfg32 ha ha0 hs
      hlg (length_roundsOfS C ds π.roots π.plains.2)

end

end Johnson.Prover.Print
