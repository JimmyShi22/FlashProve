-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Top/IdSeedHasCode.lean: EVERY KEY HAS A CODE: at the input whose code of a typed key is
the commitment ID's string with the record's seed in it (`inputIdS G T M`, IdSeedAt.lean), if the
tables' shape of the ground G leaves room; and at the library's two written grounds it does.

Why. "No two keys have one code" (`inputIdS_oneToOne`, IdSeedAt.lean) holds for nothing at a code
that gives no key a code. A key has a code only within `idOkS` (OnBytes/Tie/IdKeySeed.lean): six
numbers of the shape below 2^64; a configuration's digest and a root of 32 bytes; the bytes that are
hashed within the hash's bound on lengths. At this input none of these tests reads the key: digests
and root have 32 bytes by their types, and the number of bytes hangs on the shape alone: 176, and 24
for each element of the seeds and each answer. So at a given ground every key has a code or none
has.

One definition; statements and proofs.


Main names (namespace `OnBytes.K.Arm`):
  `ShapeRoom s`: the six numbers of the shape s are below 2^64, and 176 + 24 (answers (cubeBits +
    1)) + 24 (2^v answers) is at most 2^32 - 144.
  `idOkS_inputIdS`, `encId_hasCode`, `inputIdS_hasCode`: under `ShapeRoom G.q.link.table` every key
    (c, (root, record)) lies within `idOkS` and has a code: under the written code `encId G T`
    (IdSeedAt.lean), and so at every input whose code of a key that is.
  `room_recordGround`, `room_smallRecordGround`: the shapes of the two written grounds
    (OnBytes/Tie/EntryGrounds.lean: the full size with a record; one small example with a record)
    leave room: by evaluation in Lean's kernel.
  `seedBytes_recordGround`, `seedBytes_smallRecordGround`: at these two grounds the seeds' elements
    take at most 2^28 bytes: the premise on the ground of `idOkS_bytes` and `id_bytes`
    (IdSeedBytes.lean).

Limits.
  * The string's list of told digests is empty at this input.
  * It says that the code is defined, not what is hashed by any program: THAT THE PROGRAMS HASH THIS
    STRING FOR THE ID IS NOT SAID HERE.
  * Nothing says that a key's seed is the hash function's at its root, or that its c is the digest
    of any files.
  * T and M are letters; the code reads neither.
  * No probability; nothing on soundness by itself: it shuts out one way in which "no two keys have
    one code" could hold for nothing. For proofs only; no program imports this file.
-/
import Johnson.TypedOracleCompiler.Top.IdSeedBytes
import OnBytes.Tie.EntryGrounds

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm
open _root_.Compile TypedOracleCompiler.Iop Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (digToBytes size_digToBytes)
open OnBytes.Tie (EntryGround IdKeyS idBytesS idOkS idStrS idCodeS recordGround smallRecordGround)
open OnBytes.RunA (RestR LrG)
open OnBytes.Slice (GE NZ)
open _root_.Run.PQ (SgX)
open VerifiableInference.Rec TypedOracleCompiler.VerifiableInference.Rec
open OnBytes.K OnBytes.K.IdTable
open VerifiableInference VerifiableInference.OnPublicFiles

/-- The tables' shape leaves room for the commitment ID's string with the record's seed in it: its
six numbers are below 2^64, and the bytes that are hashed are within the hash's bound on lengths. -/
def ShapeRoom (s : OnBytes.Params.IndexShape) : Prop :=
  s.code.logN < 2 ^ 64 ∧ s.code.ell < 2 ^ 64 ∧ s.code.r < 2 ^ 64 ∧ s.v < 2 ^ 64 ∧
    s.answers < 2 ^ 64 ∧ s.saltBytes < 2 ^ 64 ∧
    176 + 24 * (s.answers * (s.cubeBits + 1)) + 24 * (2 ^ s.v * s.answers) ≤ 2 ^ 32 - 144

variable (G : EntryGround) {I' X' RI : Type} [Fintype RI] [Nonempty RI] {a : ℕ}
  {Q : InteractiveOracleProof
    (((Fin G.q.link.table.answers → (Fin G.q.link.table.cubeBits → GE) × NZ) ×
        ((Fin G.q.link.table.v → Bool) × Fin G.q.link.table.answers → GE)) ×
      ((Fin G.q.link.table.answers → (Fin G.q.link.table.cubeBits → GE) × NZ) ×
        ((Fin G.q.link.table.v → Bool) × Fin G.q.link.table.answers → GE))) (twoExternalStrings (2 ^ a) SgX)}
  (T : RestR I' X' RI (Fin G.q.link.table.answers → (Fin G.q.link.table.cubeBits → GE) × NZ)
    ((Fin G.q.link.table.v → Bool) × Fin G.q.link.table.answers → GE) a Q)

/-- Where the shape leaves room, every key, as the byte format has it, lies within `idOkS`. -/
theorem idOkS_inputIdS (hG : ShapeRoom G.q.link.table) (c : Dig 256) (k : KeyRoot 256 (LrG T)) :
    idOkS ((spellS G T).keyAt (digToBytes c) [] k) = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hG
  have hs : (idBytesS ((spellS G T).keyAt (digToBytes c) [] k)).size ≤ 2 ^ 32 - 144 := by
    rw [size_idBytesS _ rfl]
    show (digToBytes c).size + (8 + ((digToBytes k.cm).size + (digToBytes c).size + 48)) +
      (8 + 24 * (spellSeed G.q.link.table.cubeBits G.q.link.table.answers k.rcd.1).length) +
      (8 + 24 * (spellAns G.q.link.table.v G.q.link.table.answers k.rcd.2).length) + 8 ≤ _
    rw [size_digToBytes, size_digToBytes, spellSeed_length, spellAns_length]
    omega
  unfold idOkS
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, size_digToBytes c⟩, size_digToBytes k.cm⟩, hs⟩,
    fun _ hb => absurd hb List.not_mem_nil⟩

/-- **Every key has a code**, where the shape leaves room: said of the written code itself. -/
theorem encId_hasCode (hG : ShapeRoom G.q.link.table) (k : Dig 256 × KeyRoot 256 (LrG T)) :
    ∃ code, encId G T k = some code := by
  have e : encId G T k = idCodeS ((spellS G T).keyAt (digToBytes k.1) [] k.2) := rfl
  refine ⟨_root_.Run.bytesToBits (idStrS ((spellS G T).keyAt (digToBytes k.1) [] k.2)), ?_⟩
  rw [e]
  unfold idCodeS
  rw [if_pos (idOkS_inputIdS G T hG k.1 k.2)]

variable (M : IdMoreS G T)

/-- The same at the input whose code of a key it is. -/
theorem inputIdS_hasCode (hG : ShapeRoom G.q.link.table) (k : Dig 256 × KeyRoot 256 (LrG T)) :
    ∃ code, (inputIdS G T M).enc k = some code :=
  encId_hasCode G T hG k

/-- The shape of the ground at the full size with a record leaves room. -/
theorem room_recordGround : ShapeRoom recordGround.q.link.table := by
  unfold ShapeRoom
  decide +kernel

/-- The shape of the ground at the small example with a record leaves room. -/
theorem room_smallRecordGround : ShapeRoom smallRecordGround.q.link.table := by
  unfold ShapeRoom
  decide +kernel

/-- At the full size the seeds' elements take at most 2^28 bytes. -/
theorem seedBytes_recordGround :
    24 * (recordGround.q.link.table.answers * (recordGround.q.link.table.cubeBits + 1)) ≤
      2 ^ 28 := by
  decide +kernel

/-- At the small example the seeds' elements take at most 2^28 bytes. -/
theorem seedBytes_smallRecordGround :
    24 * (smallRecordGround.q.link.table.answers *
      (smallRecordGround.q.link.table.cubeBits + 1)) ≤ 2 ^ 28 := by
  decide +kernel

end OnBytes.K.Arm

#print axioms OnBytes.K.Arm.idOkS_inputIdS
#print axioms OnBytes.K.Arm.encId_hasCode
#print axioms OnBytes.K.Arm.inputIdS_hasCode
#print axioms OnBytes.K.Arm.room_recordGround
#print axioms OnBytes.K.Arm.room_smallRecordGround
#print axioms OnBytes.K.Arm.seedBytes_recordGround
#print axioms OnBytes.K.Arm.seedBytes_smallRecordGround
