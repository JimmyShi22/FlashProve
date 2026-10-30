-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Top/IdSeedBytes.lean: run on bytes, prove on bits: the typed key that is made of 32
bytes cfg, a table t read off a key file and a list l of seeds has a code, and any function g in the
place of the hash sends that code to the format's call 179 over g on the same data as bytes.

Johnson/TypedOracleCompiler/Top/IdSeedAt.lean has a code of the typed key (`encId`): the commitment ID's string,
with the record's seed in it, laid out as a list of bits. A program does not lay out bits: it hashes
bytes. Here the two are tied. The key holds the configuration's digest and no further digest: the
string's last list is empty.

Main names (namespace `OnBytes.K.Arm`):
  `keyB G cfg t l`: the key as bytes (`IdKeyS`, OnBytes/Tie/IdKeySeed.lean): G's tables' shape,
    the configuration's digest cfg, the table t (root and answers) as a key file holds it, the seeds
    l as the program draws them, laid flat; no told digest.
  `keyT G T cfg t l`: the typed key: cfg as 256 bits; t's root as 256 bits; the record: the typed
    form of l (`seedOfC`) and of t's answers (`anT`).
  `keyAt_bytes`: spelled back, the typed key is the key as bytes. Asked: cfg and the root have 32
    bytes; t has the shape's number of answers, each with words below the prime; l has the shape of
    a record's seeds (`SeedsShaped`).
  `enc_bytes`: so the typed key's code is `idCodeS` of the key as bytes.
  `size_idBytesS`, `idOkS_bytes`: the key as bytes has a code, if t was read off a file within the
    program's limit by the program's own reader, cfg has 32 bytes, l has a record's shape, and the
    seeds' elements take at most 2^28 bytes.
  `id_bytes`: THE TIE. Under these premises, at every function g: the typed key has a code, and g
    sends it to `idAtS (oB g)` of the key as bytes, as 256 bits: the format's call 179 over g on
    `idBytesS`. g DOES NO WORK IN IT: the second half holds of every key as bytes, by unfolding
    (`idAtS_eq`). All content is `keyAt_bytes` and `idOkS_bytes`.
What the premise on the seeds' bytes is. "24 s (lg + 1) is at most 2^28" is asked of the ground G,
since we have no bound on the number lg of coordinates from the program's test of a shape that is
small enough: the answers' room in the file bounds 24 s by 2^28, and the hash's bound on lengths is
below 2^32. It can be decided at a written ground.
What is not claimed. cfg AND l ARE FREE: a key file holds neither. That cfg is the digest of any
files, and that l is what the hash function gives at t's name, is not asked: `SeedsShaped` is all
that is asked of l (OnBytes/K/IdSeedSpell.lean has it of what the text of `recordSeeds` returns, at
every plain hash at which it returns). A parser that returns `keyT` at the hash function's own cfg
and l must ask the hash function for both; no parser is written in this file. At the full size one
written reader is shown to return it, where the program's reader reads the table and the drawing
returns l: `key_ownFull` (Johnson/Top/Pub/FrontOwnJoin.lean [not in this library]; over that file's
letters, in whose types laws ride: that these have a member together is not shown there), over
`keyTreeAtFull_reads` (Johnson/Top/Pub/OwnKeyReads.lean [not in this library]). That a program or
its twin computes `idAtS` as its commitment
ID: this file ties `idAtS` to no program. Where a drawing returns nothing there is no l: a text that
lays the empty list there hashes, at a shape with a record, the code of no typed key. `idOkS_bytes`
asks for a file within the limit and for the premise on the seeds' bytes;
Johnson/TypedOracleCompiler/Top/IdSeedHasCode.lean has `idOkS` of every typed key from one condition on the shape,
without either. No probability; nothing on soundness by itself: the file serves completeness, and
the tie from a verifier's yes. For proofs only; the program does not import this file.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.Top.IdSeedAt
import Johnson.TypedOracleCompiler.Top.TieIdBytes
import OnBytes.K.IdTableAnswers
import OnBytes.K.IdTableOk

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm
open _root_.Compile TypedOracleCompiler.Iop Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig digToBytes digToBytes_bytesToDig oB)
open TypedOracleCompiler.Slice (anT seedOfC)
open OnBytes.Tie (EntryGround IdKeyS idBytesS idOkS idStrS idCodeS idAtS idAtS_eq publishedBytesS_eq
  size_tableName)
open OnBytes.RunA (RestR LrG)
open OnBytes.Slice (GE NZ)
open _root_.Run.PQ (SgX)
open VerifiableInference.Rec TypedOracleCompiler.VerifiableInference.Rec
open OnBytes.K OnBytes.K.IdTable
open VerifiableInference VerifiableInference.OnPublicFiles

/-- The number of bytes that the ID hashes, at a key without told digests. -/
theorem size_idBytesS (K : IdKeyS) (hT : K.told = []) :
    (idBytesS K).size = K.base.2.1.size + (8 + (K.base.2.2.root.size + K.base.2.1.size + 48)) +
      (8 + 24 * K.seed.length) + (8 + 24 * K.base.2.2.answers.length) + 8 := by
  unfold idBytesS
  rw [publishedBytesS_eq, hT]
  unfold Fmt.list Key.nameOf
  simp only [ByteArray.size_append, Fmt.size_text, size_tableName, Fmt.size_u64n, Fmt.size_exts,
    List.length_map, List.map_nil, Fmt.cat_nil, ByteArray.size_empty]

variable (G : EntryGround) {I' X' RI : Type} [Fintype RI] [Nonempty RI] {a : ℕ}
  {Q : InteractiveOracleProof
    (((Fin G.q.link.table.answers → (Fin G.q.link.table.cubeBits → GE) × NZ) ×
        ((Fin G.q.link.table.v → Bool) × Fin G.q.link.table.answers → GE)) ×
      ((Fin G.q.link.table.answers → (Fin G.q.link.table.cubeBits → GE) × NZ) ×
        ((Fin G.q.link.table.v → Bool) × Fin G.q.link.table.answers → GE))) (twoExternalStrings (2 ^ a) SgX)}
  (T : RestR I' X' RI (Fin G.q.link.table.answers → (Fin G.q.link.table.cubeBits → GE) × NZ)
    ((Fin G.q.link.table.v → Bool) × Fin G.q.link.table.answers → GE) a Q)
  (cfg : ByteArray) (t : OnBytes.Params.TableName) (l : List (List E × E))

/-- The key as bytes: the shape, the configuration's digest, the table, the seeds laid flat; no told
digest. -/
def keyB : IdKeyS := ⟨(G.q.link.table, cfg, t), l.flatMap fun y => y.1 ++ [y.2], []⟩

/-- The root and the record of the typed key. -/
def keyR : KeyRoot 256 (LrG T) :=
  ⟨bytesToDig t.root, (seedOfC G.q.link.table.cubeBits G.q.link.table.answers l,
    anT G.q.link.table.v G.q.link.table.answers (t.answers.map E.triple))⟩

/-- The typed key: the configuration's digest; the root; the record. -/
def keyT : Dig 256 × KeyRoot 256 (LrG T) := (bytesToDig cfg, keyR G T t l)

variable {cfg t l}

/-- **Spelled back, the typed key is the key as bytes.** -/
theorem keyAt_bytes (hc : cfg.size = 32) (hr : t.root.size = 32)
    (ha : t.answers.length = 2 ^ G.q.link.table.v * G.q.link.table.answers)
    (hk : ∀ x ∈ t.answers, okE x = true)
    (hl : SeedsShaped G.q.link.table.cubeBits G.q.link.table.answers l) :
    (spellS G T).keyAt (digToBytes (bytesToDig cfg)) [] (keyR G T t l) = keyB G cfg t l := by
  have e1 := digToBytes_bytesToDig cfg hc
  have e2 := digToBytes_bytesToDig t.root hr
  have e3 : spellAns G.q.link.table.v G.q.link.table.answers
      (anT G.q.link.table.v G.q.link.table.answers (t.answers.map E.triple)) = t.answers :=
    spell_triples G.q.link.table.v G.q.link.table.answers t.answers ha hk
  have e4 : spellSeed G.q.link.table.cubeBits G.q.link.table.answers
      (seedOfC G.q.link.table.cubeBits G.q.link.table.answers l) =
      l.flatMap fun y => y.1 ++ [y.2] := by
    unfold spellSeed
    rw [spell_seedOfC G.q.link.table.cubeBits G.q.link.table.answers l hl]
  have key : (⟨(G.q.link.table, digToBytes (bytesToDig cfg),
        ⟨digToBytes (bytesToDig t.root), spellAns G.q.link.table.v G.q.link.table.answers
          (anT G.q.link.table.v G.q.link.table.answers (t.answers.map E.triple))⟩),
      spellSeed G.q.link.table.cubeBits G.q.link.table.answers
        (seedOfC G.q.link.table.cubeBits G.q.link.table.answers l), []⟩ : IdKeyS) =
      ⟨(G.q.link.table, cfg, ⟨t.root, t.answers⟩), l.flatMap fun y => y.1 ++ [y.2], []⟩ := by
    rw [e1, e2, e3, e4]
  exact key

/-- So the typed key's code is the code of the key as bytes. -/
theorem enc_bytes (hc : cfg.size = 32) (hr : t.root.size = 32)
    (ha : t.answers.length = 2 ^ G.q.link.table.v * G.q.link.table.answers)
    (hk : ∀ x ∈ t.answers, okE x = true)
    (hl : SeedsShaped G.q.link.table.cubeBits G.q.link.table.answers l) :
    encId G T (keyT G T cfg t l) = idCodeS (keyB G cfg t l) :=
  congrArg idCodeS (keyAt_bytes G T hc hr ha hk hl)

/-- **The key as bytes has a code**, if the program's own reader has read t off a file within the
program's limit, cfg has 32 bytes, l has a record's shape, and the seeds' elements take at most 2^28
bytes. -/
theorem idOkS_bytes {file : ByteArray} {j : ℕ}
    (hrd : Key.readTable G.q.link.table cfg file = .ok (t, j)) (hc : cfg.size = 32)
    (hf : file.size ≤ Shell.fileLimit)
    (hl : SeedsShaped G.q.link.table.cubeBits G.q.link.table.answers l)
    (hsd : 24 * (G.q.link.table.answers * (G.q.link.table.cubeBits + 1)) ≤ 2 ^ 28) :
    idOkS (keyB G cfg t l) = true := by
  obtain ⟨hs, hr, ha⟩ := key_readTable_ok _ _ _ _ _ hrd
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := shape_lt _ hs
  have hn : (l.flatMap fun y => y.1 ++ [y.2]).length =
      G.q.link.table.answers * (G.q.link.table.cubeBits + 1) := by
    rw [flat_length G.q.link.table.cubeBits l fun y hy => (hl.2 y hy).1, hl.1]
  have h7 : (idBytesS (keyB G cfg t l)).size ≤ 2 ^ 32 - 144 := by
    rw [size_idBytesS _ rfl]
    show cfg.size + (8 + (t.root.size + cfg.size + 48)) +
      (8 + 24 * (l.flatMap fun y => y.1 ++ [y.2]).length) + (8 + 24 * t.answers.length) + 8 ≤ _
    rw [hn]
    unfold Shell.fileLimit at hf
    omega
  unfold idOkS
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, hc⟩, hr⟩, h7⟩, fun _ hb => absurd hb List.not_mem_nil⟩

variable (M : IdMoreS G T)

/-- **RUN ON BYTES, PROVE ON BITS.** At every function g: the typed key has a code, and g sends it
to `idAtS (oB g)` of the key as bytes: the format's call 179 over g on `idBytesS`. cfg and l are
free, and `idAtS` is tied to no program here. -/
theorem id_bytes (g : ZKCP.Oracle 256) {file : ByteArray} {j : ℕ}
    (hrd : Key.readTable G.q.link.table cfg file = .ok (t, j)) (hc : cfg.size = 32)
    (hf : file.size ≤ Shell.fileLimit)
    (hl : SeedsShaped G.q.link.table.cubeBits G.q.link.table.answers l)
    (hsd : 24 * (G.q.link.table.answers * (G.q.link.table.cubeBits + 1)) ≤ 2 ^ 28) :
    ∃ code, (inputIdS G T M).enc (keyT G T cfg t l) = some code ∧
      g code = bytesToDig (idAtS (oB g) (keyB G cfg t l)) := by
  obtain ⟨-, hr, -⟩ := key_readTable_ok _ _ _ _ _ hrd
  obtain ⟨ha, hk⟩ := answers_of_keyReadTable _ _ _ _ _ hrd
  have hok := idOkS_bytes G hrd hc hf hl hsd
  refine ⟨_root_.Run.bytesToBits (idStrS (keyB G cfg t l)), ?_, ?_⟩
  · have e : (inputIdS G T M).enc (keyT G T cfg t l) = idCodeS (keyB G cfg t l) :=
      enc_bytes G T hc hr ha hk hl
    rw [e]
    unfold idCodeS
    rw [if_pos hok]
  · rw [idAtS_eq]
    exact (bytesToDig_digToBytes _).symm

end OnBytes.K.Arm

#print axioms OnBytes.K.Arm.keyAt_bytes
#print axioms OnBytes.K.Arm.enc_bytes
#print axioms OnBytes.K.Arm.idOkS_bytes
#print axioms OnBytes.K.Arm.id_bytes
