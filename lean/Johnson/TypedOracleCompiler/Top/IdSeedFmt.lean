-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Top/IdSeedFmt.lean: where a typed key has a code, that code is the bits of the string
that Lean's text of the format's rule for the commitment ID (`Fmt.publishedBytes` under the call
179) hashes at the key's own four arguments and the empty last list. No hypothesis beyond "has a
code" and what the parameters' types hold; at the two written sets of fixed public parameters every
key has one.

What this file states. The code of the typed key that is defined in Lean (`encId`,
Johnson/TypedOracleCompiler/Top/IdSeedAt.lean) is, where a key has a code, the bits of the string of the call 179 on
`Fmt.publishedBytes` (Fmt/Rules4.lean) at the key's c as 32 bytes, the name of the table, the
elements of the key's seed, the key's answers and the empty last list (`encId_fmt_of`); and every
function g sends it to `Fmt.publishedIDW`, the format's rule for the commitment ID in Lean, at the
hash over g (`encId_rule`). `encId_fmt_bytes` is the equation at the typed key that is made of 32
bytes cfg, a table t read off a key file and a list l of seeds (`keyT`,
Johnson/TypedOracleCompiler/Top/IdSeedBytes.lean). `id_fmt` is `id_bytes` (Johnson/TypedOracleCompiler/Top/IdSeedBytes.lean) with
`Fmt.publishedIDW` at the hash over g in the place of `idAtS`, and no more.

Under which hypotheses. `encId_fmt_of` and `encId_rule` hold for EVERY typed key, with no premise
beyond "has a code" and what the parameters' types hold. `encId_fmt`: at fixed public parameters
whose shape leaves room (`ShapeRoom`, Johnson/TypedOracleCompiler/Top/IdSeedHasCode.lean) every typed key has that
code. `encId_fmt_written`: so at `recordGround` and at `smallRecordGround`. `encId_fmt_bytes`'s and
`id_fmt`'s premises are `id_bytes`'s.

What it does not show. These are equations between Lean texts: they check nothing against the
format's page or the programs; what ties `Fmt.publishedIDW` to the page is three known answers in
Fmt/Rules4.lean (#guard; of `Fmt.publishedID`, which is by definition `Fmt.publishedIDW` at the
format's own hash; each at the empty last list): tests, no theorem. That a program, or its Lean
text, calls `Fmt.publishedBytes` at the hash function's own digest and seeds and at the empty list
is not said here. In the first four statements the key's c and its seed are any, and in
`encId_fmt_bytes` and `id_fmt` cfg is any 32 bytes at which `Key.readTable` returns t and l any list
of the record's shape: that c is the digest of any files, or the seed the hash function's at the
table's name, is for the checks to test. `encId_fmt_of` and `encId_rule` hold vacuously where no key
has a code: they claim nothing there. T is a parameter: the code does not read it, the key's type
does; that a T exists at written fixed public parameters is not shown here. No probability; nothing
on soundness by itself. For proofs only; no program imports this file.


-/
import Johnson.TypedOracleCompiler.Top.IdSeedHasCode
import OnBytes.Tie.IdKeySeedFmt

set_option autoImplicit false

namespace OnBytes.K.Arm
open _root_.Compile TypedOracleCompiler.Iop Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig digToBytes oB)
open OnBytes.Tie (EntryGround IdKeyS idBytesS idOkS idStrS idCodeS idAtS idAtS_eq recordGround
  smallRecordGround)
open OnBytes.RunA (RestR LrG)
open OnBytes.Slice (GE NZ)
open _root_.Run.PQ (SgX)
open VerifiableInference.Rec TypedOracleCompiler.VerifiableInference.Rec
open OnBytes.K OnBytes.K.IdTable
open VerifiableInference VerifiableInference.OnPublicFiles

variable (G : EntryGround) {I' X' RI : Type} [Fintype RI] [Nonempty RI] {a : ℕ}
  {Q : InteractiveOracleProof
    (((Fin G.q.link.table.answers → (Fin G.q.link.table.cubeBits → GE) × NZ) ×
        ((Fin G.q.link.table.v → Bool) × Fin G.q.link.table.answers → GE)) ×
      ((Fin G.q.link.table.answers → (Fin G.q.link.table.cubeBits → GE) × NZ) ×
        ((Fin G.q.link.table.v → Bool) × Fin G.q.link.table.answers → GE))) (twoExternalStrings (2 ^ a) SgX)}
  (T : RestR I' X' RI (Fin G.q.link.table.answers → (Fin G.q.link.table.cubeBits → GE) × NZ)
    ((Fin G.q.link.table.v → Bool) × Fin G.q.link.table.answers → GE) a Q)

/-- **Whatever code a typed key has is the bits of the call 179's string on `Fmt.publishedBytes`**,
at the key's own c as the configuration's digest, the table's name (made from c, the fixed public
parameters' shape and the key's root), the elements of the key's seed, the key's answers, and the
empty last list. c and the seed are any. -/
theorem encId_fmt_of (k : Dig 256 × KeyRoot 256 (LrG T)) (code : ZKCP.Str)
    (h : encId G T k = some code) :
    code = _root_.Run.bytesToBits (Fmt.oStr 0 179 0 0 Fmt.zero32
      (Fmt.publishedBytes (digToBytes k.1)
        (Key.nameOf G.q.link.table (digToBytes k.1)
          ⟨digToBytes k.2.cm, (spellS G T).answers k.2.rcd.2⟩)
        (((spellS G T).seed k.2.rcd.1).map E.triple)
        (((spellS G T).answers k.2.rcd.2).map E.triple) [])) := by
  have e : encId G T k = idCodeS ((spellS G T).keyAt (digToBytes k.1) [] k.2) := rfl
  rw [e] at h
  unfold idCodeS at h
  split at h
  · have h' := (Option.some.inj h).symm
    unfold idStrS at h'
    rw [OnBytes.Tie.idBytesS_fmt] at h'
    exact h'
  · cases h

/-- **Every function g sends a typed key's code to `Fmt.publishedIDW` at the hash over g**, at the
same five arguments, as 256 bits. It holds by unfolding: both sides are g at one string. -/
theorem encId_rule (g : ZKCP.Oracle 256) (k : Dig 256 × KeyRoot 256 (LrG T)) (code : ZKCP.Str)
    (h : encId G T k = some code) :
    g code = bytesToDig (Fmt.publishedIDW (m := Id) (Fmt.HO (oB g)) (digToBytes k.1)
        (Key.nameOf G.q.link.table (digToBytes k.1)
          ⟨digToBytes k.2.cm, (spellS G T).answers k.2.rcd.2⟩)
        (((spellS G T).seed k.2.rcd.1).map E.triple)
        (((spellS G T).answers k.2.rcd.2).map E.triple) []) := by
  have e : encId G T k = idCodeS ((spellS G T).keyAt (digToBytes k.1) [] k.2) := rfl
  rw [e] at h
  unfold idCodeS at h
  split at h
  · rw [← Option.some.inj h]
    refine Eq.trans ?_ (congrArg bytesToDig
      (OnBytes.Tie.idAtS_fmt (oB g) ((spellS G T).keyAt (digToBytes k.1) [] k.2)))
    rw [idAtS_eq]
    exact (bytesToDig_digToBytes _).symm
  · cases h

/-- Where the fixed public parameters' shape leaves room, every typed key has that code. -/
theorem encId_fmt (hG : ShapeRoom G.q.link.table) (k : Dig 256 × KeyRoot 256 (LrG T)) :
    encId G T k = some (_root_.Run.bytesToBits (Fmt.oStr 0 179 0 0 Fmt.zero32
      (Fmt.publishedBytes (digToBytes k.1)
        (Key.nameOf G.q.link.table (digToBytes k.1)
          ⟨digToBytes k.2.cm, (spellS G T).answers k.2.rcd.2⟩)
        (((spellS G T).seed k.2.rcd.1).map E.triple)
        (((spellS G T).answers k.2.rcd.2).map E.triple) []))) := by
  obtain ⟨code, h⟩ := encId_hasCode G T hG k
  rw [h, encId_fmt_of G T k code h]

/-- **So at `recordGround` and at `smallRecordGround`**, with no premise on the shape. -/
theorem encId_fmt_written (hG : G = recordGround ∨ G = smallRecordGround)
    (k : Dig 256 × KeyRoot 256 (LrG T)) :
    encId G T k = some (_root_.Run.bytesToBits (Fmt.oStr 0 179 0 0 Fmt.zero32
      (Fmt.publishedBytes (digToBytes k.1)
        (Key.nameOf G.q.link.table (digToBytes k.1)
          ⟨digToBytes k.2.cm, (spellS G T).answers k.2.rcd.2⟩)
        (((spellS G T).seed k.2.rcd.1).map E.triple)
        (((spellS G T).answers k.2.rcd.2).map E.triple) []))) :=
  encId_fmt G T (by
    rcases hG with e | e
    · rw [e]; exact room_recordGround
    · rw [e]; exact room_smallRecordGround) k

variable {cfg : ByteArray} {t : OnBytes.Params.TableName} {l : List (List E × E)}

/-- **The equation at a key that is made of bytes**: the typed key that is made of 32 bytes cfg, a
table t that `Key.readTable` has read off a key file within the file limit, and a list l of seeds of
a record's shape (`SeedsShaped`), at fixed public parameters whose seeds' elements take at most 2^28
bytes, has as its code the bits of the call 179's string on `Fmt.publishedBytes` at cfg, t's name, l
laid flat, t's answers and the empty last list. Nothing more is assumed of cfg and l. -/
theorem encId_fmt_bytes {file : ByteArray} {j : ℕ}
    (hrd : Key.readTable G.q.link.table cfg file = .ok (t, j)) (hc : cfg.size = 32)
    (hf : file.size ≤ Shell.fileLimit)
    (hl : SeedsShaped G.q.link.table.cubeBits G.q.link.table.answers l)
    (hsd : 24 * (G.q.link.table.answers * (G.q.link.table.cubeBits + 1)) ≤ 2 ^ 28) :
    encId G T (keyT G T cfg t l) = some (_root_.Run.bytesToBits (Fmt.oStr 0 179 0 0 Fmt.zero32
      (Fmt.publishedBytes cfg (Key.nameOf G.q.link.table cfg t)
        ((l.flatMap fun y => y.1 ++ [y.2]).map E.triple) (t.answers.map E.triple) []))) := by
  obtain ⟨-, hr, -⟩ := key_readTable_ok _ _ _ _ _ hrd
  obtain ⟨ha, hk⟩ := answers_of_keyReadTable _ _ _ _ _ hrd
  rw [enc_bytes G T hc hr ha hk hl]
  unfold idCodeS
  rw [if_pos (idOkS_bytes G hrd hc hf hl hsd)]
  unfold idStrS
  rw [OnBytes.Tie.idBytesS_fmt]
  rfl

variable (M : IdMoreS G T)

/-- **`id_bytes` (Johnson/TypedOracleCompiler/Top/IdSeedBytes.lean) with `Fmt.publishedIDW` in `idAtS`'s place**: at
every function g, under the five premises of the statement above, that typed key has a code at the
input `inputIdS G T M`, and g sends it to `Fmt.publishedIDW` at the hash over g, at cfg, t's name, l
laid flat, t's answers and the empty last list, as 256 bits. Nothing more is assumed of cfg and
l. -/
theorem id_fmt (g : ZKCP.Oracle 256) {file : ByteArray} {j : ℕ}
    (hrd : Key.readTable G.q.link.table cfg file = .ok (t, j)) (hc : cfg.size = 32)
    (hf : file.size ≤ Shell.fileLimit)
    (hl : SeedsShaped G.q.link.table.cubeBits G.q.link.table.answers l)
    (hsd : 24 * (G.q.link.table.answers * (G.q.link.table.cubeBits + 1)) ≤ 2 ^ 28) :
    ∃ code, (inputIdS G T M).enc (keyT G T cfg t l) = some code ∧
      g code = bytesToDig (Fmt.publishedIDW (m := Id) (Fmt.HO (oB g)) cfg
        (Key.nameOf G.q.link.table cfg t) ((l.flatMap fun y => y.1 ++ [y.2]).map E.triple)
        (t.answers.map E.triple) []) := by
  obtain ⟨code, h1, h2⟩ := id_bytes G T M g hrd hc hf hl hsd
  refine ⟨code, h1, ?_⟩
  rw [h2, OnBytes.Tie.idAtS_fmt]
  rfl

end OnBytes.K.Arm

#print axioms OnBytes.K.Arm.encId_fmt_of
#print axioms OnBytes.K.Arm.encId_rule
#print axioms OnBytes.K.Arm.encId_fmt
#print axioms OnBytes.K.Arm.encId_fmt_written
#print axioms OnBytes.K.Arm.encId_fmt_bytes
#print axioms OnBytes.K.Arm.id_fmt
