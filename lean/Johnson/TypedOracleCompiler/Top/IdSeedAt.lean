-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Top/IdSeedAt.lean: the commitment ID's string with the record's seed in it, as the code
of the typed key AT WRITTEN SPELLINGS: no bit string is the code of two keys, with no premise left;
and so the hypothesis on the commitment in the plain notion.

Johnson/TypedOracleCompiler/Top/IdKeySeedCode.lean has that code (`encSeed`) over letters: how a record's answers and
its seed are spelled, and how the public digests are read off what stands in a key. It shows that
the code is one to one under three premises: the two spellings are one to one, and what stands in a
key is determined by its digests. Here the letters are written and the three premises are proved.
Johnson/TypedOracleCompiler/Top/OnFilesArmsCPlain.lean proves the step from the key to the commitment, in the notion
whose extractor reads the commitment and the committer's log alone, from "no two keys have one
code". Here that is had.

Main names (namespace `OnBytes.K.Arm`):
  `spellS G T`: the tables' shape of the ground G; a record's answers spelled by `spellAns`
    (OnBytes/K/IdTableSpell.lean); its seed spelled by `spellSeed` (OnBytes/K/IdSeedSpell.lean): one
    flat list, for each seed its point's coordinates, then its factor. `spellS_answers_inj`,
    `spellS_seed_inj`.
  `encId G T`: THE CODE: `encSeed (spellS G T)` at a key that holds the configuration's digest and
    no further digest: the string's last list is empty. One written function of G's tables' shape,
    which names no hash function and no file.
  `encId_oneToOne`: no bit string is the code of two keys. No premise; see the first limit.
  `IdMoreS G T`: the fields of an `InputArmsC` beside I, X, L, C and enc. Letters.
    `inputIdS G T M`: an input whose key holds 256 bits beside root and record, with `encId G T` as
    the code of a key. `inputIdS_oneToOne`.
  `commitment_inputIdS`: the hypothesis on the commitment in the plain notion
    (`HoleArmsC.commitment`) at that input, at the library's extractor and cost. No premise; see the
    second and third limits.
  `verify_sound_inputIdS`: `verify_sound_arms_C_plain` at that input: the premise on the code is
    gone.
Limits.
  1. "ONE TO ONE" IS FREE WHERE NO KEY HAS A CODE. A key has a code only within `idOkS`
    (OnBytes/Tie/IdKeySeed.lean). At this code the digest and the root have 32 bytes by their types,
    and the number of bytes hangs on G's shape alone. So whether a key has a code hangs on G alone:
    on six bounds on the shape's numbers and one inequality (`ShapeRoom`,
    Johnson/TypedOracleCompiler/Top/IdSeedHasCode.lean, which shows that under them every key has a code, and that
    the two written grounds meet them). That without them no key has one is not proved. G is a
    letter here.
  2. A SECOND TOP. `HoleArmsC.commitment` belongs to the statement whose three arms' bounds have
    an extractor that reads the key and the log alone (`CoreArmsC`). The statement whose arms'
    bounds have a public reading drawn in the experiment has another hypothesis on the commitment,
    over other data; nothing here proves that one. What is proved for one statement does not count
    for the other.
  3. AN ARROW. Its left side, index binding of the scheme whose verifier holds the key itself, is
    shown of no scheme here: in `verify_sound_inputIdS` it stands as the hypothesis `CoreArmsC b`.
    The key does not hold all that the arms are meant to read: the entry file's arm reads the digest
    of the link's parameters too. So the bridge that tells the key the whole of what an arm reads
    (Johnson/Top/ArmsTold.lean) does not reach `CoreArmsC` there.
  4. THE THIRD THEOREM CAN BE MET FOR NOTHING. The three arms and nine more fields are letters M,
    which the code does not read. Arms that always say no, a builder that returns nothing, errors
    that are infinite: each makes some of its premises free, and together they meet all. No premise
    asks that the verifier ever says yes. The object's word length 2^a is a letter beside the number
    that the code spells off G's shape; nothing ties the two.
  5. THE STRING, AND WHOSE IT IS. `encId` is this library's text of a string. That a program or
    its twin hashes that string is not shown here, and it hangs on the tree: the program's
    `Key.commitmentId` and its twin's hash `Fmt.publishedBytes`, so where that takes no seeds they
    hash the string without them. A program, or a Lean text of one, that hashes the string without
    the seed hashes another string: no bit string is a code of both kinds (`idCode_ne`,
    Johnson/TypedOracleCompiler/Top/IdStringsApart.lean). So a statement that speaks of a program's commitment ID by
    name and a statement at `encId` meet only in a library in which that name has the body with the
    seed. Nothing is evaluated here at a stored file.
    `encId_fmt_of` (Johnson/TypedOracleCompiler/Top/IdSeedFmt.lean) says that whatever code a typed key has is the
    bits of the call 179's string on `Fmt.publishedBytes`. It does not say that a typed key's parts
    are a call's own parts.
  6. Nothing says that a key's seed is the hash function's at its root, or that the 256 bits c in
    a key are the digest of any files: THE ARMS MUST TEST THE SEED, AND MUST TEST c AGAINST THE HASH
    FUNCTION's OWN DIGEST OF THE PUBLIC FILES, SINCE THE PROVER NAMES BOTH: no sentence here asks
    that.
  7. The definitions stand in a section that Lean may leave without code; nothing here shows that
    `inputIdS` or its code can be run. Soundness alone. For proofs only; the program does not import
    this file.

Terms: lean/GLOSSARY.md.

-/
import Johnson.EntryRec.Defs
import OnBytes.K.ArmLetters
import Johnson.TypedOracleCompiler.Top.IdKeySeedCode
import Johnson.TypedOracleCompiler.Top.OnFilesArmsCPlain
import OnBytes.K.IdSeedSpell

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.K.Arm
open _root_.Compile TypedOracleCompiler.Iop Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Tie (EntryGround)
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

/-- The tables' shape, and how a record's answers and its seed are spelled: written. -/
def spellS : IdSpellS (LrG T) where
  shape := G.q.link.table
  answers := spellAns G.q.link.table.v G.q.link.table.answers
  seed := spellSeed G.q.link.table.cubeBits G.q.link.table.answers

/-- The spelling of a record's answers is one to one. -/
theorem spellS_answers_inj : Function.Injective (spellS G T).answers :=
  spellAns_inj G.q.link.table.v G.q.link.table.answers

/-- The spelling of a record's seed is one to one. -/
theorem spellS_seed_inj : Function.Injective (spellS G T).seed :=
  spellSeed_inj G.q.link.table.cubeBits G.q.link.table.answers

/-- **The code of a key (c, (root, record))**: the commitment ID's string with the record's seed in
it, at the key's own c as the configuration's digest; the list of further digests is empty. -/
def encId : Dig 256 × KeyRoot 256 (LrG T) → Option ZKCP.Str :=
  encSeed (spellS G T) id fun _ => []

/-- **No bit string is the code of two keys.** The three premises of `encSeed_oneToOne`
(Johnson/TypedOracleCompiler/Top/IdKeySeedCode.lean) are proved. -/
theorem encId_oneToOne : ZKCP.CodeIsOneToOne (encId G T) :=
  encSeed_oneToOne (spellS G T) (spellS_answers_inj G T) (spellS_seed_inj G T)
    (cfgOf := id) (toldOf := fun _ => []) fun c c' h => by
      have h' : (c, ([] : List (Dig 256))) = (c', []) := h
      exact (Prod.mk.inj h').1

/-- The fields of an `InputArmsC` beside I, X, L, C and enc, over the arm's object, with 256 bits
for what of the public data stands in a key. Letters. -/
structure IdMoreS where
  aT : RoundSplits (LrG T).offline.shape
  aL : RoundSplits (LrG T).link.shape
  armK : Dig 256 → Dig 256 → (LrG T).Rec → OneProtocolProof 256 (batTC (LrG T) aT) → Rom.OComp (rom 256) Bool
  armE : Dig 256 → Dig 256 → Dig 256 → (LrG T).Rec → (LrG T).Rec → OneProtocolProof 256 (batLC (LrG T) aL) →
    Rom.OComp (rom 256) Bool
  armP : Dig 256 → Dig 256 → X' → (LrG T).Rec → ℕ → OneProtocolProof 256 (LrG T).onlineBatch →
    Rom.OComp (rom 256) Bool
  build : List Token × List Token → List Token → Option X'
  nextToken : I' → List Token → Option Token
  ISK : Type
  commit : I' → Rom.OComp (rom 256) ((Dig 256 × KeyRoot 256 (LrG T)) × ISK)
  prove : ISK → (l : List (X' × Unit)) →
    Rom.OComp (rom 256) (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 (LrG T) aT aL) l)
  bound : ℕ
  π₀ : (Dig 256 × KeyRoot 256 (LrG T)) × OfflineLinkOnlineProof 256 (LrG T) aT aL

variable (M : IdMoreS G T)

/-- **An input whose key holds 256 bits c beside root and record, with the commitment ID's string,
the record's seed in it, as the code of a key.** c is any 256 bits that a committer names; it is
meant to be the configuration's digest, and it stands in that digest's place in the string. -/
def inputIdS : InputArmsC where
  I := I'
  X := X'
  L := LrG T
  aT := M.aT
  aL := M.aL
  C := Dig 256
  armK := M.armK
  armE := M.armE
  armP := M.armP
  enc := encId G T
  build := M.build
  nextToken := M.nextToken
  ISK := M.ISK
  commit := M.commit
  prove := M.prove
  bound := M.bound
  π₀ := M.π₀

/-- At that input no bit string is the code of two keys. -/
theorem inputIdS_oneToOne : ZKCP.CodeIsOneToOne (inputIdS G T M).enc := encId_oneToOne G T

/-- **The hypothesis on the commitment in the plain notion, at a written code**: the extractor reads
the commitment and the committer's log alone. -/
theorem commitment_inputIdS (b : BesideArmsC (inputIdS G T M)) :
    HoleArmsC.commitment b (extCodeC b) epsCode :=
  HoleArmsC.commitment_of_code b (inputIdS_oneToOne G T M)

/-- `verify_sound_arms_C_plain` (Johnson/TypedOracleCompiler/Top/OnFilesArmsCPlain.lean) at this input: the premise
on the code is gone. -/
theorem verify_sound_inputIdS {b : BesideArmsC (inputIdS G T M)}
    (claim : (inputIdS G T M).I → List Token → List Token → Prop) (ε : ℕ → ℝ≥0∞)
    (h : CoreArmsC b) (hs : HoleArmsC.soundFor b claim)
    (hε : ∀ tC tP, b.εK tC tP + (b.εE tC tP + b.εP tC tP) + epsCode (tC + tP) ≤ ε (tC + tP)) :
    SoundForWith (systemArmsC (inputIdS G T M))
      ((extCodeC b).buildInstance : ZKCP.Extractor 256 (inputIdS G T M).I
        (List Token × List Token) Unit (ZKCP.Digest 256)
        (List Token × (((inputIdS G T M).C × KeyRoot 256 (inputIdS G T M).L) ×
          OfflineLinkOnlineProof 256 (inputIdS G T M).L (inputIdS G T M).aT (inputIdS G T M).aL))).Ei
      claim ε :=
  verify_sound_arms_C_plain claim ε h (inputIdS_oneToOne G T M) hs hε

end OnBytes.K.Arm

#print axioms OnBytes.K.Arm.encId_oneToOne
#print axioms OnBytes.K.Arm.inputIdS_oneToOne
#print axioms OnBytes.K.Arm.commitment_inputIdS
#print axioms OnBytes.K.Arm.verify_sound_inputIdS
