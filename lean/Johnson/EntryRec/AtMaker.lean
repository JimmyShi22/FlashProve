-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/EntryRec/AtMaker.lean: three files' protocols whose key file's and proof file's are those
(`IOR.toInteractiveOracleProof`) of OnBytes/Maker/Files.lean's `keyIOR` and `proofIOR`, with the annotations `keyAnn`
and `proofAnn`, and whose entry file's is a letter.

  `LinkProtocolWithLeafCodingAndQueryLayout R a kmin`: the entry file's part with its wire record: `LinkProtocolWithLeafCoding`
    (Johnson/EntryRec/OkcFiles.lean), the number K of blocks but one of the three files' one wiring,
    at least kmin (`hK`), and the entry file's wire record at K + 1 blocks.
  `dataK`, `dataP`, `runKM`, `runPM`: the data and the decisions that the two makers lay.
  `kM`: the number of blocks but one that the rounds of these two files' data ask: the greater of
    the two (`kThree`, OnBytes/Flat/WireBlocks.lean, at no rounds of an entry).
  `kM_key`, `kM_proof`: no round of the two files' data needs more blocks than an entry's part over
    `kM` has.
  `filesM`: that value of `OnBytes.Flat.Files`, at an entry's part p over `kM`.
  `filesM_eq`: it is Johnson/EntryRec/AtFiles.lean's `filesOf` at the data, tests and decisions that
    the two makers lay, by unfolding. What the equation holds: the two whole files' makers are
    `reductionOfWholeFile` at `WholeD.of a ..`; it compares no two texts that were written apart.

Limits: those of Johnson/EntryRec/OkcFiles.lean's head. Where a test on a whole file's data fails,
the makers' data are those of three empty lists: a sentence "at the real files" needs that the tests
pass (`OkAts`, Johnson/EntryRec/AtMakerA.lean). NO ENTRY's PART IS GIVEN HERE: p is a letter;
nothing ties it to a program's entry file. THE COST OF THAT GENERALITY: `LinkProtocolWithLeafCodingAndQueryLayout` holds no law but
`hK`: nothing asks that its protocol, marks, maps and wire record fit each other or any written
entry file. So a statement that holds for every p says nothing on the entry file's arm. The laws of
the wires (`four_atMakers`, Johnson/EntryRec/AtMakerA.lean) ask two premises on p, `LinkWireOK` and
that the two maps read back what they write; that a value which meets the two is a sensible entry
file is not said anywhere here, nor, in this file, that any value meets them. `kM ..` is evaluated
nowhere here and hangs on the proof file's data at one instance.


-/
import Johnson.EntryRec.AtFiles
import OnBytes.Maker.Files
import OnBytes.Flat.WireBlocks

set_option autoImplicit false

namespace OnBytes.RunA

open _root_.Run _root_.Run.PQ Iop Hiop OnBytes.Maker OnBytes.Flat
open TypedOracleCompiler.Compile.Batch.Cms (Bodies)

attribute [local instance] ConfLetters.finRnd ConfLetters.neRnd ConfLetters.finPad
  ConfLetters.nePad ConfLetters.finSeed ConfLetters.neSeed

/-- **The entry file's part of three files, with its wire record**: the number K of blocks but one
of the three files' one wiring, at least a given number; the entry file's wire record at K + 1
blocks. -/
structure LinkProtocolWithLeafCodingAndQueryLayout (R : Type) (a kmin : ℕ) extends LinkProtocolWithLeafCoding R a where
  K : ℕ
  hK : kmin ≤ K
  wL : TypedOracleCompiler.Iop.ProtocolQueryLayout 256 (K + 1) (⟨QL, aL⟩ : BatchInteractiveOracleProof (R × R) (twoExternalStrings (2 ^ a) SgX))

variable {a : ℕ} (Kc : ConfLetters a) (f : _root_.Fmt.Fld)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool) (key : Kc.conf.Rec → TableKey)
  (k : Params.KeyChains) (rec₀ : Kc.conf.Rec) (c : Params.ProofChains)
  (block : Kc.conf.X → Blk Proof.FirstEnd) (z₀ : Kc.conf.X × Kc.conf.Rec)

/-- The data of the key file and of the proof file that the makers lay. -/
def dataK : WholeD := WholeD.of a (dataAt a (dryKey k (key rec₀)))
def dataP : WholeD := WholeD.of a (dataAt a (dryProof c (key z₀.2) (block z₀.1)))

/-- The decisions of the key file and of the proof file that the makers lay. -/
def runKM (rec : Kc.conf.Rec) (v₁ v₂ v₃ : View) : Bool :=
  okAt a (dryKey k (key rec₀)) &&
    decideKey k (key rec) (dataAt a (dryKey k (key rec₀))).t₁ (dataAt a (dryKey k (key rec₀))).t₂
      v₁ v₂ v₃
def runPM (z : Kc.conf.X × Kc.conf.Rec) (v₁ v₂ v₃ : View) : Bool :=
  okAt a (dryProof c (key z₀.2) (block z₀.1)) &&
    decideProof c (key z.2) (block z.1) (dataAt a (dryProof c (key z₀.2) (block z₀.1))).t₁
      (dataAt a (dryProof c (key z₀.2) (block z₀.1))).t₂ v₁ v₂ v₃

/-- The number of blocks but one that the rounds of the key file's and of the proof file's data ask:
the greater of the two. -/
def kM : ℕ := kThree f (dataK Kc key k rec₀) [] (dataP Kc key c block z₀)

variable (p : LinkProtocolWithLeafCodingAndQueryLayout Kc.conf.Rec a (kM Kc f key k rec₀ c block z₀)) (N : ℕ)
  (early : Kc.conf.X → Kc.conf.X) (late : Option ℕ)

/-- No round of the key file's data needs more blocks than the entry's part has. -/
theorem kM_key : ∀ d ∈ (dataK Kc key k rec₀).ds₁ ++
    ((dataK Kc key k rec₀).ds₂ ++ (dataK Kc key k rec₀).ds₃), (bsRound f d.entry d.kind).b ≤ p.K :=
  fun d hd => (kThree_key f (dataK Kc key k rec₀) [] (dataP Kc key c block z₀) d hd).trans p.hK

/-- No round of the proof file's data needs more blocks than the entry's part has. -/
theorem kM_proof : ∀ d ∈ (dataP Kc key c block z₀).ds₁ ++
    ((dataP Kc key c block z₀).ds₂ ++ (dataP Kc key c block z₀).ds₃),
    (bsRound f d.entry d.kind).b ≤ p.K :=
  fun d hd => (kThree_proof f (dataK Kc key k rec₀) [] (dataP Kc key c block z₀) d hd).trans p.hK

/-- **The two makers' values and an entry file's part as three files' protocols.** -/
@[reducible] def filesM : Files Kc.conf where
  key := (keyIOR (ckP f) a tFk tJk t3k silK key k rec₀).toInteractiveOracleProof
  entry := p.QL
  proof := (proofIOR (ckP f) a tFp tJp t3p silP key c block z₀).toInteractiveOracleProof
  N := N
  annT := keyAnn (ckP f) a tFk tJk t3k silK key k rec₀
  annL := p.aL
  ann := proofAnn (ckP f) a tFp tJp t3p silP key c block z₀
  early := early
  late := late

theorem filesM_eq :
    filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late =
      filesOf Kc f (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK
        (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding N early late := rfl

end OnBytes.RunA
