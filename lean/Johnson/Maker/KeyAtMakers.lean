-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/KeyAtMakers.lean: the typing of a key file (`typingKey`,
Johnson/Maker/TypingAKey.lean) at the values of the two makers and an entry's part
(Johnson/EntryRec/AtMaker.lean, AtMakerA.lean): the interface is that of the object made of the two
makers' values and an entry's part.

  `typingKeyM`   the typing at these values. Its wiring is `wireM`.
  `dataM_eq`, `runM_eq`   where the makers' tests pass, the makers' data and run are those of
                 Johnson/Maker/KeyPays.lean
  `blocksM`      no round of the makers' data has more blocks than the entry's part has (`p.K`): the
                 premise beside `KeyDebts` is paid
  `KeyDebtsM`    `KeyDebts` at these values
  `vTA_atMakers`   the program's yes and `KeyDebtsM` give the yes of `verifyOfflineProof` at `wireM`, at whatever
                 string `typeFile` returns at the fixed reading, if the silent rounds' test says yes
                 and X holds there

To be minded. In `vTA_atMakers` all letters stand under one "for all" with the files: of the makers'
letters the parameters k alone are pinned to the public files. A caller could choose the others
after seeing the key file.

The wiring holds the proof file's and the entry file's letters too (c, block, z₀, p): here nothing
pins them to the public files. So this statement and the like for a proof file
(Johnson/Maker/ProofAtMakers.lean) meet at one wiring only if a caller lays one set of letters for
both.

Who uses what. The sentences at a key file (Johnson/Maker/Page/PortKey.lean and the files over it)
use `dataM_eq`, `runM_eq`, `typingKeyM` and `blocksM`. They do not go through `KeyDebtsM` or
`vTA_atMakers`. No file of the library calls these two.

Not claimed. Any row of `KeyDebtsM`: no member of it is shown. That this object is the one at which
the soundness theorem is applied. Nothing on soundness.


-/
import Johnson.Maker.KeyPays
import Johnson.EntryRec.AtMakerA

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ Iop Hiop OnBytes.RunA OnBytes.Flat TypedOracleCompiler.Joined.K Rom
open OnBytes.Params (Rounds)

attribute [local instance] ConfLetters.finRnd ConfLetters.neRnd ConfLetters.finPad
  ConfLetters.nePad ConfLetters.finSeed ConfLetters.neSeed

section
variable {a : ℕ} (Kc : ConfLetters a) (f : _root_.Fmt.Fld)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool) (key : Kc.conf.Rec → TableKey)
  (k : Params.KeyChains) (rec₀ : Kc.conf.Rec) (c : Params.ProofChains)
  (block : Kc.conf.X → Blk Proof.FirstEnd) (z₀ : Kc.conf.X × Kc.conf.Rec) (p : LinkProtocolWithLeafCodingAndQueryLayout Kc.conf.Rec a
    (kM Kc f key k rec₀ c block z₀)) (N : ℕ) (early : Kc.conf.X → Kc.conf.X) (late : Option ℕ)
  (P : (filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early
    late).Provers)
  (sb depthReq depthReqT depthReqL : ℕ)

/-- Where the makers' tests pass, the makers' data of the key file are those of the three lists. -/
theorem dataM_eq {R : Rounds × Rounds × Rounds} (hR : dryKey k (key rec₀) = some R)
    (ok : okAt a (some R) = true) : dataAt a (dryKey k (key rec₀)) = dataOf R := by
  rw [hR]
  exact if_pos ok

/-- And the makers' run of the key file is the run at these data. -/
theorem runM_eq {R : Rounds × Rounds × Rounds} (hR : dryKey k (key rec₀) = some R)
    (ok : okAt a (some R) = true) : runKM Kc key k rec₀ = runOf a R key k := by
  funext rec v₁ v₂ v₃
  unfold runKM
  rw [dataM_eq Kc key k rec₀ hR ok, hR]

variable
  (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (p.K + 1)
    (TypedOracleCompiler.Compile.Batch.Cms.typedOracleCarrier
      ((filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early
        late).withProvers P) (List Bool)
      (filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late).annT
      (filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early
        late).annL)))
  (sFS : ℕ) (cfg : ByteArray) (recOf : Params.TableName → Kc.conf.Rec)
  (cA : Kc.conf.Ans → List (Dig 256)) (pF : Dat → TFk) (pJ : Dat → TJk) (p3 : Dat → T3k)
  (X : Dat → Prop)

/-- **The typing of a key file at the two makers' values and an entry's part.** -/
noncomputable def typingKeyM : TypingA :=
  typingKey f p.K a (dataAt a (dryKey k (key rec₀)))
    (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK (runKM Kc key k rec₀) silP
    (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding
    (lettersOf Kc f (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK
      (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding N early late P)
    p.wL (List Bool) depthReq depthReqT
    depthReqL
    (bodiesF f a (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK
      (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding
      (lettersOf Kc f (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK
        (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding N early late P)
      sb (embStored a sb) (prjStored a sb))
    g sb sFS cfg recOf cA pF pJ p3

/-- No round of the makers' data of the key file has more blocks than the entry's part has
(`p.K`). -/
theorem blocksM : ∀ d ∈ (WholeD.of a (dataAt a (dryKey k (key rec₀)))).ds₁ ++
      ((WholeD.of a (dataAt a (dryKey k (key rec₀)))).ds₂ ++
        (WholeD.of a (dataAt a (dryKey k (key rec₀)))).ds₃),
    (bsRound f d.entry d.kind).b ≤ p.K :=
  kM_key Kc f key k rec₀ c block z₀ p

/-- **What is owed at a key file, at the two makers' values and an entry's part.** u: the
public files. R: the three lists of rounds. -/
def KeyDebtsM (u : OnBytes.TieK.KeyPub) (R : Rounds × Rounds × Rounds) : Prop :=
  KeyDebts f p.K a (dataAt a (dryKey k (key rec₀)))
    (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK (runKM Kc key k rec₀) silP
    (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding
    (lettersOf Kc f (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK
      (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding N early late P)
    p.wL (List Bool) depthReq depthReqT
    depthReqL
    (bodiesF f a (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK
      (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding
      (lettersOf Kc f (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK
        (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding N early late P)
      sb (embStored a sb) (prjStored a sb))
    g sb sFS cfg recOf cA pF pJ p3 u k R key X

/-- **Where the program says yes to a whole call, the compiled verifier for a key file at the wiring
of the two makers' values and an entry's part has the value yes at whatever string the typing of the
whole file returns, if the silent rounds' test says yes and X holds there**, and if what is
owed holds at the file's public files. -/
theorem vTA_atMakers (pp : _root_.Compile.Params) (hMT : pp.sMT = 256 + 8 * sb)
    (hFS : pp.sFS = sFS) (F : OnBytes.K.Files) (pl : Model.Verify.Planned)
    (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok pl) (hk : k = pl.chains.key)
    (h0 : (key rec₀).item = 0)
    (hf : (key rec₀).fits (Key.tailPublic k noTable).lin.fold.index = true)
    (R : Rounds × Rounds × Rounds) (hR : dryKey k (key rec₀) = some R)
    (H : KeyDebtsM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P
      sb depthReq depthReqT depthReqL g sFS cfg recOf cA pF pJ p3 X ⟨F.pol, F.lay, F.KL⟩ R)
    (id : String) (table further : Params.TableName)
    (h : OnBytes.K.PortYesAt F id table further) :
    ∃ d, TieK.readKeyChains F.pol F.lay F.KL F.key = some (table, d) ∧ d.copy = 0 ∧
      ∀ π, typeFile (ckP f) a (dataAt a (dryKey k (key rec₀))) tFk tJk t3k silK
          (runKM Kc key k rec₀) sb cfg (pF (table, d)) (pJ (table, d)) (p3 (table, d)) d.salt d.path
          d.r = some π →
        silK (recOf table) (pF (table, d)) (pJ (table, d)) (p3 (table, d)) = true →
        X (table, d) →
        (TypedOracleCompiler.Compile.Batch.Cms.verifyOfflineProof
          (wireM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P sb
            depthReq depthReqT depthReqL) cA pp (bytesToDig table.root) (recOf table) π).det g =
          true :=
  vTA_of_port' f p.K a (dataAt a (dryKey k (key rec₀)))
    (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK (runKM Kc key k rec₀) silP
    (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding
    (lettersOf Kc f (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK
      (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding N early late P)
    p.wL (List Bool) depthReq depthReqT
    depthReqL
    (bodiesF f a (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK
      (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding
      (lettersOf Kc f (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK
        (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding N early late P)
      sb (embStored a sb) (prjStored a sb))
    g sb sFS cfg recOf cA pF pJ p3 ⟨F.pol, F.lay, F.KL⟩ k (key rec₀) R key X pl hp hk h0 hf hR
    (dataM_eq Kc key k rec₀ hR H.ok) (runM_eq Kc key k rec₀ hR H.ok) pp hMT hFS F rfl H
    (blocksM Kc f key k rec₀ c block z₀ p) id table further h

end

end OnBytes.Maker
