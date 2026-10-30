-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/WithPd.lean: a file's data, and a page, with other digests of each file's public
data in the place of its three; and that the laws which the key file's and the proof file's
encodings ask hold at all such digests if what `keyLaws_of` | `proofLaws_of` ask holds at the page
itself.

Definitions that compute, statements and proofs. The data of a file with three joined chains
(OnBytes/Maker/Page/Frame.lean, `FileJ`) hold, for each chain, the digest of its parameter bytes: an
answer of the hash. An encoding that is made at a page with such data hangs on the hash. Here these
digests are letters: so there is a family of pages, and of encodings, indexed by digests, in none of
which a hash stands at these places. `LawsJ` reads no digest. `KeyLaws` and `ProofLaws` read them
(the first calls hold a digest, and the test on a call's size reads it): they pass to all digests.

Main names:
  `Pd3`: three digests. `FileJ.pds`: those of a file's data.
  `FileJ.withPd`, `SilentJ.withPd`, `PageJ.withPd`: the data with other digests.
  `FileJ.withPd_pds`, `fill_withPd`: laying a file's own digests changes nothing; laying goes
    through `fillJ`.
  `lawsJ_withPd`: `LawsJ` (OnBytes/K/Arm/FileInj.lean) passes to other digests.
  `keyLaws_withPd`, `proofLaws_withPd`: `KeyLaws` and `ProofLaws` at the cut of the page with any
    digests, from what OnBytes/K/Arm/KeyGlue.lean's `keyLaws_of` and ProofGlue.lean's `proofLaws_of`
    ask at the page itself.
No letter stands under "there is".

What is not claimed. That what `keyLaws_of` | `proofLaws_of` ask holds at any page. That a member of
the family is fixed before a
hash: the page's other data may hold answers of one. That an encoding's strings avoid the strings at
which a hash makes these digests. Anything on the page's other data that are answers of a hash at
use (the configuration's digest; the seeds' and the leaves' codes' letters). Nothing on any hash.
Nothing on soundness.


-/
import OnBytes.Maker.Page.Fill
import OnBytes.K.Arm.KeyGlue
import OnBytes.K.Arm.ProofGlue

set_option autoImplicit false

namespace OnBytes.Maker.Page

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run _root_.Run.PQ _root_.Compile.Joined
open OnBytes.K.Arm (KeyLaws TakenCalls ProofLaws TakenCallsP digBytes)
open OnBytes.K.Arm.KeyGlue (keyCutOf keyLaws_of)
open OnBytes.K.Arm.ProofGlue (proofCutOf proofLaws_of)
open OnBytes.K.Arm.FileInj (FitJ LawsJ)

/-- Three digests: of the three chains' parameter bytes. -/
structure Pd3 where
  d₁ : ByteArray
  d₂ : ByteArray
  d₃ : ByteArray

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag} {K : ℕ}

/-- The three digests of a file's data. -/
def FileJ.pds (F : FileJ L t) : Pd3 := ⟨F.pd₁, F.pd₂, F.pd₃⟩

/-- **A file's data with other digests.** -/
def FileJ.withPd (F : FileJ L t) (d : Pd3) : FileJ L t :=
  { F with pd₁ := d.d₁, pd₂ := d.d₂, pd₃ := d.d₃ }

/-- The silent rounds' data with other digests. -/
def SilentJ.withPd {TF TJ T3 : Type} (S : SilentJ X TF TJ T3) (d : Pd3) : SilentJ X TF TJ T3 :=
  { S with pd₁ := d.d₁, pd₂ := d.d₂, pd₃ := d.d₃ }

/-- **A page with other digests**: dK for the key file, dP for the proof file. -/
def PageJ.withPd (P : PageJ L K) (dK dP : Pd3) : PageJ L K :=
  { P with key := P.key.withPd dK, proof := P.proof.withPd dP }

theorem FileJ.withPd_pds (F : FileJ L t) : F.withPd F.pds = F := rfl

theorem PageJ.withPd_pds (P : PageJ L K) : P.withPd P.key.pds P.proof.pds = P := rfl

theorem fill_withPd (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) (rd : PBt
    L t → Option (PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann)) (S : SilentJ X TF TJ
           T3) (d : Pd3) :
    (fillJ C D tF tJ t3 rd S).withPd d = fillJ C D tF tJ t3 rd (S.withPd d) := rfl

/-- **The laws on a file's data read no digest.** -/
theorem lawsJ_withPd {F : FileJ L t} {Φ : FitJ L t} (h : LawsJ F Φ K) (d : Pd3) : LawsJ (F.withPd d)
    Φ K :=
  ⟨h.l12, h.l13, h.l23, h.word, h.nonce, h.row, h.run₂, h.run₃, h.first₁, h.first₂, h.first₃,
      h.slot⟩

/-- **The laws that the key file's encoding asks, at the page with any digests.** -/
theorem keyLaws_withPd (P : PageJ L K) (Φ : FitJ L .test) (h : LawsJ P.key Φ K) (T : TakenCalls
    (keyCutOf P Φ)) (hc : P.cfg.size = digBytes) (l1 : P.key.lab₁ ≠ Fmt.recordLabel) (l2 :
    P.key.lab₂ ≠ Fmt.recordLabel) (l3 : P.key.lab₃ ≠ Fmt.recordLabel) (dK dP : Pd3) :
    KeyLaws (keyCutOf (P.withPd dK dP) Φ) :=
  keyLaws_of _ _ (lawsJ_withPd h dK) ⟨T.leafInj, T.leafTag, T.seedInj, T.seedIs⟩ hc l1 l2 l3

/-- **The laws that the proof file's encoding asks, at the page with any digests.** -/
theorem proofLaws_withPd (P : PageJ L K) (Φ : FitJ L .onl) (h : LawsJ P.proof Φ K) (T : TakenCallsP
    (proofCutOf P Φ)) (hc : P.cfg.size = digBytes) (l1 : P.proof.lab₁ ≠ Fmt.recordLabel) (l2 :
    P.proof.lab₂ ≠ Fmt.recordLabel) (l3 : P.proof.lab₃ ≠ Fmt.recordLabel) (dK dP : Pd3) :
    ProofLaws (proofCutOf (P.withPd dK dP) Φ) :=
  proofLaws_of _ _ (lawsJ_withPd h dP) ⟨T.leafInj, T.leafTag, T.seedInj, T.seedIs⟩ hc l1 l2 l3

end OnBytes.Maker.Page
