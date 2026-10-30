-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeTied.lean: three hypotheses of E2E/BridgePrivacy.lean are proved at three public files Z,
for one family of one request's honest provers, `onlineProversOfCommitter`, with one prover for each number n of a
stored copy (below: the number). The three: `ValidTied` (every valid pair of the object is tied),
`ExtIsEnc` (the family's external strings are the encoded index), and the hypothesis of
`runValsB_of` on the run values. `onlineProversOfCommitter` is the family `onlineProversAlongInstanceMap` of E2E/BridgeAlong.lean at the
parameters of `tied_atFiles_along` (E2E/TiedAtFiles.lean): the description
`F0T OnBytes.secondHashFunction Zp Np cF` (Johnson/P5J/AtTerm.lean; a description is the IOP of the proof file
as written in Lean), the library's writing map `LPFD.Full.instanceAsPlainRecord`, a prover structure H
(`ProofFile.Honest.Prover`) in which the index committer's columns and key are set (`Committer.proverAt`
at the item 0), the committer's seam with the number in the front round, and the committer's
external string. The object is `(filesAt Z).withProvers P` (E2E/ObjectAtFiles.lean). E2E/BridgePrivacy.lean
takes the three as hypotheses for the clauses on the session's prover of the fields `ext`,
`runVals`, `good` and `stops` of `OnBytes.WholeKey.PremW` (Johnson/WholeKey/Premises.lean: the
hypotheses of the statement of index privacy). General in Z, in the object's provers P and in (Zp,
Np, cF); `validTied_atFiles` has one hypothesis on the description, hit. Definitions, statements and
proofs; the proofs call theorems of other files.

  `validTied_atFiles`: `ValidTied` at the relation `TiedZ … n w (instanceAsPlainRecord a)`, at all indices and all
    OOD seeds (ok and Gs are `True`) and at the object's own relation `RyesZ Z`: for every number n,
    committer's randomness r, OOD seed e, index i and request x with `RyesZ Z i x`, the private
    input (i, r, e) is tied to what `instanceAsPlainRecord` writes for x with the OOD sample of (i, r, e). Under
    hit. By `ValidTied.mono` it goes to every smaller range of indices, set of OOD seeds and
    relation. The relation `TiedZ` stays as it is, so the hypotheses that go with `ValidTied` and
    are stated at tied inputs (`OneExact`, `HidSmall`) are then still asked at the tied inputs of
    all indices and OOD seeds, not only of those in the smaller range and set.
    E2E/BridgeJoinAtFiles.lean puts the range and the set inside the relation instead (`TiedIn`)
  `extIsEnc_atFiles`: `ExtIsEnc (onlineProversOfCommitter …)`: at every number the family's external string at
    (i, r, e) is the object's field `encodeIndex` at i and r. No hypothesis
  `runVals_tied`: at every index, committer's randomness, OOD seed, number, request, coin and
    verifier randomness, `pvZ` of the plain parts of the honest run is the pair of run₂ and run₃ at
    the coin's two run values. The prover is the session's in `proversOf hT hL (onlineProversOfCommitter …)`. This is
    the equation of the field `B` of `RunVals` (its clause on the session's prover) without that
    field's two guards: that the index is in the range ok, and that ρ is outside the abort set
    `withheld`. No hypothesis; hT and hL, the key file's prover and the link's, are free parameters
  `onlineProversOfCommitter Z Zp Np cF silent run₂ run₃ B P H`: a definition: `onlineProversAlongInstanceMap` at the parameters above.
    Free parameters, next to Z, P and (Zp, Np, cF): the book of coins B (`ProverCoinCounts`), the prover
    structure H, the test silent on the three rounds without a challenge, and the types R₂ and R₃ of
    the two run values with their codes run₂ and run₃
  `TiedZ Z Zp Np cF run₂ run₃ P H n`: a definition: `ProofFile.Honest.Tied`
    (Johnson/Desc/ProofFile/Honest/Law/Rule/Tied.lean) at the same parameters, at the number n
  `pvZ Z P`: a definition: the pair that is read off a run's plain parts at Z: the field `run` of
    the joining round's plain part, and the seam's plain part

By what. `validTied_atFiles` is `tied_atFiles_along` (E2E/TiedAtFiles.lean): the pair is valid for
the object (`validB`), the clause on the OOD sample by unfolding, the other by `RyesZ Z i x`.
`extIsEnc_atFiles` is `ext_obj` (same file). `runVals_tied` is `runValsB_of`
(E2E/BridgePrivacy.lean) at `runVals_famBC` (E2E/BridgeRunVals.lean), whose two hypotheses on the
seam hold by unfolding: the joining round's value has run₂ r2 in its field `run`, and the seam's
value is run₃ r3. Definitions: `ValidTied`, `ExtIsEnc`, `proversOf` (E2E/BridgePrivacy.lean);
`onlineProversAlongInstanceMap` (E2E/BridgeAlong.lean); `cmAlong`, `frontAt`, `joinAt`, `seamAt`, `pubAt`, `ansInst`,
`ansAt`, `shAt`, `RyesZ`, `AZ`, `PadZ`, `holdZ` (E2E/TiedAtFiles.lean); `Committer.seam`,
`Committer.ext` (Johnson/Desc/ProofFile/Honest/Committer.lean); `Committer.proverAt`
(Johnson/Desc/ProofFile/Honest/CommitterAt.lean): at 0 it is H with the committer's columns as its
stored table at the item 0, no column at another item, and the committer's key.

Hypothesis of `validTied_atFiles`. hit: `AtPublicFiles.AtZero.ItemsZero` (E2E/ItemsZero.lean) of the
description: every stored table that a round of the description declares is under the item 0, the
one item at which `proverAt 0 H` has the committer's columns. `itemsZero_of_data` (same file) proves
it wherever the description's `data` returns; a `LaidAt` (Johnson/P5J/LaidOpens.lean) says so in its
field `data`.

Limits.
- Those of E2E/BridgePrivacy.lean ("error 0 is no result by itself" among them),
  E2E/BridgeAlong.lean, E2E/BridgeRunVals.lean and E2E/TiedAtFiles.lean.
- (Zp, Np, cF) are free parameters, in `validTied_atFiles` under hit. The object's three protocols
  are those at the parameters from which the verifier is compiled (`filesAt Z`), with any provers P;
  no wiring is named in this file. The prover is arbitrary. That the description made of
  (Zp, Np, cF) is the one whose decision the object has matters for acceptance only.
- hit is a hypothesis: it is proved of no description here.
- Nothing on acceptance is stated in this file: no fall (`Falls`: a set of verifier randomness that
  is set aside on the acceptance side), no theorem on acceptance (`AccAtTied`,
  E2E/BridgeAccept.lean), no measure. What is stated on acceptance at Z is in
  E2E/BridgeLinkAtFiles.lean and E2E/BridgeJoinAtFiles.lean, at a family with rows G (`Sides`: for
  each sub-protocol the prover's part and its simulator).
- `onlineProversOfCommitter` sets in H the committer's columns and key only. For a family that has the prover's parts
  of rows G as well, take H := `G.prover H'`: to set the one and to set the other commute
  (`prover_comm`, E2E/BridgeFalls.lean). `famG_eq` (E2E/BridgeJoinAtFiles.lean) has that file's
  family `famG` as `onlineProversOfCommitter` at such an H.
- `TiedZ`, `validTied_atFiles` and `extIsEnc_atFiles` are used in no statement or proof of another
  file under E2E/: the files at a family with rows state them anew (`TiedG`, `validTiedG_atFiles`,
  E2E/BridgeLinkAtFiles.lean; `extIsEnc_famG`, E2E/BridgeJoinAtFiles.lean).
- The statement of index privacy is not called.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.BridgeRunVals
import E2E.TiedAtFiles

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (RecFull)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest (Prover ProverCoinCounts Tied relAt)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)
open P5J

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  (silent : ProofFile.Inst → OnBytes.Maker.FrontMsg (List OnBytes.E) →
    Compile.Joined.JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (P : (filesAt Z).Provers)
  (H : Prover FullSizeMatrix ((filesAt Z).withProvers P).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)

/-- The family `onlineProversAlongInstanceMap` along the library's writing map `instanceAsPlainRecord`, at the parameters of
`tied_atFiles_along` (E2E/TiedAtFiles.lean): the description `F0T OnBytes.secondHashFunction Zp Np cF`, the
prover structure `(cmAlong …).proverAt 0 H`, the committer's seam with the number n in the front
round, and the committer's external string. -/
def onlineProversOfCommitter :=
  onlineProversAlongInstanceMap Z (F0T OnBytes.secondHashFunction Zp Np cF) LPFD.Full.instanceAsPlainRecord silent B
    ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H)
    (fun n r2 r3 => (cmAlong (AZ Z) PadZ (holdZ Z)).seam (frontAt (AZ Z) PadZ (holdZ Z) n r2 r3)
      (joinAt (AZ Z) PadZ (holdZ Z) run₂ r2) (seamAt (AZ Z) PadZ (holdZ Z) run₃ r2 r3))
    (shAt Zp Np cF) ((cmAlong (AZ Z) PadZ (holdZ Z)).ext ((dataAtFiles flashProveData Z).DP.at frS.P.T.a).a) P

/-- `Tied` at the same parameters, at the copy's number n. -/
def TiedZ (n : ℕ) (w : FullSizeMatrix × ((filesAt Z).withProvers P).EncodingRandomness × ((filesAt Z).withProvers P).OutOfDomainSeed) (x : ProofFile.Inst) :
    Prop :=
  Tied ((dataAtFiles flashProveData Z).DP.at frS.P.T.a) (F0T OnBytes.secondHashFunction Zp Np cF)
    ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H)
    (fun r2 r3 => (cmAlong (AZ Z) PadZ (holdZ Z)).seam (frontAt (AZ Z) PadZ (holdZ Z) n r2 r3)
      (joinAt (AZ Z) PadZ (holdZ Z) run₂ r2) (seamAt (AZ Z) PadZ (holdZ Z) run₃ r2 r3))
    ((cmAlong (AZ Z) PadZ (holdZ Z)).ext ((dataAtFiles flashProveData Z).DP.at frS.P.T.a).a)
    (pubAt run₂ run₃ ansInst n) (shAt Zp Np cF)
    (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (RyesZ Z) LPFD.Full.instanceAsPlainRecord) w x

omit [Fintype R₂] [Nonempty R₂] [Fintype R₃] in
/-- **Every valid pair of the object at Z is tied**, at what the library's map writes for it: at all
indices, all committer's randomness, all OOD seeds, every number. hit: every stored table that a
round of the description declares is under the item 0, the one item at which the prover structure
`proverAt 0 H` has the committer's columns. -/
theorem validTied_atFiles (hit : AtPublicFiles.AtZero.ItemsZero (F0T OnBytes.secondHashFunction Zp Np cF)) :
    ValidTied (L := (filesAt Z).withProvers P)
      (fun n w a => TiedZ Z Zp Np cF run₂ run₃ P H n w (LPFD.Full.instanceAsPlainRecord a))
      (fun _ => True) (fun _ => True) (RyesZ Z) :=
  fun n i r e x _ _ hx =>
    tied_atFiles_along Z P Zp Np cF run₂ run₃ n H (i, r, e) (x, ((filesAt Z).withProvers P).recOf i r e)
      hit ⟨rfl, hx⟩

/-- **The family's external strings are the encoded index.** -/
theorem extIsEnc_atFiles : ExtIsEnc (onlineProversOfCommitter Z Zp Np cF silent run₂ run₃ B P H) :=
  fun _ i r e => ext_obj Z P (i, r, e)

/-- The pair that is read off the plain parts at Z: the joining round's run value, the seam's
bytes. -/
def pvZ (π : Plains ((filesAt Z).withProvers P).onlineBatch.loc.shape) : ByteArray × ByteArray :=
  (((OnBytes.Maker.chainsOf (_root_.Run.ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a)
      (OnBytes.Flat.front₀ (dataAtFiles flashProveData Z).G.z₀.2) (OnBytes.Flat.join₀ (dataAtFiles flashProveData Z).G.z₀.2)
      ByteArray.empty).plJ π).run,
    (OnBytes.Maker.chainsOf (_root_.Run.ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a)
      (OnBytes.Flat.front₀ (dataAtFiles flashProveData Z).G.z₀.2) (OnBytes.Flat.join₀ (dataAtFiles flashProveData Z).G.z₀.2)
      ByteArray.empty).pl3 π)

/-- **The run values at Z are in the plain parts of the honest run**: at every index, committer's
randomness, OOD seed, number, request, coin and verifier randomness, the pair read off the plain
parts of the honest run is the codes of the coin's two run values. It is the equation of the clause
on the session's prover of `RunVals`, without that clause's two guards (the index in the range ok; ρ
outside the abort set). No hypothesis. -/
theorem runVals_tied (hT) (hL) :
    ∀ i r e n x κ ρ,
      pvZ Z P (((proversOf hT hL (onlineProversOfCommitter Z Zp Np cF silent run₂ run₃ B P H)).B.strat (i, r, e, n)
        (x, ((filesAt Z).withProvers P).recOf i r e) κ).run ρ).1.plains =
      (fun κ : (ProofFile.Honest.Purse B.shared × R₂) ×
        ((ProofFile.Honest.Purse B.first × ProofFile.Honest.Purse B.second) × R₃) =>
          (run₂ κ.1.2, run₃ κ.2.2)) κ :=
  runValsB_of hT hL (onlineProversOfCommitter Z Zp Np cF silent run₂ run₃ B P H) (pvZ Z P) _
    fun n w a κ ρ => runVals_famBC (_root_.Run.ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a)
      (OnBytes.Flat.front₀ (dataAtFiles flashProveData Z).G.z₀.2) (OnBytes.Flat.join₀ (dataAtFiles flashProveData Z).G.z₀.2)
      ByteArray.empty (F0T OnBytes.secondHashFunction Zp Np cF) silent B
      ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H)
      (fun n r2 r3 => (cmAlong (AZ Z) PadZ (holdZ Z)).seam (frontAt (AZ Z) PadZ (holdZ Z) n r2 r3)
        (joinAt (AZ Z) PadZ (holdZ Z) run₂ r2) (seamAt (AZ Z) PadZ (holdZ Z) run₃ r2 r3))
      (shAt Zp Np cF) ((cmAlong (AZ Z) PadZ (holdZ Z)).ext ((dataAtFiles flashProveData Z).DP.at frS.P.T.a).a)
      (·.run) id run₂ run₃ (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl) n w
      (LPFD.Full.instanceAsPlainRecord a) κ ρ

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.runVals_tied
#print axioms AtPublicFiles.AtFiles.validTied_atFiles
#print axioms AtPublicFiles.AtFiles.extIsEnc_atFiles
#print axioms AtPublicFiles.AtFiles.onlineProversOfCommitter
#print axioms AtPublicFiles.AtFiles.TiedZ
#print axioms AtPublicFiles.AtFiles.pvZ
