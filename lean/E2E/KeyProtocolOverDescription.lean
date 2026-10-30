-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyProtocolOverDescription.lean: where the key file's decision is the `run` of a description of the key file
(`FileDescription`, Johnson/Desc/Block.lean: the file's IOP as written in Lean), the key file's protocol in
the library's object with OOD samples (`F.withProvers P`, OnBytes/Flat/Object.lean), taken with its
annotation of the rounds, is `batchOf` over that description
(Johnson/Desc/ProofFile/Honest/Record.lean). `batchOf` is the protocol in the type of a prover
structure built by `honestBatchProverOfFile` (Johnson/Desc/ProofFile/Honest/StratC.lean) from parameters that
nothing here fixes. So the one-slot structure of such a structure has the type of the first field of
the object's provers (`Files.Provers.hT`). It is for files that import this one and build such a
structure for the key file. Stated first at any parameters of the library's full size, then at three
public files Z. E2E/ProtocolOverDescription.lean and E2E/TiedAlong.lean do the same for the proof file.
Definitions, equations between protocols, and facts about types.

The key file's instance in the object is an OOD sample (OOD seeds and answers, `RecFull`) of a
committed table: there is no request. The key file's description has an instance type of its own,
`KeyInst`: the table's key as the program writes it. `Key.keyInstanceOfOutOfDomainSample` (Johnson/Desc/Key/Slot.lean) is the
library's map from the first to the second.

  `key_protocol_along`: for all X, N, P with `KeyNamed Z X N P`: `keyBatch (filesAt Z)`, the key
    file's protocol at Z with its annotation, is `keyOverOwn` at `keyFileDescription X N P`, the protocol over
    that description at its own instance type, with its instances read through `keyInstanceOfOutOfDomainSample`
    (`BatchInteractiveOracleProof.comap`, Hiop/RecKit.lean)
  `key_named`: where the IOP's own test on the public files accepts (`protocolDataWellFormed (asDescriptionFiles Z) = true`),
    there are X, N, P with `KeyNamed Z X N P`
  `KeyNamed Z X N P`: a structure of propositions: X, N, P are what the key file's description at Z
    is made of. It holds what the library's `kseat_name` says of them, in the terms that occur in
    `filesAt Z`, and the field `depth`. Field by field: its docstring
  `keyOver_along`: for every description Fx at `KeyInst`: `keyOver` at `Fx.pull keyInstanceOfOutOfDomainSample` is
    `(keyOverOwn DK Fx rK).comap keyInstanceOfOutOfDomainSample`: the protocol over the pulled-back description, with the
    library's test `silK`, is the protocol over Fx, with `silKey`, read through `keyInstanceOfOutOfDomainSample`
  `keyBatch_eq_batchOf`: by unfolding, at any claims, rounds' data and decisions, and any
    description Fk at the instance type `RecFull`: `keyBatch` of `filesWithKey` is
    `keyOver DK Fk rK`
  `test_eq_loc`: so the object's field `offline` is `(keyOver DK Fk rK).loc`, whatever the provers are
  `seatT`, `seatOne`: definitions: so a prover structure over `(keyOver DK Fk rK).loc` (`Honest`,
    Iop/InteractiveOracleProof.lean), and the one-slot structure `hB.one` of a prover structure over
    `keyOver DK Fk rK` (`BatchHonestProver`, Iop/Batch.lean), have the type that `Files.Provers.hT` asks. The
    type of private inputs is the same expression: (index, (pads, encoding randomness), OOD seed).
    No re-indexing, no cast
  `atDecision`: a definition that shows a fact about the type, and a warning. The type `Honest Q Wt`
    depends on the protocol Q only through the rounds' shape, and the shape of a whole file's
    protocol (`reductionOfWholeFile`, OnBytes/Maker/Whole.lean) depends neither on its decision nor on its test
    on the three plain parts. So the fields of a prover structure at one test and decision are,
    unchanged, the fields of one at any other test and decision. That a term has the type "honest
    prover of this protocol" therefore says nothing about the protocol's decision. It is a case of
    the general form `honestRe` (E2E/OneAlong.lean)
  `atDecision_fields`, `atDecision_self`, `cast_eq_atDecision`: each of the fields `Coin`, `ext`,
    `strat`, `Bad`, `Hid` is H's; at the same test and decision it is H; where the two decisions are
    equal it is H carried along that equation (`h ▸ H`)
  `atDecision_law`, `atTest_law`: where the two tests are equal and the two decisions are equal (in
    the second: the tests, at one decision), every predicate p on test, decision and prover
    structure that holds of H holds of `atDecision` of H
  `batchOf_comap`: by unfolding, for every description F, test on the three plain parts and map f:
    the protocol over F, its instances read through f, is the protocol over `F.pull f`, with the
    test read through f
  `silKey`, `silK_fun`: a definition: the test on the three plain parts at an instance of `KeyInst`.
    The library's test at the key file is that test after `keyInstanceOfOutOfDomainSample`:
    `silK = fun x => silKey (keyInstanceOfOutOfDomainSample x)`. The proof unfolds by name the library's list of the answers
    of an OOD sample (`ansL`, OnBytes/Flat/FilesAt.lean), which is marked irreducible
  `filesWithKey_eq`: if `Fk.run` is the key file's decision at Z (`(dataAtFiles flashProveData Z).runK`), then
    `filesWithKeyAt Z Fk` is `filesAt Z` (E2E/ObjectAtFiles.lean)
  `keyRun_eq_of_laid`: where the test on the public files accepts and `FlashProve.theKeyLaid`
    returns a pair p of rounds' data and a decision, the key file's decision at Z is p.2: the
    hypothesis of `filesWithKey_eq`, for an Fk whose `run` is p.2
  `filesAt_eq_key`: under `KeyNamed Z X N P`: `filesAt Z` is `filesWithKeyAt Z` at
    `(keyFileDescription X N P).pull keyInstanceOfOutOfDomainSample`
  `KeyNamed.data_at`: under `KeyNamed Z X N P`: the rounds' data with which the key file's protocol
    at Z is built, `(dataAtFiles flashProveData Z).DK.at frS.P.T.a`, are what `(keyFileDescription X N P).data` returns
  `at_self`: for rounds' data D with `D.a = a`: `D.at a = D` (`WholeD.at`,
    Johnson/EntryRec/OkcFiles.lean, sets the field `a`, the stored table's depth)
  `keyBatch F`: a definition: the key file's protocol of three protocols F with its annotation
    `F.annT` (which rounds are in its shared chain), as a batch protocol. The object itself keeps
    only the protocol: `Files.withProvers` does not read `annT`
  `filesWithKey`: short for the library's three protocols of the full size (`threeProtocolsAtFullSize`,
    Johnson/Flat/Dec/WiresAtSizes.lean) with `Fk.run` as the key file's decision
  `keyOver DK Fk rK`: short for `batchOf` at these parameters: the choice of challenge types at the
    second field, `ckP .two`; the key file's rounds' data with the depth set to the table's,
    `DK.at frS.P.T.a`; the three fixed plain parts `front₀ rK`, `join₀ rK` and `ByteArray.empty`;
    the description Fk; the library's test on the three plain parts at the key file (`silK`: both
    copies of the answers are the instance's, and the copy's number is 0)
  `keyOverOwn DK Fx rK`: the same at a description Fx at `KeyInst` and the test `silKey`
  `filesWithKeyAt Z Fk`: a definition: `filesWithKey` at the parameters of `filesAt Z`
  `KeyInst`, `keyFileDescription X N P`: short for the instance type `Key.Xi` of a key file's description
    (Johnson/Desc/Key/Xi.lean) and for the library's `Key.descriptionFromSource X N P` (Johnson/Desc/Key/Desc.lean)

By what. `keyBatch_eq_batchOf`, `test_eq_loc`, `batchOf_comap` and the facts on `atDecision` hold by
unfolding, or by substituting the equation in the hypothesis. `keyOver_along` rewrites by
`silK_fun`, and `key_protocol_along` joins it with `filesAt_eq_key`. `key_named` is the library's
`kseat_name` (Johnson/Goal/Description/KeySeat.lean), carried to the terms of `filesAt Z` by
`dk_built_live` (Johnson/Goal/Conditions/LiveAtThe.lean) and `theKeyGate_live`
(Johnson/Goal/Description/Gates.lean); its field `depth` is by `theLive_depth`
(Johnson/Goal/Description/Live.lean) and `at_self`. `keyRun_eq_of_laid` is by `theKeyGate_live` and
`theKeyRun_ok` (Johnson/Goal/Description/KeyFold.lean). The step from a description's `run` to the
key file's decision at Z is a proved equation, not an unfolding, as at the proof file. That decision
is "the test on the public files accepts, and `theKeyRun` accepts" (`theKeyGate`), and `theKeyRun`
is a match on whether `theKeyLaid` returns: on whether the description could be made, passed its
tests and gave its rounds' data. A statement that reads the decision (acceptance) passes from a
description's own `run` to `filesAt Z` only by that equation (`KeyNamed.run`). The type of a prover
structure needs no equation (`atDecision`).

Limits. Nothing is shown of any prover: no completeness, nothing on what a view shows. No statement
here says that a prover structure has any property. `atDecision` is defined at every pair of
decisions, also at the decision that rejects everything. It is so for the trivial reason given at
its entry above, and to show that is its point. Nothing on acceptance follows from it. Values that
meet `KeyNamed` are shown only by `key_named`: where the test on the public files accepts. That it
accepts is a theorem of the side library at the written files `storedPublicFiles` and `zGap`
(`AtFullSide.Top.theLive_zFull`, `theLive_zGap`); this file, in the main library, cannot call it.
Where the test rejects, the key file's rounds' data at Z are empty lists and its decision rejects
everything: this is read off the library's definitions (`FlashProve.emptyRoundsData`,
Johnson/Goal/Tie/DescriptionOfData.lean; `theKeyGate`) and is no theorem here. `KeyNamed` does not say that
X, N, P are the only such: two triples could make one description. The rounds' data D are a free
parameter of `batchOf` and of `honestBatchProverOfFile`; here D is set to the term that occurs in `filesAt Z`,
unfolded. The proof file's and the link's provers (`hB`, `hL`) are not touched. No property of a
protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.ObjectAtFiles
import E2E.OneAlong
import Johnson.Desc.ProofFile.Honest.Record
import Johnson.Goal.Description.KeySeat
import Johnson.Goal.Conditions.LiveAtThe

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut
open OnBytes.Flat (Files relationsAndEncodingOfClaims RecFull)
open OnBytes.Slice (frS frZ DecR)
open _root_.Run.PQ (View XO CK)
open OnBytes.Maker (WholeD reductionOfWholeFile)
open _root_.Run (ckP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize)
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Key (keyInstanceOfOutOfDomainSample)
open ProofFile.Honest (batchOf)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (protocolDataWellFormed flashProveData)

/-! ## 1. At any parameters -/

/-- The key file's protocol with its annotation of the rounds (`annT`), as a batch protocol. -/
def keyBatch {C : ConfigurationWithOutOfDomainSample} (F : Files C) : BatchInteractiveOracleProof C.Rec C.E0 := ⟨F.key, F.annT⟩

section General
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD) (Fk : FileDescription RecFull)
  (runP : X × RecFull → View → View → View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List XO) (dec : RecFull × RecFull → View → Bool)
  (rK rP : RecFull) (depthReq : ℕ) (early : X → X) (salt : ℕ)

/-- The library's three protocols of the full size, with the description's `run` as the key file's
decision. -/
abbrev filesWithKey : Files (DecR.configurationOfStoredTable A R) :=
  threeProtocolsAtFullSize A R DK DP Fk.run runP ds xs dec rK rP depthReq early salt

/-- The protocol in the type of a prover structure for the key file, at the library's parameters. -/
abbrev keyOver : BatchInteractiveOracleProof RecFull (oneExternalString (2 ^ (DK.at frS.P.T.a).a) _root_.Run.PQ.SgX) :=
  batchOf (ckP .two) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK) (OnBytes.Flat.join₀ rK)
    ByteArray.empty Fk OnBytes.Flat.silK

/-- **The key file's protocol with its annotation is `keyOver`**, the protocol in the type of a
prover structure: by unfolding. -/
theorem keyBatch_eq_batchOf :
    keyBatch (filesWithKey A R DK DP Fk runP ds xs dec rK rP depthReq early salt) =
      keyOver DK Fk rK := rfl

/-- The object's field `offline` is the field `loc` of that protocol, whatever the provers are: by
unfolding. -/
theorem test_eq_loc
    (P : (filesWithKey A R DK DP Fk runP ds xs dec rK rP depthReq early salt).Provers) :
    ((filesWithKey A R DK DP Fk runP ds xs dec rK rP depthReq early salt).withProvers P).offline =
      (keyOver DK Fk rK).loc := rfl

/-- A prover structure over it has the type that the provers' first field `hT` asks: the same term;
the type of private inputs is the same expression. -/
def seatT
    (hT : Honest (keyOver DK Fk rK).loc
      ((DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed)) :
    Honest (filesWithKey A R DK DP Fk runP ds xs dec rK rP depthReq early salt).key
      ((DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed) :=
  hT

/-- The same for the one-slot structure of a prover structure of the batch protocol. -/
def seatOne
    (hB : BatchHonestProver (keyOver DK Fk rK)
      ((DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed)) :
    Honest (filesWithKey A R DK DP Fk runP ds xs dec rK rP depthReq early salt).key
      ((DecR.configurationOfStoredTable A R).I × ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (DecR.configurationOfStoredTable A R).Seed) :=
  seatT A R DK DP Fk runP ds xs dec rK rP depthReq early salt hB.one

end General

/-! ## 2. The type of a prover structure depends only on the rounds' shape -/

section Shape
variable (C : CK) (D : WholeD) {TF TJ T3 Xi Wt : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- **The fields of a prover structure of a whole file's protocol, at another test and decision.**
The test: that on the three plain parts. Every field is unchanged. It says nothing on either
decision. It is `honestRe` (E2E/OneAlong.lean) at the identity on instances and private inputs. -/
def atDecision (sil sil' : Xi → TF → TJ → T3 → Bool) (run run' : Xi → View → View → View → Bool)
    (H : Honest (reductionOfWholeFile C D tF tJ t3 sil run).toInteractiveOracleProof Wt) :
    Honest (reductionOfWholeFile C D tF tJ t3 sil' run').toInteractiveOracleProof Wt :=
  AtPublicFiles.Along.honestRe H id (reductionOfWholeFile C D tF tJ t3 sil' run').toInteractiveOracleProof.accept id

/-- Every field is H's: by unfolding. -/
theorem atDecision_fields (sil sil' : Xi → TF → TJ → T3 → Bool)
    (run run' : Xi → View → View → View → Bool)
    (H : Honest (reductionOfWholeFile C D tF tJ t3 sil run).toInteractiveOracleProof Wt) :
    (atDecision C D tF tJ t3 sil sil' run run' H).Coin = H.Coin ∧
    (atDecision C D tF tJ t3 sil sil' run run' H).ext = H.ext ∧
    (atDecision C D tF tJ t3 sil sil' run run' H).strat = H.strat ∧
    (atDecision C D tF tJ t3 sil sil' run run' H).Bad = H.Bad ∧
    (atDecision C D tF tJ t3 sil sil' run run' H).Hid = H.Hid := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- At the same test and decision it is H. -/
theorem atDecision_self (sil : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)
    (H : Honest (reductionOfWholeFile C D tF tJ t3 sil run).toInteractiveOracleProof Wt) :
    atDecision C D tF tJ t3 sil sil run run H = H := rfl

/-- Where the two decisions are equal, it is H carried along that equation. -/
theorem cast_eq_atDecision (sil : Xi → TF → TJ → T3 → Bool)
    {run run' : Xi → View → View → View → Bool} (h : run = run')
    (H : Honest (reductionOfWholeFile C D tF tJ t3 sil run).toInteractiveOracleProof Wt) :
    (h ▸ H : Honest (reductionOfWholeFile C D tF tJ t3 sil run').toInteractiveOracleProof Wt) =
      atDecision C D tF tJ t3 sil sil run run' H := by
  subst h
  rfl

/-- Where the tests are equal and the decisions are equal, every predicate on test, decision and
prover structure passes from H to it. p: any such predicate. -/
theorem atDecision_law {sil sil' : Xi → TF → TJ → T3 → Bool}
    {run run' : Xi → View → View → View → Bool} (hs : sil = sil') (hr : run = run')
    (p : (s : Xi → TF → TJ → T3 → Bool) → (r : Xi → View → View → View → Bool) →
      Honest (reductionOfWholeFile C D tF tJ t3 s r).toInteractiveOracleProof Wt → Prop)
    (H : Honest (reductionOfWholeFile C D tF tJ t3 sil run).toInteractiveOracleProof Wt) (hp : p sil run H) :
    p sil' run' (atDecision C D tF tJ t3 sil sil' run run' H) := by
  subst hs
  subst hr
  exact hp

/-- The same where only the test changes. -/
theorem atTest_law {sil sil' : Xi → TF → TJ → T3 → Bool} (hs : sil = sil')
    (run : Xi → View → View → View → Bool)
    (p : (s : Xi → TF → TJ → T3 → Bool) → Honest (reductionOfWholeFile C D tF tJ t3 s run).toInteractiveOracleProof Wt → Prop)
    (H : Honest (reductionOfWholeFile C D tF tJ t3 sil run).toInteractiveOracleProof Wt) (hp : p sil H) :
    p sil' (atDecision C D tF tJ t3 sil sil' run run H) := by
  subst hs
  exact hp

end Shape

/-! ## 3. Along `keyInstanceOfOutOfDomainSample`, the map that writes the table's key -/

section Any
variable (C : CK) (D : WholeD) {TF TJ T3 Xi Xi' : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (F : FileDescription Xi) (silent : Xi → TF → TJ → T3 → Bool) (f : Xi' → Xi)

/-- The protocol over a description, its instances read through f, is the protocol over the
description pulled back along f, with the test read through f: by unfolding. -/
theorem batchOf_comap :
    (batchOf C D tF tJ t3 F silent).comap f =
      batchOf C D tF tJ t3 (F.pull f) (fun x => silent (f x)) := rfl

end Any

/-- The instance type of a key file's description: the table's key as the program writes it. -/
abbrev KeyInst : Type := VerifiableInference.Desc.Key.Xi

/-- A key file's description, by the library's `Key.descriptionFromSource`. X: what it is made of; N: the numbers of
the place of the ranges' test; P: those of the places of the three later proximity tests. -/
abbrev keyFileDescription (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
    (P : VerifiableInference.Desc.Key.LaterPlaces) : FileDescription KeyInst :=
  VerifiableInference.Desc.Key.descriptionFromSource X N P

/-- The test on the three plain parts at an instance of `KeyInst`: both copies of the answers are
the key's list of answers; the copy's number is 0. -/
def silKey : KeyInst → OnBytes.Maker.FrontMsg (List OnBytes.E) →
    Compile.Joined.JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool :=
  OnBytes.Maker.silentOf (fun x : KeyInst => x.key.record.toList) fun _ => 0

/-- The library's test at the key file is that test after `keyInstanceOfOutOfDomainSample`, the map that writes the key. -/
theorem silK_fun :
    (OnBytes.Flat.silK : RecFull → _) = fun x => silKey (keyInstanceOfOutOfDomainSample x) := by
  funext x f j t
  simp only [OnBytes.Flat.silK, silKey, OnBytes.Maker.silentOf, OnBytes.Flat.ansL,
    keyInstanceOfOutOfDomainSample]
  rfl

/-- The protocol over a key file's description at its own instance type, at the library's
parameters. -/
abbrev keyOverOwn (DK : WholeD) (Fx : FileDescription KeyInst) (rK : RecFull) :
    BatchInteractiveOracleProof KeyInst (oneExternalString (2 ^ (DK.at frS.P.T.a).a) _root_.Run.PQ.SgX) :=
  batchOf (ckP .two) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK) (OnBytes.Flat.join₀ rK)
    ByteArray.empty Fx silKey

/-- **The protocol over `Fx.pull keyInstanceOfOutOfDomainSample` is the protocol over Fx, read through `keyInstanceOfOutOfDomainSample`**, the map
that writes the key. -/
theorem keyOver_along (DK : WholeD) (Fx : FileDescription KeyInst) (rK : RecFull) :
    keyOver DK (Fx.pull keyInstanceOfOutOfDomainSample) rK =
      (keyOverOwn DK Fx rK).comap keyInstanceOfOutOfDomainSample := by
  unfold keyOver
  rw [silK_fun]
  rfl

/-! ## 4. At three public files Z -/

/-- The three protocols at Z with the key file's decision replaced by a description's `run`. -/
def filesWithKeyAt (Z : PublicFiles) (Fk : FileDescription RecFull) : Files (Cz Z) :=
  filesWithKey (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK
    (dataAtFiles flashProveData Z).DP Fk (dataAtFiles flashProveData Z).runP PV.EntryFive.dsF PV.EntryFive.xsF
    (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).G.rec₀ (dataAtFiles flashProveData Z).G.z₀.2
    (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early
    (LPFD.Full.saltG (dataAtFiles flashProveData Z).G)

/-- If the description's `run` is the key file's decision at Z, these are `filesAt Z`. -/
theorem filesWithKey_eq (Z : PublicFiles) (Fk : FileDescription RecFull)
    (h : Fk.run = (dataAtFiles flashProveData Z).runK) : filesWithKeyAt Z Fk = filesAt Z := by
  unfold filesWithKeyAt filesWithKey
  rw [h]
  rfl

/-- The key file's decision at Z, where the test on the public files accepts: if `theKeyLaid`
returns the pair p at Z's public files, that decision is p.2. This is the hypothesis of
`filesWithKey_eq`, for a description whose `run` is p.2. -/
theorem keyRun_eq_of_laid (Z : PublicFiles) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (p : WholeD × (RecFull → View → View → View → Bool))
    (h : FlashProve.theKeyLaid (asDescriptionFiles Z) = .ok p) : (dataAtFiles flashProveData Z).runK = p.2 :=
  (FlashProve.theKeyGate_live (asDescriptionFiles Z) live).trans (FlashProve.theKeyRun_ok h)

/-- Rounds' data whose depth is a, with the depth set to a, are unchanged. -/
theorem at_self (D : WholeD) (a : ℕ) (h : D.a = a) : D.at a = D := by
  subst h
  rfl

/-- **X, N, P are what the key file's description at Z is made of.** What the library's `kseat_name`
(Johnson/Goal/Description/KeySeat.lean) says of them, in the terms that occur in `filesAt Z`, and
the field `depth`.
  named: the library's `publicOfO` returns X₀ at Z's three public files; `Key.madeAt` returns m at
    X₀, the layout file and the constant `Key.fixedDigest`; `Key.descAt` returns `keyFileDescription X N P`
    there; every test in the list `Key.lawsAsk` accepts
  plan, wanted, owed: the description's own three tests accept
  data: its own rounds' data are the key file's data at Z
  depth: setting the depth of these to the table's depth changes nothing
  run: its decision, pulled back along `keyInstanceOfOutOfDomainSample`, is the key file's decision at Z.
Values that meet it: `key_named`, where the IOP's own test on the public files accepts. -/
structure KeyNamed (Z : PublicFiles) (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
    (P : VerifiableInference.Desc.Key.LaterPlaces) : Prop where
  named : ∃ X₀ m,
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀ ∧
    VerifiableInference.Desc.Key.madeAt X₀ Z.lay VerifiableInference.Desc.Key.fixedDigest =
      .ok m ∧
    VerifiableInference.Desc.Key.descAt X₀ Z.lay VerifiableInference.Desc.Key.fixedDigest =
      .ok (keyFileDescription X N P) ∧
    ∀ t ∈ VerifiableInference.Desc.Key.lawsAsk X₀ Z.lay m (keyFileDescription X N P) (dataAtFiles flashProveData Z).DK,
      t.2 = true
  plan : (keyFileDescription X N P).planOk = true
  wanted : (keyFileDescription X N P).wantedOk = true
  owed : (keyFileDescription X N P).owedOk = true
  data : (keyFileDescription X N P).data "key file" = .ok (dataAtFiles flashProveData Z).DK
  depth : (dataAtFiles flashProveData Z).DK.at frS.P.T.a = (dataAtFiles flashProveData Z).DK
  run : ((keyFileDescription X N P).pull keyInstanceOfOutOfDomainSample).run = (dataAtFiles flashProveData Z).runK

/-- **Where the test on the public files accepts, there are such X, N, P.** -/
theorem key_named (Z : PublicFiles) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) : ∃ X N P, KeyNamed Z X N P := by
  obtain ⟨X₀, m, X, N, P, h0, hm, hd, h1, h2, h3, h4, h5, h6⟩ := FlashProve.kseat_name Z live
  have e := FlashProve.dk_built_live Z live
  refine ⟨X, N, P, ⟨X₀, m, h0, hm, hd, ?_⟩, h1, h2, h3, ?_, ?_, ?_⟩
  · rw [e]
    exact h4
  · rw [e]
    exact h5
  · rw [e]
    exact at_self _ _ (FlashProve.theLive_depth (asDescriptionFiles Z) live).1
  · exact h6.symm.trans (FlashProve.theKeyGate_live (asDescriptionFiles Z) live).symm

section Named
variable {Z : PublicFiles} {X : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
  {P : VerifiableInference.Desc.Key.LaterPlaces}

/-- The rounds' data with which the key file's protocol at Z is built are the description's own. -/
theorem KeyNamed.data_at (h : KeyNamed Z X N P) :
    (keyFileDescription X N P).data "key file" = .ok ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) := by
  rw [h.depth]
  exact h.data

/-- `filesAt Z` is `filesWithKeyAt Z` at that description, pulled back along `keyInstanceOfOutOfDomainSample`. -/
theorem filesAt_eq_key (h : KeyNamed Z X N P) :
    filesWithKeyAt Z ((keyFileDescription X N P).pull keyInstanceOfOutOfDomainSample) = filesAt Z :=
  filesWithKey_eq Z _ h.run

/-- **The key file's protocol at Z is the protocol over that description, read through `keyInstanceOfOutOfDomainSample`.**
The protocol at Z is taken with its annotation, the description at its own instance type. -/
theorem key_protocol_along (h : KeyNamed Z X N P) :
    keyBatch (filesAt Z) =
      (keyOverOwn (dataAtFiles flashProveData Z).DK (keyFileDescription X N P) (dataAtFiles flashProveData Z).G.rec₀).comap keyInstanceOfOutOfDomainSample := by
  rw [← filesAt_eq_key h]
  exact keyOver_along _ _ _

end Named

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.keyBatch_eq_batchOf
#print axioms AtPublicFiles.AtFiles.test_eq_loc
#print axioms AtPublicFiles.AtFiles.atDecision_fields
#print axioms AtPublicFiles.AtFiles.atDecision_self
#print axioms AtPublicFiles.AtFiles.cast_eq_atDecision
#print axioms AtPublicFiles.AtFiles.atDecision_law
#print axioms AtPublicFiles.AtFiles.atTest_law
#print axioms AtPublicFiles.AtFiles.batchOf_comap
#print axioms AtPublicFiles.AtFiles.silK_fun
#print axioms AtPublicFiles.AtFiles.keyOver_along
#print axioms AtPublicFiles.AtFiles.filesWithKey_eq
#print axioms AtPublicFiles.AtFiles.keyRun_eq_of_laid
#print axioms AtPublicFiles.AtFiles.at_self
#print axioms AtPublicFiles.AtFiles.key_named
#print axioms AtPublicFiles.AtFiles.KeyNamed.data_at
#print axioms AtPublicFiles.AtFiles.filesAt_eq_key
#print axioms AtPublicFiles.AtFiles.key_protocol_along
#print axioms AtPublicFiles.AtFiles.keyBatch
#print axioms AtPublicFiles.AtFiles.filesWithKey
#print axioms AtPublicFiles.AtFiles.keyOver
#print axioms AtPublicFiles.AtFiles.seatT
#print axioms AtPublicFiles.AtFiles.seatOne
#print axioms AtPublicFiles.AtFiles.atDecision
#print axioms AtPublicFiles.AtFiles.KeyInst
#print axioms AtPublicFiles.AtFiles.keyFileDescription
#print axioms AtPublicFiles.AtFiles.silKey
#print axioms AtPublicFiles.AtFiles.keyOverOwn
#print axioms AtPublicFiles.AtFiles.filesWithKeyAt
#print axioms AtPublicFiles.AtFiles.KeyNamed
