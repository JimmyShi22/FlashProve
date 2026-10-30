--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyHonestLetters.lean: THE SEAT OF THE KEY FILE's HONEST PROVER (E2E/KeyHonest.lean) WITH THOSE
OF ITS LETTERS FILLED THAT HANG ON NO PART OF A PROVER; the small equations that tie these letters
to each other; and a member, so that the seat is seen to be inhabited. Types, and equations that
hold by unfolding. NOTHING IS SHOWN OF ANY PROVER: no completeness, nothing on what a view shows.

The letters that are filled.
  description   the key file's IOP as written in Lean: `keyFileDescription X N P`
  witness       none: the type with one member; every index has that trace at every instance
  key           the table's key: the instance's one field
  sh            `keyFirst X N P`
  run values    256 bits each, read as 32 bytes
  J             `keySeam` at these
  ext           `tableOf`: the configuration's encoder
The letters that stay: the book of coins; of the prover of parts: the stored table's columns, the
test "in range" with its named member, what the parts hand on, the three lists of halves, the
meeting of chains.

What is shown.
  `keyLetters H`: a prover of parts with its trace and its key replaced as above; H's other fields
    stay.
  `keyLetters_trace`: it has a trace at every index and instance. `keyLetters_first`: the
    description's own first state of the shared chain is sh at this prover's key of the instance.
    `keyLetters_seam`: the key that J writes at (i, r, e) is this prover's key of the written
    key of the honest OOD sample. All three by unfolding.
  `keyHonestOf … B H P`: `keyHonest` at these letters. `keyHonestOf_ext`: its table at (i, r, e) is
    the object's encoded index at (i, r): by unfolding.
  `keyHonestOfAt Z X N P B H`: `offlineProverAtFilesDecision` at these letters: typed at `(filesAt Z).key`, AT EVERY
    Z AND EVERY X, N, P. **`keyHonestOfAt_law`**: where `KeyNamed Z X N P` (E2E/KeyProtocolOverDescription.lean),
    every sentence on protocol and prover passes to it from the carried-back prover at the
    description's own decision. `keyHonestOfAt_ext`, `_coin`: its table and coins at Z;
    `keyHonestOfAt_eq`: it is `keyHonestAny` at Z's letters: by unfolding.
  `noBook`, `noParts i₀`, `idleKeyHonest`: A MEMBER: the book without a row, the prover without a
    half.

Limits.
- THE MEMBER IS SILLY, AND MEANT SO: a prover without a half plays no sub-protocol. It shows that
  the types can be filled, and nothing else.
- X, N, P are letters: which they are at public files is E2E/KeyProtocolOverDescription.lean's `KeyNamed`, which
  has a member where the IOP's own test on the public files accepts (`key_named`).
- That the stored table's columns, a letter of H, are those of `tableOf` is asked nowhere here.
- "In range" is a letter of H: that it is the library's test on matrices is asked nowhere here.


-/
import E2E.KeyHonest
import Run.CodingBits

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut
open OnBytes.Flat (Files relationsAndEncodingOfClaims RecFull)
open OnBytes.Slice (frS frZ DecR)
open _root_.Run.PQ (View XO)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP digToBytes)
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Key (keyInstanceOfOutOfDomainSample)
open ProofFile.Honest (Prover KeyAndJoiningRoundMessages ProverCoinCounts Purse)
open VerifierAndGoals (PublicFiles asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)

/- At the literal 256 Lean's search for these two instances runs out of its budget; at a letter
instead of 256 it finds them. So they are laid by hand, for this file alone. -/
local instance : Nonempty (Dig 256) := ⟨fun _ => false⟩
local instance : Inhabited (Dig 256) := ⟨fun _ => false⟩

/-- **A prover of parts of the key file, its trace and its key laid**: there is no witness; the key
is the instance's field. H's other fields stay. -/
def keyLetters {W₀ Rc X₀ X' : Type} (H : Prover W₀ Rc KeyInst OnBytes.TableKey Unit X₀ X') :
    Prover W₀ Rc KeyInst OnBytes.TableKey Unit X₀ X' :=
  { H with trace := fun _ _ => some (), key := fun x => x.key }

/-- It has a trace at every index and instance. -/
theorem keyLetters_trace {W₀ Rc X₀ X' : Type}
    (H : Prover W₀ Rc KeyInst OnBytes.TableKey Unit X₀ X') (w₀ : W₀) (x : KeyInst) :
    ((keyLetters H).trace w₀ x).isSome = true := rfl

/-- **The description's own first state of the shared chain is `keyFirst` at this prover's key of
the instance.** -/
theorem keyLetters_first {W₀ Rc X₀ X' : Type}
    (H : Prover W₀ Rc KeyInst OnBytes.TableKey Unit X₀ X')
    (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
    (P : VerifiableInference.Desc.Key.LaterPlaces) (x : KeyInst) :
    (keyFileDescription X N P).start₂ ((keyFileDescription X N P).pub x) = keyFirst X N P ((keyLetters H).key x) :=
  rfl

section General
variable {Y : Type} (A : (frS.toDecR frZ 402653181).Claims Y)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
  (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces)
  (runP : Y × RecFull → View → View → View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List XO) (dec : RecFull × RecFull → View → Bool)
  (rK rP : RecFull) (depthReq : ℕ) (early : Y → Y) (salt : ℕ)
  {X₀ X' : Type} (B : ProverCoinCounts)
  (H : Prover (DecR.configurationOfStoredTable A R).I ((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) KeyInst
    OnBytes.TableKey Unit X₀ X')

/-- **The key that J writes is this prover's key of the written key of the honest OOD
sample.** -/
theorem keyLetters_seam (r2 r3 : Dig 256) (i : (DecR.configurationOfStoredTable A R).I)
    (r : (DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) (e : (DecR.configurationOfStoredTable A R).Seed) :
    (keySeam A R digToBytes digToBytes r2 r3).keyOf i r e =
      (keyLetters H).key (keyInstanceOfOutOfDomainSample (sampleOf A R i r e)) := rfl

/-- **The seat of the key file's honest prover at the letters of this file's head.** The book B and,
of the prover of parts H, all but its trace and key are ARGUMENTS: no part of a prover is written.
-/
def keyHonestOf
    (Q : (filesWithKey A R DK DP ((keyFileDescription X N P).pull keyInstanceOfOutOfDomainSample) runP ds xs dec rK rP depthReq early
      salt).Provers) :=
  keyHonest A R DK DP (keyFileDescription X N P) runP ds xs dec rK rP depthReq early salt B (keyLetters H)
    (keySeam A R digToBytes digToBytes) (keyFirst X N P) (tableOf A R DK) Q

/-- Its table is the object's encoded index. -/
theorem keyHonestOf_ext
    (Q : (filesWithKey A R DK DP ((keyFileDescription X N P).pull keyInstanceOfOutOfDomainSample) runP ds xs dec rK rP depthReq early
      salt).Provers)
    (i : (DecR.configurationOfStoredTable A R).I) (r : (DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd)
    (e : (DecR.configurationOfStoredTable A R).Seed) :
    (keyHonestOf A R DK DP X N P runP ds xs dec rK rP depthReq early salt B H Q).ext (i, r, e) =
      ((filesWithKey A R DK DP ((keyFileDescription X N P).pull keyInstanceOfOutOfDomainSample) runP ds xs dec rK rP depthReq early
        salt).withProvers Q).encodeIndex i r := rfl

end General

/-- **The same at three public files Z, typed at the key file's protocol at Z itself.** THE TYPE
SAYS NOTHING ON THE DECISION, AND X, N, P ARE FREE OF Z: it is typed at every Z and every X, N, P.
What ties them to Z is the premise `KeyNamed Z X N P` of `keyHonestOfAt_law`. -/
def keyHonestOfAt (Z : PublicFiles) (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
    (P : VerifiableInference.Desc.Key.LaterPlaces) {X₀ X' : Type} (B : ProverCoinCounts)
    (H : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst OnBytes.TableKey Unit X₀ X') :
    Honest (filesAt Z).key ((Cz Z).I × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) :=
  offlineProverAtFilesDecision Z (keyFileDescription X N P) B (keyLetters H)
    (keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) digToBytes digToBytes)
    (keyFirst X N P)
    (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK)

section AtZ
variable (Z : PublicFiles) (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces) {X₀ X' : Type} (B : ProverCoinCounts)
  (H : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst OnBytes.TableKey Unit X₀ X')

/-- The carried-back prover at Z's letters and the letters of this file's head. -/
abbrev keySlotOfAt :=
  offlineOneInstanceProverAtFiles Z (keyFileDescription X N P) B (keyLetters H)
    (keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) digToBytes digToBytes)
    (keyFirst X N P)
    (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK)

/-- **Where X, N, P are what the key file's description at Z is made of, every sentence on protocol
and prover passes** from the carried-back prover, at the description's own decision, to
`keyHonestOfAt`, at the key file's decision at Z. -/
theorem keyHonestOfAt_law (h : KeyNamed Z X N P)
    (p : (s : RecFull → OnBytes.Maker.FrontMsg (List OnBytes.E) →
        Compile.Joined.JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool) →
      (r : RecFull → View → View → View → Bool) →
      Honest (OnBytes.Maker.reductionOfWholeFile (ckP .two) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a)
        (OnBytes.Flat.front₀ (dataAtFiles flashProveData Z).G.rec₀)
        (OnBytes.Flat.join₀ (dataAtFiles flashProveData Z).G.rec₀) ByteArray.empty s r).toInteractiveOracleProof
        ((Cz Z).I × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) → Prop)
    (hp : p (fun x : RecFull => silKey (keyInstanceOfOutOfDomainSample x)) ((keyFileDescription X N P).pull keyInstanceOfOutOfDomainSample).run
      (keySlotOfAt Z X N P B H)) :
    p OnBytes.Flat.silK (dataAtFiles flashProveData Z).runK (keyHonestOfAt Z X N P B H) :=
  keyHonestAt_law Z (keyFileDescription X N P) B (keyLetters H) _ _ _ h.run p hp

/-- Its table at (i, r, e) is the encoded index at (i, r) of the object at Z, for every Q. -/
theorem keyHonestOfAt_ext (Q : (filesAt Z).Provers) (i : (Cz Z).I)
    (r : (Cz Z).Pad × (Cz Z).Rnd) (e : (Cz Z).Seed) :
    (keyHonestOfAt Z X N P B H).ext (i, r, e) = ((filesAt Z).withProvers Q).encodeIndex i r := rfl

/-- Its coins: the three purses, and two run values of 256 bits. -/
theorem keyHonestOfAt_coin :
    (keyHonestOfAt Z X N P B H).Coin =
      ((Purse B.shared × Dig 256) × ((Purse B.first × Purse B.second) × Dig 256)) := rfl

/-- **It is `keyHonestAny` at Z's letters and the letters of this file's head**, for every Q: so
`keyHonestAny_fields` (table, coins, strategy, abort set) and `keyHonestAny_law` speak of it. -/
theorem keyHonestOfAt_eq (Q : (filesAt Z).Provers) :
    keyHonestOfAt Z X N P B H =
      keyHonestAny (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK
        (dataAtFiles flashProveData Z).DP (keyFileDescription X N P) (dataAtFiles flashProveData Z).runP PV.EntryFive.dsF
        PV.EntryFive.xsF (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).G.rec₀ (dataAtFiles flashProveData Z).G.z₀.2
        (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early
        (LPFD.Full.saltG (dataAtFiles flashProveData Z).G) B (keyLetters H)
        (keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) digToBytes digToBytes)
        (keyFirst X N P)
        (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK)
        (dataAtFiles flashProveData Z).runK Q := rfl

end AtZ

/-! ## A member -/

/-- The book without a row. -/
def noBook : ProverCoinCounts := ⟨[], [], [], [], []⟩

/-- The prover without a half. i₀: any index. -/
def noParts {W₀ Rc : Type} (i₀ : W₀) : Prover W₀ Rc KeyInst OnBytes.TableKey Unit Unit Unit :=
  { stored := fun _ _ _ _ => none, trace := fun _ _ => some (), key := fun x => x.key
    inRange := fun _ => true, dummy := i₀, own₀ := (), ownShared₀ := (), first := [], shared := []
    second := [], meet := fun _ _ => () }

/-- **A member of the seat at Z**: silly, and meant so: no sub-protocol is played. THE TYPE SAYS
NOTHING ON THE DECISION. -/
def idleKeyHonest (Z : PublicFiles) (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
    (P : VerifiableInference.Desc.Key.LaterPlaces) (i₀ : (Cz Z).I) :
    Honest (filesAt Z).key ((Cz Z).I × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) :=
  keyHonestOfAt Z X N P noBook (noParts i₀)

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.keyLetters_trace
#print axioms AtPublicFiles.AtFiles.keyLetters_first
#print axioms AtPublicFiles.AtFiles.keyLetters_seam
#print axioms AtPublicFiles.AtFiles.keyHonestOf
#print axioms AtPublicFiles.AtFiles.keyHonestOf_ext
#print axioms AtPublicFiles.AtFiles.keyHonestOfAt
#print axioms AtPublicFiles.AtFiles.keyHonestOfAt_law
#print axioms AtPublicFiles.AtFiles.keyHonestOfAt_ext
#print axioms AtPublicFiles.AtFiles.keyHonestOfAt_coin
#print axioms AtPublicFiles.AtFiles.keyHonestOfAt_eq
#print axioms AtPublicFiles.AtFiles.idleKeyHonest
