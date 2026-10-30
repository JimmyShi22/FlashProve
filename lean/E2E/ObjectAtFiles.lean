-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ObjectAtFiles.lean: the object of the IOP as written in Lean, from which `VerifierAndGoals.verify` is
compiled, with its index type cut to the matrices in range; and those of the interface's properties
(Hiop/RecInterface.lean) that need no honest prover or ask of it one equation.

Why. The library's object at three public files Z is `F.withProvers P : Iop.HolographicProtocol` (OnBytes/Flat/Object.lean),
F the three files' protocols (key file, copy's file with its link proof, proof file). Its index type
is EVERY matrix of the full size's shape over the extension field. The index decoder returns
matrices in range alone (its text: `DecR.configurationOfStoredTable`, OnBytes/Slice/ConfOf.lean), so the clause "from an
honest committed table and its honest OOD sample the decoder returns the index" (`WiredR.dec_enc`)
cannot hold at a matrix out of range, whatever the protocols are. (An argument from the decoder's
text; no theorem here states it.) Here the index type is cut (E2E/CutIndex.lean) and nothing else is
touched: the three protocols, with their proof of work in the rounds, are the library's own terms.

Definitions.
  `FullSizeMatrix`: the matrices of the full size's shape. `inRange`: the library's test
    (`VerifiableInference.OnPublicFiles.Flat.InRange`, Johnson/Flat/LedgerClaim.lean: the matrix holds an
    index of the integer model: every entry is the cast of a digit in [-2^7, 2^7), two-byte weights
    in [-2^12, 2^12)). It is the test in the decoder's own text. `Ix`: the matrices in range.
  `ConfAt pp req`: the full size's configuration at a table pp of scales and policy and a reading
    req of instances as requests. pp and req are read by the claim on requests alone.
  `cutObj F P`: for ANY three protocols F over that configuration and ANY provers P: `F.withProvers P`, cut.
  `Cz Z`, `filesAt Z`: the configuration and the three protocols at public files Z, as they stand in
    the type of the letters from which the verifier is compiled (`FlashProve.DescriptionDataAtFiles.inputFieldsAtReadings`,
    Johnson/Goal/Tie/DescriptionOnDecodedProof.lean; `LPFD.Full.FsAtR`, Johnson/Top/Fire/Code/TieAtValues.lean). That
    they are the configuration and the three protocols of the IOP as written in Lean, where all
    goals but two read it, is a theorem: E2E/DescriptionTie.lean.
  `objAt Z P`: `cutObj (filesAt Z) P`.

What is shown.
  `wired_cutObj`: `WiredR` of `cutObj F P`, for every F and P, from the three equations `ExtR` on P
    (the table that a prover holds is the encoder's). The decoder's clause is the library's
    `obj_decodes_cells_full` (Johnson/Flat/CodingCells.lean).
  `ext_silent`, `ext_cutObj_silent`: the three equations hold of the provers that send fixed
    messages (`Files.fixedMessageProvers`, OnBytes/Flat/Silent.lean), by unfolding. So `ExtR` has a member.
  `linkW_point`: every round's oracle of the written link is a string.
  `formats_fullD`: the seven clauses on formats for the three protocols of the full size at ANY
    rounds' data and ANY three decisions: by the library's theorems, which are general in these
    letters.
  `formats_objAt`, `wired_objAt`: the same at `objAt Z P`, at every Z and P.

Limits.
- `objAt Z P` is another term than the object in the verifier's types: in the index type, and,
  unless P is what the library lays there (E2E/ObjectGuards.lean: `ownProvers`), in the provers.
  Types of keys and proofs have the object as a parameter, so a theorem "for every object" applied
  here speaks of another term than `VerifierAndGoals.verify`. What ties the two: E2E/DescriptionTie.lean (the
  object in the input at which `VerifierAndGoals.verify` calls the compiled verifier is `(filesAt Z).withProvers
  (filesAt Z).fixedMessageProvers`) and E2E/SameVerifier.lean (the compiled verifier at the cut object with any
  provers is the same function).
- Every statement here holds at every Z. Where the test on the public files (`protocolDataWellFormed`) rejects, the
  key file's and the proof file's rounds' data are empty lists, and all three decisions reject
  everything (the library's text: `FlashProve.emptyRoundsData`, Johnson/Goal/Tie/DescriptionOfData.lean;
  Johnson/Goal/Description/Gates.lean). The link keeps its rounds and its reads there: its data are
  closed terms; its decision alone is shut. So there these statements are about protocols that
  accept nothing.
- `flashProveData` is the IOP as written in Lean at the second hash function (the library's word:
  our second, non-standard hash, built on BLAKE2b's compression function), which the test on the
  public files reads. The library's family at another such function is not covered.
- `WiredR` and the formats say nothing on soundness, completeness or what a view shows.
- That `Ix` has two different members is not shown in this file (E2E/ObjectGuards.lean; from two
  different weights: E2E/ObjectAtWeights.lean). With one member every clause "does not depend on the
  index" would hold for nothing.
- That a prover program lays its tables as the encoder here does is not said.
- `wired_cutObj` rests on the library's Johnson/Flat/CodingCells.lean and
  OnBytes/Flat/CodingHonest.lean.

This file's definitions may be read as part of a goal: they fix the object of which
E2E/WholeView.lean and the files over it speak. They count as none: no goal of this library
says that this is the object of which something is to be proved.

BESIDE EVERY TELLING of the result on the index's committed tables, to which this file belongs
(E2E/WholeViewAtFiles.lean, E2E/TablesAtOwnObject.lean):
- placeholder provers: no message of the protocol is covered; it is not zero knowledge;
- before compilation: no hashing; each OOD seed is chosen before its table's coins are drawn, from
  nothing but what has been shown and coins of the environment's own: of a seed that hangs on
  anything hidden, another table's pads too, nothing is said;
- fresh uniform pads and encoding randomness for each table (as run: derived from the committer's
  secret seed); one OOD sample a table; one set of public files. One table's randomness is used
  under one set of public files alone. The same rows and pads under other public files would get
  another seed, and of two OOD samples on one table's pads this file says nothing.
- the budget is table by table, is kept by nobody, and has no slack: at one column more the
  interface's clause on the encoder fails (a theorem: some OOD seed, two matrices in range, at every
  set of that size; it states no size of the difference, only that the two laws differ; typed for
  the form with all OOD seeds alone); that the result itself fails there is typed by no environment;
- that the IOP's own tests on the public files pass is shown in the side library: at the library's
  two named sets of public files (AtFullSide/E2E/AtWrittenFiles.lean), and at the first set's files
  under every policy within four bounds (`theLive_zAt`, AtFullSide/Top/LiveAtPolicies.lean); no
  theorem ties any of these to a file on a disk.


-/
import E2E.CutIndex
import Johnson.Goal.Description.Lay
import Johnson.Flat.Dec.WiresAtSizes
import Johnson.Flat.CodingCells
import OnBytes.Maker.WholeLocal
import OnBytes.Flat.Silent

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut
open OnBytes.Flat (Files relationsAndEncodingOfClaims Coding RecFull Cells claimsLedgerOnAt codingCells linkProtocolOfRoundData)
open OnBytes.Slice (frS frZ DecR)
open _root_.Run.PQ (View CK XO)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open VerifiableInference.OnPublicFiles (threeProtocolsAtFullSize numsRef ppAtFiles)
open LPFD.Full (XF FsAtR)
open VerifierAndGoals (PublicFiles asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)
open scoped ENNReal

/-! ## 1. The index type and the cut, for any three protocols over the full size's configuration -/

/-- The matrices of the full size's shape, over the extension field: every one of them. -/
abbrev FullSizeMatrix : Type := Cells (frS.toDecR frZ 402653181) numsRef

/-- In range: the matrix holds an index of the integer model. The library's own test. -/
abbrev inRange : FullSizeMatrix → Prop := VerifiableInference.OnPublicFiles.Flat.InRange

/-- **The matrices in range.** No public file occurs in this type. -/
abbrev Ix : Type := {M : FullSizeMatrix // inRange M}

/-- The full size's configuration at a table pp of scales and policy; req: the request that an
instance says. -/
abbrev ConfAt {X : Type} (pp : Inst.Model.ScalesAndPolicy) (req : X → Inst.Model.Instance Inst.Model.ppref) :
    ConfigurationWithOutOfDomainSample :=
  DecR.configurationOfStoredTable (claimsLedgerOnAt (frS.toDecR frZ 402653181) numsRef pp req)
    (relationsAndEncodingOfClaims _ (codingCells frS frZ 402653181 numsRef pp req))

section General
variable {X : Type} {pp : Inst.Model.ScalesAndPolicy} {req : X → Inst.Model.Instance Inst.Model.ppref}

/-- **The object of three protocols F and provers P, cut to the matrices in range.** The provers
are typed at every matrix, as `Files.Provers` wants them; the cut reads them at matrices in range.
-/
def cutObj (F : Files (ConfAt pp req)) (P : F.Provers) : HolographicProtocol Ix X :=
  cut (I := FullSizeMatrix) (X := X) (F.withProvers P) inRange

theorem cutObj_eq (F : Files (ConfAt pp req)) (P : F.Provers) :
    cutObj F P = cut (I := FullSizeMatrix) (X := X) (F.withProvers P) inRange := rfl

/-- **`WiredR` of the cut object**, for every F and P, from the three equations on the provers. -/
theorem wired_cutObj (F : Files (ConfAt pp req)) (P : F.Provers) (hE : ExtR (cutObj F P)) :
    (cutObj F P).WiredR :=
  (wired_cut_iff (I := FullSizeMatrix) (X := X) (F.withProvers P) inRange).2
    ⟨fun M hM r s => OnBytes.Flat.obj_decodes_cells_full pp req F P M hM r s, hE⟩

end General

/-- The provers that send fixed messages hold the encoder's tables: by unfolding. For every
configuration and every three protocols. -/
theorem ext_silent {C : ConfigurationWithOutOfDomainSample} (F : Files C) : ExtR (F.withProvers F.fixedMessageProvers) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- The same at the cut object: `ExtR` has a member there. -/
theorem ext_cutObj_silent {X : Type} {pp : Inst.Model.ScalesAndPolicy}
    {req : X → Inst.Model.Instance Inst.Model.ppref} (F : Files (ConfAt pp req)) :
    ExtR (cutObj F F.fixedMessageProvers) :=
  ext_reIndex (I := FullSizeMatrix) (X := X) Subtype.val (back inRange) (ext_silent F)

/-! ## 2. The formats, at any rounds' data and any three decisions -/

/-- The oracle of a round of the written link is a string. (As the library's `pointT`,
OnBytes/Maker/TreesLaws.lean, which is stated for a whole file's rounds.) -/
def pointL1 (C : CK) (d : TypedOracleCompiler.Run.PQ.RD) : (TypedOracleCompiler.Run.PQ.roundS C d).up.IsPoint :=
  ⟨TypedOracleCompiler.Run.PQ.finPosT d.trees, TypedOracleCompiler.Run.PQ.decPosT d.trees, fun f => f,
    fun _ _ => rfl, fun _ => rfl, TypedOracleCompiler.Run.PQ.zeroT d.trees⟩

/-- The same for all its rounds behind the round in front. -/
def pointsL (C : CK) : (ds : List TypedOracleCompiler.Run.PQ.RD) → (TypedOracleCompiler.Run.PQ.uL C ds).IsPoint
  | [] => ()
  | d :: ds => (pointL1 C d, pointsL C ds)

/-- **Every round's oracle of the written link is a string.** -/
theorem linkW_point (C : CK) (ds : List TypedOracleCompiler.Run.PQ.RD) (a : ℕ) (xs : List XO) {X : Type}
    (dec : X → View → Bool) : Nonempty (linkProtocolOfRoundData C ds a xs dec).shape.IsPoint :=
  ⟨(OnBytes.Maker.pointFront C, pointsL C ds)⟩

/-- **The seven clauses on formats for the three protocols of the full size**, at any claims, any
rounds' data DK, DP, ds, any openings xs and any three decisions runK, runP, dec. -/
theorem formats_fullD {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
    (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
    (runK : RecFull → View → View → View → Bool)
    (runP : X × RecFull → View → View → View → Bool) (ds : List TypedOracleCompiler.Run.PQ.RD)
    (xs : List XO) (dec : RecFull × RecFull → View → Bool) (rK rP : RecFull)
    (depthReq : ℕ) (early : X → X) (salt : ℕ)
    (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers) :
    FormatsR ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P) where
  localT := (VerifiableInference.OnPublicFiles.threeProtocolsAtFullSize_local A R DK DP runK runP ds xs dec rK rP
    depthReq early salt).1
  localL := (VerifiableInference.OnPublicFiles.threeProtocolsAtFullSize_local A R DK DP runK runP ds xs dec rK rP
    depthReq early salt).2.1
  localB := (VerifiableInference.OnPublicFiles.threeProtocolsAtFullSize_local A R DK DP runK runP ds xs dec rK rP
    depthReq early salt).2.2
  cohB := (VerifiableInference.OnPublicFiles.threeProtocolsAtFullSize_coherent A R DK DP runK runP ds xs dec rK rP
    depthReq early salt).2
  pointT := OnBytes.Maker.wholeIOR_point (ckP .two) (DK.at frS.P.T.a) (OnBytes.Flat.front₀ rK)
    (OnBytes.Flat.join₀ rK) ByteArray.empty OnBytes.Flat.silK runK
  pointL := linkW_point (ckP .two) ds frS.P.T.a xs dec
  pointB := OnBytes.Maker.wholeIOR_point (ckP .two) (DP.at frS.P.T.a) (OnBytes.Flat.front₀ rP)
    (OnBytes.Flat.join₀ rP) ByteArray.empty OnBytes.Flat.silP runP

/-! ## 3. At three public files Z -/

/-- The configuration at Z: the table of scales and policy is what the library's reader returns at
Z's policy file and its file of scales (the reference's where it refuses). -/
abbrev Cz (Z : PublicFiles) : ConfigurationWithOutOfDomainSample :=
  ConfAt (X := XF) (ppAtFiles (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL) Subtype.val

/-- **The three protocols at Z, with their proof of work in the rounds**: the library's own, at the
letters from which the verifier is compiled. -/
def filesAt (Z : PublicFiles) : Files (Cz Z) :=
  FsAtR (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E (dataAtFiles flashProveData Z).G (dataAtFiles flashProveData Z).DK
    (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runK (dataAtFiles flashProveData Z).runP (dataAtFiles flashProveData Z).dec

/-- **The object at Z, cut to the matrices in range**, for any provers P of the three protocols. -/
def objAt (Z : PublicFiles) (P : (filesAt Z).Provers) : HolographicProtocol Ix XF := cutObj (filesAt Z) P

/-- `WiredR` at every Z and P, from the three equations on P. -/
theorem wired_objAt (Z : PublicFiles) (P : (filesAt Z).Provers) (hE : ExtR (objAt Z P)) :
    (objAt Z P).WiredR :=
  wired_cutObj (filesAt Z) P hE

/-- The seven clauses on formats at every Z and P. -/
theorem formats_objAt (Z : PublicFiles) (P : (filesAt Z).Provers) : FormatsR (objAt Z P) :=
  (formats_cut_iff (I := FullSizeMatrix) (X := XF) ((filesAt Z).withProvers P) inRange).2
    (formats_fullD (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK
      (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runK (dataAtFiles flashProveData Z).runP PV.EntryFive.dsF
      PV.EntryFive.xsF (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).G.rec₀ (dataAtFiles flashProveData Z).G.z₀.2
      (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early
      (LPFD.Full.saltG (dataAtFiles flashProveData Z).G) P)

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.wired_cutObj
#print axioms AtPublicFiles.AtFiles.ext_silent
#print axioms AtPublicFiles.AtFiles.ext_cutObj_silent
#print axioms AtPublicFiles.AtFiles.linkW_point
#print axioms AtPublicFiles.AtFiles.formats_fullD
#print axioms AtPublicFiles.AtFiles.wired_objAt
#print axioms AtPublicFiles.AtFiles.formats_objAt
