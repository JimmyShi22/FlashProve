-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OutputHeadAtTheHonestProver.lean: THE OUTPUT HEAD's OWN ROUNDS (kind K6 of the online proof):
what Johnson/Desc/ProofFile/Honest/K6/Term/Statements.lean states of this kind, AT THE VALUES OF THE
HONEST PROVER (E2E/TheHonestProver.lean). Definitions alone.

WHAT IT IS NOT.
  * Nothing is proved here. It does not say that the verifier accepts.
  * IT DOES NOT SAY THAT THE KIND PAYS ALL THAT IT OWES. SideAndBook holds where the kind stands,
    which side the prover has there, the seat, and (P1). Of (P2) it holds nothing: the five
    statements at border 341 are general in the prover (Statements.lean, § 5) and are had at every
    prover with the seat. At the frame's riders csHead and the border 339, four of them then stand
    under two premises on the frame's letter for "keeps". The fifth, ExchangeS, which bears the
    weight, stands under the twelve fields of K6HeadBelow, of which no value is shown at these
    values.
  * THEY MAY HOLD FOR NOTHING: "the maker returns" is a premise, shown at no files in any sealed
    tree; so is the library's hypothesis on the first chain.
  * All limits in the head of Statements.lean hold here.

WHAT IT IS. Two values of the maker's return.
  THE BASE PROVER: the maker's return at onlineProverPartsInUse matrixInput secondHashFunction Sz.ref openHonest, at
    the stored tables' randomness IndexCommitterCoins. The first chain's thread is laid at this prover's sides;
    the crossing from there to the honest prover is one law for the whole file, of other authors.
  THE HONEST PROVER's OWN RETURN: onlineMaker files, which is the maker at that filling read through
    id and tableCoins files.
  FillingIsTheValue            the honest prover's filling is onlineFillingAt at its six values
  FramedProverIsHandedToTheFrame   framedProver is the prover that onlineProverAt hands to the
                               frame: onlineProverAt is the frame's family onlineProversAlongInstanceMap at it
  FramedProverKeepsTheSides    that prover has the maker's sides in all three chains, its range of
                               the index and its named index
  OnlineProverIsTheProverAtTheReturn   where the maker returns, under the library's hypothesis: the
                               honest prover's online term, onlineProver files, is onlineProverAt at
                               that return and at the hypothesis's places and first chain
  OutputHeadAtTheBaseProver, OutputHeadAtTheHonestProver   SideAndBook at the two returns

ON refuseUnserved. The value that the statements on completeness and zero knowledge read is the
honest provers under refuseUnserved, which widens the online prover's private stop SET and changes
no side and no strategy. The statements here read no prover's stop set. PlaysS and AcceptedS read
the two stops of the PARTS of the side at the member; this kind's parts never stop (RowNeverStops).
-/
import E2E.TheHonestProver
import Johnson.Desc.ProofFile.Honest.K6.Term.Statements

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm.OutputHead
open AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Cut
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest
open ProofFile.Honest.Term (OnlineReturn onlineMaker onlineFilling matrixInput tableCoins)
open ProofFile.Honest.K6 (K6HalfAt)
open ProofFile.Honest.K6.Term
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)
open P5J (AtMgA TS F0T)

local instance (priority := high) padsOfTheOutputHeadStatements : Nonempty PadZ :=
  pads_nonempty frS 402653181

/-- As in E2E/TheHonestProver.lean, where these two are local: given by hand. -/
local instance (priority := high) someRunValueOfTheOutputHeadStatements : Nonempty RunValue :=
  ⟨fun _ => 0⟩

local instance (priority := high) defaultRunValueOfTheOutputHeadStatements :
    Inhabited RunValue := ⟨fun _ => 0⟩

/-! ## 1 The two values -/

/-- **The maker at the base filling**: the honest prover's filling before it is read through. -/
abbrev baseMaker (files : PublicFiles) : Except String (OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) :=
  onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
    (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest)

/-- **The honest prover's online filling is the general one at its six values.** -/
def FillingIsTheValue : Prop :=
  ∀ files : PublicFiles, onlineFilling files =
    onlineFillingAt id (tableCoins files) matrixInput.dummy matrixInput
      OnBytes.HonestTrace.Sz.ref openHonest

/-- **The prover that the online honest prover hands to the frame**: the maker's, with the
committer's columns as its stored table at the item 0, no column at any other item, and the
committer's key (onlineProversOfCommitter, E2E/BridgeTied.lean). -/
abbrev framedProver {files : PublicFiles} (returned : OnlineReturn files) :=
  (cmAlong (AZ files) PadZ (holdZ files)).proverAt 0 returned.H

/-- **It is what the frame is handed**: the online honest prover at a return of the maker is the
frame's family onlineProversAlongInstanceMap at the online description, the maker's book and framedProver. The other
arguments are those of onlineProversOfCommitter (E2E/BridgeTied.lean), at the run values' bytes. -/
def FramedProverIsHandedToTheFrame : Prop :=
  ∀ (files : PublicFiles) (returned : OnlineReturn files) (places : H2U.Places4)
    (firstChain : Chain TS ProofFile.Cl),
    onlineProverAt returned places firstChain =
      onlineProversAlongInstanceMap files (F0T OnBytes.secondHashFunction returned.Z places firstChain) LPFD.Full.instanceAsPlainRecord silInst
        returned.B (framedProver returned)
        (fun n r2 r3 => (cmAlong (AZ files) PadZ (holdZ files)).seam
          (frontAt (AZ files) PadZ (holdZ files) n r2 r3)
          (joinAt (AZ files) PadZ (holdZ files) runValueBytes r2)
          (seamAt (AZ files) PadZ (holdZ files) runValueBytes r2 r3))
        (shAt returned.Z places firstChain)
        ((cmAlong (AZ files) PadZ (holdZ files)).ext ((dataAtFiles flashProveData files).DP.at frS.P.T.a).a)
        (dataAtFiles flashProveData files).P

/-- **It has the maker's sides in all three chains, its range of the index and its named index**: so
what is shown of these five at the maker's prover holds at the prover that the frame is handed. -/
def FramedProverKeepsTheSides : Prop :=
  ∀ (files : PublicFiles) (returned : OnlineReturn files),
    (framedProver returned).first = returned.H.first ∧
      (framedProver returned).shared = returned.H.shared ∧
      (framedProver returned).second = returned.H.second ∧
      (framedProver returned).inRange = returned.H.inRange ∧
      (framedProver returned).dummy = returned.H.dummy

/-- **The honest prover's online term is the online prover at the maker's return**: where the maker
returns, the places and the first chain that onlineProver reads off the return's public part are
those of the library's hypothesis on the first chain, so the term takes neither of its two arms that
send the fixed messages. -/
def OnlineProverIsTheProverAtTheReturn (files : PublicFiles) : Prop :=
  ∀ (returned : OnlineReturn files) (places : H2U.Places4) (firstChain : Chain TS ProofFile.Cl)
    (D : WholeD) (r : LPFD.Full.RunPF) (x : VerifiableInference.Desc.First.Look.Place),
    onlineMaker files = .ok returned →
    AtMgA OnBytes.secondHashFunction files D r returned.Z places firstChain x →
    onlineProver files = onlineProverAt returned places firstChain

/-! ## 2 What is had of the kind at a return of the maker -/

/-- **Where the kind stands, which side the prover has there, the seat, and (P1)**: at a return of
the maker at the matrices, whatever the type of the stored tables' randomness. Nothing of (P2). -/
structure SideAndBook {Rc : Type} (returned : OnlineProverWithDescription FullSizeMatrix Rc Cells Unit Unit) (places : H2U.Places4)
    (firstChain : Chain TS ProofFile.Cl) : Prop where
  /-- the kind stands at number 341 of the first chain and nowhere else -/
  stands : StandsAtOneBorder (F0T OnBytes.secondHashFunction returned.Z places firstChain)
  /-- the prover's first side there is the row; no other side of the first chain is of the kind -/
  side : SideIsTheOnlyOne returned.H.first (headSide id matrixInput returned.Z returned.G)
  /-- no side of the shared chain is of the kind -/
  noneShared : ∀ q ∈ returned.H.shared, q.place.kind ≠ .K6
  /-- no side of the last chain is of the kind -/
  noneLast : ∀ q ∈ returned.H.second, q.place.kind ≠ .K6
  /-- the seat: the premise of the statements (P2) -/
  seat : K6HalfAt returned.Z returned.H (headReader id matrixInput returned.Z returned.G)
  /-- (P1) in the first chain -/
  paysFirst : KindPays returned.B 0 (F0T OnBytes.secondHashFunction returned.Z places firstChain).first.blocksInOrder
    returned.H.first .K6
  /-- against emptiness: a member of the first chain stands at the kind's place, and the frame's
  set-up routine returns at it at the prover's own list of sides -/
  stepsReturn : ∃ member ∈ (F0T OnBytes.secondHashFunction returned.Z places firstChain).first.blocksInOrder,
    member.place = IM.k6Place ∧
      ∀ (view : Option (Local FullSizeMatrix Rc ProofFile.Inst Cells)) (coins : Coins returned.B),
        ∃ steps, chainSteps returned.B (returned.B.rowsOf 0) (coins.look 0) view [member]
          returned.H.first = .ok steps
  /-- (P1) in the shared chain: of nothing -/
  paysShared : KindPays returned.B 1 (F0T OnBytes.secondHashFunction returned.Z places firstChain).shared.blocksInOrder
    returned.H.shared .K6
  /-- (P1) in the last chain: of nothing -/
  paysLast : KindPays returned.B 2 (F0T OnBytes.secondHashFunction returned.Z places firstChain).second.blocksInOrder
    returned.H.second .K6

/-- **At the base prover.** Under the library's hypothesis on the first chain, at every return of
the maker at the base filling. -/
def OutputHeadAtTheBaseProver (files : PublicFiles) : Prop :=
  ∀ (base : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) (places : H2U.Places4)
    (firstChain : Chain TS ProofFile.Cl) (D : WholeD) (r : LPFD.Full.RunPF)
    (x : VerifiableInference.Desc.First.Look.Place),
    baseMaker files = .ok base →
    AtMgA OnBytes.secondHashFunction files D r base.Z places firstChain x →
    SideAndBook base places firstChain

/-- **At the honest prover's own return.** Under the same hypothesis, at every return of
onlineMaker. -/
def OutputHeadAtTheHonestProver (files : PublicFiles) : Prop :=
  ∀ (returned : OnlineReturn files) (places : H2U.Places4) (firstChain : Chain TS ProofFile.Cl)
    (D : WholeD) (r : LPFD.Full.RunPF) (x : VerifiableInference.Desc.First.Look.Place),
    onlineMaker files = .ok returned →
    AtMgA OnBytes.secondHashFunction files D r returned.Z places firstChain x →
    SideAndBook returned places firstChain

end AtPublicFiles.AtFiles.HonestTerm.OutputHead
