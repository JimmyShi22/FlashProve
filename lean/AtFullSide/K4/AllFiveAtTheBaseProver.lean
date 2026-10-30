-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K4/AllFiveAtTheBaseProver.lean: CONDITIONAL.

Can the hypotheses be met together? The first statement asks that the base maker returns A at the
files (hA : `baseMaker files = .ok A`, E2E/BaseMaker.lean), h : `HeadAtReturn files A`
(Honest/Thread/TheFirstThread.lean) and g < 12, and nothing else: facts on the public files and the
maker's return alone. BOTH ARE MET TOGETHER AT THE STORED FILES `VerifierAndGoals.storedPublicFiles`, with no hypothesis:
`base_met_zFull` (Johnson/Desc/ProofFile/Honest/K4/Law/BaseMetAtFull.lean; not called here). The
second asks hyes besides: the run on shapes over all 358 members of the first chain says yes from
the shape a₀: a premise that all kinds of the first chain share; that it is true at any public part
is not shown here. AND ALL FIELDS OF BOTH ENDS ARE IMPLICATIONS FROM THE THREAD's STAND IN FRONT OF
THE MEMBER: A STAND OF THIS THREAD IS SHOWN AT BORDER 0, WHERE ready RETURNS AND okStart ACCEPTS
(`enters_at_the_written_script`, AtFullSide/HonestTrace/StartFieldsAtTheWrittenScript.lean); NO
THEOREM OF THIS LIBRARY THAT NAMES THIS THREAD SHOWS A STAND OF IT AT ANY BORDER BEYOND 0 BUT FROM A
PREMISE THAT HOLDS ONE, SO THE STATEMENTS ARE NOT SHOWN HERE TO SPEAK AT ANY RUN.

What is here. THE THREADS' WRITERS' TWO STRUCTURES `FiveAtBorder` AND `FiveAtBorderJ`
(Honest/Thread/FiveAtBorder.lean) AT THE TWELVE MEMBERS OF THE FEED-FORWARD LAYERS' OWN ROUNDS (kind
K4), the members number 28 g + 4, g < 12, AT THEIR ONE TERM FOR THE FIRST CHAIN's THREAD
(`firstThread`) AT THE BASE PROVER, WITH THE BASE PROVER's SCRIPT LAID FOR THE THREAD's SCRIPT
(`theScript h`, AtFullSide/K4/SignsLetters.lean) AND THE THREAD's OWN LIST OF FALLS, WITH NO FIELD
OF THE END LEFT AS A HYPOTHESIS. No definition; statements with their proofs: calls. Each end stands
twice: by the group g, at the number 28 g + 4; and BY MEMBER AND KIND, in the form that the writers
of K5's lemmas gave theirs (`kindFive_five_at_every_member_honest`): at any number b at which a
member of the kind K4 stands.

  `k4_all_five_at_the_base_prover`   **`FiveAtBorder` there**: `PlaysS`, `BehindS`, `ExchangeS`,
      `RidesPastS`, `AcceptedS`: from h, hA and g < 12.
  `k4_all_six_with_shapes_at_the_base_prover`   **`FiveAtBorderJ` there**, at the family J := "the
      run on shapes over the members in front returns the state's shape": the first four,
      `AcceptedJ` and `NextJ`: from h, hA, g < 12 and hyes.
  `kindFour_member_number`   a member of the first chain of the kind K4 stands at one of the twelve
      numbers.
  `kindFour_five_at_every_member_honest`   **`FiveAtBorder` by member and kind**, at any fall under
      cover: the fall speaks wherever the thread's own falls speak at the member. K4 HAS A FALL (the
      zero challenge), SO THE STATEMENT DOES NOT STAND AT EVERY FALL.
  `kindFour_five_at_every_member_honest_at_the_threads_falls`   the same at the thread's own falls.
  `kindFour_six_with_shapes_at_every_member_honest`   **`FiveAtBorderJ` by member and kind**, under
      cover and runOnShapesSaysYes (hyes).
  `kindFour_base_maker_is`   the base maker written out: by unfolding.

Whence each field. Law/FiveAtBaseProver.lean and Law/FiveWithShapesAtBaseProver.lean (under
Johnson/Desc/ProofFile/Honest/K4/) name the payers of all but `ExchangeS`; that one is
`column_hX_at_first_thread_whole` (AtFullSide/K4/ColumnAtTheFirstThreadWhole.lean).

Letters. The public files, the return A, the falls' stated numbers, the run's input w, what has been
said (Said) and the shape a₀ are arguments: nothing is asked of them beyond h, hA and hyes.

Limits. CONDITIONAL, as said at the top. This is K4's share (P2) of "accepted" at the base prover;
its share (P1) is not here. How often the fall speaks is not said here. `enters_firstThread`
(Honest/Thread/EntersFirst.lean) gives border 0 under ready's return, okStart, the parse, `ServesAt`
and `ScriptTies` at this Script; under ready's return and okStart the other three are paid and
border 0 is had (`start_fields_at_the_written_script`, `enters_at_the_written_script`,
AtFullSide/HonestTrace/StartFieldsAtTheWrittenScript.lean); that ready returns is not shown here; at
storedPublicFiles some input meets the three clauses of `ReadyInput` at this prover
(inputAroundTheStart_atStoredFiles, AtFullSide/HonestTrace/EntersAtStoredFilesInput.lean); at other
files in scope where protocolDataWellFormed passes the three stand apart (`servedInput_atBaseReturn`, the same
file; `okStart_of_live`, AtFullSide/T3/StartOfLive.lean), joined by no statement named here; and at
an input that does not meet it the thread stands nowhere. AT THE BASE MAKER's RETURN, AT `IndexCommitterCoins`:
NOT AT THE ONLINE MAKER's RETURN (`onlineFilling`, E2E/TheHonestProver.lean, is this filling read
through `OnlineProverParts.through`): the crossing is not here. BENEATH `ExchangeS` AT THE GROUPS g > 0 LIE 25
CLOSED FACTS ON THE CODE SWITCHES' CLOSINGS, BY LEAN's KERNEL, REPLAYED BY NO INDEPENDENT CHECKER
(Honest/K2/Law/ClosingW0.lean to ClosingW4.lean, their writers' files). `firstThread`,
`FiveAtBorder`, `FiveAtBorderJ` and `baseMaker` are other writers' definitions; if they turn, these
statements turn with them. THE FULL SIZE ALONE, AND THE FORMAT's EARLIER HASH ALONE. A LAW, NOT A
PART; it states no goal. Nothing on soundness, on completeness or on any other property.
No property is claimed.
-/
import AtFullSide.K4.ColumnAtTheFirstThreadWhole
import E2E.BaseMaker
import Johnson.Desc.ProofFile.Honest.K4.Law.FiveAtBaseProver
import Johnson.Desc.ProofFile.Honest.K4.Law.FiveWithShapesAtBaseProver
import Johnson.Road.K4.K04Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K4
open ProofFile ProofFile.Honest ProofFile.Honest.K4
open ProofFile.Honest.Term (baseMaker matrixInput)
open ProofFile.Honest.FirstThread (HeadAtReturn FallNumbers firstThread firstFalls seatGround)
open ProofFile.Honest.K1 (LocB firstScriptAt)
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Block KindName)
open VerifiableInference.Desc.Sound (linksFull)
open P5J (TS)
open AtFullSide.K4.Signs (theScript column_hX_at_first_thread_whole)
open Johnson.AtFull.Shape (Tab.g Tab.vals firstZA ShA)
open AtPublicFiles.AtFiles (FullSizeMatrix)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
  (h : HeadAtReturn files A)

/-- CONDITIONAL: on h, hA and hg. **ALL FIVE STATEMENTS AT K4's BORDER 28 g + 4, AT THE BASE
PROVER's FIRST THREAD WITH THE BASE PROVER's SCRIPT, AT THAT THREAD's OWN FALLS.** Each of the five
is an implication from the thread's stand in front of the member; no theorem of this library that
names this thread shows a stand of it at any border beyond 0 but from a premise that holds one. -/
theorem k4_all_five_at_the_base_prover (hA : baseMaker files = .ok A) (numbers : FallNumbers)
    (w : LocB FullSizeMatrix) (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop) {g : ℕ} (hg : g < 12) :
    FiveAtBorder (firstThread h ⟨theScript h, numbers⟩ w) Said
      (fallsBy (firstFalls A numbers) h.firstChain.blocksInOrder) (28 * g + 4) :=
  k4_five_at_base_prover h ⟨theScript h, numbers⟩ w Said hA hg
    (column_hX_at_first_thread_whole h hA numbers w Said hg)

/-- CONDITIONAL: on h, hA, hyes and hg. **ALL SIX STATEMENTS OF THE FORM WITH THE FAMILY "THE RUN ON
SHAPES RETURNS THE STATE's SHAPE", THERE.** hyes: the run on shapes over all 358 members says yes
from a₀. Each of the six is an implication from the thread's stand in front of the member; no
theorem of this library that names this thread shows a stand of it at any border beyond 0 but from a
premise that holds one. -/
theorem k4_all_six_with_shapes_at_the_base_prover (hA : baseMaker files = .ok A)
    (numbers : FallNumbers) (w : LocB FullSizeMatrix) (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop)
    (a₀ : ShA)
    (hyes : (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))).yes a₀ 358 = true)
    {g : ℕ} (hg : g < 12) :
    FiveAtBorderJ (firstThread h ⟨theScript h, numbers⟩ w) Said
      (shapeJ (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))) a₀)
      (fallsBy (firstFalls A numbers) h.firstChain.blocksInOrder) (28 * g + 4) :=
  k4_five_with_shapes_at_base_prover h ⟨theScript h, numbers⟩ w Said hA a₀ hyes hg
    (column_hX_at_first_thread_whole h hA numbers w Said hg)

/-! ## By member and kind -/

/-- The base maker, written out. -/
theorem kindFour_base_maker_is (files : VerifierAndGoals.PublicFiles) :
    baseMaker files = onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction Sz.ref openHonest) := rfl

/-- CONDITIONAL: on head. **A member of the first chain of the kind K4 stands at one of the twelve
numbers 28 g + 4.** -/
theorem kindFour_member_number (head : HeadAtReturn files A) {b : Nat} {member : Block TS ProofFile.Cl}
    (atNumber : head.firstChain.blocksInOrder[b]? = some member)
    (ofTheKind : member.place.kind = KindName.K4) : ∃ g, g < 12 ∧ b = 28 * g + 4 := by
  have e := P5J.At.places_paid head.head.scope head.head.reads head.head.laid
  have hp : P5J.At.ps[b]? = some member.place := by
    rw [← e]
    unfold VerifiableInference.Desc.First.blockPlaces
    rw [List.getElem?_map, atNumber]
    rfl
  have e' : P5J.At.ps = VerifiableInference.Desc.First.flatPlacesOf linksFull true := by
    unfold P5J.At.ps
    rw [Second.Seam.links_one.1]
  rw [e'] at hp
  obtain ⟨g, hg, eb, -⟩ := OnBytes.Road.K4.k04_places_full b member.place hp ofTheKind
  exact ⟨g, hg, eb⟩

/-- CONDITIONAL: on head, made and cover. **ALL FIVE STATEMENTS AT EVERY MEMBER OF THE KIND K4, AT
THE BASE PROVER's FIRST THREAD WITH THE BASE PROVER's SCRIPT**, at any fall that speaks wherever the
thread's own falls speak at the member (cover). Each of the five is an implication from the thread's
stand in front of the member; no theorem of this library that names this thread shows a stand of it
at any border beyond 0 but from a premise that holds one. -/
theorem kindFour_five_at_every_member_honest (head : HeadAtReturn files A)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction Sz.ref openHonest) = .ok A)
    (numbers : FallNumbers) (input : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) {b : Nat} {member : Block TS ProofFile.Cl}
    (atNumber : head.firstChain.blocksInOrder[b]? = some member)
    (ofTheKind : member.place.kind = KindName.K4)
    (cover : ∀ s ds, fall b s ds = none →
      fallsBy (firstFalls A numbers) head.firstChain.blocksInOrder b s ds = none) :
    FiveAtBorder
      (firstThread head ⟨firstScriptAt matrixInput Sz.ref openHonest A head.firstChain, numbers⟩
        input)
      Said fall b := by
  obtain ⟨g, hg, rfl⟩ := kindFour_member_number head atNumber ofTheKind
  have F := k4_all_five_at_the_base_prover head made numbers input Said hg
  exact ⟨F.plays, F.behind, F.exchange, F.ridesPast,
    fun blk hblk k s m E ds y cols hT hd hst hf hM =>
      F.accepted blk hblk k s m E ds y cols hT hd hst (cover s ds hf) hM⟩

/-- CONDITIONAL: on head and made. **THE SAME AT THE THREAD's OWN FALLS.** -/
theorem kindFour_five_at_every_member_honest_at_the_threads_falls (head : HeadAtReturn files A)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction Sz.ref openHonest) = .ok A)
    (numbers : FallNumbers) (input : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    {b : Nat} {member : Block TS ProofFile.Cl} (atNumber : head.firstChain.blocksInOrder[b]? = some member)
    (ofTheKind : member.place.kind = KindName.K4) :
    FiveAtBorder
      (firstThread head ⟨firstScriptAt matrixInput Sz.ref openHonest A head.firstChain, numbers⟩
        input)
      Said (fallsBy (firstFalls A numbers) head.firstChain.blocksInOrder) b :=
  kindFour_five_at_every_member_honest head made numbers input Said _ atNumber ofTheKind
    fun _ _ hf => hf

/-- CONDITIONAL: on head, made, runOnShapesSaysYes and cover. **ALL SIX STATEMENTS OF THE FORM WITH
THE FAMILY "THE RUN ON SHAPES RETURNS THE STATE's SHAPE", AT EVERY MEMBER OF THE KIND K4, THERE.**
Each of the six is an implication from the thread's stand in front of the member; no theorem of this
library that names this thread shows a stand of it at any border beyond 0 but from a premise that
holds one. -/
theorem kindFour_six_with_shapes_at_every_member_honest (head : HeadAtReturn files A)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction Sz.ref openHonest) = .ok A)
    (numbers : FallNumbers) (input : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) (firstShape : ShA)
    (runOnShapesSaysYes :
      (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))).yes firstShape 358 = true)
    {b : Nat} {member : Block TS ProofFile.Cl} (atNumber : head.firstChain.blocksInOrder[b]? = some member)
    (ofTheKind : member.place.kind = KindName.K4)
    (cover : ∀ s ds, fall b s ds = none →
      fallsBy (firstFalls A numbers) head.firstChain.blocksInOrder b s ds = none) :
    FiveAtBorderJ
      (firstThread head ⟨firstScriptAt matrixInput Sz.ref openHonest A head.firstChain, numbers⟩
        input)
      Said (shapeJ (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))) firstShape)
      fall b := by
  obtain ⟨g, hg, rfl⟩ := kindFour_member_number head atNumber ofTheKind
  have F := k4_all_six_with_shapes_at_the_base_prover head made numbers input Said firstShape
    runOnShapesSaysYes hg
  exact ⟨F.plays, F.behind, F.exchange, F.ridesPast,
    fun blk hblk k s m E ds y cols hT hJ hd hst hf hM =>
      F.accepted blk hblk k s m E ds y cols hT hJ hd hst (cover s ds hf) hM,
    fun blk hblk k s m E ds y cols s' hT hJ hd hst hf hS =>
      F.next blk hblk k s m E ds y cols s' hT hJ hd hst (cover s ds hf) hS⟩

end AtFullSide.K4

#print axioms AtFullSide.K4.kindFour_base_maker_is
#print axioms AtFullSide.K4.kindFour_member_number
#print axioms AtFullSide.K4.kindFour_five_at_every_member_honest
#print axioms AtFullSide.K4.kindFour_five_at_every_member_honest_at_the_threads_falls
#print axioms AtFullSide.K4.kindFour_six_with_shapes_at_every_member_honest
#print axioms AtFullSide.K4.k4_all_five_at_the_base_prover
#print axioms AtFullSide.K4.k4_all_six_with_shapes_at_the_base_prover
