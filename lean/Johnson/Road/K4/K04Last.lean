-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K04Last.lean: WHAT IS LEFT OF THE KIND K4's NAMED CONDITIONS OVER THE ENTRY TESTS'
THIRTEEN ROWS: ONE TEST WITH CODE ON THE PUBLIC PARAMETERS. One structure, four statements with
their proofs. No new argument: calls.

FIRST. NO FILE STATES A MEMBER OF `K4Last`. `K4Last hA` FOLLOWS
FROM THE HEAD hA (`k4Last_of_head`, Johnson/Road/K4/K04OfHead.lean). NO
PUBLIC FILES ARE SHOWN AT WHICH IT HOLDS. A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE
(AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/); NO FILE JOINS `K4Last` TO THAT MEMBER. K04_law IS NOT
PROVED BY THIS. EVALUATIONS ARE NO PROOFS.

THE GROUND. THIS FILE STANDS ONLY WHERE THE VERIFIER's DOOR HOLDS THE ENTRY TESTS' FIRST THIRTEEN
ROWS (Johnson/Desc/Laid/ProofAsks.lean, whose list has fourteen: row 9, `madeRow`, "the pin",
compares the plan with the written values, and row 10, `cutRow`, the first chain's cut; both at the
full size's key): the door of which the join's theorem is to speak; NOT a door of the first eight.
Over these thirteen rows `written_of_head`, `cut_of_head`, `laid_of_head`
(Johnson/Road/K4/K4HeadWritten.lean) draw three of `K4Owes`' five fields from the head alone, and a
fourth, sends, comes of `Meaning.K2.hB_paid` (Johnson/IMR/EndFiveMade.lean) at
`P5J.AtMg.pins` (Johnson/P5T/FenceAtMg.lean: row 9's accept at the head). THAT IS A
MOVE, NOT A PAYMENT: the four leave K4's list because the head is heavier there: its entry tests
have five rows more; the four are drawn from rows 9 and 10, read by name, and from the yes of the
whole list, which gives back that the value is laid; row 9 is a stronger premise than the test sends
that falls for it (its payer's own words): WHOEVER COUNTS SAYS BOTH: "one field" AND "under a head
whose entry tests have thirteen rows, not eight".

THREE LAYERS. `K4Cond hA L Pp` (K04Cond.lean): the form in which K4's law takes its conditions, and
which the join names · `K4Owes hA L` (K04Owes.lean): what is left behind the payers that need no
more than the head's own ground · `K4Last hA` (here): what is left over the entry tests' thirteen
rows.

  `K4Last hA`: ONE FIELD: row: ONE TEST WITH CODE ON THE PUBLIC PARAMETERS. NO LETTER L, NO Pp,
    NOTHING ALONG THE RUN.
  `k4Owes_of_last`: `K4Last hA` → ∃ L, `K4Owes hA L`.
  `k4Cond_of_last`: `K4Last hA` → ∃ L, `K4Cond hA L Pp`, at every Pp: THE FORM OF THE JOIN's FIELD
    FOR THE KIND K4.
  `k04_of_last`: `K4Last hA` → for every Pp and every 𝔏 with the three lists' heads: the end of
    `k04_of_cond_pub`.
  `k04_counted_of_last`: `K4Last hA` → for every such 𝔏: `AtMgA.Kind hA 𝔏 KindName.K4`: THE FORM IN
    WHICH A KIND's LAW IS COUNTED (through `k04_counted`, K04Counted.lean).

Limits. THE FIELD IS A PREMISE, AND IT IS ASKED BY NOBODY: no row of either door named above
asks it, and no theorem that we know gives it. The written values beneath rest on prints of
the evaluator. The full size alone. The second hash function alone. Nothing on soundness.

-/
import Johnson.Road.K4.K04Owes
import Johnson.Road.K4.K4HeadWritten
import Johnson.Road.K4.K04Counted
import Johnson.IMR.EndFiveMade
import Johnson.P5T.FenceAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop
open OnBytes OnBytes.Flat OnBytes.Maker KObj
open OnBytes.Model (Fork WsLay)
open OnBytes.Model.Verify (Public)
open VerifiableInference.OnPublicFiles (LeftQ)
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Road.K4.InT (StatesAt)
open _root_.Run (ckP)
open VerifiableInference.Desc (Block FileDescription KindName Wit Claim Link K9.LinkHoles K9.statesOfLink)
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers flatPlacesOf start openSets)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K13.Law (lowBits)
open Inst.Model (Scl ppref)
open Meaning.Emb (EmbNums)
open OnBytes.Model.Verify (layerShape)
open Inst.Model.Layout (kRef hRef)
open Inst.Model.FFSeg (LW)
open Cb.Pv.Tail (Size)
open OnBytes.Model (Forest.elems)
open OnBytes.Desc.First.K4 (formsBack)
open VerifiableInference.PlanWritten (PublicSteps publicSteps_of)
open VerifiableInference.Desc.First (readsOpen moreItem)
open VerifiableInference.Desc.First.Look (pubAt stepOf)
open VerifiableInference.Desc.Plain.K04 (FormsT frontRun)
open VerifiableInference.Desc.K13.Law (matOfCells)

open Johnson.Desc.First.Walk.Tied (RchAt RchPub)
open OnBytes.Slice (frS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
/-- The IOP as written in Lean, at the head's letters. -/
local notation "𝐅" => (P5J.F0T OnBytes.secondHashFunction Zp Np cF)

set_option quotPrecheck false in
/-- The first chain's frame, at the head's letters. -/
local notation "𝐅𝐫" => (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)

/-- **WHAT K4's LAW IS OWED, BY NAME, OVER THE ENTRY TESTS' THIRTEEN ROWS.** NO MEMBER IS
KNOWN. -/
structure K4Last (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) : Prop where
  /-- WHAT IS LEFT OF `K4Cond`'s FIELD named (nine tests: three that name no group, six asked at
  each of the twelve: 75 closed tests by a count): ONE TEST WITH CODE ON THE PUBLIC
  PARAMETERS ALONE (`k4RowB`, Johnson/Road/K4/K4RowTest.lean). WHAT IT GIVES, WHICHEVER VERSION OF
  ITS TEXT LIES: under the head its accept yields that at each of the twelve groups the listing
  front and the routine wsPending's row accept (`k4Row_two`, Johnson/Road/K4/K4RowTestLaws.lean:
  called): 24 tests. ASKED BY NOBODY: neither the eight entry tests nor the thirteen have such a
  row, and no theorem gives it. The other seven of the
  nine are other files' theorems (called): four with no written value (toldFit, book, lookIn,
  readsP), three under written, cut and laid (fence, room1, maskP). The 24 have been evaluated
  true at the shipped full-size set, both negative tests rejecting at each group (a run, as
  reported, not shown here). -/
  row : k4RowB Zp = true

/-- **Over the entry tests' thirteen rows the last list gives the shorter one, at the L that the
reader returns.** -/
theorem k4Owes_of_last {hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀} (C : K4Last hA) :
    ∃ L, K4Owes hA L := by
  obtain ⟨L, hL⟩ := laid_of_head hA.toAtMg
  exact ⟨L,
    { sends := fun {Bs base} O =>
        Meaning.K2.hB_paid hA.scope hA.laid.planOk hA.toAtMg.pins.1 Bs base _ _ O
      row := C.row
      written := written_of_head hA.toAtMg
      cut := cut_of_head hA.toAtMg
      laid := hL }⟩

/-- **THE FORM OF THE JOIN's FIELD FOR THE KIND K4**, at every Pp. NO FILE STATES A MEMBER OF
`K4Last`. `K4Last hA` follows from the head (`k4Last_of_head`); A MEMBER OF THE HEAD IS PROVED AT
`storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/). -/
theorem k4Cond_of_last {hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀}
    {Pp : ProofFile.InstPub → Prop} (C : K4Last hA) : ∃ L, K4Cond hA L Pp := by
  obtain ⟨L, O⟩ := k4Owes_of_last C
  exact ⟨L, k4Cond_of_owes O⟩

/-- **K4's OWN SENTENCE FOR THE JOIN, UNDER THE LAST LIST.** NO FILE STATES A MEMBER OF `K4Last`;
UNDER THE HEAD hA: A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE
LIBRARY AtFullSide/Top/). -/
theorem k04_of_last (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (Pp : ProofFile.InstPub → Prop) (C : K4Last hA)
    (𝔏 : P5J.Free numsFull D 𝐅 P5J.At.Tok)
    (q₁ : (𝐅).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) (q₂ : (𝐅).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (𝐅).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    KindTiedR (Fr := 𝐅𝐫) (P5J.At.N Zp cF) (P5J.mgAt hA.toAtMg hA.𝔇) P5J.fullLinks P5J.At.ps
      (RchPub 𝐅 Pp) (hA.toAtMg.ex 𝔏) (hA.toAtMg.row 𝔏) KindName.K4 := by
  obtain ⟨L, O⟩ := k4Owes_of_last C
  exact k04_of_owes hA L Pp O 𝔏 q₁ q₂ q₃

/-- **THE SAME IN THE FORM IN WHICH A KIND's LAW IS COUNTED.** NO FILE STATES A MEMBER OF `K4Last`;
UNDER THE HEAD hA: A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE
LIBRARY AtFullSide/Top/). -/
theorem k04_counted_of_last (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (C : K4Last hA)
    (𝔏 : P5J.Free numsFull D 𝐅 P5J.At.Tok)
    (q₁ : (𝐅).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) (q₂ : (𝐅).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (𝐅).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) : P5J.AtMgA.Kind hA 𝔏 KindName.K4 := by
  obtain ⟨L, O⟩ := k4Cond_of_last (Pp := hA.toAtMg.typed) C
  exact k04_counted hA L O 𝔏 q₁ q₂ q₃

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4Owes_of_last
#print axioms OnBytes.Road.K4.k4Cond_of_last
#print axioms OnBytes.Road.K4.k04_of_last
#print axioms OnBytes.Road.K4.k04_counted_of_last
set_option pp.deepTerms true in
set_option pp.maxSteps 1000000 in
set_option pp.proofs true in
#check @OnBytes.Road.K4.k4Cond_of_last
set_option pp.deepTerms true in
set_option pp.maxSteps 1000000 in
set_option pp.proofs true in
#check @OnBytes.Road.K4.k04_counted_of_last
set_option pp.deepTerms true in
set_option pp.maxSteps 1000000 in
#print OnBytes.Road.K4.K4Last
