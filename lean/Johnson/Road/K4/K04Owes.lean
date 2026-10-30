-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K04Owes.lean: WHAT IS LEFT OF THE KIND K4's NAMED CONDITIONS ONCE THE PAYERS THAT
NEED NO MORE THAN THE HEAD's OWN GROUND ARE CALLED. One structure, two statements with their proofs.
No new argument: calls.

FIRST. NO FILE STATES A MEMBER OF `K4Owes`. AT SOME L,
`K4Owes hA L` FOLLOWS FROM THE HEAD hA (`k4Owes_of_last` at `k4Last_of_head`:
Johnson/Road/K4/K04Last.lean, K04OfHead.lean). NO PUBLIC FILES ARE SHOWN AT WHICH IT HOLDS. A MEMBER
OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/); NO FILE
JOINS `K4Owes` TO THAT MEMBER. K04_law IS NOT PROVED BY THIS. EVALUATIONS ARE NO PROOFS.

LAYERS, AND WHY. `K4Cond hA L Pp` (K04Cond.lean) IS THE FORM IN WHICH K4's LAW TAKES ITS CONDITIONS:
it stays as it is, so that the payers, which end in its fields to the letter, and the join, which
names it, need not turn each time one more field is paid. `K4Owes hA L` IS THE SHORTER LIST THAT
GIVES IT: this file turns whenever a payer comes home.

  `K4Owes hA L`: five fields, each named, ALL ON THE PUBLIC PARAMETERS: NOTHING IS LEFT ALONG THE
    RUN: sends: what is left of `K4Cond`'s wide, room and lay7 · row: what is left of its field
    named · written: `K4Cond`'s own · cut, laid: what the payers take. IT READS NO Pp: it gives
    `K4Cond` at every Pp.
  `k4Cond_of_owes`: `K4Owes hA L` → `K4Cond hA L Pp`.
  `k04_of_owes`: `K4Owes hA L` → for every Pp and every 𝔏 with the three lists' heads: the end of
    `k04_of_cond_pub`.

AGAINST `K4Cond`, FIELD BY FIELD, EACH A CALL AT THE HEAD's OWN OPENING. wide (fifteen facts at each
of twelve borders): `wide_of_left`, `tidy_at_pub`, `seats_at_pub`, `shapes_at_pub`,
`pileMasks_at_pub`, `pileWithin_at_pub`: other files' theorems; their equations on the parameters
go by unfolding at the constant · lay7: `l7_paid` · room: `r0_paid`, with `startB_at` ·
nextFits, pins (seventy-two tests and sentences): `nextFits_paid`, `pins_paid`
(Johnson/Road/K4/K4PinsPaid.lean), by decisions of the kernel at the written values · named (75
closed tests by a count, not shown here): `named_const` and `k4Row_two`. L: A LETTER,
PINNED BY THE FIELD laid, WHICH THE PAYERS SPEND: under written there is such an L (`laid_written`).
NEVER "∀ L".

Limits. EVERY FIELD IS A PREMISE. sends AND row ARE ASKED BY NOBODY. SHORTER IS NOT LIGHTER
EVERYWHERE: written and cut are stronger than the tests that fell for them. The written values rest
on prints of the evaluator. The full size alone. The second hash function alone. Nothing on
soundness.
-/
import Johnson.Road.K4.K4PinsPaid
import Johnson.Road.K4.K4RowTestLaws
import Johnson.Road.K4.K04CondPaidA
import Johnson.Road.K4.K04CondPaidL7
import Johnson.Road.K4.K04CondPaidT
import Johnson.Road.K4.K04CondPaidB
import Johnson.Road.K4.StartWritten
import Johnson.IMR.PlanOkFlat

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

/-- **WHAT K4's LAW TAKES BESIDE THE HEAD IN THIS FILE, BY NAME.** NO FILE STATES A MEMBER. At some
L it follows from the head (`k4Owes_of_last` at `k4Last_of_head`: K04Last.lean, K04OfHead.lean); A
MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/).
-/
structure K4Owes (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (L : VerifiableInference.Desc.K12.Door.Laid) : Prop where
  /-- WHAT IS LEFT OF `K4Cond`'s THREE FIELDS ALONG THE RUN (wide, room, lay7: seventeen sentences
  at each of twelve borders): ONE TEST WITH CODE ON THE PUBLIC PARAMETERS, asked at every opening
  (`sendsAreB`, at the proof file's first list of what is sent, 358 and the opening's own ground):
  the one premise of the payers of seatsCarried and msgShapes that neither the head nor another
  field here gives. THE SEVENTEEN THEMSELVES ARE THEOREMS OF FIVE OTHER SETS OF FILES AT AN OPENING,
  called through four files (Johnson/Road/K4/K04CondPaidA.lean: ten of wide's fifteen;
  K04CondPaidT.lean: tidy; K04CondPaidL7.lean: lay7; K04CondPaidB.lean: the other four and room);
  room's payer takes one more test, which is a theorem under written and cut, by
  the kernel (`startB_at`, Johnson/Road/K4/StartWritten.lean). ASKED BY NOBODY. Evaluated
  true at the shipped full-size set, two negative tests rejecting (a run, as reported, not
  shown here). -/
  sends : ∀ {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)},
    IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL 𝐅 Zp Bs base cF (Desc.K14.Law.seatZ Zp Np)
      (Desc.K14.Law.secondAt Zp Np) →
    VerifiableInference.Desc.K12.Door.sendsAreB Zp.made.proof.1 358
      (VerifiableInference.Desc.K12.Door.snAt Zp Bs.G₀ IM.placesW) = true
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
  /-- THE PUBLIC PART's PLAN IS THE WRITTEN ONE: five equations. WHO ASKS IT HANGS ON THE
  VERIFIER's DOOR (Johnson/Desc/Laid/ProofAsks.lean): in the entry tests' list of eight rows
  no row does: there `written` is a condition beside the head; in their list of thirteen
  rows, row 9, `madeRow`, does, and the field follows from the head (`written_of_head`,
  Johnson/Road/K4/K4HeadWritten.lean: called in K04Last.lean, not here). The five, as tests, have
  been evaluated true once at the full-size public files, each bend false (a run, as reported,
  not shown here). -/
  written : WrittenAt Zp
  /-- THE FIRST CHAIN's CUT INTO SUB-PROTOCOLS IS THE WRITTEN ONE: one equation: 358 rows of six
  columns, of which the payers spend ONE (what each sub-protocol tells): a cheaper condition would
  do. Row 10, `cutRow`, of the entry tests' thirteen rows asks it, and there it follows from the
  head (`cut_of_head`: called in K04Last.lean); their eight rows do not ask it. That row has
  been evaluated true at five sets in the goals' scope, full size, with negative tests (a run, as
  reported, not shown here); the equation itself, as a test
  row by row, true at the shipped full-size set's public files: 358 rows; three negative tests false
  (a run, as reported, not shown here). -/
  cut : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = VerifiableInference.PlanWritten.cutFirstFull
  /-- L IS WHAT THE READER OF THE CHAIN's LISTED SEATS (`P5J.At.laid?`, LettersAt2.lean) RETURNS.
  Spent by the payers. Under `written` there is such an L (`laid_written`). -/
  laid : P5J.At.laid? Zp = some L

/-- **The shorter list gives the form in which K4's law takes its conditions.** -/
theorem k4Cond_of_owes {hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀}
    {L : VerifiableInference.Desc.K12.Door.Laid} {Pp : ProofFile.InstPub → Prop}
    (C : K4Owes hA L) : K4Cond hA L Pp where
  wide := by
    obtain ⟨Bs, base, O⟩ := hA.laid.opened
    have hp : ∀ b ∈ cF.blocksInOrder, b.planOk = true := by
      intro b hb
      have h := List.all_eq_true.1 (IM.blocksOk_of_planOk O hA.laid.planOk) b hb
      simp only [Bool.and_eq_true] at h
      exact h.1
    exact fun g hg a hr hm => wide_of_left hA.𝔇 (eAll Zp cF L) hA.scope hA.reads O hp rfl rfl rfl
      rfl rfl Pp a hr hm (l7_paid (eAll Zp cF L) hA.scope hA.reads O hg rfl Pp a hr)
      ⟨seats_at_pub (eAll Zp cF L) hA.scope hA.reads O hA.laid.planOk (C.sends O) C.laid Pp a hr hm,
        shapes_at_pub (eAll Zp cF L) hA.scope hA.reads O hA.laid.planOk (C.sends O) rfl Pp a hr hm,
        pileMasks_at_pub hA.scope hA.reads O Pp a hr hm,
        pileWithin_at_pub O hA.laid.planOk Pp a hr hm,
        tidy_at_pub O hA.laid.value hA.laid.planOk Pp a hr hm⟩
  room := by
    obtain ⟨Bs, base, O⟩ := hA.laid.opened
    have hp : ∀ b ∈ cF.blocksInOrder, b.planOk = true := by
      intro b hb
      have h := List.all_eq_true.1 (IM.blocksOk_of_planOk O hA.laid.planOk) b hb
      simp only [Bool.and_eq_true] at h
      exact h.1
    exact fun g hg a hr hm => r0_paid (eAll Zp cF L) hA.scope hA.reads O hp hg rfl rfl
      (startB_at C.written C.cut) Pp a hr hm
  lay7 := by
    obtain ⟨Bs, base, O⟩ := hA.laid.opened
    exact fun g hg a hr _ => l7_paid (eAll Zp cF L) hA.scope hA.reads O hg rfl Pp a hr
  named := named_const hA C.laid C.written C.cut (k4Row_two hA C.row)
  nextFits := nextFits_paid hA L C.written C.cut
  pins := pins_paid hA L C.laid C.written C.cut
  written := C.written

/-- **K4's OWN SENTENCE FOR THE JOIN, UNDER THE SHORTER LIST.** NO FILE STATES A MEMBER OF `K4Owes`;
at some L `K4Owes hA L` follows from the head (`k4Owes_of_last` at `k4Last_of_head`); UNDER THE HEAD
hA: A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY
AtFullSide/Top/). -/
theorem k04_of_owes (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (L : VerifiableInference.Desc.K12.Door.Laid) (Pp : ProofFile.InstPub → Prop) (C : K4Owes hA L)
    (𝔏 : P5J.Free numsFull D 𝐅 P5J.At.Tok)
    (q₁ : (𝐅).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) (q₂ : (𝐅).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (𝐅).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    KindTiedR (Fr := 𝐅𝐫) (P5J.At.N Zp cF) (P5J.mgAt hA.toAtMg hA.𝔇) P5J.fullLinks P5J.At.ps
      (RchPub 𝐅 Pp) (hA.toAtMg.ex 𝔏) (hA.toAtMg.row 𝔏) KindName.K4 :=
  k04_of_cond_pub hA L Pp (k4Cond_of_owes C) 𝔏 q₁ q₂ q₃

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4Cond_of_owes
#print axioms OnBytes.Road.K4.k04_of_owes
set_option pp.deepTerms true in
set_option pp.maxSteps 1000000 in
set_option pp.proofs true in
#check @OnBytes.Road.K4.k04_of_owes
set_option pp.deepTerms true in
set_option pp.maxSteps 1000000 in
#print OnBytes.Road.K4.K4Owes
