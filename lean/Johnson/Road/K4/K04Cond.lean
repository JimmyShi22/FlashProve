-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K04Cond.lean: the kind K4's own sentence for the join: named conditions → its share
of the chain of promises, in `AtMg.Kind`'s own text but for the condition beside the promise. One
structure, three statements with their proofs: `k04_kind` (K04LawKind.lean) with all that lies
called. No new argument. It pays nothing of weight.

First. No file states a member of `K4Cond`. K04_law is not proved by this: `K4Cond` is what
is owed. (In this tree the head gives it: hA ⟹ ∃ L, K4Cond hA L Pp: `k4Cond_of_last` at
`k4Last_of_head`, Johnson/Road/K4/K04Last.lean and K04OfHead.lean.) A member of the head is proved
at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). What speaks for each field is
said at the field:
evaluations are no proofs, and what was evaluated on one honest run says nothing of the other states
that the IOP's run reaches.

  `K4Cond hA L Pp`: seven fields, each named: three families of facts at the twelve borders in front
    of K4, at every state that the IOP's run reaches there without a mark and whose public part
    meets Pp (wide, room, lay7), three families on the plan (named, nextFits, pins: tests with code,
    but for two inequalities and three sentences "at every place of the segment with the planned
    number of slots", each of which reads the place's segment and that number alone: one closed test
    each), and one condition on the public part (written).
  `k04_of_cond_pub`: `K4Cond hA L Pp` → for every 𝔏 with the three lists' heads: `AtMg.Kind`'s own
    text at the kind K4, with "reached, and Pp of the public part" (`RchPub`) as the condition
    beside the promise. `k04_of_cond`: at Pp := "true": `hA.toAtMg.Kind hA.𝔇 𝔏 KindName.K4`.

Every letter of the end but 𝔏 and Pp is a term over the head's seven letters: the structure of data
is the closed constant `hA.𝔇`; the condition beside the promise is `RchPub` of the IOP
as written in Lean, over the letter Pp; the second hash function. 𝔏 is a binder of the theorem, not
of the condition: the join lays its own. L: the listed seats and trees' shapes of the chain: a free
letter of the condition; it does not stand in the end: so the theorem says "(∃ L, K4Cond hA L Pp) →
…": the generous form. What the top needs is "the head → ∃ L, K4Cond hA L Pp": not typed in this
file: it is `k4Cond_of_last` at `k4Last_of_head` (Johnson/Road/K4/K04Last.lean, K04OfHead.lean).
Never "∀ L": at the meant Pp that is false (at the empty list `wide` fails wherever an unmarked
state whose book holds a place is reached). Whoever pays `wide` picks L; its one known source is
what `P5J.At.laid? Zp` returns (both runners evaluated there); that it returns (`P5J.At.laidB Zp`)
is no field here. Three things bear the word
"laid": `hA.laid` (`LaidAt`: the verifier's own value is laid) · `hA.plan.laid`
(`Meaning.laidThere`: a test on the request's layout) · `At.laid?`. Pp: a letter: the narrower,
the cheaper (`K4Cond.anti`): at "never" three fields are free and the end says next to nothing: a
count names Pp: the counted one is "the public part is a typed instance's" (`AtMg.typed`).

O is no binder: `LaidAt.opened` gives an opening; the two
fields that speak of its base (named, pins) are asked at every opening: that asks no more than at
the one: two openings of the same three files have one base and one list: `IM.Open.unique`
(Johnson/IMR/SeatOpen.lean): not called here. Pf := `pinsFill_const`, reqT :=
`reqTies_const` (Johnson/Road/K4/K4PinsFirstScope.lean), at the head's own fields. lw, the idle
letter, := the weights that are 0. The seam's eleven tests, the plan's common test and its twelve
first tests are theorems under `written`, with the names' tie paid at the opening
(`namesTied_of_scope`) and the nine matrices' number, owners and sizes read off the head's own test
`hA.plan.laid` (`Meaning.laidThere`; by `xNine_of_laid`: so that test of the head is spent here: for
the nine matrices K4 adds no test of its own).




Limits. Every field is a premise. The full size alone. Nothing on soundness.
-/
import Johnson.Road.K4.K04LawKind
import Johnson.Road.K4.K4PlanAllPaid
import Johnson.Road.K4.K4PlanNames
import Johnson.Road.K4.NineInScope

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

/-- **WHAT K4's LAW IS OWED, BY NAME.** SHOWN TO HOLD NOWHERE. -/
structure K4Cond (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (L : VerifiableInference.Desc.K12.Door.Laid) (Pp : ProofFile.InstPub → Prop) : Prop where
  /-- THE FIFTEEN FACTS (`WideFacts`, each under the name of its field in `FoldFacts`) at
  every state reached without a mark in front of K4 whose public part meets Pp. It follows from
  `K4Owes` (`k4Cond_of_owes`, Johnson/Road/K4/K04Owes.lean). Evaluated true
  on one honest run a size, at every border; ten negative tests reject at K4's borders; tidy has
  none that bites there; none is typed for bookFits, weightsOk, oneRow. -/
  wide : ∀ g, g < 12 → ∀ a : (ProofFile.InstPub × S) × 𝐅𝐫.E.Str,
      RchPub 𝐅 Pp (28 * g + 4) a → a.1.2.failed = none → WideFacts hA.𝔇 (eAll Zp cF L) a.1
  /-- The test of "pile.room" at the segment's own number, there. It follows from `K4Owes`
  (`k4Cond_of_owes`, Johnson/Road/K4/K04Owes.lean).
  Evaluated true on one honest run a size, with negative tests. -/
  room : ∀ g, g < 12 → ∀ a : (ProofFile.InstPub × S) × 𝐅𝐫.E.Str,
      RchPub 𝐅 Pp (28 * g + 4) a → a.1.2.failed = none →
        Johnson.Desc.First.Walk.Tied.roomIsB (eAll Zp cF L).dP.free0 (eAll Zp cF L).dP.fvs (2 * g)
        a.1.2 = true
  /-- The test of "K8.lay7" at the segment's own number, there. A theorem ends in it, from the scope
  and an opening alone (`l7_paid`, called in Johnson/Road/K4/K04Owes.lean); not called in this file.
  Evaluated true on one
  honest run a size, with negative tests. -/
  lay7 : ∀ g, g < 12 → ∀ a : (ProofFile.InstPub × S) × 𝐅𝐫.E.Str,
      RchPub 𝐅 Pp (28 * g + 4) a → a.1.2.failed = none →
        (((eAll Zp cF L).dP.tl (2 * g)).any fun tlP =>
          VerifiableInference.Desc.First.K8.Ready.lay7B tlP a.1.2) = true
  /-- The row's nine tests, at every opening: three that name no group, six asked at each of the
  twelve. Evaluated true ×12 at the constant's own fields (its second laying), full size, every
  negative test rejecting (a run, as reported, not shown here). PAID BUT
  FOR TWO OF THE SIX, under written and two more named conditions: `named_const` ends in
  this field (called in K04Owes.lean, which imports this file). -/
  named : ∀ {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)},
    IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL 𝐅 Zp Bs base cF (Desc.K14.Law.seatZ Zp Np)
      (Desc.K14.Law.secondAt Zp Np) →
    ∀ g, g < 12 → ∀ x b, K4Here cF Zp Bs.G₀ g x b →
      K4NamedW hA.𝔇 (eAll Zp cF L) (28 * g + 4) (2 * g) (parOf x)
      (cF.blocksInOrder.map fun b => b.oracles.flatMap id)
        (Forest.elems (P5J.At.X Zp).y.fo)
  /-- One test a group on the mask entry's name. Evaluated true ×12, full size, at the letters
  of a file of evaluations, two negative tests (a run, as reported, not
  shown here). PAID under written and one more named condition: `nextFits_paid` ends
  in this field (called in K04Owes.lean). -/
  nextFits : ∀ g, g < 12 →
      Rec.nextFitsB (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).cs
      (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).d12.M
      ((k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).N.msgsAt
      (flatPlacesOf linksFull true)[28 * g + 4 + 1]?)
        (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).N.indexNo
        (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).free0
        (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).fvs (2 * g) = true
  /-- THE PINS' FIVE OTHER TESTS A GROUP, at every opening: maskFits, indexTie, maskPlan, arrays,
  ell (`K4PinsTests`, Johnson/Road/K4/K4PinsLaterScope.lean), ASKED IN THE FORM "GIVEN ITS FIRST
  FIELD, ALL SIX": the first is a theorem under the field below. All five have been evaluated true
  ×12 at the full size AT THE LETTERS OF FILES OF EVALUATIONS (runs, as reported,
  their prints not shown here). PAID under written
  and two more named conditions: `pins_paid` ends in this field (called in K04Owes.lean). -/
  pins : ∀ {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)},
    IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL 𝐅 Zp Bs base cF (Desc.K14.Law.seatZ Zp Np)
      (Desc.K14.Law.secondAt Zp Np) →
    ∀ g, g < 12 → ∀ x b, K4Here cF Zp Bs.G₀ g x b → firstFastB Zp g = true →
      K4PinsTests hA.𝔇 (eAll Zp cF L) Zp (28 * g + 4) g (parOf x)
  /-- THE PUBLIC PART's PLAN IS THE WRITTEN ONE: five equations. HERE `written` IS A CONDITION
  BESIDE THE HEAD. In this tree the comparison is the ninth row of the verifier's entry tests
  (madeRow, Johnson/Desc/Laid/ProofAsks.lean), and the head (a member of the head is proved at
  `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/)) gives the field:
  `written_of_head` (Johnson/Road/K4/K4HeadWritten.lean); not called in this file.
  Under `written` the plan's common test, the seam's eleven and, with the head's own test
  `hA.plan.laid` and the names' tie at the opening, the plan's twelve first tests are theorems
  (called). The five, as tests, have been evaluated true once at the full-size public files, each
  bend false (a run, as reported, not shown here). -/
  written : WrittenAt Zp

/-- **THE CONDITION IS ANTITONE IN Pp: THE NARROWER Pp, THE CHEAPER.** One payment at "true" serves
every Pp. AT Pp := "never" THREE FIELDS ARE FREE: WHOEVER SAYS THAT `K4Cond` HOLDS NAMES Pp. -/
theorem K4Cond.anti {hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀}
    {L : VerifiableInference.Desc.K12.Door.Laid} {Pp Pp' : ProofFile.InstPub → Prop}
    (h : ∀ p, Pp' p → Pp p) (C : K4Cond hA L Pp) : K4Cond hA L Pp' where
  wide := fun g hg a hr hm => C.wide g hg a ⟨hr.1, h _ hr.2⟩ hm
  room := fun g hg a hr hm => C.room g hg a ⟨hr.1, h _ hr.2⟩ hm
  lay7 := fun g hg a hr hm => C.lay7 g hg a ⟨hr.1, h _ hr.2⟩ hm
  named := C.named
  nextFits := C.nextFits
  pins := C.pins
  written := C.written

/-- **K4's OWN SENTENCE FOR THE JOIN, AT EVERY CONDITION Pp ON THE PUBLIC PART: THE NAMED CONDITIONS
GIVE ITS SHARE, WITH "REACHED, AND Pp" IN HAND.** `K4Cond` IS SHOWN TO HOLD NOWHERE; UNDER THE
HEAD hA: A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY
AtFullSide/Top/). -/
theorem k04_of_cond_pub (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (L : VerifiableInference.Desc.K12.Door.Laid) (Pp : ProofFile.InstPub → Prop) (C : K4Cond hA L Pp)
    (𝔏 : P5J.Free numsFull D 𝐅 P5J.At.Tok)
    (q₁ : (𝐅).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) (q₂ : (𝐅).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (𝐅).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    KindTiedR (Fr := 𝐅𝐫) (P5J.At.N Zp cF) (P5J.mgAt hA.toAtMg hA.𝔇) P5J.fullLinks P5J.At.ps
      (RchPub 𝐅 Pp) (hA.toAtMg.ex 𝔏) (hA.toAtMg.row 𝔏) KindName.K4 := by
  obtain ⟨Bs, base, O⟩ := hA.laid.opened
  have hpub : OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := O.W ▸ O.public
  have H9 : XNine Zp.p.X :=
    xNine_of_laid hpub (Hd.core_of_scope hA.scope hA.reads hpub) C.written.layout hA.plan.laid
  exact k04_kind hA 𝔏 q₁ q₂ q₃ O L
    (fun _ => ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0,
      fun _ _ => 0, fun _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0⟩)
    (C.named O) C.nextFits
    (pinsFill_const OnBytes.secondHashFunction Zp Np cF (P5J.At.EAt Z) hA.plan.shape Z.lay hA.plan.laid
      hA.plan.hN hA.plan.hG x₀ OnBytes.Flat.numsFull.rows)
    (fun g hg x b h => C.pins O g hg x b h
      (first_paid C.written H9 (namesTied_of_scope hA.scope hA.reads O) hg))
    C.written
    (reqTies_const OnBytes.secondHashFunction Zp Np cF (P5J.At.EAt Z) hA.plan.shape Z.lay hA.plan.laid
      hA.plan.hN hA.plan.hG x₀ OnBytes.Flat.numsFull.rows (eAll Zp cF L) rfl)
    Pp C.wide C.room C.lay7

/-- **AT Pp := "TRUE": THE FORM `AtMg.Kind`**, at bare "reached": `rows_at_mg` takes it
through a further call (`AtMg.Kind.toR`, RowsAtMg.lean). UNDER THE HEAD hA: A MEMBER OF THE HEAD IS
PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/). -/
theorem k04_of_cond (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (L : VerifiableInference.Desc.K12.Door.Laid) (C : K4Cond hA L fun _ => True)
    (𝔏 : P5J.Free numsFull D 𝐅 P5J.At.Tok)
    (q₁ : (𝐅).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) (q₂ : (𝐅).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (𝐅).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) : hA.toAtMg.Kind hA.𝔇 𝔏 KindName.K4 :=
  KindTiedR.mono (fun _ _ h => ⟨h, trivial⟩) (k04_of_cond_pub hA L _ C 𝔏 q₁ q₂ q₃)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.K4Cond.anti
#print axioms OnBytes.Road.K4.k04_of_cond_pub
#print axioms OnBytes.Road.K4.k04_of_cond
set_option pp.deepTerms true in
set_option pp.maxSteps 1000000 in
set_option pp.proofs true in
#check @OnBytes.Road.K4.k04_of_cond_pub
set_option pp.deepTerms true in
set_option pp.maxSteps 1000000 in
set_option pp.proofs true in
#check @OnBytes.Road.K4.k04_of_cond
set_option pp.deepTerms true in
set_option pp.maxSteps 1000000 in
#print OnBytes.Road.K4.K4Cond
