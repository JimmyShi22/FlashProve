-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT ANY FILLING: the prover H, the Script Q, the book Bk, the index's reader and the thread's other
letters are variables; the trace's type is Cells.
Johnson/Desc/ProofFile/Honest/K3/Term/LookupWitnessFactsAtTheHonestTrace.lean: the honest side of the
kind "lookup" (K3): CONDITIONAL: clause 12 of the two bundles "that speak of a run" (the premises at
one witness), at the Script's witness, where the row is handed `lookupWitness Zp weights s`
(Honest/K3/Term/LookupDataAtTheHonestTrace.lean). Two theorems, which end to the letter in
`DigitsWitnessFacts` and `CallsWitnessFacts` (Honest/K3/Term/LookupExchangeFromWitnessFacts.lean).
IT MOVES THE CLAUSE ONTO PREMISES ON THE SCRIPT AND THE INPUT; IT SHOWS NO DEBT OF THE FRAME.

  `ScriptHoldsThePackedTraceCellsAtTheLink`  (definition) the first named premise of
        ScriptHoldsTheHonestValues.lean at the head's letters, by what the public readers answer
  `digitsWitnessFactsAtTheHonestTrace`       ends in `DigitsWitnessFacts`: SIX premises beside the head
  `callsWitnessFactsAtTheHonestTrace`        ends in `CallsWitnessFacts`: NINE premises beside the head
  helpers: `recordFoundAtTheDigitsIsTheLookupsOwn`, `callerAndGroupAreTheLinks`,
  `attentionPlaceIsThePlans`, `layersPlaceIsThePlans`, `indexIsZeroOutsideTheStoredTable` (public);
  `traceMatricesOfAnHonestInputAreTheTraces`, `traceCellsAreSmallAtValidInputs`,
  `weightEntriesOfAnHonestInputAreTheIndexs` (the input); `symbolsPackTheHonestTraceAtTheWitness`,
  `headKeyFormsAreTheLibrarysKeysAtTheWitness` (the Script's witness, conditional)
THE PREMISES, counted. Both: the head h. Public, or on the letter Said:
  siteOfThePublicPart · onTheDigits | onTheCalls · placeIsFound (digits) · saidGivesWordsBelowThePrime
RE-NAMED, NOT SHOWN: each is a premise of a theorem here; this file shows none of them:
  enoughChallengesInFront          the guard's number is at most the challenges heard at the border
  scriptHoldsTheDigitArrays        (digits) ON THE SCRIPT: `ScriptHoldsTheDigitArrays` at the array
                                   zzOwn … (tritsAt heard ‹the site's sampling round›)
  validInputsHoldTheHonestTrace    (calls) ON THE INPUT: `InputHoldsTheHonestTrace` at some index and
                                   request. AT A LETTER Vd THAT LETS ANOTHER INPUT BY IT IS FALSE
  scriptHoldsThePackedTraceCells   (calls) ON THE SCRIPT: the definition above
  scriptCellsAreTheIndexWeights    (calls) ON THE SCRIPT's STORED TABLE; spent at the layers' links
                                   and the head's
  seatAtTheHeadsLink               (calls, link 24 alone) ON THE PROVER's LIST: `SiteRest`
  replyClauseSpeaksInFront         (calls, link 24 alone) b₀ is at most the lookup's border
SHOWN, here or beneath, from these, `ThrS` and the member's step: the four fields:
  zero    by definition
  fills   the library's law of the filling (`digitsFillingIsTheLibrarys`, `libraryKeysAndBitsAtLayers` |
          `…AtAttention` | `…AtTheHead`), turned to the witness's own reading
          (LookupFillsAtTheWitness.lean); the keys by LookupKeyFormsAreTheLibrarysKeysAtDigits |
          AtAttention | AtLayers | AtTheHead.lean; the planes' number and room on public data
  masks   MaskEntriesAtTheWitness.lean
  cubes   (calls) RidersVanishAtTheLinks.lean
and beside them: the trace's cells are small; the sampling round is heard in front of the digits'
border; the token that the state has heard is the request's (ReplyTokenBehindTheLookup.lean).

Limits. Implications from `ThrS` and the member's step: no state is shown to meet these at any of the
fifty borders: there both theorems hold emptily. That the premises can hold together is shown nowhere.
On the digits nothing is asked of the input. The guard's number challengesHeard is one letter at a
site: it is meant at the challenges heard at the site's own border, roundsTo cF.blocksInOrder (borderOf link
digits); a caller may take another number at each site. The elder row `proverSideOfLookupInChainAtOneOwner` (in `SiteRest`).
The full size alone: that limit comes with the head. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupExchangeFromWitnessFacts
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupFillsAtTheWitness
import Johnson.Desc.ProofFile.Honest.K3.Term.MaskEntriesAtTheWitness
import Johnson.Desc.ProofFile.Honest.K3.Term.TraceMatricesOfTheCells
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupKeyFormsAreTheLibrarysKeysAtDigits
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupKeyFormsAreTheLibrarysKeysAtAttention
import Johnson.Desc.ProofFile.Honest.K3.Term.PaddingRowsAtAttentionAreTheLibrarys
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupKeyFormsAreTheLibrarysKeysAtLayers
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupKeyFormsAreTheLibrarysKeysAtTheHead
import Johnson.Desc.ProofFile.Honest.K3.Term.ReplyTokenBehindTheLookup
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupDataAtTheHonestTrace
import Johnson.Desc.ProofFile.Honest.K3.Term.BorrowedMatricesBearOneNumber
import Johnson.Desc.ProofFile.Honest.K3.Term.RidersVanishAtTheLinks
import Johnson.Desc.ProofFile.Honest.K3.Term.RequestLetterUnderTheHead
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupBaseWritten
import Johnson.Desc.First.Look.K3CallerCellsLaw
import Johnson.Desc.First.Look.K3PlanLetters
import Johnson.Desc.First.Look.K3PlanLettersLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.Model (HTailF2)
open OnBytes.Model.Verify (publicOf)
open OnBytes.Slice (GE)
open OnBytes.Road (Hd.shapeA)
open OnBytes.HonestTrace (entryOf theTrace fromH fsAt)
open Cb.Pv.Tail (BaseAt)
open VerifiableInference.Desc (Block Chain Strs)
open VerifiableInference.Desc.First.Look (Sent digAt attAt layAt lookAt szOf symAt sigListCalls
  seatCalls)
open VerifiableInference.Desc.Kinds.Head (Sizes Policy Request)
open VerifiableInference.Desc.Kinds.Head.Law (headLay)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.OnPublicFiles (K3Letters headLink k3SizesAt k3PolicyAt k3AdrAt layMu attMs)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.AtThr

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place
local notation "recordAt" => VerifiableInference.Desc.First.Look.tlAt
local notation "stepAt" => VerifiableInference.Desc.First.Look.stepOf

/-! ## 0 Public facts in scope, and the trace at an honest input -/

section InScope
variable {files : VerifierAndGoals.PublicFiles} {settings : Inst.Model.ScalesAndPolicy} {layout : Option ByteArray}
  {publicPart : ProofFile.Pub}

/-- **The record that the public reader finds at a link's digits is the lookups' own.** The reader
lays the lookup's shape anew, as the kind's parameters make it; at a site that shape is the
record's. -/
theorem recordFoundAtTheDigitsIsTheLookupsOwn
    (publicPartIsMade : publicOf files.pol files.KL layout = .ok publicPart.p.X) (s : Site)
    (siteOfThePublicPart : s ∈ lookSites publicPart) (onTheDigits : s.digits = true) {x : PlaceL}
    {tl : HTailF2} (placeIsFound : digAt publicPart.p.X s.link = some (x, tl)) :
    tl = tlOf publicPart.p.X s.link := by
  obtain ⟨shapeIsTheTails, -, -⟩ :=
    Exchange.table_digits publicPart s siteOfThePublicPart onTheDigits placeIsFound
  obtain ⟨_, _, shapeOfTheRecord, _, _⟩ :=
    Spec.site_digits publicPart s siteOfThePublicPart onTheDigits
  have shapeIsThePlans : fsOf publicPart.p.X s = some s.shape :=
    shapeIsFs_of_public publicPartIsMade s siteOfThePublicPart
  have sameShape : (tlOf publicPart.p.X s.link).f9 = tl.f9 := by
    rw [← shapeIsTheTails]
    exact Option.some.inj (shapeOfTheRecord.symm.trans shapeIsThePlans)
  unfold digAt at placeIsFound
  obtain ⟨_, -, rest⟩ := Option.bind_eq_some_iff.1 placeIsFound
  obtain ⟨record, recordIsFound, rest⟩ := Option.bind_eq_some_iff.1 rest
  obtain ⟨made, -, rest⟩ := Option.map_eq_some_iff.1 rest
  obtain ⟨-, rfl⟩ := Prod.mk.inj rest
  have own : tlOf publicPart.p.X s.link = record := by
    rw [Ties.tlOf_eq_tlAt, recordIsFound]
    rfl
  rw [own] at sameShape ⊢
  have madeIs : record.f9 = made := sameShape
  subst madeIs
  rfl

/-- **A site's caller and group, by its link's number.** -/
theorem callerAndGroupAreTheLinks (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (publicPartIsMade : publicOf files.pol files.KL layout = .ok publicPart.p.X) (s : Site)
    (siteOfThePublicPart : s ∈ lookSites publicPart) :
    (s.link = 24 → s.caller = .head) ∧
      (s.link ≠ 24 → s.link % 2 = 0 → s.caller = .layers ∧ s.group = s.link / 2) ∧
      (s.link ≠ 24 → s.link % 2 = 1 → s.caller = .attention ∧ s.group = s.link / 2) := by
  obtain ⟨attentionLinks, twelveGroups, -, -⟩ :=
    publicNumbersInScope filesAreInScope filesAreRead publicPartIsMade
  obtain ⟨_, _, _, callerIs, groupIs, _⟩ := Spec.sites_look publicPart s siteOfThePublicPart
  have stepIsTwo : (if publicPart.p.X.p4 = true then 2 else 1) = 2 := by
    rw [attentionLinks]
    rfl
  unfold callerOf at callerIs groupIs
  dsimp only at callerIs groupIs
  rw [stepIsTwo, twelveGroups] at callerIs groupIs
  refine ⟨fun isTheHeads => ?_, fun notTheHeads even => ?_, fun notTheHeads odd => ?_⟩
  · rw [if_pos (by rw [isTheHeads]; rfl)] at callerIs
    exact callerIs
  · have first : ¬ (s.link == 2 * 12) = true := fun c => notTheHeads (by
      have := eq_of_beq c
      omega)
    rw [if_neg first, if_pos (by rw [even]; rfl)] at callerIs groupIs
    exact ⟨callerIs, groupIs⟩
  · have first : ¬ (s.link == 2 * 12) = true := fun c => notTheHeads (by
      have := eq_of_beq c
      omega)
    rw [if_neg first, if_neg (by rw [odd]; decide)] at callerIs groupIs
    exact ⟨callerIs, groupIs⟩

variable {X : OnBytes.Model.Verify.Public}

/-- **What attention's public reader answers at a link is the plan's.** -/
theorem attentionPlaceIsThePlans (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (publicPartIsMade : publicOf files.pol files.KL layout = .ok X) {link : ℕ}
    (linkBelow : link < 25) {x : PlaceL} {A : OnBytes.Attention.Shape} {tl : HTailF2}
    (placeIsFound : attAt X link = some (x, A, tl)) :
    ∃ plan : OnBytes.Attention.Plan, X.A[link / 2]? = some plan ∧ A = plan.S ∧
      tl = plan.seam.tl ∧ x.fs = plan.fs ∧ x.lm = plan.S.cf.lmb ∧ recordAt X link = some tl ∧
      A = Hd.shapeA X (link / 2) ∧ x.fs = fsAt X (link / 2) := by
  have marks :=
    OnBytes.HonestTrace.planMarks_in_scope filesAreInScope filesAreRead publicPartIsMade
  have stepIsTwo : (if X.p4 then 2 else 1) = 2 := by
    rw [marks.p4]
    rfl
  have linkIsOdd : link % 2 = 1 := VerifiableInference.OnPublicFiles.attAt_odd placeIsFound
  have linkIs : 2 * (link / 2) + 1 = link := by omega
  have foundAtTheGroup : attAt X (2 * (link / 2) + 1) = some (x, A, tl) := by
    rw [linkIs]
    exact placeIsFound
  obtain ⟨-, shapeIsThePlans, -, looked⟩ :=
    VerifiableInference.Desc.First.Look.attAt_letters filesAreInScope filesAreRead
      publicPartIsMade (by omega : link / 2 < 12) foundAtTheGroup
  rw [linkIs] at looked
  obtain ⟨plan, planIsFound, recordIsFound, placesShape, placesRows, -⟩ :=
    VerifiableInference.Desc.First.Look.lookAt_att looked
      (by rw [stepIsTwo, marks.groups]; omega) (by rw [stepIsTwo]; omega)
  rw [stepIsTwo] at planIsFound
  have shapeOfThePlan : Hd.shapeA X (link / 2) = plan.S := by
    unfold OnBytes.Road.Hd.shapeA
    rw [planIsFound]
    rfl
  have lookupShapeOfThePlan : fsAt X (link / 2) = plan.fs := by
    unfold OnBytes.HonestTrace.fsAt
    rw [planIsFound]
    rfl
  have recordIs : tl = plan.seam.tl := by
    unfold attAt at placeIsFound
    split at placeIsFound
    · obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.1 placeIsFound
      obtain ⟨plan', planIsFound', rest⟩ := Option.bind_eq_some_iff.1 rest
      obtain ⟨_, _, rest⟩ := Option.map_eq_some_iff.1 rest
      obtain rfl : plan' = plan := Option.some.inj (planIsFound'.symm.trans planIsFound)
      exact (congrArg (fun t => t.2.2) rest).symm
    · cases placeIsFound
  exact ⟨plan, planIsFound, shapeIsThePlans.trans shapeOfThePlan, recordIs, placesShape,
    placesRows, by rw [recordIs]; exact recordIsFound, shapeIsThePlans,
    placesShape.trans lookupShapeOfThePlan.symm⟩

/-- **What the layers' public reader answers at a link is the plan's.** -/
theorem layersPlaceIsThePlans (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (publicPartIsMade : publicOf files.pol files.KL layout = .ok X) {link : ℕ}
    (linkBelow : link < 25) {x : PlaceL} {tl : HTailF2} (placeIsFound : layAt X link = some x)
    (recordIsFound : recordAt X link = some tl) :
    link % 2 = 0 ∧ link ≠ 24 ∧ stepAt X = 2 ∧ x.fs = X.y.fo ∧ x.lm = X.y.h.lmb ∧
      ∃ plan : OnBytes.Model.Layer.HPlan2, X.G[link / 2]? = some plan ∧ tl = plan.tl := by
  have marks :=
    OnBytes.HonestTrace.planMarks_in_scope filesAreInScope filesAreRead publicPartIsMade
  have stepIsTwo : (if X.p4 then 2 else 1) = 2 := by
    rw [marks.p4]
    rfl
  obtain ⟨linkIsEven, linkIsNotTheHeads⟩ :=
    VerifiableInference.OnPublicFiles.layAt_even marks.p4 marks.groups placeIsFound
  have linkIs : 2 * (link / 2) = link := by omega
  have foundAtTheGroup : layAt X (2 * (link / 2)) = some x := by
    rw [linkIs]
    exact placeIsFound
  obtain ⟨looked, -⟩ :=
    VerifiableInference.Desc.First.Look.layAt_letters filesAreInScope filesAreRead
      publicPartIsMade (by omega : link / 2 < 12) foundAtTheGroup
  rw [linkIs] at looked
  obtain ⟨plan, planIsFound, recordIsThePlans, placesShape, placesRows, -⟩ :=
    VerifiableInference.Desc.First.Look.lookAt_lay looked
      (by rw [stepIsTwo, marks.groups]; omega) (by rw [stepIsTwo]; omega)
  rw [stepIsTwo] at planIsFound
  exact ⟨linkIsEven, linkIsNotTheHeads, stepIsTwo, placesShape, placesRows, plan, planIsFound,
    Option.some.inj (recordIsFound.symm.trans recordIsThePlans)⟩

variable {W₀ Rc : Type} {weights : W₀ → Weights}

/-- **At an input that holds the honest trace, the integers behind its cells are the trace's.** -/
theorem traceMatricesOfAnHonestInputAreTheTraces (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (publicPartIsMade : publicOf files.pol files.KL layout = .ok publicPart.p.X)
    {input : Local W₀ Rc ProofFile.Inst Cells} {index : Cm.Idx}
    {request : Inst.Model.Instance Inst.Model.ppref}
    (holds : InputHoldsTheHonestTrace publicPart weights input index request) {link : ℕ}
    (linkBelow : link < 25) :
    traceMatricesOfTheCells publicPart.p.X input.trace.cell link =
      theTrace publicPart.p.X index request link := by
  rw [holds.traceIsTheHonestTrace]
  exact traceMatricesOfTheCellsAtATrace
    (OnBytes.HonestTrace.namesFit_theTrace filesAreInScope filesAreRead publicPartIsMade
      holds.requestIsServed) linkBelow fun number row column =>
    lt_trans (traceCellsAreBelow129 filesAreInScope filesAreRead publicPartIsMade
      holds.requestIsServed link number row column) (by norm_num)

/-- **THE SECOND NAMED PREMISE, PAID**: where valid inputs hold the honest trace of a served request,
the integers behind their cells are below twice the shift. At every record. -/
theorem traceCellsAreSmallAtValidInputs (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (publicPartIsMade : publicOf files.pol files.KL layout = .ok publicPart.p.X)
    {valid : Local W₀ Rc ProofFile.Inst Cells → Prop}
    (validInputsHoldTheHonestTrace : ∀ input, valid input →
      ∃ index request, InputHoldsTheHonestTrace publicPart weights input index request)
    {link : ℕ} (linkBelow : link < 25) (tl : HTailF2) :
    TraceCellsAreSmall valid tl fun input =>
      traceMatricesOfTheCells publicPart.p.X input.trace.cell link := by
  intro input isValid matrix column row
  obtain ⟨index, request, holds⟩ := validInputsHoldTheHonestTrace input isValid
  show |traceMatricesOfTheCells publicPart.p.X input.trace.cell link matrix.val row.val
    column.val| < 2 * (((szOf tl).beta : Nat) : ℤ)
  rw [traceMatricesOfAnHonestInputAreTheTraces filesAreInScope filesAreRead publicPartIsMade holds
    linkBelow]
  have shiftIs : (((szOf tl).beta : Nat) : ℤ) = 2 ^ 17 := by
    show (((2 : ℕ) ^ 17 : ℕ) : ℤ) = 2 ^ 17
    norm_num
  rw [shiftIs]
  exact traceCellsAreSmall filesAreInScope filesAreRead publicPartIsMade holds.requestIsServed link
    matrix.val row.val column.val

/-- **Behind the committed symbols that the calls' callers read off the Script's witness stands the
honest trace's list at the link**, cut to the record's sizes: the library's `BaseAt`. Conditional on
the first named premise. -/
theorem symbolsPackTheHonestTraceAtTheWitness {Bk : ProverCoinCounts} {Stored Tok : Type}
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst Cells) Stored Tok MsgT} {sent : Sent}
    {letters : K3Letters Stored Tok} {valid : Local W₀ Rc ProofFile.Inst Cells → Prop}
    {challengesHeard : ℕ} {x : PlaceL} {tl : HTailF2} {link : ℕ}
    (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (publicPartIsMade : publicOf files.pol files.KL layout = .ok publicPart.p.X)
    (validInputsHoldTheHonestTrace : ∀ input, valid input →
      ∃ index request, InputHoldsTheHonestTrace publicPart weights input index request)
    (linkBelow : link < 25)
    (packed : ScriptHoldsThePackedTraceCells Q sent letters valid challengesHeard x tl fun input =>
      traceMatricesOfTheCells publicPart.p.X input.trace.cell link)
    (k : Coins Bk) {input : Local W₀ Rc ProofFile.Inst Cells} {heard : List Fmt.Drawn}
    (isValid : valid input) (enough : challengesHeard ≤ heard.length) {index : Cm.Idx}
    {request : Inst.Model.Instance Inst.Model.ppref}
    (holds : InputHoldsTheHonestTrace publicPart weights input index request) :
    BaseAt (symAt sent.codes (sigListCalls sent letters.rad x.link) (seatCalls sent x.link) tl
        (attMs x sent letters.rad (fun j => letters.seat x.link false j.1) letters.arr
          (Q.wit k input heard)))
      (restrictedToTheSizes (szOf tl) (theTrace publicPart.p.X index request link)) := by
  have base := symbolsHaveTheTraceCellsBehindThem packed
    (traceCellsAreSmallAtValidInputs filesAreInScope filesAreRead publicPartIsMade
      validInputsHoldTheHonestTrace linkBelow tl) k isValid enough
  rw [← traceMatricesOfAnHonestInputAreTheTraces filesAreInScope filesAreRead publicPartIsMade
    holds linkBelow]
  exact base

/-- **At an input that holds the honest trace the reader of the index yields the index's digits.** -/
theorem weightEntriesOfAnHonestInputAreTheIndexs {input : Local W₀ Rc ProofFile.Inst Cells}
    {index : Cm.Idx} {request : Inst.Model.Instance Inst.Model.ppref}
    (holds : InputHoldsTheHonestTrace publicPart weights input index request) (row column : ℕ) :
    (weights input.w₀).entry row column = ((index.mat row column : ℤ) : Cb.Gl.F) := by
  rw [holds.weightsAreTheIndex]
  rfl

end InScope

/-- **An index's matrix is 0 outside the stored table's rows and columns**, at the full size. -/
theorem indexIsZeroOutsideTheStoredTable (index : Cm.Idx) (row column : ℕ)
    (outside : ¬ (row < OnBytes.Flat.numsFull.rows ∧
      column < P5J.colsAt OnBytes.Flat.numsFull)) : index.mat row column = 0 :=
  OnBytes.HonestTrace.entryZ_out index fun inside => outside ⟨inside.1, by
    have columnsAre : P5J.colsAt OnBytes.Flat.numsFull = 2 ^ Inst.Model.Layout.kRef :=
      congrArg (2 ^ ·) OnBytes.Flat.full_columns
    rw [columnsAre]
    exact inside.2⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : PlaceL}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {Bk : ProverCoinCounts} {W₀ Rc Ky X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Cells X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Cells → Prop)
  (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Cells) TS))
  (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Cells)

local notation "LH" =>
  lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w

/-! ## 1 A premise, by name -/

/-- **ON THE SCRIPT, at the calls of one link: every committed symbol of the link's list of matrices is
the packing of the integers behind the input's cells**: `ScriptHoldsThePackedTraceCells`
(Honest/K3/Term/ScriptHoldsTheHonestValues.lean) at the head's letters, at the integers
`traceMatricesOfTheCells` of the input's own cells, at the place and the record that the public
readers answer at the link: three implications, in the form of `AtCalls`
(Honest/K3/Law/Thread/ExchangeOpensCallsAtHead.lean); at most one of them speaks. A definition, meant
as a hypothesis. -/
def ScriptHoldsThePackedTraceCellsAtTheLink (challengesHeard link : Nat) : Prop :=
  (∀ x A tl, attAt Zp.p.X link = some (x, A, tl) →
    ScriptHoldsThePackedTraceCells Q h.𝔇.sent h.𝔇.l3 Vd challengesHeard x tl
      fun input => traceMatricesOfTheCells Zp.p.X input.trace.cell link) ∧
  (∀ x tl, layAt Zp.p.X link = some x → recordAt Zp.p.X link = some tl →
    ScriptHoldsThePackedTraceCells Q h.𝔇.sent h.𝔇.l3 Vd challengesHeard x tl
      fun input => traceMatricesOfTheCells Zp.p.X input.trace.cell link) ∧
  (link = headLink Zp.p.X →
    ScriptHoldsThePackedTraceCells Q h.𝔇.sent h.𝔇.l3 Vd challengesHeard x₀ Zp.p.X.H.tl
      fun input => traceMatricesOfTheCells Zp.p.X input.trace.cell link)


/-! ## 1b The head's keys, at the Script's witness -/

/-- **At the head's link the key vectors that the table of joints' item reads off the Script's
witness, at the request's reply token, have the joint vector of the library's**, at the public data
that the row itself reads. `lookupKeyFormsAreTheLibrarysKeysAtTheHead` called once, at the letters that
`AtCalls` hands `AtHead`; its premises on the plan, the request and the token are shown from the
head and "the instance is read as the request". Conditional on the two premises on the Script. -/
theorem headKeyFormsAreTheLibrarysKeysAtTheWitness (weights : W₀ → Weights)
    (validInputsHoldTheHonestTrace : ∀ input, Vd input →
      ∃ index request, InputHoldsTheHonestTrace Zp weights input index request)
    {challengesHeard : Nat}
    (packed : ScriptHoldsThePackedTraceCells Q h.𝔇.sent h.𝔇.l3 Vd challengesHeard x₀ Zp.p.X.H.tl
      fun input => traceMatricesOfTheCells Zp.p.X input.trace.cell 24)
    (stored : ScriptCellsAreTheIndexWeights Q h.𝔇.l3 Vd challengesHeard fun input =>
      (weights input.w₀).entry)
    (k : Coins Bk) {input : Local W₀ Rc ProofFile.Inst Cells} {heard : List Fmt.Drawn}
    (isValid : Vd input) (enough : challengesHeard ≤ heard.length) {index : Cm.Idx}
    {request : Inst.Model.Instance Inst.Model.ppref}
    (holds : InputHoldsTheHonestTrace Zp weights input index request)
    (shape : OnBytes.Model.Forest.Shape) (shapeIsThePlans : shape = Zp.p.X.HLy.fs)
    (shapeIsLawful : FoNums.ok shape = true) (theta : GE) :
    ∀ n, n < 2 ^ shape.v →
      OnBytes.Ends.jointKey shape
        (Cb.Fo.forK Cb.Gl.E
          (@headLay (k3SizesAt (P5J.At.X Zp)) (h.𝔇.rq input.x.pub) (k3AdrAt (P5J.At.X Zp))
            x₀.fs x₀.lm x₀.F.next x₀.ns Zp.p.X.H.tl h.𝔇.l3.nr h.𝔇.l3.nc)
          request.y.val
          (Cb.Fo.zext (layMu x₀ Zp.p.X.H.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr
            h.𝔇.l3.nc (fun j => h.𝔇.l3.seat x₀.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW
            (Q.wit k input heard)))) theta n =
      OnBytes.Ends.jointKey shape
        (OnBytes.Ends.H.kvH (headPub Zp.p.X (reqAt Zp input.x).1 (reqAt Zp input.x).2)
          (fromH Zp.p.X (OnBytes.HonestTrace.cellOf Zp.p.X (theTrace Zp.p.X index request))
            (entryOf index))) theta n := by
  have publicPartIsMade : publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := h.pubOne
  have instanceIsTheRequest := holds.instanceIsTheRequest
  have numbers := VerifiableInference.Desc.Kinds.Head.Law.InScope.numbers_in_scope h.scope h.reads
    publicPartIsMade
  rw [requestLetterUnderTheHeadIsTheInstances h instanceIsTheRequest,
    headKeysAtTheRequest h.scope h.reads publicPartIsMade instanceIsTheRequest]
  letI : Sizes := k3SizesAt Zp.p.X
  letI : Policy := k3PolicyAt Zp.p.X
  letI : Request := VerifiableInference.Desc.Kinds.Head.Law.reqX request
  have positions : VerifiableInference.Desc.Kinds.Norm.T = 1024 := by
    unfold VerifiableInference.Desc.Kinds.Norm.T
    show 2 ^ Zp.p.X.hS.lt = 1024
    rw [numbers.lt]
  have vocabulary : VerifiableInference.Desc.Kinds.Head.V = 202048 := numbers.V
  have tokensBelow : ∀ t, request.tok t < 202048 := by
    intro t
    unfold Inst.Model.Instance.tok
    split
    · exact (request.prompt _).isLt
    · exact request.y.isLt
  have planIsOk : VerifiableInference.Desc.Kinds.Head.planOk 4 = true :=
    VerifiableInference.Desc.Kinds.Head.Law.InScope.planOk_of_numbers 4 numbers.lt
      (by
        show Zp.p.X.hS.la - Zp.p.X.hS.lt = 6
        rw [numbers.la, numbers.lt])
      numbers.d numbers.V numbers.sh numbers.F rfl numbers.m1 numbers.m2 numbers.m3 numbers.k1
      numbers.k2 numbers.k3 numbers.e1 numbers.e2 numbers.c1 numbers.c2 numbers.c3
  have requestIsOk : VerifiableInference.Desc.Kinds.Head.Request.ok = true := by
    unfold VerifiableInference.Desc.Kinds.Head.Request.ok
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    refine ⟨⟨(ProofFile.instOf_bytes instanceIsTheRequest).2.2.1, ?_⟩, fun t _ => ?_⟩
    · rw [positions]
      exact request.e_le
    · rw [vocabulary]
      show (if t < Inst.Model.ppref.T then request.tok t else 0) < 202048
      split
      · exact tokensBelow t
      · norm_num
  have base := symbolsPackTheHonestTraceAtTheWitness h.scope h.reads publicPartIsMade
    validInputsHoldTheHonestTrace (by norm_num : 24 < 25) packed k isValid enough holds
  refine lookupKeyFormsAreTheLibrarysKeysAtTheHead (publicPart := Zp.p.X) h.scope h.reads
    publicPartIsMade rfl rfl 4 planIsOk requestIsOk request.y.val
    (by rw [vocabulary]; exact request.y.isLt) (OnBytes.Road.Hd.covReq request)
    ((Array.range 1024).map request.w) (fun t below => ?_) (fun t below => ?_)
    (fun t below _ => ?_) (fun _ => ?_) h.𝔇.sent h.𝔇.l3 x₀ (Q.wit k input heard)
    (theTrace Zp.p.X index request) index
    (OnBytes.HonestTrace.namesFit_theTrace h.scope h.reads publicPartIsMade holds.requestIsServed)
    (messagesHoldTheTraceWhereTheSymbolsPackIt Zp.p.X index request
      (plansOwnRecordHasThePlansMatrices h.scope h.reads publicPartIsMade (by norm_num : 24 < 25))
      x₀ h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc
      (VerifiableInference.OnPublicFiles.layMs x₀ h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW
        (fun j => h.𝔇.l3.seat x₀.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW (Q.wit k input heard))
      base)
    (fun number row column => lt_trans (traceCellsAreBelow129 h.scope h.reads publicPartIsMade
      holds.requestIsServed 24 number row column) (by norm_num))
    (fun row column => storedEntriesAreTheIndexWeights stored x₀ Zp.p.X.H.tl h.𝔇.sent k isValid
      enough index.mat (weightEntriesOfAnHonestInputAreTheIndexs holds)
      (indexIsZeroOutsideTheStoredTable index) row column)
    shape shapeIsThePlans shapeIsLawful theta
  · show ((Array.range 1024).map fun t => decide (request.r ≤ t ∧ t < request.e)).getD t false =
      (decide (request.r ≤ t) && decide (t < request.e))
    rw [entryOfMappedRange, if_pos below, Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
  · show ((Array.range 1024).map fun t =>
        decide (request.r ≤ t ∧ t < min request.e 1023)).getD t false =
      ((decide (request.r ≤ t) && decide (t < request.e)) &&
        decide (t + 1 < VerifiableInference.Desc.Kinds.Norm.T))
    rw [entryOfMappedRange, if_pos below, positions, Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  · rw [entryOfMappedRange, if_pos (by omega)]
    show request.tok (t + 1) = if t + 1 < Inst.Model.ppref.T then request.tok (t + 1) else 0
    rw [if_pos (show t + 1 < Inst.Model.ppref.T from below)]
  · rw [entryOfMappedRange, if_pos (by norm_num)]
    show request.tok (1023 + 1) = request.y.val
    unfold Inst.Model.Instance.tok
    rw [dif_neg (show ¬ 1023 + 1 < Inst.Model.ppref.T from (by omega : ¬ 1023 + 1 < 1024))]

/-! ## 2 The digits -/

/-- **CLAUSE 12 OF THE DIGITS' BUNDLE, AT THE SCRIPT's WITNESS.** Conditional on the head and six
premises: the site, its sort and what the public reader answers at its link; Said gives `SaidOk`; the
guard's number; the premise on the Script, at the site's own sampling round. Nothing is asked of the
input. -/
theorem digitsWitnessFactsAtTheHonestTrace (weights : W₀ → Weights)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Cells) X → Prop)
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m)
    (s : Site) (siteOfThePublicPart : s ∈ lookSites Zp) (onTheDigits : s.digits = true)
    {x : PlaceL} {tl : HTailF2} (placeIsFound : digAt Zp.p.X s.link = some (x, tl))
    (challengesHeard : Nat)
    (enoughChallengesInFront : challengesHeard ≤
      (LH).thread.front + roundsTo (LH).thread.bs (borderOf s.link s.digits))
    (scriptHoldsTheDigitArrays : ∀ samplingRound, s.rng = some samplingRound →
      ScriptHoldsTheDigitArrays Q h.𝔇.sent h.𝔇.l3 Vd challengesHeard x tl
        fun input heard => zzOwn Zp.p.X s.link input.trace (tritsAt heard samplingRound)) :
    DigitsWitnessFacts h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w Said s
      (lookupWitness Zp weights s) x tl := by
  intro blk memberAtTheBorder k st m En ds y cols st' pairInFront drawsAreFit memberStepped a
    openSegment ds'
  have publicPartIsMade : publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := h.pubOne
  have inputIsValid : Vd m.st.input :=
    (show m.st.input = w ∧ Vd m.st.input from pairInFront.1.2.2.2.2.2.2).2
  have heardLength := (LH).thread.heard_length pairInFront.1.2.1
  have linkBelow := link_lt_head h s siteOfThePublicPart
  obtain ⟨sub, linkHasASort, -, -⟩ := K3Lot.k03_sub_full s.link linkBelow
  obtain rfl := recordFoundAtTheDigitsIsTheLookupsOwn publicPartIsMade s siteOfThePublicPart
    onTheDigits placeIsFound
  obtain ⟨shapeIsTheTails, planesRowsAreThirtyTwo, -⟩ :=
    Exchange.table_digits Zp s siteOfThePublicPart onTheDigits placeIsFound
  obtain ⟨samplingRound, roundIs, library⟩ :=
    digitsFillingIsTheLibrarys publicPartIsMade id weights (reqAt Zp) m.st.input s
      siteOfThePublicPart onTheDigits (fun _ => 0)
      (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) m.st.heard
  have roundIsHeard : samplingRound < m.st.heard.length := by
    obtain ⟨attentionLinks, twelveGroups, -, -⟩ :=
      publicNumbersInScope h.scope h.reads publicPartIsMade
    have inFront := roundInFrontAtWrittenTable attentionLinks twelveGroups (cuts_head h) s
      siteOfThePublicPart linkBelow roundIs
    have base : s.at_.base = roundsTo (LH).thread.bs (borderOf s.link s.digits) :=
      lookupBaseIsTheRoundsToTheBorder h s siteOfThePublicPart
    omega
  have sameDigits : zzOwn Zp.p.X s.link m.st.input.trace (tritsAt m.st.heard samplingRound) =
      zzOwn Zp.p.X s.link m.st.input.trace
        (tritsAt (m.st.heard ++ ds ++ ds') samplingRound) := by
    rw [List.append_assoc, tritsAt_append _ _ roundIsHeard]
  have enough : challengesHeard ≤ (m.st.heard ++ ds ++ ds').length := by
    rw [List.length_append, List.length_append, heardLength]
    omega
  have fromPieces := digitsTailComesFromPieces publicPartIsMade s siteOfThePublicPart onTheDigits
  have arrays := scriptHoldsTheDigitArrays samplingRound roundIs
  refine lookupFillsAtTheWitnessAtTheDigits arrays fromPieces s _ _ _ _ k inputIsValid enough
    shapeIsTheTails planesRowsAreThirtyTwo library sameDigits ?_
    (digitsMaskEntriesAtEveryWitness h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s
      siteOfThePublicPart onTheDigits linkHasASort Said saidGivesWordsBelowThePrime placeIsFound blk
      memberAtTheBorder k st m En ds y cols st' pairInFront drawsAreFit memberStepped a openSegment
      _)
  have shapeIsLawful : FoNums.ok (tlOf Zp.p.X s.link).f9 = true := by
    rw [← shapeIsTheTails]
    exact (FastLaw.sites_ok Zp s siteOfThePublicPart).2
  have keys := lookupKeyFormsAtDigitsFromTheScript arrays
    (OnBytes.HonestTrace.tailOK_Z fromPieces) shapeIsLawful k inputIsValid enough
    (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta)
  rw [shapeIsTheTails]
  show ∀ n, n < 2 ^ (tlOf Zp.p.X s.link).f9.v → _ = OnBytes.Ends.jointKey (tlOf Zp.p.X s.link).f9
    (OnBytes.HonestTrace.kvZ (tlOf Zp.p.X s.link)
      (inExt (zzOwn Zp.p.X s.link m.st.input.trace (tritsAt m.st.heard samplingRound)))) _ n
  rw [sameDigits]
  exact keys

/-! ## 3 The calls -/

/-- **CLAUSE 12 OF THE CALLS' BUNDLE, AT THE SCRIPT's WITNESS.** Conditional on the head and nine
premises: the site and its sort; Said gives `SaidOk`; valid inputs hold the honest trace of a served
request; the guard's number; two premises on the Script; and, where the link is the head's, the seat
and the border of the reply's clause. summands: a letter of the seat. -/
theorem callsWitnessFactsAtTheHonestTrace (weights : W₀ → Weights)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Cells) X → Prop)
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m)
    (s : Site) (siteOfThePublicPart : s ∈ lookSites Zp) (onTheCalls : s.digits = false)
    (validInputsHoldTheHonestTrace : ∀ input, Vd input →
      ∃ index request, InputHoldsTheHonestTrace Zp weights input index request)
    (challengesHeard : Nat)
    (enoughChallengesInFront : challengesHeard ≤
      (LH).thread.front + roundsTo (LH).thread.bs (borderOf s.link s.digits))
    (scriptHoldsThePackedTraceCells :
      ScriptHoldsThePackedTraceCellsAtTheLink h Q Vd challengesHeard s.link)
    (scriptCellsAreTheIndexWeights :
      ScriptCellsAreTheIndexWeights Q h.𝔇.l3 Vd challengesHeard fun input =>
        (weights input.w₀).entry)
    (summands : LookJobs Ask)
    (seatAtTheHeadsLink : s.link = headLink Zp.p.X → ∃ lot : Block TS ProofFile.Cl,
      SiteRest Zp cF H.first s lot summands (lookupWitness Zp weights s))
    (replyClauseSpeaksInFront : s.link = headLink Zp.p.X → b₀ ≤ borderOf s.link s.digits) :
    CallsWitnessFacts h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w Said s
      (lookupWitness Zp weights s) := by
  intro blk memberAtTheBorder k st m En ds y cols st' pairInFront drawsAreFit memberStepped a
    openSegment ds'
  have publicPartIsMade : publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := h.pubOne
  have inputIsValid : Vd m.st.input :=
    (show m.st.input = w ∧ Vd m.st.input from pairInFront.1.2.2.2.2.2.2).2
  have heardLength := (LH).thread.heard_length pairInFront.1.2.1
  have linkBelow := link_lt_head h s siteOfThePublicPart
  obtain ⟨sub, linkHasASort, -, -⟩ := K3Lot.k03_sub_full s.link linkBelow
  have enough : challengesHeard ≤ (m.st.heard ++ ds ++ ds').length := by
    rw [List.length_append, List.length_append, heardLength]
    omega
  obtain ⟨index, request, holds⟩ := validInputsHoldTheHonestTrace m.st.input inputIsValid
  have namesFit := OnBytes.HonestTrace.namesFit_theTrace h.scope h.reads publicPartIsMade
    holds.requestIsServed
  have callerAndGroup :=
    callerAndGroupAreTheLinks h.scope h.reads publicPartIsMade s siteOfThePublicPart
  have shapeIsLawful := (FastLaw.sites_ok Zp s siteOfThePublicPart).2
  have matricesAreTheTraces := traceMatricesOfAnHonestInputAreTheTraces h.scope h.reads
    publicPartIsMade holds linkBelow
  have small := fun tl : HTailF2 => traceCellsAreSmallAtValidInputs h.scope h.reads
    publicPartIsMade validInputsHoldTheHonestTrace linkBelow tl
  have cellsAreTheIntegers : ∀ number row column,
      OnBytes.HonestTrace.atNo Zp.p.X
        (OnBytes.HonestTrace.cellOf Zp.p.X (theTrace Zp.p.X index request)) s.link number row
        column =
      ((traceMatricesOfTheCells Zp.p.X m.st.input.trace.cell s.link number row column : ℤ) :
        Cb.Gl.E) := by
    intro number row column
    rw [holds.traceIsTheHonestTrace]
    exact cellsByNumberAreTheCastsOfTheirIntegers _ _ _ _ _ _
  unfold Exchange.AtCalls
  refine ⟨fun x A tl placeIsFound => ?_, fun x tl placeIsFound recordIsFound => ?_,
    fun linkIsTheHeads => ?_⟩
  · -- attention
    obtain ⟨plan, planIsFound, shapeIsOfThePlan, recordIs, placesShape, placesRows, recordIsFound,
      shapeIsThePlans, placesShapeIsThePlans⟩ :=
      attentionPlaceIsThePlans h.scope h.reads publicPartIsMade linkBelow placeIsFound
    have linkIsOdd : s.link % 2 = 1 := VerifiableInference.OnPublicFiles.attAt_odd placeIsFound
    obtain ⟨callerIs, groupIs⟩ := callerAndGroup.2.2 (by omega) linkIsOdd
    have groupBelow : s.group < 12 := by omega
    have linkIs : 2 * s.group + 1 = s.link := by omega
    rw [← groupIs] at shapeIsThePlans placesShapeIsThePlans
    obtain ⟨sitesShape, sitesRows, -⟩ :=
      Exchange.table_attention Zp s siteOfThePublicPart onTheCalls placeIsFound
    have packed := scriptHoldsThePackedTraceCells.1 x A tl placeIsFound
    have base := symbolsPackTheHonestTraceAtTheWitness h.scope h.reads publicPartIsMade
      validInputsHoldTheHonestTrace linkBelow packed k inputIsValid enough holds
    have record := recordAtTheLinkHasThePlansMatrices h.scope h.reads publicPartIsMade linkBelow
      recordIsFound
    have cut : matricesCutToTheSizes tl
        (traceMatricesOfTheCells Zp.p.X m.st.input.trace.cell s.link) =
        theTrace Zp.p.X index request s.link := by
      rw [matricesAreTheTraces]
      exact (honestTraceIsItsRestrictionToTheSizes Zp.p.X index request record).symm
    have witnessCellsAreTheTraces :
        VerifiableInference.Desc.First.Att.P.matsOfMsg x tl h.𝔇.sent h.𝔇.l3.rad
          (attMs x h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat x.link false j.1) h.𝔇.l3.arr
            (Q.wit k m.st.input (m.st.heard ++ ds ++ ds'))) =
        OnBytes.Road.Rows.Norms.castM (theTrace Zp.p.X index request (2 * s.group + 1)) := by
      funext number row column
      have entry : _ = ((matricesCutToTheSizes tl
          (traceMatricesOfTheCells Zp.p.X m.st.input.trace.cell s.link) number row column : ℤ) :
          Cb.Gl.E) :=
        attentionEntryIsTheTraceCell packed (small tl) k inputIsValid enough number row column
      rw [cut] at entry
      rw [linkIs]
      exact entry
    refine lookupFillsAtTheWitnessAtAttention packed (small tl) A s _ _ _ _ k inputIsValid enough
      (libraryKeysAndBitsAtAttention h.scope h.reads publicPartIsMade holds s siteOfThePublicPart
        onTheCalls callerIs groupBelow (fun _ => 0) _ _) ?_ ?_ ?_ ?_
      (attentionMaskEntriesAtEveryWitness h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s
        siteOfThePublicPart onTheCalls linkHasASort Said saidGivesWordsBelowThePrime placeIsFound
        blk memberAtTheBorder k st m En ds y cols st' pairInFront drawsAreFit memberStepped a
        openSegment _)
      (attentionRiderVanishesAtTheLink h.scope h.reads publicPartIsMade holds.requestIsServed
        linkBelow placeIsFound h.𝔇.sent h.𝔇.l3.rad Iop.extNone Unit _ base)
    · rw [shapeIsThePlans]
      exact OnBytes.HonestTrace.bNo_odd Zp.p.X s.group
    · rw [sitesShape, sitesRows, placesShape, placesRows, shapeIsOfThePlan, recordIs]
      exact VerifiableInference.Desc.First.Look.planesAtB_att publicPartIsMade _ plan planIsFound
    · intro row _ column _
      rw [linkIs]
      exact cellsAreTheIntegers _ row column
    · exact lookupKeyFormsAreTheLibrarysKeysAtAttention h.scope h.reads publicPartIsMade groupBelow
        A shapeIsThePlans
        (paddingRowsAtAttentionAreTheLibrarys h.scope h.reads publicPartIsMade groupBelow)
        h.𝔇.sent h.𝔇.l3 x tl _ (theTrace Zp.p.X index request) namesFit witnessCellsAreTheTraces
        s.shape (sitesShape.trans placesShapeIsThePlans) shapeIsLawful _
  · -- layers
    obtain ⟨linkIsEven, linkIsNotTheHeads, stepIsTwo, placesShape, placesRows, plan, planIsFound,
      recordIs⟩ := layersPlaceIsThePlans h.scope h.reads publicPartIsMade linkBelow placeIsFound
        recordIsFound
    obtain ⟨callerIs, groupIs⟩ := callerAndGroup.2.1 linkIsNotTheHeads linkIsEven
    have groupBelow : s.group < 12 := by omega
    have linkIs : 2 * s.group = s.link := by omega
    have groupOfTheLink : s.link / stepAt Zp.p.X = s.group := by rw [stepIsTwo, groupIs]
    obtain ⟨sitesShape, sitesRows, -⟩ :=
      Exchange.table_layers Zp s siteOfThePublicPart onTheCalls placeIsFound
    have packed := scriptHoldsThePackedTraceCells.2.1 x tl placeIsFound recordIsFound
    have base := symbolsPackTheHonestTraceAtTheWitness h.scope h.reads publicPartIsMade
      validInputsHoldTheHonestTrace linkBelow packed k inputIsValid enough holds
    have record := recordAtTheLinkHasThePlansMatrices h.scope h.reads publicPartIsMade linkBelow
      recordIsFound
    have matrices := messagesHoldTheTraceWhereTheSymbolsPackIt Zp.p.X index request record x
      h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc
      (VerifiableInference.OnPublicFiles.layMs x h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW
        (fun j => h.𝔇.l3.seat x.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW
        (Q.wit k m.st.input (m.st.heard ++ ds ++ ds'))) base
    rw [← linkIs] at matrices
    have weightsAre := layersWeightsAreTheIndexWeights scriptCellsAreTheIndexWeights x tl h.𝔇.sent
      s.group k inputIsValid enough index.mat
      (weightEntriesOfAnHonestInputAreTheIndexs holds) (indexIsZeroOutsideTheStoredTable index)
    have cubes := layersRiderVanishesAtTheLink h.scope h.reads publicPartIsMade
      holds.requestIsServed linkBelow placeIsFound recordIsFound h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW
      h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc Iop.extNone Unit
      (VerifiableInference.OnPublicFiles.layMs x h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW
        (fun j => h.𝔇.l3.seat x.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW
        (Q.wit k m.st.input (m.st.heard ++ ds ++ ds'))) base
    rw [groupOfTheLink] at cubes ⊢
    refine lookupFillsAtTheWitnessAtLayers packed (small tl)
      (VerifiableInference.Desc.First.Look.pubAt Zp.p.X s.group) s _ _ _ _ k inputIsValid enough
      (libraryKeysAndBitsAtLayers h.scope h.reads publicPartIsMade holds s siteOfThePublicPart
        onTheCalls callerIs groupBelow (fun _ => 0) _ _) ?_ ?_ ?_ ?_
      (layersMaskEntriesAtEveryWitness h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s
        siteOfThePublicPart onTheCalls linkHasASort Said saidGivesWordsBelowThePrime _ tl
        placeIsFound blk memberAtTheBorder k st m En ds y cols st' pairInFront drawsAreFit
        memberStepped a openSegment _) cubes
    · exact OnBytes.HonestTrace.bNo_even Zp.p.X groupBelow
    · rw [sitesShape, sitesRows, placesShape, placesRows, recordIs]
      exact VerifiableInference.Desc.First.Look.planesAtB_lay publicPartIsMade _ plan planIsFound
    · intro row _ column _
      rw [linkIs]
      exact cellsAreTheIntegers _ row column
    · exact lookupKeyFormsAreTheLibrarysKeysAtLayers h.scope h.reads publicPartIsMade groupBelow
        h.𝔇.sent h.𝔇.l3 x tl _ (theTrace Zp.p.X index request) index namesFit matrices weightsAre
        s.shape (sitesShape.trans placesShape) shapeIsLawful _
  · -- the head
    have linkIsTwentyFour : s.link = 24 := linkIsTheHeads.trans (P1K8T.headLink_at h)
    have callerIs := callerAndGroup.1 linkIsTwentyFour
    have marks := OnBytes.HonestTrace.planMarks_in_scope h.scope h.reads publicPartIsMade
    have headsLinkIs : (if Zp.p.X.p4 then 2 else 1) * Zp.p.X.NGr = 24 := by
      rw [marks.p4, marks.groups]
      rfl
    obtain ⟨-, placesShape, placesRows, -⟩ :=
      VerifiableInference.Desc.First.Look.lookAt_head (X := Zp.p.X) (x := x₀) (by
        rw [headsLinkIs]
        exact P5J.k03_look_head h)
    obtain ⟨sitesShape, sitesRows, -⟩ := Exchange.table_head Zp s siteOfThePublicPart onTheCalls
      linkIsTheHeads h.headAt
    have packed := scriptHoldsThePackedTraceCells.2.2 linkIsTheHeads
    have packedAtTwentyFour := packed
    rw [linkIsTwentyFour] at packedAtTwentyFour
    have base := symbolsPackTheHonestTraceAtTheWitness h.scope h.reads publicPartIsMade
      validInputsHoldTheHonestTrace linkBelow packed k inputIsValid enough holds
    rw [linkIsTwentyFour] at base
    obtain ⟨lot, seat⟩ := seatAtTheHeadsLink linkIsTheHeads
    have tokenIsTheRequests : st'.replyTok? = some request.y.val :=
      replyTokenBehindTheLookupIsTheRequests h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s
        siteOfThePublicPart lot summands _ seat (replyClauseSpeaksInFront linkIsTheHeads) Said
        memberAtTheBorder pairInFront memberStepped holds.instanceIsTheRequest
    rw [tokenIsTheRequests]
    letI : Sizes := k3SizesAt (P5J.At.X Zp)
    letI : Policy := k3PolicyAt (P5J.At.X Zp)
    letI : Request := h.𝔇.rq m.st.input.x.pub
    refine lookupFillsAtTheWitnessAtTheHead Zp packed (small Zp.p.X.H.tl) (k3AdrAt (P5J.At.X Zp)) s
      _ _ _ _ _ k inputIsValid enough
      (libraryKeysAndBitsAtTheHead h.scope h.reads publicPartIsMade holds s siteOfThePublicPart
        onTheCalls callerIs (fun _ => 0) _ _) ?_ ?_ ?_ ?_
      (headMaskEntriesAtEveryWitness h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s
        siteOfThePublicPart onTheCalls linkHasASort Said saidGivesWordsBelowThePrime _
        linkIsTheHeads _ blk memberAtTheBorder k st m En ds y cols st' pairInFront drawsAreFit
        memberStepped a openSegment _)
      (headRiderVanishesAtTheLink h.scope h.reads publicPartIsMade holds.requestIsServed Zp
        holds.instanceIsTheRequest x₀ h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr
        h.𝔇.l3.nc Iop.extNone Unit
        (VerifiableInference.OnPublicFiles.layMs x₀ h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW
          (fun j => h.𝔇.l3.seat x₀.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW
          (Q.wit k m.st.input (m.st.heard ++ ds ++ ds'))) base _)
    · exact OnBytes.HonestTrace.bNo_head Zp.p.X
    · rw [sitesShape, sitesRows, placesShape, placesRows]
      exact VerifiableInference.Desc.First.Look.planesAtB_head publicPartIsMade
    · intro row _ column _
      have cells := cellsAreTheIntegers (k3AdrAt (P5J.At.X Zp)).iB row column
      rw [linkIsTwentyFour] at cells
      rw [linkIsTwentyFour]
      exact cells
    · exact headKeyFormsAreTheLibrarysKeysAtTheWitness h Q Vd weights validInputsHoldTheHonestTrace
        packedAtTwentyFour scriptCellsAreTheIndexWeights k inputIsValid enough holds s.shape
        (sitesShape.trans placesShape) shapeIsLawful _

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.recordFoundAtTheDigitsIsTheLookupsOwn
#print axioms ProofFile.Honest.K3.Term.callerAndGroupAreTheLinks
#print axioms ProofFile.Honest.K3.Term.attentionPlaceIsThePlans
#print axioms ProofFile.Honest.K3.Term.layersPlaceIsThePlans
#print axioms ProofFile.Honest.K3.Term.traceMatricesOfAnHonestInputAreTheTraces
#print axioms ProofFile.Honest.K3.Term.traceCellsAreSmallAtValidInputs
#print axioms ProofFile.Honest.K3.Term.symbolsPackTheHonestTraceAtTheWitness
#print axioms ProofFile.Honest.K3.Term.weightEntriesOfAnHonestInputAreTheIndexs
#print axioms ProofFile.Honest.K3.Term.indexIsZeroOutsideTheStoredTable
#print axioms ProofFile.Honest.K3.Term.headKeyFormsAreTheLibrarysKeysAtTheWitness
#print axioms ProofFile.Honest.K3.Term.ScriptHoldsThePackedTraceCellsAtTheLink
#print axioms ProofFile.Honest.K3.Term.digitsWitnessFactsAtTheHonestTrace
#print axioms ProofFile.Honest.K3.Term.callsWitnessFactsAtTheHonestTrace
