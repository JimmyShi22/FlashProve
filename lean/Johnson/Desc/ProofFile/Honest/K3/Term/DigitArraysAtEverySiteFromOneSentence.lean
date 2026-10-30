-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT ANY SCRIPT, UNDER THE LIBRARY's HEAD ON THE PUBLIC INPUT.
Johnson/Desc/ProofFile/Honest/K3/Term/DigitArraysAtEverySiteFromOneSentence.lean: the honest side of
the kind "lookup" (K3): AT EVERY SITE OF A LOOKUP ON THE DIGITS, THE NAMED PREMISE
`ScriptHoldsTheDigitArrays` (Term/ScriptHoldsTheHonestValues.lean) FROM ONE SENTENCE ON THE
`Script`'s FIELD `msg`, the head (`P5J.AtMgA`) and nothing else but the name of the ground. It pays,
under the head, the public premise of Term/DigitArraysFromTheDigitsFilling.lean. Three definitions
with code (two closed tests, a second text of a list), controls, theorems.

  `publicDataServeTheDigitsUnderTheHead`   `PublicDataServeTheDigitsAtTheLink`, PAID: under the
      head, at the ground that `blankBy` makes of the plan, at a link below 25, at the round that
      the table of places names (`K3.rngIn`), at every `challengesHeard` from round + 1 on
  `siteRoundIsTheTablesRound`   a site's field rng is that round, by `siteAt`'s text
  `digitArraysAtTheSiteFromOneSentence`   THE END, at a site s of `lookSites Zp` on the digits with
      s.rng = some round: the digits are `zzOwn Zp.p.X link v.trace (tritsAt heard round)`
  `threeWaysToOneRoundAtWrittenValues`, `digitArraysAreSeatedAtWrittenValues`   the closed
      tests, that each accepts, and a control of each
  `roundNumbersOfEntries`, `roundNumbersReadTheEntries`   the rounds of a name, off the
      entries alone

So the public premise is not empty under the head: all seven fields hold together there.

Limits. CONDITIONAL on the head and on the sentence: NO FILE SHOWS THE SENTENCE OF ANY SCRIPT; what
it takes to meet it stands in the head of Term/DigitArraysFromTheDigitsFilling.lean. The ground is
the one of a request of zeros (`blankBy`): the digits' filling reads of a ground its first chain's
parameters, its public record and the built links' records alone, which no request turns; no
statement here says so of another ground. The trace's type is the frame's reader of cells itself.
Closed facts are decided by Lean's kernel by evaluation at the library's written values. That a head
can be had is not said. The full size and the earlier hash alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.DigitArraysFromTheDigitsFilling
import Johnson.Desc.ProofFile.Honest.K2.Law.DigitsLightAtHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LinkLtHead
import Johnson.Desc.ProofFile.Honest.K8.AddressLaw
import Johnson.HB.LLHARD.Q38E.TiesAtHead
import Johnson.P1K8R.SecondLaidAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.Model (HTailF2)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (seatsOf pairOf heardOf bzAtOf)
open OnBytes.HonestTrace.U3.Fit (seatsW)
open VerifiableInference.Desc (Chain arrayOf)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (digAt)
open ProofFile.Honest.K2 (roundNumbers)
open ProofFile.Honest.K2.Law (rngBy)
open ProofFile.Honest.K1 (digitsFill)
open ProofFile.Honest.FirstThread (Script)
open Johnson.G (layoutFull)
open Johnson.AtFull.Desc (spotsWritten)
open H2K5.Row (roundsBy cutPairsW)
open P5J (AtMgA TS CellsM)

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

/-! ## 1 The closed tests -/

/-- The numbers, among a chain's rounds, of the rounds of a name, off the rounds' entries alone. -/
def roundNumbersOfEntries (entries : List Fmt.Entry) (name : String) : List ℕ :=
  entries.zipIdx.filterMap fun e => if e.1.name == name then some e.2 else none

/-- `roundNumbers` (Honest/K2/Rounds.lean) reads of the declared rounds their entries alone. -/
theorem roundNumbersReadTheEntries (rounds : List Fmt.DeclaredRound) (name : String) :
    roundNumbers rounds name = roundNumbersOfEntries (rounds.map (·.entry)) name := by
  unfold roundNumbers roundNumbersOfEntries
  rw [List.zipIdx_map, List.filterMap_map]
  rfl

/-- **A CLOSED TEST, at the library's written values: THREE WAYS TO ONE ROUND.** At each of the 25
links the round that samples the matrix of the link's smallness test is one number by the table of
places (`K3.rngIn`, Honest/K3/Lot.lean: the sites' own), by the first round of the link's place of
the smallness test (`rngBy`, Honest/K2/Law/DigitsWritten.lean: BZ's values') and as entry number
link of the rounds named "RNG" (ZZ's values'). -/
def threeWaysToOneRoundAtWrittenValues : Bool :=
  (List.range 25).all fun link =>
    ((rngBy (roundsBy cutPairsW) P5T.esFull.1 spotsWritten link).map (·.1) ==
        rngIn spotsWritten link) &&
      ((roundNumbersOfEntries P5T.esFull.1 "RNG")[link]? == rngIn spotsWritten link)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- It accepts: decided by Lean's kernel by evaluation. -/
theorem threeWaysToOneRoundAtWrittenValuesAccepts :
    threeWaysToOneRoundAtWrittenValues = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Two controls: the table of places names a round at each of the 25 links, so that the test did
not compare nothing with nothing; and with the entries moved by one the third way parts from the
first at some link. -/
theorem threeWaysToOneRoundControl :
    (((List.range 25).all fun link => (rngIn spotsWritten link).isSome) &&
      !((List.range 25).all fun link =>
        (roundNumbersOfEntries (P5T.esFull.1.drop 1) "RNG")[link]? ==
          rngIn spotsWritten link)) = true := by
  decide +kernel

/-- **A CLOSED TEST, at the library's written values: BOTH ARRAYS' MESSAGE IS SEATED.** At each of
the 25 links, for "BZ" and for "ZZ": the written layout's array of that name lies in a message that
a written seat of "BZ" names at that link, and the sending there begins just behind the round. -/
def digitArraysAreSeatedAtWrittenValues : Bool :=
  (List.range 25).all fun link =>
    ["BZ", "ZZ"].all fun name =>
      (arrayOf layoutFull link name).all fun array =>
        (seatsW "BZ").any fun s =>
          (pairOf (seatsW "BZ") s.addr == some (link, array.message)) &&
            (rngIn spotsWritten link).any fun round => heardOf (seatsW "BZ") s.addr == round + 1

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- It accepts: decided by Lean's kernel by evaluation. -/
theorem digitArraysAreSeatedAtWrittenValuesAccepts :
    digitArraysAreSeatedAtWrittenValues = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Two controls: the written layout has both arrays at each of the 25 links, so that the test did
ask; and of the array "U3", which lies in another message, it says no. -/
theorem digitArraysAreSeatedControl :
    (((List.range 25).all fun link =>
        ["BZ", "ZZ"].all fun name => (arrayOf layoutFull link name).isSome) &&
      !((List.range 25).all fun link =>
        (arrayOf layoutFull link "U3").all fun array =>
          (seatsW "BZ").any fun s =>
            pairOf (seatsW "BZ") s.addr == some (link, array.message))) = true := by
  decide +kernel

/-! ## 2 The site's round -/

/-- **A site's round is the table's**: at a site of a lookup on the digits the field rng is what the
table of places names at the site's link. By `siteAt`'s text (Honest/K3/Lot.lean). -/
theorem siteRoundIsTheTablesRound {plan : ProofFile.Pub} {s : Site} (siteIsALookups : s ∈ lookSites plan)
    (siteIsOnTheDigits : s.digits = true) {round : ℕ} (siteRound : s.rng = some round) :
    rngIn ((spotsOf plan.cuts).getD []) s.link = some round := by
  unfold lookSites at siteIsALookups
  obtain ⟨x, -, hs⟩ := List.mem_filterMap.1 siteIsALookups
  unfold siteAt at hs
  obtain ⟨p, -, hs⟩ := Option.bind_eq_some_iff.1 hs
  obtain ⟨shape, -, hs⟩ := Option.bind_eq_some_iff.1 hs
  obtain ⟨n, -, hs⟩ := Option.bind_eq_some_iff.1 hs
  dsimp only at hs
  split at hs
  · obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 hs
    obtain rfl : r' = round := Option.some.inj siteRound
    exact hr'
  · obtain rfl := Option.some.inj hs
    cases siteRound

/-! ## 3 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : PlaceL}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)

include h in
/-- **THE PUBLIC PREMISE, PAID UNDER THE HEAD.** At the ground that `blankBy` makes of the plan; at
a link below 25; at the place and the record that `digAt` answers; at the round that the table of
places names at the link; at every `challengesHeard` from round + 1 on. -/
theorem publicDataServeTheDigitsUnderTheHead {ground : ProofFile.Ground}
    (groundIsThePlans : ProofFile.blankBy ProofFile.pureRoad.links Zp = some ground) {link : ℕ}
    (linkBelow : link < 25) {x : PlaceL} {tl : HTailF2}
    (placeAndTail : digAt (P5J.At.X Zp) link = some (x, tl)) {round : ℕ}
    (roundIsTheTables : rngIn ((spotsOf Zp.cuts).getD []) link = some round)
    {challengesHeard : ℕ} (roundIsHeard : round + 1 ≤ challengesHeard) :
    PublicDataServeTheDigitsAtTheLink Zp ground link round challengesHeard tl := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = ground := Option.some.inj (O.blank.symm.trans groundIsThePlans)
  obtain ⟨-, tailIs, -, -, -, -⟩ := digitArraysAddressesAreFound h linkBelow placeAndTail
  obtain ⟨Y, hY⟩ := P1K8T.built_at h.scope h.reads O (Nat.le_of_lt_succ linkBelow)
  have eT : tl = Y.tl := Q38.j_tl_built h O.blank (Nat.le_of_lt_succ linkBelow) hY tailIs
  have spots := OnBytes.HonestTrace.U3.Fit.spots_at_head h
  have roundW : rngIn spotsWritten link = some round := by
    rw [spots] at roundIsTheTables
    exact roundIsTheTables
  have entries := ProofFile.Honest.K2.Law.entries_at_head h.toAtMg O
  have rounds := threeWaysToOneRoundAtWrittenValuesAccepts
  unfold threeWaysToOneRoundAtWrittenValues at rounds
  have roundsAt := List.all_eq_true.1 rounds link (List.mem_range.2 linkBelow)
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, roundW] at roundsAt
  obtain ⟨countsWay, digitsWay⟩ := roundsAt
  refine ⟨O.first, O.W, by rw [hY, eT]; rfl, ?_, ?_, ?_, ?_⟩
  · obtain ⟨n, hn, e1⟩ := Option.map_eq_some_iff.1 countsWay
    have hr : OnBytes.HonestTrace.rngAt Zp spotsWritten link =
        rngBy (roundsBy cutPairsW) P5T.esFull.1 spotsWritten link := by
      unfold OnBytes.HonestTrace.rngAt
      rw [ProofFile.Honest.K2.Law.rngIn_by, OnBytes.HonestTrace.U3.Fit.before_at_head h, entries]
    refine ⟨n.2, ?_⟩
    unfold bzAtOf
    rw [spots]
    show (OnBytes.HonestTrace.rngAt Zp spotsWritten link).bind (fun n =>
      (Bs.G₀.built[link]?).bind fun Y =>
        some ({ rng := n.1, declared := n.2, tl := Y.tl, mats := matsOwn Bs.G₀.W link } :
          OnBytes.HonestTrace.BzAt)) = _
    rw [hr, hn, hY, eT, ← e1]
    rfl
  · rw [roundNumbersReadTheEntries, entries]
    exact digitsWay
  · exact ProofFile.Honest.K8.mz_allRows tl
      ⟨Q38.cols_at_head h placeAndTail,
        by rw [eT]; exact VerifiableInference.Desc.First.K8.Honest.matrix_at_built h.scope h.reads O
            h.laid.planOk linkBelow hY,
        by rw [eT]; exact VerifiableInference.Desc.First.K8.Honest.made_count
            (_root_.P1K8.made_at_built h.scope h.reads O linkBelow hY)⟩
  · intro name array nameIs arrayIs
    have layoutIs : Zp.first.layout = layoutFull := by
      rw [← O.first]
      exact (OnBytes.HonestTrace.U3.Fit.first_at_head h O.blank).2.2
    rw [OnBytes.HonestTrace.U3.Fit.seats_at_head h O.blank "BZ"]
    rw [layoutIs] at arrayIs
    have seats := digitArraysAreSeatedAtWrittenValuesAccepts
    unfold digitArraysAreSeatedAtWrittenValues at seats
    have seatsAt := List.all_eq_true.1 (List.all_eq_true.1 seats link (List.mem_range.2 linkBelow))
      name (by rcases nameIs with rfl | rfl <;> simp)
    rw [arrayIs, Option.all_some] at seatsAt
    obtain ⟨s, -, holds⟩ := List.any_eq_true.1 seatsAt
    rw [Bool.and_eq_true, beq_iff_eq, roundW, Option.any_some, beq_iff_eq] at holds
    exact ⟨s.addr, holds.1, by omega, by omega⟩

/-- **THE END, AT A SITE, FROM ONE SENTENCE ON `Q.msg`.** s: a site of the plan's lookups, on the
digits, at the link, whose round is `round`. x, tl: what `digAt` answers at the link. The trace is
the frame's reader of cells itself. CONDITIONAL: under the head h; at least round + 1 challenges are
spoken of; `readersReadTheTrace`: the frame's reader of the cells is the input's trace;
`groundIsThePlans`: ground names what `blankBy` makes of the plan (public; under the head there is
one); `lays`: THE ONE SENTENCE (`ScriptLaysTheFillingAtTheLink`,
Term/DigitArraysFromTheDigitsFilling.lean) at the digits' filling of that ground and the seats of
"BZ". It moves the debt: the sentence is shown of no `Script`. -/
theorem digitArraysAtTheSiteFromOneSentence {Bk : ProverCoinCounts} {W₀ Rc : Type}
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    {s : Site} (siteIsALookups : s ∈ lookSites Zp) (siteIsOnTheDigits : s.digits = true)
    {link : ℕ} (siteIsAtTheLink : s.link = link) {round : ℕ} (siteRound : s.rng = some round)
    {x : PlaceL} {tl : HTailF2} (placeAndTail : digAt Zp.p.X link = some (x, tl))
    {valid : Local W₀ Rc ProofFile.Inst Cells → Prop} {challengesHeard : ℕ}
    (roundIsHeard : round + 1 ≤ challengesHeard)
    {readers : Local W₀ Rc ProofFile.Inst Cells → Readers}
    (readersReadTheTrace : ∀ v, (readers v).cells = v.trace) {ground : ProofFile.Ground}
    (groundIsThePlans : ProofFile.blankBy ProofFile.pureRoad.links Zp = some ground)
    (lays : ScriptLaysTheFillingAtTheLink Zp Q valid challengesHeard readers
      (digitsFill Zp ground (matsOwn ground.W)) (pairOf (seatsOf Zp ground "BZ")) link) :
    ScriptHoldsTheDigitArrays Q h.𝔇.sent h.𝔇.l3 valid challengesHeard x tl
      (fun v heard => zzOwn Zp.p.X link v.trace (tritsAt heard round)) := by
  subst siteIsAtTheLink
  have linkBelow : s.link < 25 := Law.AtThr.link_lt_head h s siteIsALookups
  exact digitArraysFromTheDigitsFilling h Q linkBelow placeAndTail (cells := id)
    readersReadTheTrace
    (publicDataServeTheDigitsUnderTheHead h groundIsThePlans linkBelow placeAndTail
      (siteRoundIsTheTablesRound siteIsALookups siteIsOnTheDigits siteRound) roundIsHeard) lays

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.roundNumbersOfEntries
#print axioms ProofFile.Honest.K3.Term.roundNumbersReadTheEntries
#print axioms ProofFile.Honest.K3.Term.threeWaysToOneRoundAtWrittenValues
#print axioms ProofFile.Honest.K3.Term.threeWaysToOneRoundAtWrittenValuesAccepts
#print axioms ProofFile.Honest.K3.Term.threeWaysToOneRoundControl
#print axioms ProofFile.Honest.K3.Term.digitArraysAreSeatedAtWrittenValues
#print axioms ProofFile.Honest.K3.Term.digitArraysAreSeatedAtWrittenValuesAccepts
#print axioms ProofFile.Honest.K3.Term.digitArraysAreSeatedControl
#print axioms ProofFile.Honest.K3.Term.siteRoundIsTheTablesRound
#print axioms ProofFile.Honest.K3.Term.publicDataServeTheDigitsUnderTheHead
#print axioms ProofFile.Honest.K3.Term.digitArraysAtTheSiteFromOneSentence
