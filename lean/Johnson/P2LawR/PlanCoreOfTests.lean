-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/PlanCoreOfTests.lean: WHAT STAYS OF THE TESTS ON THE LAST TABLE's PLAN
(`LLT25.PlanCore₃`, Johnson/P5J/L0/PlanCore.lean: fourteen fields and indexNeW) FROM ONE TEST WITH
CODE. One definition, two theorems. Joinings: general in every letter; no test and no law is typed
here: each is another file's.

  `core_of_tests`: the structure from five tests' accepts, one text at the base `D.t₁ + D.t₂` and
    nine fields in their own texts: so that a field can be handed in by its test's accept or as a
    fact shown otherwise.
  `coreB`: the conjunction of fifteen tests.
  `coreB_law`: `coreB … = true → PlanCore₃ …`.

  field       test                                        law
  nodup       `LLT25.PlanB.nodupB`                        `nodup_of`
  seats       `P2Law.PlanLeft.seatsB`                     `seatsB_law`
  fence       `PlanB.fenceB` at the base D.t₁ + D.t₂      `fence_of` · `fence_of_base`
  placeB      the field's own Bool at that base           `placeB_of_base`
  someW       `PlanB.someB ms₁ N₁.w`                      `some_of`
  someI       `PlanB.someB ms₁ N₁.index`                  `some_of`
  oneSeat     `PlanB.oneSeatB` (stronger than the field)  `oneSeat_of`
  oneOmega    `ToldDesc.oneOmegaB`                        `oneOmega_iff`
  omegaSeat   `PlanB.omegaSeatB`                          `omegaSeat_of`
  mineI       `PlanB.mineAtB` at V.index                  `mineAt_of`
  mineW       `PlanB.mineAtB` at V.w                      `mineAt_of`
  planAt      `P2Law.PlanLeft.planAtAllB`                 `planAtAll_law`, under the field seats
  oneTable    `PlanB.oneTableAllB`                        `oneTableAll_of`
  planShapes  `ToldDesc.planShapesB`                      `planShapes_iff`
  indexNeW    `PlanB.apartB V.index V.w`                  `apart_of`
  (PlanB: Johnson/LLT25R/PlanLeftTests.lean · P2Law.PlanLeft: Johnson/P2LawR/PlanLeftSeats.lean,
  PlanLeftAt.lean, PlanLeftBase.lean · ToldDesc: Johnson/ToldDescR/OneOmegaB.lean, BookAtW.lean.)

Limits. NO TEST IS EVALUATED HERE. The law says: the fields follow FROM the test's accept; it does
not say that the test accepts at any plan. A sheet's printed "true" is no term of Lean. Five of the
tests accept at an empty list of members, `planAtAllB` at an empty list of stages, `planShapesB`
where a number has no listed shape or no told tree. omegaSeat, mineI and mineW each give a member,
and indexNeW parts the last two: TWO members at least by this file; that Omega's seat is a third
follows with elderBelow, which is none of the fifteen. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P5J.L0.PlanCore
import Johnson.LLT25R.PlanLeftTests
import Johnson.P2LawR.PlanLeftSeats
import Johnson.P2LawR.PlanLeftAt
import Johnson.P2LawR.PlanLeftBase
import Johnson.ToldDescR.OneOmegaB
import Johnson.ToldDescR.BookAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P2Law.PlanLeft
open LLT25
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Fo.Peel Cb
    Johnson.Pack
open Iop Prob _root_.Run
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn onOwn)
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers openSets sampledIn start)
open VerifiableInference.Desc.K13 (Where)
open _root_.Desc.K14 (St)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At)
open _root_.Desc.K14.Law.Fence (CoreFacts MemberFacts)
open H2K.Pin (NTuple)

open LLT25.PlanB

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4) (c : Chain S Cl)
  (D : WholeD) {Xi' : Type} (G : FileDescription Xi') (arr : ℕ → ℕ → ℕ) (dB : RDT) (dt : List RDT)
  (ms₁ ms₂ : List Mem) (N₁ : Numbers) (Ns : NumbersS) (r : Fmt.M1.Stage → ℕ) (n₁ ft nΩ : ℕ)
  (V : VerifiableInference.Desc.Last.OwnSeats) (Ld : VerifiableInference.Desc.K12.Door.Laid)

/-- **What stays of the tests on the plan, field by field: by a test's accept or as a fact.** -/
theorem core_of_tests
    (tSeats : P2Law.PlanLeft.seatsB G (p14At Z).codes (mineOf ms₁ ms₂ N₁ Ns) = true)
    (tPlanAt : planAtAllB G (p14At Z).codes
      (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber) r
      (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.stages (mineOf ms₁ ms₂ N₁ Ns) = true)
    (tPlace : PlaceB
      (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber)
      (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) (VerifiableInference.Desc.numAt D.t₁ D.t₂ 2)
      (D.t₁ + D.t₂) dB dt = true)
    (tOmega : ToldDesc.oneOmegaB (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) nΩ = true)
    (tShapes : ToldDesc.planShapesB G Ld ft n₁ = true)
    (hFence : Fenced (D.t₁ + D.t₂) (mineOf ms₁ ms₂ N₁ Ns))
    (nodup : ((mineOf ms₁ ms₂ N₁ Ns).map (numOf arr)).Nodup)
    (someW : ∃ x ∈ ms₁, SitsAt x N₁.w.1 N₁.w.2)
    (someI : ∃ x ∈ ms₁, SitsAt x N₁.index.1 N₁.index.2)
    (oneSeat : ∀ x ∈ (mineOf ms₁ ms₂ N₁ Ns), ∀ y ∈ (mineOf ms₁ ms₂ N₁ Ns),
      seatOf x = seatOf y → x = y)
    (omegaSeat : ∃ x ∈ (mineOf ms₁ ms₂ N₁ Ns), seatOf x = (D.t₁ + nΩ, 0) ∧
      (p14At Z).S.omega = (x.1.l.get x.2).1)
    (mineI : ∃ x ∈ (mineOf ms₁ ms₂ N₁ Ns), seatOf x = V.index ∧
      (x.1.l.get x.2).1 = V.indexShape)
    (mineW : ∃ x ∈ (mineOf ms₁ ms₂ N₁ Ns), seatOf x = V.w ∧ (x.1.l.get x.2).1 = V.wShape)
    (oneTable : ∀ x ∈ (mineOf ms₁ ms₂ N₁ Ns), seatOf x = (D.t₁ + nΩ, 0) →
      ToldDesc.OneTable (p14At Z).codes (x.1.l.get x.2).1)
    (indexNeW : V.index ≠ V.w) :
    PlanCore₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns r n₁ ft nΩ V Ld :=
  { nodup := nodup
    seats := seatsB_law G (p14At Z).codes _ tSeats
    fence := fence_of_base o mk Z (seatK Z N) N c D _ hFence
    placeB := placeB_of_base o mk Z (seatK Z N) N c D _ dB dt tPlace
    someW := someW
    someI := someI
    oneSeat := oneSeat
    oneOmega := (ToldDesc.oneOmega_iff _ _).1 tOmega
    omegaSeat := omegaSeat
    mineI := mineI
    mineW := mineW
    planAt := planAtAll_law G (p14At Z).codes _ r _ _ (seatsB_law G (p14At Z).codes _ tSeats)
      tPlanAt
    oneTable := oneTable
    planShapes := (ToldDesc.planShapes_iff G Ld ft n₁).1 tShapes
    indexNeW := indexNeW }

/-- **The fifteen tests as one.** -/
def coreB : Bool :=
  nodupB arr (mineOf ms₁ ms₂ N₁ Ns) &&
  P2Law.PlanLeft.seatsB G (p14At Z).codes (mineOf ms₁ ms₂ N₁ Ns) &&
  fenceB (D.t₁ + D.t₂) (mineOf ms₁ ms₂ N₁ Ns) &&
  PlaceB (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber)
    (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) (VerifiableInference.Desc.numAt D.t₁ D.t₂ 2)
    (D.t₁ + D.t₂) dB dt &&
  someB ms₁ N₁.w &&
  someB ms₁ N₁.index &&
  oneSeatB (mineOf ms₁ ms₂ N₁ Ns) &&
  ToldDesc.oneOmegaB (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) nΩ &&
  omegaSeatB (mineOf ms₁ ms₂ N₁ Ns) (D.t₁ + nΩ, 0) (p14At Z).S.omega &&
  mineAtB (mineOf ms₁ ms₂ N₁ Ns) V.index V.indexShape &&
  mineAtB (mineOf ms₁ ms₂ N₁ Ns) V.w V.wShape &&
  planAtAllB G (p14At Z).codes (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber)
    r (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.stages (mineOf ms₁ ms₂ N₁ Ns) &&
  oneTableAllB (p14At Z).codes (mineOf ms₁ ms₂ N₁ Ns) (D.t₁ + nΩ, 0) &&
  ToldDesc.planShapesB G Ld ft n₁ &&
  apartB V.index V.w

/-- **From the one test's accept to what stays of the tests on the plan.** -/
theorem coreB_law
    (h : coreB o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns r n₁ ft nΩ V Ld = true) :
    PlanCore₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns r n₁ ft nΩ V Ld := by
  unfold coreB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩ := h
  exact core_of_tests o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns r n₁ ft nΩ V Ld h2 h12 h4 h8 h14
    (fence_of h3) (nodup_of h1) (some_of h5) (some_of h6) (oneSeat_of h7) (omegaSeat_of h9)
    (mineAt_of h10) (mineAt_of h11) (oneTableAll_of h13) (apart_of h15)

end P2Law.PlanLeft

#print axioms P2Law.PlanLeft.core_of_tests
#print axioms P2Law.PlanLeft.coreB_law
