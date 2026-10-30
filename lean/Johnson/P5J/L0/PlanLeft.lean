-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/L0/PlanLeft.lean: THE LAST TABLE's TESTS ON THE LIST OF ROUNDS (`LLT25.PlanOk₃`, 33
fields, with `LastPlan8`) CUT IN TWO STRUCTURES, in
that structure's own letters: `PlanPaid₃` (ten fields, which a head pays: PlanAtHead.lean) and
`PlanLeft₃` (the other 23, LEFT BY NAME). EACH FIELD BEARS ITS OWN NAME AND ITS OWN TEXT, copied
by program; in the eight of `LastPlan8` four letters are replaced by program as `PlanOk₃` itself
fills them (A, cs, mine, num). `PlanOk₃.of_parts`: the two give `PlanOk₃`: SO LEAN HOLDS EACH COPIED
TEXT AGAINST THE FIELD. `PlanOk₃.left`, `PlanOk₃.paid`: back: nothing is added, nothing lost.
Two structures, three theorems. Nothing on soundness. `PlanLeft₃` is shown at no letters.
PAID: closed · stretch · someO · free0 · dataIs · planOk · ownMask · twoStages · places · planTreeO.
LEFT: sampled · wIn · iIn · omega · nodup · seats · fence · placeB · someW · someI · apartWO · apartIO · oneSeat · oneOmega · omegaSeat · mineI · mineW · seatsApart · allSeats · planAt · oneTable · planShapes · elderBelow.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LLT25R.LastOwedCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace LLT25
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

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4) (c : Chain S Cl)
  (D : WholeD) {Xi' : Type} (G : FileDescription Xi') (arr : ℕ → ℕ → ℕ) (dB : RDT) (dt : List RDT)
  (ms₁ ms₂ : List Mem) (N₁ : Numbers) (Ns : NumbersS) (links : List ModelPart)
  (ps : List VerifiableInference.Desc.Place) (r : Fmt.M1.Stage → ℕ) (n₁ ft nΩ : ℕ)
  (V : VerifiableInference.Desc.Last.OwnSeats) (Ld : VerifiableInference.Desc.K12.Door.Laid)

/-- **OF THE 33: what a head pays.** -/
structure PlanPaid₃ : Prop where
  /-- K12's files' structure at the place: four tests with code, and the chain's errors at
  2⁻¹ ^ 128. PAYER: K12's files. -/
  closed : ∃ ch b₁ b₂ T, ClosedL (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) r ch b₁ b₂ T
  /-- The third piece's stretch of the written rounds is dB :: dt. -/
  stretch : ds₂ D.ds₃ (held (P := (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁
      × St) (c0 Z)) (held (P := (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ ×
      St) (c1 N)) (held (P := (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ ×
      St) (c2 N)) = dB :: dt
  /-- Likewise, of the shared table's list, at Omega's seat. -/
  someO : ∃ x ∈ ms₂, SitsAt x (Ns.tenant .oOmega).1 (Ns.tenant .oOmega).2
  /-- The place's first own tree is number 0 of the chain's own. -/
  free0 : (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.free = 0
  /-- The description's data are made, and are D. -/
  dataIs : ∃ file, (FL o mk Z (seatK Z N) N c).data file = .ok D
  /-- The description's own test on the plan. -/
  planOk : (FL o mk Z (seatK Z N) N c).planOk = true
  /-- The first arm. -/
  ownMask : (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.ownMask = false
  /-- Two stages at least. -/
  twoStages : 2 ≤ (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.stages.length
  /-- The places are the plan's. -/
  places : H2U.placesOfMade Z.made = .ok N
  /-- The shape that the verifier's own layout makes of the plan's one notice for Omega is what the
  description tells of the tree number D.t₁ + nΩ. -/
  planTreeO : PlanTreeO G (p14At Z).codes (p14At Z).S (D.t₁ + nΩ)

/-- **THE OTHERS, LEFT BY NAME.** -/
structure PlanLeft₃ : Prop where
  /-- A TEST ON THE FIRST TABLE: every sampled seat that is open at its last border lies in a tree
  below the last chain's first. -/
  sampled : sampledBelow (D.t₁ + D.t₂) N₁ ((openSets links ps (start links))[ps.length]?.getD []) =
      true
  /-- A TEST ON THE FIRST TABLE: W's seat is among these. -/
  wIn : N₁.w ∈ sampledIn N₁ ((openSets links ps (start links))[ps.length]?.getD [])
  /-- A TEST ON THE FIRST TABLE: so is the index masks'. -/
  iIn : N₁.index ∈ sampledIn N₁ ((openSets links ps (start links))[ps.length]?.getD [])
  /-- A COMPARISON: Omega's tree lies below the last chain's first. -/
  omega : (Ns.tenant .oOmega).1 < D.t₁ + D.t₂
  /-- A TEST ON THE PLAN: no two of mine have one number. -/
  nodup : ((mineOf ms₁ ms₂ N₁ Ns).map (numOf arr)).Nodup
  /-- A TEST ON THE PLAN: the members' seats fit. -/
  seats : SeatsFit (p14At Z).codes G (mineOf ms₁ ms₂ N₁ Ns)
  /-- A TEST ON THE PLAN: they lie in trees sent in front of block 2. -/
  fence : Fenced (baseTwoAt (FL o mk Z (seatK Z N) N c) D (c0 Z) (c1 N)) (mineOf ms₁ ms₂ N₁ Ns)
  /-- A Bool: the tests on the place and on its stretch's data, together (`PlaceB`,
  Johnson/Desc/K12/Coin/BoolsTests.lean). PAYER of this and the next five: K12's files,
  by evaluation. -/
  placeB : PlaceB (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber) (H2U.proximityTestParametersAt ⟨3, none, 2,
                                        .K12⟩ N.W) (VerifiableInference.Desc.numAt D.t₁ D.t₂ 2) (baseTwoAt (FL o mk Z (seatK Z N) N c) D (c0 Z) (c1 N)) dB dt = true
  /-- A member of the first table's list sits at W's seat. -/
  someW : ∃ x ∈ ms₁, SitsAt x N₁.w.1 N₁.w.2
  /-- Likewise at the index masks' seat. -/
  someI : ∃ x ∈ ms₁, SitsAt x N₁.index.1 N₁.index.2
  /-- W's seat is not Omega's. -/
  apartWO : N₁.w ≠ Ns.tenant .oOmega
  /-- The index masks' seat is not Omega's. -/
  apartIO : N₁.index ≠ Ns.tenant .oOmega
  /-- No two of mine have one seat. -/
  oneSeat : ∀ x ∈ (mineOf ms₁ ms₂ N₁ Ns), ∀ y ∈ (mineOf ms₁ ms₂ N₁ Ns), seatOf x = seatOf y → x = y
  /-- The block's declared rounds open one number only under "taken 1". -/
  oneOmega : ToldDesc.OneOmega (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) nΩ
  /-- One of mine has the seat (D.t₁ + nΩ, 0) and the plan's shape for Omega. -/
  omegaSeat : ∃ x ∈ (mineOf ms₁ ms₂ N₁ Ns), seatOf x = (D.t₁ + nΩ, 0) ∧ (p14At Z).S.omega =
      (x.1.l.get
      x.2).1
  /-- One of mine has the index masks' seat and shape. -/
  mineI : ∃ x ∈ (mineOf ms₁ ms₂ N₁ Ns), seatOf x = V.index ∧ (x.1.l.get x.2).1 = V.indexShape
  /-- Likewise W's. -/
  mineW : ∃ x ∈ (mineOf ms₁ ms₂ N₁ Ns), seatOf x = V.w ∧ (x.1.l.get x.2).1 = V.wShape
  /-- The three seats are apart. -/
  seatsApart : V.index ≠ V.w ∧ V.index ≠ (D.t₁ + nΩ, 0) ∧ V.w ≠ (D.t₁ + nΩ, 0)
  /-- Every one of mine has one of the three seats. -/
  allSeats : ∀ z ∈ (mineOf ms₁ ms₂ N₁ Ns), seatOf z = V.index ∨ seatOf z = V.w ∨ seatOf z = (D.t₁ +
      nΩ, 0)
  /-- At every one of mine and the test's first stage: `PlanAt`. -/
  planAt : ∀ x ∈ (mineOf ms₁ ms₂ N₁ Ns), ∀ st rest, (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.stages =
      st :: rest → PlanAt (p14At Z).codes G (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N
      c).lastChainFirstTreeNumber) r st x
  /-- Whoever of mine sits at Omega's seat has rows of one kind alone (five tests on the shape). -/
  oneTable : ∀ x ∈ (mineOf ms₁ ms₂ N₁ Ns), seatOf x = (D.t₁ + nΩ, 0) → ToldDesc.OneTable (p14At
      Z).codes (x.1.l.get x.2).1
  /-- The plan's list of the first chain's trees' shapes is what the description tells of these
  trees (a
  test with code: `planShapesB`, Johnson/ToldDescR/BookAtW.lean). -/
  planShapes : ToldDesc.PlanShapes G Ld ft n₁
  /-- TWO COMPARISONS: the two elder seats lie in trees of the first chain. -/
  elderBelow : V.index.1 < D.t₁ ∧ V.w.1 < D.t₁

variable {o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links ps r n₁ ft nΩ V Ld}

/-- **The two parts give the whole.** -/
theorem PlanOk₃.of_parts (P : PlanPaid₃ o mk Z N c D G dB dt ms₂ Ns r nΩ)
    (L : PlanLeft₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links ps r n₁ ft nΩ V Ld) :
    PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links ps r n₁ ft nΩ V Ld :=
  { sampled := L.sampled
    wIn := L.wIn
    iIn := L.iIn
    omega := L.omega
    nodup := L.nodup
    seats := L.seats
    fence := L.fence
    placeB := L.placeB
    closed := P.closed
    stretch := P.stretch
    someW := L.someW
    someI := L.someI
    someO := P.someO
    apartWO := L.apartWO
    apartIO := L.apartIO
    free0 := P.free0
    oneSeat := L.oneSeat
    dataIs := P.dataIs
    planOk := P.planOk
    ownMask := P.ownMask
    twoStages := P.twoStages
    places := P.places
    oneOmega := L.oneOmega
    omegaSeat := L.omegaSeat
    mineI := L.mineI
    mineW := L.mineW
    seatsApart := L.seatsApart
    allSeats := L.allSeats
    planAt := L.planAt
    oneTable := L.oneTable
    planShapes := L.planShapes
    elderBelow := L.elderBelow
    planTreeO := P.planTreeO }

/-- Back: the part that is left. -/
theorem PlanOk₃.left (H : PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links ps r n₁ ft nΩ V Ld) :
    PlanLeft₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links ps r n₁ ft nΩ V Ld :=
  { sampled := H.sampled
    wIn := H.wIn
    iIn := H.iIn
    omega := H.omega
    nodup := H.nodup
    seats := H.seats
    fence := H.fence
    placeB := H.placeB
    someW := H.someW
    someI := H.someI
    apartWO := H.apartWO
    apartIO := H.apartIO
    oneSeat := H.oneSeat
    oneOmega := H.oneOmega
    omegaSeat := H.omegaSeat
    mineI := H.mineI
    mineW := H.mineW
    seatsApart := H.seatsApart
    allSeats := H.allSeats
    planAt := H.planAt
    oneTable := H.oneTable
    planShapes := H.planShapes
    elderBelow := H.elderBelow }

/-- Back: the part that is paid. -/
theorem PlanOk₃.paid (H : PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links ps r n₁ ft nΩ V Ld) :
    PlanPaid₃ o mk Z N c D G dB dt ms₂ Ns r nΩ :=
  { closed := H.closed
    stretch := H.stretch
    someO := H.someO
    free0 := H.free0
    dataIs := H.dataIs
    planOk := H.planOk
    ownMask := H.ownMask
    twoStages := H.twoStages
    places := H.places
    planTreeO := H.planTreeO }

end LLT25

#print axioms LLT25.PlanOk₃.of_parts
#print axioms LLT25.PlanOk₃.left
#print axioms LLT25.PlanOk₃.paid
