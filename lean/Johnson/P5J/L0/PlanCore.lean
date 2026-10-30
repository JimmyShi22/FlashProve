-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/L0/PlanCore.lean: OF THE 23 FIELDS OF `LLT25.PlanLeft₃` (PlanLeft.lean) FIVE FOLLOW FROM
OTHERS, in the structure's own letters: omega, apartWO, apartIO, allSeats and two of seatsApart's
three clauses follow from omegaSeat, elderBelow, "the own seats are the first table's" (V.index =
N₁.index, V.w = N₁.w) and nΩ < D.t₂. `PlanCore₃`: the 14 fields that stay, each under its own name and in
its own text (copied by program), and `indexNeW` (seatsApart's first clause). `PlanLeft₃.of_core`:
`PlanLeft₃` from `PlanCore₃`, these four small premises and the four fields elderBelow, sampled, wIn,
iIn (which other files pay at a head). One structure, two theorems.
CALLED: `P2R0.omega_seat_two` (Omega's seat is (t + nΩ, 0), from omegaSeat and
two inequations); `LLT25.mem_mineOf`.
Nothing on soundness. `PlanCore₃` is shown at no letters.
STAY: nodup · seats · fence · placeB · someW · someI · oneSeat · oneOmega · omegaSeat · mineI · mineW · planAt · oneTable · planShapes · indexNeW.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.L0.PlanLeft
import Johnson.P2R0R.OmegaOfSeats

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

/-- **WHAT STAYS, BY NAME.** -/
structure PlanCore₃ : Prop where
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
  /-- The first clause of seatsApart: the two elder seats are apart. -/
  indexNeW : V.index ≠ V.w

variable {o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links ps r n₁ ft nΩ V Ld}

/-- A seat in a tree below t is not (t + n, 0). -/
theorem ne_of_below {x : ℕ × ℕ} {t n : ℕ} (h : x.1 < t) : x ≠ (t + n, 0) := by
  rintro rfl
  exact absurd h (by simp)

/-- **`PlanLeft₃` from what stays.** -/
theorem PlanLeft₃.of_core (C : PlanCore₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns r n₁ ft nΩ V Ld)
    (hI : V.index = N₁.index) (hW : V.w = N₁.w) (hn : nΩ < D.t₂)
    (elderBelow : V.index.1 < D.t₁ ∧ V.w.1 < D.t₁)
    (sampled : sampledBelow (D.t₁ + D.t₂) N₁ ((openSets links ps (start links))[ps.length]?.getD []) =
      true)
    (wIn : N₁.w ∈ sampledIn N₁ ((openSets links ps (start links))[ps.length]?.getD []))
    (iIn : N₁.index ∈ sampledIn N₁ ((openSets links ps (start links))[ps.length]?.getD [])) :
    PlanLeft₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links ps r n₁ ft nΩ V Ld := by
  have aI : N₁.index ≠ (D.t₁ + nΩ, 0) := hI ▸ ne_of_below elderBelow.1
  have aW : N₁.w ≠ (D.t₁ + nΩ, 0) := hW ▸ ne_of_below elderBelow.2
  obtain ⟨x, hx, sx, -⟩ := C.omegaSeat
  have eO : Ns.tenant .oOmega = (D.t₁ + nΩ, 0) := P2R0.omega_seat_two ⟨x, hx, sx⟩ aI aW
  exact
    { nodup := C.nodup
      seats := C.seats
      fence := C.fence
      placeB := C.placeB
      someW := C.someW
      someI := C.someI
      oneSeat := C.oneSeat
      oneOmega := C.oneOmega
      omegaSeat := C.omegaSeat
      mineI := C.mineI
      mineW := C.mineW
      planAt := C.planAt
      oneTable := C.oneTable
      planShapes := C.planShapes
      elderBelow := elderBelow
      sampled := sampled
      wIn := wIn
      iIn := iIn
      omega := by
        rw [eO]
        exact Nat.add_lt_add_left hn _
      apartWO := eO ▸ aW
      apartIO := eO ▸ aI
      seatsApart := ⟨C.indexNeW, hI ▸ aI, hW ▸ aW⟩
      allSeats := fun z hz => by
        rcases mem_mineOf.1 hz with ⟨-, h | h⟩ | ⟨-, h⟩
        · exact .inr (.inl ((show seatOf z = N₁.w from h).trans hW.symm))
        · exact .inl ((show seatOf z = N₁.index from h).trans hI.symm)
        · exact .inr (.inr ((show seatOf z = Ns.tenant .oOmega from h).trans eO)) }

end LLT25

#print axioms LLT25.ne_of_below
#print axioms LLT25.PlanLeft₃.of_core
