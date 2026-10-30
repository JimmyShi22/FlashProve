--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeFullInScope.lean: THE KEY FILE's FIRST CHAIN ON ITS SHAPE, IN THE GOALS' SCOPE: the
start state's shape, the guards' run, the Bool that the frame's rule asks, and the first chain's
part of the file's last test: AT THE PUBLIC VALUES OF EVERY PUBLIC FILES IN SCOPE at which the two
makers return. A join: calls. Guards on shapes: NOTHING IS SHOWN OF ANY PROVER, and nothing of the
verifier's sub-protocols.

  `samples_full`, **`six_in_scope`**: E2E/KeyShapeFullTies.lean's six equations hold in scope: the
    library's `five_in_scope` (Johnson/RunOne/Law/KeyInScope.lean) and `samples_in_scope`
    (Johnson/RunOne/KeySamples.lean): CALLED.
  **`entries_six`**: E2E/KeyShapeAtFull.lean's two named premises, off the description's own test on
    public values: E2E/KeyFacesInDesc.lean's `fit_in_desc`: CALLED.
  **`first_in_scope`**: the four, where the description passes its own test on public values and the
    ranges' place is `nKRFull`.
  `nums_eq`: the library's written place of the ranges' test is `nKRFull`. By `rfl`.
  **`first_at_named`**: the four at the description that the library names in scope, with its
    written declared rounds, table of trees and places: from the scope and the two makers' returns
    alone.

Limits.
- That the two makers return at any public files is not shown here (the library has it at its
  written full-size files).
- `first_at_named` stands at the constant in the digest's place (`fixedDigest`), as the verifier's
  own description does; `six_in_scope` and `first_in_scope` hold at every digest that is handed in.
- THAT THE VERIFIER RUNS THE DESCRIPTION OF `first_at_named` IS NOT SAID HERE, and does not follow
  from its three premises: the routine behind the two makers may still reject.
  E2E/KeyShapeFullSourced.lean speaks at the description that the verifier runs.
- That the chain has nineteen members is not shown here.
- `T0` … `T19` are the terms of E2E/KeyShapeAtFull.lean: made at a synthetic value; that they are
  the run's values in scope is what is shown here.
- The first chain alone. (B1), (B2) and the frame's rule are other files'
  (E2E/KeyShapeFirstAll.lean, with its limits). Nothing here says that a sub-protocol's decision
  returns.


-/
import E2E.KeyShapeFullTies
import E2E.KeyFacesInDesc
import Johnson.RunOne.KeySamples
import Johnson.AtFull.KeyBack.KeyBackAtFixed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.AtFiles.Full
open OnBytes OnBytes.Params AtPublicFiles.AtFiles AtPublicFiles.KeyShape
open Lk6.AtPlan (keyFull)
open H2K.Member (nKRFull)
open VerifiableInference.Desc.Key (FirstState Source LaterPlaces lookupPlace lookupsOf madeAt
  sourceOf fixedDigest)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.G.OfPlan (Made)

/-! ## The six equations, in the goals' scope -/

theorem samples_full : keyFull.set.samples = 1 := by decide +kernel

/-- **IN SCOPE THE SIX EQUATIONS HOLD**: the library's `five_in_scope` and `samples_in_scope`. -/
theorem six_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : Model.Verify.Public} (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Made} {X : Source}
    {N : H2U.PlaceNums} {P : LaterPlaces} (hm : madeAt Z Zp.lay cfg = .ok m)
    (hX : sourceOf m = .ok X) (hp : (keyFileDescription X N P).planOk = true) : Six (pubOf X) := by
  obtain ⟨hset, hrg, hlin, hidx, hcd⟩ :=
    Johnson.RunOne.Law.KeyInScope.five_in_scope hZ hP hm hX hp
  exact ⟨hlin, hrg, hcd, hidx,
    (Johnson.RunOne.KeySendGood.samples_in_scope hZ hP hm hX hp).trans samples_full.symm, hset⟩

/-! ## The two premises on the lookups' places, off the description's own test on public values -/

/-- Under the six equations, so at the synthetic value's places. -/
theorem entries_six (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    (hp : (keyFileDescription X N P).planOk = true) (h : Six (pubOf X)) (i : Nat) (hi : i < 2) :
    (lookupPlace QF.set i (lookAt QF.one i)).entries.isSome = true := by
  have hl : lookupsOf X.Y.k.oneTime = lookupsOf QF.one := by
    rw [lookups_norm, norm_six h]
    rfl
  have hn : (lookupsOf QF.one).length = 2 := by decide +kernel
  have hs : X.set = QF.set := h.set
  have hx : (lookAt QF.one i, i) ∈ (lookupsOf X.Y.k.oneTime).zipIdx := by
    rw [hl, List.mem_zipIdx_iff_getElem?]
    unfold lookAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hn]; exact hi)]
    rfl
  obtain ⟨-, es, e, -⟩ := AtPublicFiles.KeyFaces.fit_in_desc X N P hp _ hx
  rw [hs] at e
  have e' : (lookupPlace QF.set i (lookAt QF.one i)).entries = some es := e
  rw [e']
  rfl

/-! ## The join -/

/-- **IN SCOPE, WHERE THE DESCRIPTION PASSES ITS OWN TEST ON THE PLAN AND THE RANGES' PLACE IS THE
WRITTEN ONE**: the start state's shape is `T0`; the first chain's guards' run from it returns `T19`;
the first chain's part of the file's last test accepts that. -/
theorem first_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : Model.Verify.Public} (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Made} {X : Source}
    {P : LaterPlaces} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (keyFileDescription X nKRFull P).planOk = true)
    (v : Nat → FirstState → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (x : (keyFileDescription X nKRFull P).XiPub) :
    (Z₁W (pubOf X) CF X.Y.D.1 X.Y.told.1 nKRFull v).sh ((keyFileDescription X nKRFull P).start₁ x) = T0 ∧
      (Z₁W (pubOf X) CF X.Y.D.1 X.Y.told.1 nKRFull v).run 19 T0 = .ok T19 ∧
      (Z₁W (pubOf X) CF X.Y.D.1 X.Y.told.1 nKRFull v).yes T0 19 = true ∧
      firstEndS (pubOf X) T19 = true := by
  have h := six_in_scope hZ hP hm hX hp
  have h0 := entries_six X nKRFull P hp h 0 (by decide)
  have h1 := entries_six X nKRFull P hp h 1 (by decide)
  exact ⟨start_six X nKRFull P h v x, run_six h _ _ v h0 h1, yes_six h _ _ v h0 h1, end_six h⟩

/-- The library's written place of the ranges' test is the one at which the run is made. -/
theorem nums_eq : Johnson.KB8.rangesNumsFull = nKRFull := rfl

/-- **AT THE DESCRIPTION THAT THE LIBRARY NAMES IN SCOPE**
(Johnson/AtFull/KeyBack/KeyBackAtFixed.lean): from the scope and the two makers' returns alone. -/
theorem first_at_named {Zp : VerifierAndGoals.PublicFiles} {o : Nat → ByteArray → ByteArray}
    {X₀ : Model.Verify.Public} {m : Made} (hZ : VerifierAndGoals.InScope Zp = true)
    (hX : VerifiableInference.PlanWritten.publicOfO o Zp.pol Zp.KL (some Zp.lay) = .ok X₀)
    (hm : madeAt X₀ Zp.lay fixedDigest = .ok m)
    (v : Nat → FirstState → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (x : (keyFileDescription (Johnson.AtFull.KeyBack.sourceKFull m) nKRFull
      Johnson.KB8.laterPlacesFull).XiPub) :
    (Z₁W (pubOf (Johnson.AtFull.KeyBack.sourceKFull m)) CF Johnson.KB8.declKeyFull.1
        Johnson.KB4.toldKeyFull.1 nKRFull v).sh
        ((keyFileDescription (Johnson.AtFull.KeyBack.sourceKFull m) nKRFull
          Johnson.KB8.laterPlacesFull).start₁ x) = T0 ∧
      (Z₁W (pubOf (Johnson.AtFull.KeyBack.sourceKFull m)) CF Johnson.KB8.declKeyFull.1
        Johnson.KB4.toldKeyFull.1 nKRFull v).run 19 T0 = .ok T19 ∧
      (Z₁W (pubOf (Johnson.AtFull.KeyBack.sourceKFull m)) CF Johnson.KB8.declKeyFull.1
        Johnson.KB4.toldKeyFull.1 nKRFull v).yes T0 19 = true ∧
      firstEndS (pubOf (Johnson.AtFull.KeyBack.sourceKFull m)) T19 = true := by
  have r1 := Johnson.AtFull.KeyBack.sourceOf_named_in_scope hZ hX hm
  have r2 := Johnson.AtFull.KeyBack.rangesNumbers_in_scope hZ hX hm
  have r3 := Johnson.AtFull.KeyBack.laterPlaces_in_scope hZ hX hm
  have hp := Johnson.KB4.key_planOk_in_scope hZ hX hm r1 r2 r3
  exact first_in_scope hZ (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO hX) hm r1 hp v x

end AtPublicFiles.AtFiles.Full

#print axioms AtPublicFiles.AtFiles.Full.samples_full
#print axioms AtPublicFiles.AtFiles.Full.six_in_scope
#print axioms AtPublicFiles.AtFiles.Full.entries_six
#print axioms AtPublicFiles.AtFiles.Full.first_in_scope
#print axioms AtPublicFiles.AtFiles.Full.nums_eq
#print axioms AtPublicFiles.AtFiles.Full.first_at_named
