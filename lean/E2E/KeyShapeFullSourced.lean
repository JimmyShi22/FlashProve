-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeFullSourced.lean: THE KEY FILE's FIRST CHAIN ON ITS SHAPE, AT THE DESCRIPTION THAT THE
VERIFIER RUNS: in the goals' scope, at whatever X, N, P the key file's description at the public
files is made of (`KeySourced`, E2E/KeyPublic.lean: its field `named.run` says that this
description's decision is the key file's decision there). A join: calls. Guards on shapes: NOTHING
IS SHOWN OF ANY PROVER, and nothing of the verifier's sub-protocols.

  `six_sourced`: E2E/KeyShapeFullTies.lean's six equations. `nums_sourced`: the ranges' place is
    `nKRFull`: the library's `rangesNumbers_in_scope`: CALLED.
  **`public_first_sourced`**: E2E/KeyQuietFirst.lean's four conditions on public values
    (`PublicFirst`).
  **`first_of_sourced`**: the ranges' place; the codes at which the shape is read are the written
    ones; the two shapes of the test on the table are one; the chain has nineteen members
    (E2E/KeyThreadFits.lean's `lengths`: CALLED); the start state's shape is `T0`; the guards' run
    from it returns `T19`; the Bool that the frame's rule asks; the first chain's part of the file's
    last test accepts `T19`.

Limits.
- That there are such X, N, P at any public files is E2E/KeyPublic.lean's `key_sourced`: where the
  IOP's own test on the public files accepts.
- The first chain alone. What the guards are worth hangs on (B1) and (B2):
  E2E/KeyShapeFirstAll.lean, with its limits.
- `T19` is "what the guards return": the one thing said of it is that `firstEndS` accepts it.


-/
import E2E.KeyShapeFullInScope
import E2E.KeyQuietFirst
import E2E.KeyPublic
import E2E.KeyThreadFits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.AtFiles.Full
open OnBytes OnBytes.Params AtPublicFiles.AtFiles AtPublicFiles.KeyShape
open Lk6.AtPlan (keyFull)
open H2K.Member (nKRFull)
open VerifiableInference.Desc.Key (FirstState Source LaterPlaces)

variable {Z : VerifierAndGoals.PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

theorem six_sourced (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true) :
    Six (pubOf X) := by
  obtain ⟨X₀, m, h0, hm, hX, -, -⟩ := hs.source
  exact six_in_scope scope (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0) hm hX hs.named.plan

theorem nums_sourced (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true) :
    N = nKRFull := by
  obtain ⟨X₀, m, h0, hm, -, hN, -⟩ := hs.source
  have r2 := Johnson.AtFull.KeyBack.rangesNumbers_in_scope scope h0 hm
  rw [hN] at r2
  exact (Except.ok.inj r2).trans nums_eq

/-- **The four conditions on public values, in scope.** -/
theorem public_first_sourced (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true) :
    PublicFirst X N := by
  have h := six_sourced hs scope
  obtain rfl := nums_sourced hs scope
  have hw : (sendWAt (pubOf X) X.Y.D.1 X.Y.told.1).isSome = true := by
    show ((linMessageW (pubOf X).one.lin).map _).isSome = true
    rw [h.lin, Option.isSome_map]
    decide +kernel
  obtain ⟨bw, hbw⟩ := Option.isSome_iff_exists.1 hw
  refine ⟨bw, hbw, by decide +kernel, by decide +kernel, fun e => ?_⟩
  have hr : (H2K.JointK.rngEntry QF.one nKRFull).rounds.isEmpty = false := by decide +kernel
  have e' : (H2K.JointK.rngEntry QF.one nKRFull).rounds = [] := e
  rw [e'] at hr
  cases hr

/-- **AT THE DESCRIPTION THAT THE VERIFIER RUNS, IN SCOPE.** -/
theorem first_of_sourced (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (v : Nat → FirstState → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) :
    N = nKRFull ∧ X.chains.made.sized.key.codes = CF ∧
      X.Y.k.oneTime.lin = X.chains.made.sized.key.once.shape ∧
      (keyFileDescription X N P).first.blocksInOrder.length = 19 ∧ firstShape X CF = T0 ∧
      (Z₁W (pubOf X) CF X.Y.D.1 X.Y.told.1 N v).run 19 T0 = .ok T19 ∧
      (Z₁W (pubOf X) CF X.Y.D.1 X.Y.told.1 N v).yes T0 19 = true ∧
      firstEndS (pubOf X) T19 = true := by
  have h := six_sourced hs scope
  have hk := sized_sourced hs scope
  obtain rfl := nums_sourced hs scope
  have h0 := entries_six X nKRFull P hs.named.plan h 0 (by decide)
  have h1 := entries_six X nKRFull P hs.named.plan h 1 (by decide)
  have hc : X.Y.k.oneTime.codes = CF := h.codes
  have hl : X.Y.k.oneTime.lin = SF := h.lin
  refine ⟨rfl, by rw [hk], by rw [hk]; exact hl, (AtPublicFiles.KeyThread.lengths scope hs.named).1, ?_,
    run_six h _ _ v h0 h1, yes_six h _ _ v h0 h1, end_six h⟩
  show a₀ X.Y.k.oneTime.codes (backOf X.Y.k.oneTime.lin CF ([], #[], #[], none)) = T0
  rw [hc, hl]
  rfl

end AtPublicFiles.AtFiles.Full

#print axioms AtPublicFiles.AtFiles.Full.six_sourced
#print axioms AtPublicFiles.AtFiles.Full.nums_sourced
#print axioms AtPublicFiles.AtFiles.Full.public_first_sourced
#print axioms AtPublicFiles.AtFiles.Full.first_of_sourced
