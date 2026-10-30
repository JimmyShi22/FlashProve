--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeSharedFull.lean: THE KEY FILE's SHARED CHAIN ON SHAPES, AT THE FULL SIZE's WRITTEN
PUBLIC VALUES: THE RUN OVER ALL TWELVE SUB-PROTOCOLS RETURNS, AND AT ITS END AND THE FIRST CHAIN's
THE THIRD CHAIN's START ON SHAPES RETURNS. Definitions with code, and evaluations in Lean's kernel.
Guards on shapes at closed terms: NOTHING IS SHOWN OF ANY PROVER, and nothing of any state.

  `PF`, `QK`, `sentUF`: the later places' numbers (the library's written value), the linear claim's
    parameters at the written sized key, and what goes out with o_u.
  `gK₂`: the guard of the sub-protocol number b, b below 9: the hash build's one test and one update
    (Johnson/Desc/K14/Shape/Facts.lean: `factsB`; Run.lean: `updS`), under the mark on the statement
    (E2E/KeyShapeSharedChain.lean: `withMark`).
  `V0`: the first state's shape at a key whose sizes fit, with the mark. `V1` to `V12`: what the
    guards return, one behind the other.
  **`stepS0` to `stepS11`**: each guard returns at the term in front of it. By Lean's kernel.
  `v9_is`: the ninth term is the hash build's closed form (End.lean: `endAt`), with the mark.
  **`run₂_full`**, `yes₂_full`: so the run of E2E/KeyShapeSharedChain.lean's letters `Z₂` over the
    twelve returns `V12`.
  **`door_full`**: E2E/KeyShapeDoor.lean's `doorS` returns at the first chain's last term `T19`
    (E2E/KeyShapeAtFull.lean) and what the start reads of `V12`. `X0`: what it returns: the third
    chain's first shape at these terms.
  `early₂`: five negative tests: the end's guard in front of each proximity test, and three of the
    linear claim's guards one term early: all reject.

Limits.
- CLOSED TERMS ALONE: no tie here to the description that the verifier runs, to a state or to a
  `Thread`.
- The two proximity tests' guards are `gTest₂`: they ask fewer guards than the tests: (B2) there is
  not served by them.
- `T19` stands at a synthetic count of trees sent in front of the batching
  (E2E/KeyShapeAtFull.lean's `sentF`).


-/
import E2E.KeyShapeAtFull
import E2E.KeyShapeDoor
import Johnson.Desc.K14.Shape.End
import Johnson.HB.LLHARD.KB8.Written

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.AtFiles.Full
open OnBytes OnBytes.Params AtPublicFiles.AtFiles AtPublicFiles.KeyShape
open ProofFile.Honest
open Lk6.AtPlan (keyFull)
open VerifiableInference.Desc.Key (LaterPlaces beforeSharedPoint)
open _root_.Desc.K14 (P14 St withU)
open _root_.Desc.K14.Shape (Sh2 sh2 factsB updS upTo endAt)
open _root_.Desc.K14.Honest (keyW)

/-- The later places' numbers: the library's written value. -/
def PF : LaterPlaces := Johnson.KB8.laterPlacesFull

/-- The linear claim's parameters at the written sized key. -/
def QK : P14 :=
  { set := keyFull.set, scope := if keyFull.once.lines.oneTime then .once else .shared
    codes := keyFull.codes, S := keyFull.once.shape, item := 0
    beforePoint := beforeSharedPoint PF }

/-- What goes out with o_u. -/
def sentUF : Array OracleNotice := (withU QK.S).getD #[]

/-- **The guard of the sub-protocol number b, b below 9.** -/
def gK₂ (b : Nat) : Sh₂ → Except String Sh₂ :=
  withMark fun a =>
    if factsB QK b a then .ok (updS QK sentUF b a) else .error "a guard on the shape"

/-- The two proximity tests' guards. -/
def gU₂ : Sh₂ → Except String Sh₂ :=
  gTest₂ (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ PF.U) (·.gU) (·.firstMask)

def gO₂ : Sh₂ → Except String Sh₂ :=
  gTest₂ (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ (PF.O.getD PF.U)) (·.gOmega) (fun _ => none)

/-- What a guard returns; where it rejects: the shape in front. -/
def nxt₂ (g : Sh₂ → Except String Sh₂) (a : Sh₂) : Sh₂ := ((g a).toOption).getD a

theorem ok_nxt₂ {g : Sh₂ → Except String Sh₂} {a : Sh₂} (h : (g a).toOption.isSome = true) :
    g a = .ok (nxt₂ g a) := by
  unfold nxt₂
  cases e : g a with
  | error w => rw [e] at h; cases h
  | ok t => rfl

/-! ## The terms and the steps -/

def V0 : Sh₂ := (sh2 (_root_.Desc.K14.first QK.codes (keyW QK.par.S.fold.index)), true)

def V1 : Sh₂ := nxt₂ (gK₂ 0) V0
theorem stepS0 : gK₂ 0 V0 = .ok V1 := ok_nxt₂ (by decide +kernel)

def V2 : Sh₂ := nxt₂ (gK₂ 1) V1
theorem stepS1 : gK₂ 1 V1 = .ok V2 := ok_nxt₂ (by decide +kernel)

def V3 : Sh₂ := nxt₂ (gK₂ 2) V2
theorem stepS2 : gK₂ 2 V2 = .ok V3 := ok_nxt₂ (by decide +kernel)

def V4 : Sh₂ := nxt₂ (gK₂ 3) V3
theorem stepS3 : gK₂ 3 V3 = .ok V4 := ok_nxt₂ (by decide +kernel)

def V5 : Sh₂ := nxt₂ (gK₂ 4) V4
theorem stepS4 : gK₂ 4 V4 = .ok V5 := ok_nxt₂ (by decide +kernel)

def V6 : Sh₂ := nxt₂ (gK₂ 5) V5
theorem stepS5 : gK₂ 5 V5 = .ok V6 := ok_nxt₂ (by decide +kernel)

def V7 : Sh₂ := nxt₂ (gK₂ 6) V6
theorem stepS6 : gK₂ 6 V6 = .ok V7 := ok_nxt₂ (by decide +kernel)

def V8 : Sh₂ := nxt₂ (gK₂ 7) V7
theorem stepS7 : gK₂ 7 V7 = .ok V8 := ok_nxt₂ (by decide +kernel)

def V9 : Sh₂ := nxt₂ (gK₂ 8) V8
theorem stepS8 : gK₂ 8 V8 = .ok V9 := ok_nxt₂ (by decide +kernel)

def V10 : Sh₂ := nxt₂ gU₂ V9
theorem stepS9 : gU₂ V9 = .ok V10 := ok_nxt₂ (by decide +kernel)

def V11 : Sh₂ := nxt₂ gO₂ V10
theorem stepS10 : gO₂ V10 = .ok V11 := ok_nxt₂ (by decide +kernel)

def V12 : Sh₂ := nxt₂ gEnd₂ V11
theorem stepS11 : gEnd₂ V11 = .ok V12 := ok_nxt₂ (by decide +kernel)

/-- The ninth term is the hash build's closed form, with the mark. -/
theorem v9_is : V9 = (endAt QK sentUF (keyW QK.par.S.fold.index), true) := by decide +kernel

/-- There is a place of Omega. -/
theorem omega_full : PF.O = some (PF.O.getD PF.U) := by
  have h : PF.O.isSome = true := by decide +kernel
  cases e : PF.O with
  | none => rw [e] at h; cases h
  | some a => rfl

/-! ## The run of the letters -/

/-- **The run of the shared chain's letters over the twelve returns the last term.** -/
theorem run₂_full (v : Nat → St → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) :
    (Z₂ PF 9 gK₂ v).run 12 V0 = .ok V12 := by
  have g9 : (Z₂ PF 9 gK₂ v).g 9 = gU₂ := rfl
  have g10 : (Z₂ PF 9 gK₂ v).g 10 = gO₂ := by
    show (match PF.O with
      | some nO => gTest₂ (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) (·.gOmega) (fun _ => none)
      | none => gEnd₂) = gO₂
    rw [omega_full]
    rfl
  have g11 : (Z₂ PF 9 gK₂ v).g 11 = gEnd₂ := by
    show (match PF.O with
      | some _ => gEnd₂
      | none => gEnd₂) = gEnd₂
    rw [omega_full]
  show ((((((((((((Except.ok V0 : Except String Sh₂).bind (gK₂ 0)).bind (gK₂ 1)).bind
    (gK₂ 2)).bind (gK₂ 3)).bind (gK₂ 4)).bind (gK₂ 5)).bind (gK₂ 6)).bind (gK₂ 7)).bind
    (gK₂ 8)).bind ((Z₂ PF 9 gK₂ v).g 9)).bind ((Z₂ PF 9 gK₂ v).g 10)).bind
    ((Z₂ PF 9 gK₂ v).g 11) = _
  rw [g9, g10, g11]
  show (((((((((((gK₂ 0 V0).bind (gK₂ 1)).bind (gK₂ 2)).bind (gK₂ 3)).bind (gK₂ 4)).bind
    (gK₂ 5)).bind (gK₂ 6)).bind (gK₂ 7)).bind (gK₂ 8)).bind gU₂).bind gO₂).bind gEnd₂ = _
  rw [stepS0]
  show ((((((((((gK₂ 1 V1).bind (gK₂ 2)).bind (gK₂ 3)).bind (gK₂ 4)).bind (gK₂ 5)).bind
    (gK₂ 6)).bind (gK₂ 7)).bind (gK₂ 8)).bind gU₂).bind gO₂).bind gEnd₂ = _
  rw [stepS1]
  show (((((((((gK₂ 2 V2).bind (gK₂ 3)).bind (gK₂ 4)).bind (gK₂ 5)).bind (gK₂ 6)).bind
    (gK₂ 7)).bind (gK₂ 8)).bind gU₂).bind gO₂).bind gEnd₂ = _
  rw [stepS2]
  show ((((((((gK₂ 3 V3).bind (gK₂ 4)).bind (gK₂ 5)).bind (gK₂ 6)).bind (gK₂ 7)).bind
    (gK₂ 8)).bind gU₂).bind gO₂).bind gEnd₂ = _
  rw [stepS3]
  show (((((((gK₂ 4 V4).bind (gK₂ 5)).bind (gK₂ 6)).bind (gK₂ 7)).bind (gK₂ 8)).bind gU₂).bind
    gO₂).bind gEnd₂ = _
  rw [stepS4]
  show ((((((gK₂ 5 V5).bind (gK₂ 6)).bind (gK₂ 7)).bind (gK₂ 8)).bind gU₂).bind gO₂).bind
    gEnd₂ = _
  rw [stepS5]
  show (((((gK₂ 6 V6).bind (gK₂ 7)).bind (gK₂ 8)).bind gU₂).bind gO₂).bind gEnd₂ = _
  rw [stepS6]
  show ((((gK₂ 7 V7).bind (gK₂ 8)).bind gU₂).bind gO₂).bind gEnd₂ = _
  rw [stepS7]
  show (((gK₂ 8 V8).bind gU₂).bind gO₂).bind gEnd₂ = _
  rw [stepS8]
  show ((gU₂ V9).bind gO₂).bind gEnd₂ = _
  rw [stepS9]
  show (gO₂ V10).bind gEnd₂ = _
  rw [stepS10]
  exact stepS11

/-- The Bool that the frame's rule asks. -/
theorem yes₂_full (v : Nat → St → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) :
    (Z₂ PF 9 gK₂ v).yes V0 12 = true := by
  show ((Z₂ PF 9 gK₂ v).run 12 V0).toOption.isSome = true
  rw [run₂_full]
  rfl

/-! ## The third chain's start -/

/-- What the third chain's start on shapes returns at the two chains' last terms; where it rejects:
nothing. -/
def X0 : Option Sh₃ := (doorS CF SF T19.1 T19.2.tidy T19.2.back.door (sharedOf V12)).toOption

/-- **THE THIRD CHAIN's START ON SHAPES RETURNS AT THE TWO CHAINS' LAST TERMS.** -/
theorem door_full : X0.isSome = true := by decide +kernel

/-- **Five negative tests**: the end's guard in front of each of the two proximity tests; three of
the linear claim's guards one term early: all reject. (The like at the two proximity tests' guards
did not reduce in Lean's kernel.) -/
theorem early₂ : (gEnd₂ V9).toOption.isSome = false ∧ (gEnd₂ V10).toOption.isSome = false ∧
    (gK₂ 2 V1).toOption.isSome = false ∧ (gK₂ 5 V4).toOption.isSome = false ∧
    (gK₂ 8 V7).toOption.isSome = false :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

end AtPublicFiles.AtFiles.Full

#print axioms AtPublicFiles.AtFiles.Full.ok_nxt₂
#print axioms AtPublicFiles.AtFiles.Full.stepS0
#print axioms AtPublicFiles.AtFiles.Full.stepS1
#print axioms AtPublicFiles.AtFiles.Full.stepS2
#print axioms AtPublicFiles.AtFiles.Full.stepS3
#print axioms AtPublicFiles.AtFiles.Full.stepS4
#print axioms AtPublicFiles.AtFiles.Full.stepS5
#print axioms AtPublicFiles.AtFiles.Full.stepS6
#print axioms AtPublicFiles.AtFiles.Full.stepS7
#print axioms AtPublicFiles.AtFiles.Full.stepS8
#print axioms AtPublicFiles.AtFiles.Full.stepS9
#print axioms AtPublicFiles.AtFiles.Full.stepS10
#print axioms AtPublicFiles.AtFiles.Full.stepS11
#print axioms AtPublicFiles.AtFiles.Full.v9_is
#print axioms AtPublicFiles.AtFiles.Full.omega_full
#print axioms AtPublicFiles.AtFiles.Full.run₂_full
#print axioms AtPublicFiles.AtFiles.Full.yes₂_full
#print axioms AtPublicFiles.AtFiles.Full.door_full
#print axioms AtPublicFiles.AtFiles.Full.early₂
