-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeFullTies.lean: WHAT THE KEY FILE's FIRST CHAIN's GUARDS ON THE SHAPE READ OF THE PUBLIC
VALUES, AND SO: THE RUN OF E2E/KeyShapeAtFull.lean AT EVERY PUBLIC VALUE THAT MEETS SIX EQUATIONS.
Statements and proofs. Guards on shapes: NOTHING IS SHOWN OF ANY PROVER, and nothing of the
verifier's sub-protocols.

What for. E2E/KeyShapeAtFull.lean runs the nineteen guards at a synthetic value `QF` and at guessed
lists of groups told. No key file's public values are `QF`: the parameter bytes' own fields in it
are empty. Two laws make its theorems usable.

  `gIdx_free`, `gMsg_free`, `gSendW_free`, `gBatt_free`, **`gAll₁_free`**: NO GUARD READS THE GROUPS
    TOLD, OR THE NUMBER OF TREES SENT IN FRONT OF THE BATCHING: the guards are the same at all
    declared rounds and at whatever is told of the trees. By `rfl`.
  `normOne`; `gIdx_norm` … `lookups_norm`, **`gAll₁_norm`**: the guards read no field of the
    one-time chain's public values outside five: the shape of the test on the table, the ranges, the
    codes, the index-mask message, the plan's number of answers to an OOD sample. By `rfl`.
  **`Six`**: the six equations: these five and the setting are the written sizes'. `six_QF`: a
    member. `norm_six`.
  **`gAll₁_six`**: under them the guards are E2E/KeyShapeAtFull.lean's nineteen.
  **`run_six`**: THE RUN's VALUE: from `T0` the nineteen return `T19`. **`yes_six`**: the Bool that
    the frame's rule asks.
  **`end_six`**: the first chain's part of the file's last test accepts `T19`. **`start_six`**: the
    start state's shape is `T0`.

Limits.
- That any public files meet the six equations is not shown here.
- `run_six` and `yes_six` keep E2E/KeyShapeAtFull.lean's two named premises (`entries.isSome` at
  each lookup's place), and stand at the ranges' place `nKRFull` alone.
- "Reads no field outside" is said of the guards on the shape, not of the sub-protocols' decisions,
  nor of the reader `sh₁B`.


-/
import E2E.KeyShapeAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.AtFiles.Full
open OnBytes OnBytes.Params AtPublicFiles.AtFiles AtPublicFiles.KeyShape
open Lk6.AtPlan (keyFull keyX)
open H2K.Member (nKRFull)
open ProofFile.Honest (Shape)
open VerifiableInference.Desc.Key (FirstState pieces lookupPlace lookupsOf groupsTold rootsBefore
  rootsAt Pieces)

/-! ## No guard reads the groups told, or the number of trees sent -/

theorem gIdx_free (Q : Pub1) (N : Pieces) (g g' : List (List Nat)) :
    gIdx (Bk := BackSh) Q N g = gIdx Q N g' := rfl

theorem gMsg_free (Q : Pub1) (N : Pieces) (g g' : List (List Nat)) :
    gMsg (Bk := BackSh) Q N g = gMsg Q N g' := rfl

theorem gSendW_free (Q : Pub1) (N : Pieces) (g g' : List (List Nat)) :
    gSendW Q N g = gSendW Q N g' := rfl

theorem gBatt_free (Q : Pub1) (cs : Codes) (N : Pieces) (n n' : Nat) :
    gBatt Q cs N n = gBatt Q cs N n' := rfl

/-- **The first chain's guards do not hang on the declared rounds or on what is told of the trees.**
-/
theorem gAll₁_free (Q : Pub1) (cs : Codes) (D D' : List Fmt.DeclaredRound) (told told' : List ProofFile.Root)
    (N : H2U.PlaceNums) : gAll₁ Q cs D told N = gAll₁ Q cs D' told' N := by
  unfold gAll₁
  rw [gIdx_free Q pieces _ (groupsTold told' 0 (rootsAt D' 0)),
    gMsg_free Q pieces _ (groupsTold told' (rootsBefore D' 2) (rootsAt D' 2)),
    gBatt_free Q cs pieces _ (sentAt D'), gSendW_free Q pieces _ (groupsW D' told')]

/-! ## What the guards read of the one-time chain's public values -/

/-- The synthetic value with five fields of one laid in. -/
def normOne (one : OneTime) : OneTime :=
  { oneF with
    given := { oneF.given with plan := { oneF.given.plan with samples := one.given.plan.samples } }
    indexMasks := one.indexMasks, ranges := one.ranges, codes := one.codes, lin := one.lin }

theorem gIdx_norm (one : OneTime) (set : Setting) (N : Pieces) (g : List (List Nat)) :
    gIdx (Bk := BackSh) ⟨one, set⟩ N g = gIdx ⟨normOne one, set⟩ N g := rfl

theorem gMsg_norm (one : OneTime) (set : Setting) (N : Pieces) (g : List (List Nat)) :
    gMsg (Bk := BackSh) ⟨one, set⟩ N g = gMsg ⟨normOne one, set⟩ N g := rfl

theorem gLink_norm (one : OneTime) (set : Setting) (i : Nat) :
    gLink (Bk := BackSh) ⟨one, set⟩ i = gLink ⟨normOne one, set⟩ i := rfl

theorem gLayRows_norm (one : OneTime) (set : Setting) :
    gLayRows (Bk := BackSh) ⟨one, set⟩ = gLayRows ⟨normOne one, set⟩ := rfl

theorem gBatt_norm (one : OneTime) (set : Setting) (cs : Codes) (N : Pieces) (n : Nat) :
    gBatt ⟨one, set⟩ cs N n = gBatt ⟨normOne one, set⟩ cs N n := rfl

theorem gSendW_norm (one : OneTime) (set : Setting) (N : Pieces) (g : List (List Nat)) :
    gSendW ⟨one, set⟩ N g = gSendW ⟨normOne one, set⟩ N g := rfl

theorem lookups_norm (one : OneTime) : lookupsOf one = lookupsOf (normOne one) := rfl

/-- **The first chain's guards read no field of the one-time chain's public values outside these
five**: they cannot tell a value from the synthetic one with its five fields laid in. -/
theorem gAll₁_norm (one : OneTime) (set : Setting) (cs : Codes) (D : List Fmt.DeclaredRound)
    (told : List ProofFile.Root) (N : H2U.PlaceNums) :
    gAll₁ ⟨one, set⟩ cs D told N = gAll₁ ⟨normOne one, set⟩ cs D told N := rfl

/-- **The six equations**: what of the public values the guards read is the written sizes'. -/
structure Six (Q : Pub1) : Prop where
  lin : Q.one.lin = SF
  ranges : Q.one.ranges = keyX
  codes : Q.one.codes = CF
  indexMasks : Q.one.indexMasks = keyFull.once.input
  samples : Q.one.given.plan.samples = keyFull.set.samples
  set : Q.set = keyFull.set

/-- A member. -/
theorem six_QF : Six QF := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem norm_six {Q : Pub1} (h : Six Q) : normOne Q.one = oneF := by
  unfold normOne
  rw [h.lin, h.ranges, h.codes, h.indexMasks, h.samples]
  rfl

/-- **Under the six equations the first chain's guards are the nineteen**, at whatever declared
rounds and whatever is told of the trees. -/
theorem gAll₁_six {Q : Pub1} (h : Six Q) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root) :
    gAll₁ Q CF D told nKRFull = gsF := by
  have e0 : Q = ⟨Q.one, Q.set⟩ := rfl
  have hl : (lookupsOf QF.one).length = 2 := by decide +kernel
  rw [e0, gAll₁_norm, norm_six h, h.set]
  show gAll₁ QF CF D told nKRFull = gsF
  unfold gAll₁ gsF g0 g1
  rw [gIdx_free QF pieces _ [[]], gMsg_free QF pieces _ [[], []],
    gBatt_free QF CF pieces _ sentF, gSendW_free QF pieces _ [[], []],
    flat_range (fun i => gLink QF i) (lookupsOf QF.one) 0, hl]
  rfl

/-! ## The run's value, the Bool, the end -/

section
variable {Q : Pub1} (h : Six Q) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
  (v : Nat → FirstState → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
  (h0 : (lookupPlace QF.set 0 (lookAt QF.one 0)).entries.isSome = true)
  (h1 : (lookupPlace QF.set 1 (lookAt QF.one 1)).entries.isSome = true)
include h h0 h1

/-- **THE RUN's VALUE**: under the six equations, at whatever D, told and v. -/
theorem run_six : (Z₁W Q CF D told nKRFull v).run 19 T0 = .ok T19 := by
  unfold Z₁W
  rw [gAll₁_six h]
  show (ZL (sh₁B Q CF) gsF v).run gsF.length T0 = _
  rw [run_runL, run_full h0 h1]
  rfl

/-- **The Bool that the frame's rule asks.** -/
theorem yes_six : (Z₁W Q CF D told nKRFull v).yes T0 19 = true := by
  show ((Z₁W Q CF D told nKRFull v).run 19 T0).toOption.isSome = true
  rw [run_six h D told v h0 h1]
  rfl

end

/-- The first chain's part of the file's last test, under the six equations. -/
theorem end_six {Q : Pub1} (h : Six Q) : firstEndS Q T19 = true := by
  have e : firstEndS Q T19 = firstEndS QF T19 := by
    have e0 : Q = ⟨Q.one, Q.set⟩ := rfl
    have e1 : firstEndS ⟨Q.one, Q.set⟩ T19 = firstEndS ⟨normOne Q.one, Q.set⟩ T19 := rfl
    rw [e0, e1, norm_six h, h.set]
    rfl
  rw [e]
  exact end_full

/-- The start state's shape is the first term, under two of the six. -/
theorem start_six (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
    (P : VerifiableInference.Desc.Key.LaterPlaces) (h : Six (pubOf X))
    (v : Nat → FirstState → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (x : (keyFileDescription X N P).XiPub) :
    (Z₁W (pubOf X) CF X.Y.D.1 X.Y.told.1 N v).sh ((keyFileDescription X N P).start₁ x) = T0 := by
  rw [start₁_shape]
  have h3 : X.Y.k.oneTime.codes = CF := h.codes
  have h1 : X.Y.k.oneTime.lin = SF := h.lin
  rw [h3, h1]
  rfl

end AtPublicFiles.AtFiles.Full

#print axioms AtPublicFiles.AtFiles.Full.gIdx_free
#print axioms AtPublicFiles.AtFiles.Full.gMsg_free
#print axioms AtPublicFiles.AtFiles.Full.gSendW_free
#print axioms AtPublicFiles.AtFiles.Full.gBatt_free
#print axioms AtPublicFiles.AtFiles.Full.gAll₁_free
#print axioms AtPublicFiles.AtFiles.Full.gIdx_norm
#print axioms AtPublicFiles.AtFiles.Full.gMsg_norm
#print axioms AtPublicFiles.AtFiles.Full.gLink_norm
#print axioms AtPublicFiles.AtFiles.Full.gLayRows_norm
#print axioms AtPublicFiles.AtFiles.Full.gBatt_norm
#print axioms AtPublicFiles.AtFiles.Full.gSendW_norm
#print axioms AtPublicFiles.AtFiles.Full.lookups_norm
#print axioms AtPublicFiles.AtFiles.Full.gAll₁_norm
#print axioms AtPublicFiles.AtFiles.Full.six_QF
#print axioms AtPublicFiles.AtFiles.Full.norm_six
#print axioms AtPublicFiles.AtFiles.Full.gAll₁_six
#print axioms AtPublicFiles.AtFiles.Full.run_six
#print axioms AtPublicFiles.AtFiles.Full.yes_six
#print axioms AtPublicFiles.AtFiles.Full.end_six
#print axioms AtPublicFiles.AtFiles.Full.start_six
