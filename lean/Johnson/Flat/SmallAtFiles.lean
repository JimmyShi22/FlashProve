-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/SmallAtFiles.lean: the data of the key file's and the proof file's protocols at the
small size, as a value made of three public files; and the makers' tests on it as one test.

The small twin of bigReq and guardsAtB (Johnson/Flat/ThreeAtFiles.lean). Z are
three public files (K.Pub, OnBytes/K/Served.lean: in the order parameter file, layout file, scale
file); p is the answer of the program's planner at Z (planOf, OnBytes/Flat/BigAt.lean). The
instances are the requests that the program's reader takes at the small example's sizes (ReqAt
sizesSmall, Johnson/Flat/ClaimsTrue.lean; sizesSmall, Johnson/Flat/ClaimsSizes.lean).

Main definitions and theorems.
  sizesSmall_V_pos: the small example's vocabulary has a token.
  recZeroSmall: the record of zeros with the factor 1.
  firstReqSmall: tokens 0, the last position alone covered, the reply 0, as a request.
  withoutReplySmall x: the request with the reply 0.
  bigReqSmall p: the two files' chains and the depth of a batch's tree are p's (bigAt); the first
    chain's block at a request is the program's own Proof.firstBlock at the links and the reply of
    that request (pubOf p sizesSmall, Johnson/Flat/PubOf.lean); the dry runs are made at
    recZeroSmall and firstReqSmall; what of a request is fixed first is the request with the reply
    0.
  atPlan_bigReqSmall: it is at the plan of Z.
  guardsSmallAtB Z, guardsSmall_of_test, guardsSmall_at: "the makers' tests on the dry runs pass"
    (GuardsPassSmall, Johnson/Flat/WireAt.lean) at bigReqSmall of the planner's answer at Z, as one
    test with its theorem.

Limits: definitions, and what follows by unfolding. No file is evaluated here: that the planner
returns at the small example's three files and that guardsSmallAtB says true there are evaluations
that are owed; where it says false, either the planner refuses Z and there are no data, or a test
fails: then that file's data are those of three empty lists and that file's decision says no at
every record and all views (Johnson/Flat/WireAt.lean). Whether guardsSmallAtB has code is not shown
here: in a noncomputable section Lean marks silently what it cannot compile. That bigReqSmall p is
bigOf of a record of public values, as its big twin is, is not typed. NO STATEMENT ON SOUNDNESS
STANDS HERE: at the small size the library has no relation with the cost ledger, and the small
example's scale words are refused by the library's intervals (Johnson/Flat/ScalesOf.lean). The sizes
are typed, not read off Z: at a Z with another window the links' block fails at every request. That
the data do not hang on the two records: Johnson/Flat/DataAtZero.lean [not in this library], under
three equations on the tables' shape. That the dry runs at firstReqSmall give the rounds of every
request is not shown here.

-/
import Johnson.Flat.TwoAtPlan
import Johnson.Flat.PubOf
import Johnson.Flat.ClaimsSizes
import Johnson.Flat.ClaimsTrue

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Flat OnBytes.Slice
open Inst.Model

/-- The small example's vocabulary has a token. -/
theorem sizesSmall_V_pos : 0 < sizesSmall.V := by decide

/-- The record of zeros with the factor 1. -/
def recZeroSmall : RecSmall := (fun _ => (fun _ => 0, ⟨1, one_ne_zero⟩), fun _ => 0)

/-- The instance at which the dry runs are made, as a request. -/
def firstReqSmall : ReqAt sizesSmall :=
  ⟨firstInstance sizesSmall sizesSmall_V_pos, by decide, fun h => absurd h (by decide)⟩

/-- A request with the reply 0. -/
def withoutReplySmall (x : ReqAt sizesSmall) : ReqAt sizesSmall :=
  ⟨withoutReply sizesSmall_V_pos x.val, x.property.1, fun _ => rfl⟩

/-- **The data of the two big files' protocols at the small size, made of a planner's answer.** -/
def bigReqSmall (p : Model.Verify.Planned) : FilesParameters (ReqAt sizesSmall) RecSmall :=
  bigAt p (fun x => (pubOf p sizesSmall sizesSmall_V_pos).block x.val) recZeroSmall
    (firstReqSmall, recZeroSmall) withoutReplySmall

/-- It is at the plan of the three public files. -/
theorem atPlan_bigReqSmall {Z : K.Pub} {p : Model.Verify.Planned} (h : planOf Z = .ok p) :
    AtPlan Z (bigReqSmall p) :=
  atPlan_bigAt h _ _ _ _

/-- A run can decide whether the makers' tests pass. -/
instance decGuardsPassSmall {X : Type} (G : FilesParameters X RecSmall) : Decidable (GuardsPassSmall G) := by
  unfold GuardsPassSmall
  infer_instance

/-- "The makers' tests on the dry runs pass" at the data made of three public files, as one test. -/
def guardsSmallAtB (Z : K.Pub) : Bool :=
  match planOf Z with
  | .ok p => decide (GuardsPassSmall (bigReqSmall p))
  | .error _ => false

/-- **If the test says true, the planner returns at Z and the makers' tests pass at its data.** -/
theorem guardsSmall_of_test {Z : K.Pub} (t : guardsSmallAtB Z = true) :
    ∃ p, planOf Z = .ok p ∧ GuardsPassSmall (bigReqSmall p) := by
  unfold guardsSmallAtB at t
  cases h : planOf Z with
  | error e =>
    rw [h] at t
    cases t
  | ok p =>
    rw [h] at t
    exact ⟨p, rfl, of_decide_eq_true t⟩

/-- The same at a named answer of the planner. -/
theorem guardsSmall_at {Z : K.Pub} {p : Model.Verify.Planned} (hp : planOf Z = .ok p)
    (t : guardsSmallAtB Z = true) : GuardsPassSmall (bigReqSmall p) := by
  obtain ⟨p', h', g⟩ := guardsSmall_of_test t
  obtain rfl : p' = p := Except.ok.inj (h'.symm.trans hp)
  exact g

end VerifiableInference.OnPublicFiles
