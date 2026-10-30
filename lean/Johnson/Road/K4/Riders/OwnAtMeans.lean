-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/OwnAtMeans.lean: THE LINE hOwn OF `make_of_means` (Riders/MakeOfMeans.lean):
behind an accept of K4's sub-protocol the public item formsInT m 3 "own" holds of the verifier's
state, AT A MEANING WITH `K4Means`: out of the law `formsInT_own` (InT/FormsInTOwn.lean) and its
corollary at a link's readers. One statement with its proof: the equation, two equations on the
letters, two calls.

  **`hOwn_of_means`**: `K4Means Mg D` · hRd (segment m's readers are a segment's: D.Rd m =
    readersOfLink Hh l) · hruns (the map of names gives the item the caller's two runs: D.runs m 3
    "own" = [(2, "front"), (2, "back")]) · asks (at a Yes inside the promise in front: the law's own
    premises: `KeptAsks` · `InTAsks` at the first sending's seats · `StatesAt` at the two names) ⟹
    the line.

Limits. asks IS A PREMISE, WHOLE: who pays its parts stands in InT/Statement.lean's and
Total/AtKept.lean's heads (the member: one test on the public parameters, Total/PlanMember.lean; the
seat's tie: InT/SeatTie.lean; three tests on the verifier's state: nobody). hRd and hruns are
equations on letters. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on
soundness.
-/
import Johnson.Road.K4.K4Means
import Johnson.Road.K4.K4PromiseBehind
import Johnson.Road.K4.InT.FormsInTOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open Iop OnBytes OnBytes.Model
open OnBytes.Model.Layer (Pub Own)
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Desc.First.K4.Total (KeptAsks)
open OnBytes.Road.K4.InT (InTAsks StatesAt formsInT_own inT_ofLink)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Wit Claim Link K9.LinkHoles K9.statesOfLink K9.readersOfLink)
open VerifiableInference.Desc.First (S ModelPart Meaning)
open VerifiableInference.Desc.Sound (Frame Piece onQ MsgT)

variable {Xi P Tok Cl : Type} {rows cols nR kC : ℕ} {X : Verify.Public} {Fr : Frame}
  {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {D : K4Data Xi P Tok rows cols nR kC X} {Z : P}
  {links : List ModelPart} {ps : List Place} {k m : ℕ}
  {q : Piece (ckP .two) Fr S Cl (Wit (CellsK rows cols) Tok MsgT)} {par : Par}

/-- **Behind an accept of K4's sub-protocol the public item formsInT m 3 "own" holds.** -/
theorem hOwn_of_means (E : K4Means Mg D) {Hh : K9.LinkHoles} {l : Link S Claim}
    (hRd : D.Rd m = K9.readersOfLink Hh l)
    (hruns : D.runs m 3 "own" = [(2, "front"), (2, "back")])
    (asks : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∃ (P₀ : Pub) (o₀ : Own),
        KeptAsks par a.1 (behindOf seatS q a τ o G').1 P₀ o₀ ∧
        InTAsks (D.N.sent m 0) par a.1 (behindOf seatS q a τ o G').1 ∧
        StatesAt (K9.statesOfLink l) 2 par "front" (behindOf seatS q a τ o G').1 ∧
        StatesAt (K9.statesOfLink l) 2 par "back" (behindOf seatS q a τ o G').1) :
    ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' →
      Mg.pub (.formsInT m 3 "own") (Z, (behindOf seatS q a τ o G').1) = true := by
  intro a τ fo o G' ha hu y
  obtain ⟨P₀, o₀, A, I, s1, s2⟩ := asks a τ fo o G' ha hu y
  obtain ⟨h1, h2⟩ := formsInT_own (D.N.sent m 0) par a.1 _ P₀ o₀ (K9.statesOfLink l)
    (kept_of_yes y) A I s1 s2
  rw [E.formsInT, hruns, hRd]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨inT_ofLink Hh l _ 2 "front" _ (by decide) h1, inT_ofLink Hh l _ 2 "back" _ (by decide) h2⟩

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.hOwn_of_means
