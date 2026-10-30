-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/RunsPlanes.lean: CONDITIONAL: THE RUN OF CLAIMS "planes" OF THE
LOOKUP ON THE CALLS AT AN ATTENTION LINK, ON THE FIRST CHAIN's SHAPE: THE CALLER's TWO READERS ON
SHAPES, AND THAT THEY AGREE. The law is not this folder's (planesLaw,
Johnson/Desc/ProofFile/Honest/K3/Shape/ClaimPlanes.lean), general in a letter readersG for the
caller's readers on shapes, under the premise ReadersAgree, which it leaves to the calling kind. At
an attention link the caller is the kind "an attention segment's own rounds" (K5): its readers are
readersOfO A (Johnson/Desc/First/Att/SeatO.lean, Guest.lean). Definitions, and statements with their
proofs.

Main names:
  `atSh`, `readersSh`   the three readers' calls at an input of the runs, each form's shape
  `k5ReadersG A`   **the caller's readers on shapes**: these calls AT THE BLANK OF THE SHAPE, behind
    the one Bool of the tables (tabsGC, Johnson/Desc/K5/Honest/Law/TabsChain.lean)
  `at_sh`   two inputs that meet ShIn, at one place: both readers refuse, or forms of one shape
  `places_one`   the three tables on the lookup's matrix lie at one place in both inputs: by the
    library's starts_one (Johnson/Desc/First/Att/Claims/SameTabs.lean)
  `readers_agree`   **the four runs' one premise on values (preK5) gives ReadersAgree lm (readersOfO
    A) (k5ReadersG A) s, at every lm**
  `planesLawA A lm`   `planesLaw` at these letters
  `planesA_pre`   its premise, from preK5

The pattern: readersAgree_head (Johnson/Desc/ProofFile/Honest/K3/Shape/ClaimPlanesHead.lean): the
sister at the output head's caller.
Limits. `readers_agree` IS CONDITIONAL on preK5 A n s. THE LAW IS GENERAL IN lm: that the
description's run at an attention link has the place's own lm is not said here. k5ReadersG RUNS THE
READERS AT ZEROS: whoever evaluates it at the full size pays that. The one Bool is sufficient, not
shown to be necessary: where it says no, k5ReadersG refuses and the law says nothing. No theorem
here says that k5ReadersG or the run on shapes returns anywhere, nor that the premise holds
anywhere. Shapes alone: nothing on a claim's worth.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K3.Shape.ClaimPlanes
import Johnson.Desc.K5.Honest.Law.RunsLaw
import Johnson.Desc.First.Att.Claims.SameTabs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc (First.S First.AttOwn)
open VerifiableInference.Desc.K9.Shape (RunLaw)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Heard)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh AffSh affSh heard5Sh heardAll ledSh)
open ProofFile.Honest.K3.Shape (ReadersSh ReadersAgree planesLaw)
open K5Law (OptRel)

/-! ## 1 The readers on shapes -/

/-- One reader's call at an input of the runs: the form's shape. -/
def atSh (x : P.Runs.In × Nat) (place col : Nat) : Option AffSh :=
  ((P.Runs.gather x.2 (P.Runs.u3at x.1 place col)).map (·.1)).map affSh

/-- The caller's two readers at an input of the runs, on shapes: the text of readersOfK
(Johnson/Desc/First/Att/Guest.lean), each form's shape. -/
def readersSh (x : P.Runs.In × Nat) : ReadersSh :=
  (fun e col => atSh x (if e == 0 then x.1.t.tBit0 else x.1.t.tBit1) col,
    fun col => atSh x x.1.t.tPin col)

/-- **THE CALLER's READERS ON SHAPES.** -/
def k5ReadersG (A : Attention.Plan) (a : ChainSh) : Option ReadersSh :=
  if tabsGC A a then (inBlank A a).map readersSh else none

/-! ## 2 They agree -/

/-- Two inputs that meet ShIn, with one number of columns, at one place and column: both readers
refuse, or they return forms of one shape. -/
theorem at_sh {x x' : P.Runs.In × Nat} (S : ShIn x.1 x'.1) (eK : x.2 = x'.2) (place col : Nat) :
    atSh x place col = atSh x' place col := by
  have r := gather_sh (sh_u3at (K := x.2) S place col)
  unfold atSh
  rw [← eK]
  cases h1 : P.Runs.gather x.2 (P.Runs.u3at x.1 place col) with
  | none =>
    cases h2 : P.Runs.gather x.2 (P.Runs.u3at x'.1 place col) with
    | none => rfl
    | some v' =>
      rw [h1, h2] at r
      exact r.elim
  | some v =>
    cases h2 : P.Runs.gather x.2 (P.Runs.u3at x'.1 place col) with
    | none =>
      rw [h1, h2] at r
      exact r.elim
    | some v' =>
      rw [h1, h2] at r
      exact congrArg some r.1

/-- **The three tables on the lookup's matrix lie at one place in both inputs.** CONDITIONAL on both
inputs' return. -/
theorem places_one {c : P.ParC} {gl gl' : Forest.Heard} {h h' : Heard} {F F' : Fork}
    {x x' : P.Runs.In × Nat} (S : ShIn x.1 x'.1) (hx : K5Law.inAt c gl h F = some x)
    (hx' : K5Law.inAt c gl' h' F' = some x') :
    x.1.t.tBit0 = x'.1.t.tBit0 ∧ x.1.t.tBit1 = x'.1.t.tBit1 ∧ x.1.t.tPin = x'.1.t.tPin := by
  obtain ⟨p, t, _, ht, _, e⟩ := inAt_holds hx
  obtain ⟨p', t', _, ht', _, e'⟩ := inAt_holds hx'
  have hs : p.scores.size = p'.scores.size := by
    have l := S.scores.length_eq
    rw [e, e'] at l
    simpa using l
  obtain ⟨T, _⟩ := K5Law.starts_one hs ht ht'
  rw [e, e']
  exact ⟨T.tBit0, T.tBit1, T.tPin⟩

/-- The caller's readers at a state's parts. -/
theorem readersO_at (A : Attention.Plan) {s : First.S} {a : First.AttOwn} {h : Heard}
    {gl : Forest.Heard} (hh : s.here = .att a) (h5 : a.heard5 = some h) (hg : a.g = some gl) :
    P.readersOfO A s = (K5Law.inAt (P.parCOf A) gl h a.F).map fun x =>
      let at_ (place col : Nat) : Option Aff :=
        (P.Runs.gather x.2 (P.Runs.u3at x.1 place col)).map (·.1)
      (fun e col => at_ (if e == 0 then x.1.t.tBit0 else x.1.t.tBit1) col,
        fun col => at_ x.1.t.tPin col) := by
  unfold P.readersOfO P.readersOfK
  rw [inOf_at hh h5 hg]

/-- **THE CALLER's READERS AGREE WITH THE READERS ON SHAPES**, at every column and every lm.
CONDITIONAL on the four runs' one premise on values. -/
theorem readers_agree (A : Attention.Plan) (lm n : Nat) {s : First.S} (hp : preK5 A n s) :
    ReadersAgree lm (P.readersOfO A) (k5ReadersG A) s := by
  intro q hq
  unfold k5ReadersG at hq
  split at hq
  · rename_i hG
    obtain ⟨a, h, gl, hh, h5, hg, hT, eB⟩ := front_of A hG
    rw [eB] at hq
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.1 hq
    have hV : valsT A gl h a.F = true := by
      rw [← vals_at A hh h5 hg]
      exact hp
    obtain ⟨x, hx⟩ := real_in A hT hV hx'
    obtain ⟨S, eK⟩ := blank_sh hx hx'
    obtain ⟨b0, b1, bp⟩ := places_one S hx hx'
    refine ⟨_, by rw [readersO_at A hh h5 hg, hx]; rfl, fun col _ => ⟨fun e _ => ?_, ?_⟩⟩
    · show atSh x (if e == 0 then x.1.t.tBit0 else x.1.t.tBit1) col =
        atSh x' (if e == 0 then x'.1.t.tBit0 else x'.1.t.tBit1) col
      rw [b0, b1]
      exact at_sh S eK _ _
    · show atSh x x.1.t.tPin col = atSh x' x'.1.t.tPin col
      rw [bp]
      exact at_sh S eK _ _
  · cases hq

/-! ## 3 The law at these letters -/

/-- **`planesLaw`, the law of the run "planes", at the attention link's letters.** -/
def planesLawA (A : Attention.Plan) (lm : Nat) :
    RunLaw (VerifiableInference.Desc.K3.planesRun
      (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm) lm (P.readersOfO A)) :=
  planesLaw lm (P.readersOfO A) (k5ReadersG A)

/-- **Its premise, from the four runs' one premise on values.** -/
theorem planesA_pre (A : Attention.Plan) (lm n : Nat) {s : First.S} (hp : preK5 A n s) :
    (planesLawA A lm).pre n s :=
  readers_agree A lm n hp

end H2K5.Honest

#print axioms H2K5.Honest.at_sh
#print axioms H2K5.Honest.places_one
#print axioms H2K5.Honest.readersO_at
#print axioms H2K5.Honest.readers_agree
#print axioms H2K5.Honest.planesLawA
#print axioms H2K5.Honest.planesA_pre
