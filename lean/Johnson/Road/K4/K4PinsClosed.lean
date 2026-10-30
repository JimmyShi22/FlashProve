-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsClosed.lean: THE THREE TESTS OF `K4PinsTests`
(Johnson/Road/K4/K4PinsLaterScope.lean) THAT ARE ASKED "AT EVERY PLACE WITH THE SEGMENT's NUMBER AS
ITS LINK" ARE ONE TEST EACH: of the place they read the link alone (and the third its number of
slots, which the premise names). One Lean structure and nine theorems; nothing is evaluated.

  `maskPlanB_at`, `maskEllP_atLink`, `arraysPlanB_at`: at a place whose link is l, at any radii and
    cells, each is itself at `pin0 D (seat l false) l` (Johnson/Road/K4/K4PinsAnyRad.lean).
    `arrayPlanB_pin0`, `arraysPlanB_pin0`: the step on the radii for the arrays.
  `K4PinsClosed Dm Ew k g par`: five tests: `maskFitsB` and `indexTieB` as `K4PinsTests` has them;
    `maskPlanB`, `arraysPlanB` and "the number of slots is at most the mask row's length" at `pin0`.
  **`tests_of_closed`**: `firstFastB Z g = true` and `K4PinsClosed` give `K4PinsTests`.
  `maskPlanB_free`, `arrayArm_free`, `maskEllP_free`: what the tests at `pin0` do not read of the
    plan's letters: the built segments' lists of names; the ledgers' looks: each by rfl, at letters.

OBJECT: the tests' texts. USER: Johnson/Road/K4/K4PinsPaid.lean.

Limits. K04_law IS NOT PROVED BY THIS. `K4PinsClosed` IS A PREMISE: no test is shown to accept here.

-/
import Johnson.Road.K4.K4PinsLaterScope
import Johnson.Road.K4.K4PinsAnyRad
import Johnson.Desc.First.SentTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes
open OnBytes.Model (HTailF2)
open OnBytes.Model.Verify (Public)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc.First (flatPlacesOf)
open VerifiableInference.Desc.First.FillSent (SentData sentDataOf TreeLook)
open VerifiableInference.Desc.First.Look (Place Sent szOf)
open VerifiableInference.Desc.Sound
open Johnson.Desc.First.Walk.Tied (rowsBefore)
open OnBytes.Road.K4.Rec (RecPlan maskFitsB recPlanOf maskPlanB arrayPlanB arraysPlanB maskEllP)
open Inst.Model.Layout (kRef hRef)

/-! ## At a place -/

section
variable {C : Type} (D : Sent) (rad : OnBytes.OracleShape → ℕ) (i : ℕ) (f : ℕ → ℕ × ℕ)
  (rc : C → ℕ → ℕ → Cb.Gl.E) (posI : ℕ → Bool × ℕ × ℕ) (own : List (ℕ × ℕ)) (R : RecPlan)
  (n m : ℕ)

/-- The test at an array at any radii and cells is the test at `pin0`. -/
theorem arrayPlanB_pin0 (T I K : ℕ) :
    arrayPlanB (⟨D, rad, i, fun j => f j.val, rc, posI⟩ : PinPlan C) own R n m T I K =
      arrayPlanB (pin0 D f i) own R n m T I K :=
  (arrayPlanB_arm D rad i f rc posI own R n m T I K).trans
    ((elim_congr _ false fun bn => arrayArm_rad D rad (fun _ => 0) i f own R n m I K bn).trans
      (arrayPlanB_arm D (fun _ => 0) i f (fun (e : Empty) _ _ => e.elim) (fun _ => (false, 0, 0))
        own R n m T I K).symm)

/-- So is the walk over the matrices. -/
theorem arraysPlanB_pin0 (tl : HTailF2) :
    arraysPlanB (⟨D, rad, i, fun j => f j.val, rc, posI⟩ : PinPlan C) tl own R n m =
      arraysPlanB (pin0 D f i) tl own R n m := by
  unfold arraysPlanB
  exact congrArg (fun p => (List.finRange (szOf tl).NM).all p)
    (funext fun μ => arrayPlanB_pin0 D rad i f rc posI own R n m _ _ _)

end

section
variable {C : Type} (xL : Place) (D : Sent) (rad : OnBytes.OracleShape → ℕ)
  (seat : ℕ → Bool → ℕ → ℕ × ℕ) (rc : C → ℕ → ℕ → Cb.Gl.E) (posI : ℕ → Bool × ℕ × ℕ) {l : ℕ}
  (hl : xL.link = l)
include hl

theorem maskPlanB_at (own : List (ℕ × ℕ)) (R : RecPlan) (n m : ℕ) :
    maskPlanB (planAt xL D rad (fun j => seat xL.link false j.1) rc posI) own R n m =
      maskPlanB (pin0 D (seat l false) l) own R n m := by
  subst hl
  exact maskPlanB_pin0 D rad xL.link (seat xL.link false) rc posI own R n m

theorem arraysPlanB_at (tl : HTailF2) (own : List (ℕ × ℕ)) (R : RecPlan) (n m : ℕ) :
    arraysPlanB (planAt xL D rad (fun j => seat xL.link false j.1) rc posI) tl own R n m =
      arraysPlanB (pin0 D (seat l false) l) tl own R n m := by
  subst hl
  exact arraysPlanB_pin0 D rad xL.link (seat xL.link false) rc posI own R n m tl

theorem maskEllP_atLink :
    maskEllP (planAt xL D rad (fun j => seat xL.link false j.1) rc posI) =
      maskEllP (pin0 D (seat l false) l) := by
  subst hl
  exact maskEllP_pin0 D rad xL.link (seat xL.link false) rc posI

end

/-! ## The five tests, closed over the place -/

variable {Xi : Type} {nQ : ℕ} {X : Public}

/-- **Five tests at border k and group g: no place is named.** -/
structure K4PinsClosed (Dm : MgData Xi ProofFile.InstPub ℕ hRef (2 ^ kRef) nQ X)
    (Ew : WideData ProofFile.InstPub) (k g : ℕ) (par : Par) : Prop where
  maskFits : maskFitsB Dm.cs Ew.d12.M Ew.d12.L
    (Dm.N.msgsAt (flatPlacesOf linksFull true)[k + 1]?)
    (Dm.N.treesAt (flatPlacesOf linksFull true)[k + 1]?) Dm.N.indexNo
    (rowsBefore Ew.dP.fvs (2 * g)) = true
  indexTie : indexTieB Dm.cs Ew.d12.M Ew.d12.L.places Dm.ms Dm.N
    (rowsBefore Ew.dP.fvs (2 * g) + 1) = true
  maskPlan : maskPlanB
    (pin0 (sentOf (k4DataWide Dm Ew mgBase)) ((k4DataWide Dm Ew mgBase).L3.seat (2 * g) false)
      (2 * g)) ((k4DataWide Dm Ew mgBase).N.sent (2 * g) 0)
    (recPlanOf (k4DataWide Dm Ew mgBase) (k4DataWide Dm Ew mgBase).sd)
    ((k4DataWide Dm Ew mgBase).N.msgsAt (flatPlacesOf linksFull true)[k]?) (2 * g) = true
  arrays : arraysPlanB
    (pin0 (sentOf (k4DataWide Dm Ew mgBase)) ((k4DataWide Dm Ew mgBase).L3.seat (2 * g) false)
      (2 * g)) par.hp.tl ((k4DataWide Dm Ew mgBase).N.sent (2 * g) 0)
    (recPlanOf (k4DataWide Dm Ew mgBase) (k4DataWide Dm Ew mgBase).sd)
    ((k4DataWide Dm Ew mgBase).N.msgsAt (flatPlacesOf linksFull true)[k]?) (2 * g) = true
  ell : par.hp.ns ≤ maskEllP
    (pin0 (sentOf (k4DataWide Dm Ew mgBase)) ((k4DataWide Dm Ew mgBase).L3.seat (2 * g) false)
      (2 * g))

/-- **The five, with the plan's first test, give the six.** -/
theorem tests_of_closed {Dm : MgData Xi ProofFile.InstPub ℕ hRef (2 ^ kRef) nQ X}
    {Ew : WideData ProofFile.InstPub} {Z : ProofFile.Pub} {k g : ℕ} {par : Par}
    (h1 : firstFastB Z g = true) (H : K4PinsClosed Dm Ew k g par) :
    K4PinsTests Dm Ew Z k g par where
  first := h1
  maskFits := H.maskFits
  indexTie := H.indexTie
  maskPlan := fun xL hl _ =>
    (maskPlanB_at xL _ _ (k4DataWide Dm Ew mgBase).L3.seat _ _ hl _ _ _ _).trans H.maskPlan
  arrays := fun xL hl _ =>
    (arraysPlanB_at xL _ _ (k4DataWide Dm Ew mgBase).L3.seat _ _ hl _ _ _ _ _).trans H.arrays
  ell := fun xL hl hs =>
    le_trans (le_of_eq hs) (le_trans H.ell
      (le_of_eq (maskEllP_atLink xL _ _ (k4DataWide Dm Ew mgBase).L3.seat _ _ hl).symm))

/-! ## What the tests at `pin0` do not read -/

section
variable (c c' : Codes) (s s' s'' : Params.ReqShape) (l l' : Params.ReqLayout)
  (a a' : Array (Array (ℕ × String))) (ps : List P5T.PSeat) (i : ℕ) (own : List (ℕ × ℕ))
  (arrs arrs' : ℕ → Array (ℕ × String)) (L : VerifiableInference.Desc.K12.Door.Laid)
  (M : List OracleShape) (base : ℕ → ℕ)
  (tr tr' : ℕ → List TreeLook) (n m : ℕ)

theorem maskPlanB_free :
    maskPlanB (pin0 ⟨c, s, l, a⟩ (P6T.seatCallsT ps ⟨c, s, l, a⟩ i) i) own
        ⟨c', s', l', arrs, L, M, sentDataOf s'' base tr⟩ n m =
      maskPlanB (pin0 ⟨c, s, l, a'⟩ (P6T.seatCallsT ps ⟨c, s, l, a'⟩ i) i) own
        ⟨c', s', l', arrs', L, M, sentDataOf s'' base tr'⟩ n m := rfl

theorem arrayArm_free (rad : OracleShape → ℕ) (I K : ℕ) (bn : ℕ × String) :
    arrayArm ⟨c, s, l, a⟩ rad i (P6T.seatCallsT ps ⟨c, s, l, a⟩ i) own
        ⟨c', s', l', arrs, L, M, sentDataOf s'' base tr⟩ n m I K bn =
      arrayArm ⟨c, s, l, a'⟩ rad i (P6T.seatCallsT ps ⟨c, s, l, a'⟩ i) own
        ⟨c', s', l', arrs', L, M, sentDataOf s'' base tr'⟩ n m I K bn := rfl

theorem maskEllP_free (f f' : ℕ → ℕ × ℕ) :
    maskEllP (pin0 ⟨c, s, l, a⟩ f i) = maskEllP (pin0 ⟨c, s, l, a'⟩ f' i) := rfl

end

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.arraysPlanB_pin0
#print axioms OnBytes.Road.K4.maskPlanB_at
#print axioms OnBytes.Road.K4.arraysPlanB_at
#print axioms OnBytes.Road.K4.maskEllP_atLink
#print axioms OnBytes.Road.K4.tests_of_closed
#print axioms OnBytes.Road.K4.maskPlanB_free
#print axioms OnBytes.Road.K4.arrayArm_free
#print axioms OnBytes.Road.K4.maskEllP_free
