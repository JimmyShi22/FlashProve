-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4FillAll.lean: THE TWELVE LINES OF THE STRUCTURE K4Fill
(Johnson/Road/K4/K4RowWideScope.lean) HOLD AT THE COMPOSED MEANING's CONSTANT: at the structure of
parameters under the one head AtMgA (Johnson/P5J/MgAtAll.lean; written out a field a line in
Johnson/P5J/LettersAll.lean), at the wider meaning's data eAll Zp cF L
(Johnson/Road/K4/K4EAll.lean), at the head's own public part Zp and first chain cF. One definition,
two statements. Stated at the constant (the head's
structure of parameters takes no number).

  `hpK6`: the text of headPartK6 (Johnson/Desc/Kinds/Law/HeadCutsK6.lean) with the request and the
    heard token as two letters. `headK6_form`: headPartK6 is hpK6 at H.req a and tokH a, and reads
    no string: by cases on the part.
  **`k4Fill_all`**: K4Fill at the head h's own structure of parameters, eAll Zp cF L, Zp and cF.
  PREMISE: the head h alone.
  LINE BY LINE: links: the two written lists have one text · built, d1: by unfolding · lk:
  linkAt_open (Johnson/Road/K4/Riders/LinkAtOpen.lean) at the opening that the head's field laid
  holds · smp: by unfolding, at the constant's own list of seats · dec: noRec_decT
  (Johnson/P5J/LettersAt.lean) · req: by unfolding: the request is read off the public part's bytes
  · head: headK6_form, with tokHOf_rides (Johnson/Road/K4/Riders/TokRides.lean) · fvs, free0, tl,
  ft: by the make of eAll.
Limits. A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY
AtFullSide/Top/). L, the laid lists of K12's data,
is a letter. THE WIDER MEANING IS A BRIDGE's SIDE. K04_law, the law of K4's sub-protocol itself, IS
NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.K4RowWideScope
import Johnson.Road.K4.K4EAll
import Johnson.Road.K4.Riders.LinkAtOpen
import Johnson.Road.K4.Riders.TokRides
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open OnBytes.Road.K4.Riders (linkAt_open tokHOf_rides)
open OnBytes.Maker (WholeD)
open Inst.Model (ppref)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Kinds.Head.Law (headPartK6 partsAtX)
open VerifiableInference.Desc.Sound (Mem MsgT)

section
variable {rows cols : ℕ} (cs : OnBytes.Codes) {Tok : Type} (arr : ℕ → ℕ → ℕ) (msR : List Mem)
  (N : Numbers) (s : ℕ → Cb.Pv.Tail.Size) (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)
  (Wp : OnBytes.Model.Verify.Public) (pl : ℕ → ℕ × Bool × ℕ × ℕ) {P : Type} (tab : ℕ → ℕ)
  (put : P5J.TReq → Fin ppref.V → P5J.TReq)
  (H : P5J.HidAt Wp P (Wit (Fin rows → Fin cols → GE) Tok MsgT) rows cols)

/-- headPartK6's text, with the request and the heard token as two letters. -/
def hpK6 : P5J.TPart → IdxM → P5J.TReq → Fin ppref.V →
    Wit (Fin rows → Fin cols → GE) Tok MsgT → Prop :=
  fun p i rq t w =>
    match p with
    | .lookCallsHeard => partsAtX cs arr msR N s seat Wp pl tab i (put rq t).val w .lookCalls
    | p => partsAtX cs arr msR N s seat Wp pl tab i (put rq (H.hid w).tok).val w p

/-- headPartK6 reads no string, and of the state the values of H.req and tokH alone. -/
theorem headK6_form (tokH : P × P5J.TS → Fin ppref.V) :
    headPartK6 cs arr msR N s seat Wp pl tab put H tokH =
      fun p i a _ w => hpK6 cs arr msR N s seat Wp pl tab put H p i (H.req a) (tokH a) w := by
  funext p i a y w
  cases p <;> rfl

end

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The twelve lines at the constant.** -/
theorem k4Fill_all (h : P5J.AtMgA o Z D r Zp Np cF x)
    (L : VerifiableInference.Desc.K12.Door.Laid) : K4Fill h.𝔇 (eAll Zp cF L) Zp cF := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact
    { links := rfl
      built := rfl
      d1 := rfl
      lk := funext fun m => linkAt_open O m
      smp := ⟨P5J.At.seats Zp, rfl⟩
      dec := P5J.At.noRec_decT o Zp Np cF (P5J.At.EAt Z) h.plan.shape
      req := ⟨fun q => (Meaning.backReq (P5J.At.reqB q)).getD P5J.At.d₀, rfl⟩
      head := ⟨Fin ppref.V, hpK6 _ _ _ _ _ _ _ _ _ _ _, P5J.tokHOf,
        headK6_form _ _ _ _ _ _ _ _ _ _ _ _, fun z _ _ hr => tokHOf_rides z hr⟩
      fvs := rfl
      free0 := rfl
      tl := rfl
      ft := rfl }

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.headK6_form
#print axioms OnBytes.Road.K4.k4Fill_all
