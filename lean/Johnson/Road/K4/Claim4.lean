-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/Claim4.lean: THE CLAIMED SUM OF THE TYPED BATCHED SUMCHECK OF A LAYERS' SUB-PROOF,
AT THE LIBRARY's VALUE, IS THE PUBLIC PART OF THE VERIFIER's START FORM, READ. It is the fourth of
the seven equations `StgH.Claim` (OnBytes/Tie/Pv/Lay/OwnTieL.lean); the file
Johnson/Road/K4/Claims.lean has the others. Four theorems. An
identity between values: no draw, no count.

  `shown_slot`: in a ledger's world at the mask row 0 the value under a slot is what was shown.
  `cl4`: the stage's claimed sum is the typed target at the stage's own state. By unfolding.
  `target4`: `claim4`'s content, of the typed target at a state, at every `MidPar`.
  `claim4`: let X : Pub34 be read by `Reading.gl`, P : FullPar at X's table of scales, sizes and
    tables, F0 the ledger in front of the own rounds, F the ledger at which the batched sumcheck
    begins, W := F's world at the mask row 0 with all entries of virtual rows 0, and st the stage's
    state at the statement y that it finds. If t reads as the start form's value in W (ht: what
    `public_value` gives of `F.publicPart C = some t`), then `(s4.cl y r).1 = gl t`, UNDER
    THESE TIES OF st TO WHAT WAS HEARD: its point is the lookup's; its kTg is `kTgAt fo F0`; its
    sent sum is what F shows under the slot of the terms' claimed sum; its drawn element reads
    om[1]; the last claim and eps of the terms' typed output read the record's; AND THESE FACTS ON
    THE LEDGERS: the lookup's end form has one value at what F0 and at what F shows (hkeep); F shows
    0 under the slots of the terms' hiding coefficients (h0); the terms' record's target reads as
    its start form's value in W (htt).

Paid inside: the eight factors' constants against the typed `lnTg`
(Johnson/Road/K4/StartAtPub.lean); KT's value at what was shown against the typed `overTg`
(KTShown.lean, TermsS0.lean).

Limits. ALL THE TIES AND FACTS NAMED ABOVE ARE PREMISES. Those of StartAtPub.lean (a `Pub34` holds
hfl for all eight calls). A sub-proof that is not the first.
-/
import Johnson.Road.K4.StartAtPub
import Johnson.Road.K4.KTShown
import Johnson.Road.K4.TermsS0
import Cb.Pv.Lay.At.OwnW

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset Cb Cb.Pv.Lay Cb.Pv.Lay.At
open OnBytes.Model (Reading World Aff Fork)
open OnBytes.Road.Rows (Pub34)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW)

/-- At the mask row 0 the value under a slot is what was shown. -/
theorem shown_slot {K : Type} [CommRing K] (ρ : Reading K) (F : Fork) (e : ℕ → ℕ → ℕ → K)
    (j : ℕ) : (F.worldOf ρ (fun _ => 0) e).slot j = ρ.val (F.vp.getD j zeroE) := by
  simp [Fork.worldOf]

variable [scl : Scl] {M Xs : Type}

/-- The stage's claimed sum is the typed target at the stage's own state. -/
theorem cl4 {E : Type} [Field E] [Fintype E] (P : FullPar E M Xs)
    (y : P.own.toOwn.tail.s3.Nx × E) (r : Fin 0 → E) :
    (P.own.toOwn.tail.s4.cl y r).1 = P.ip.inn.tg (P.own.toOwn.tail.s4.cl y r).2 := rfl

/-- The typed target at a state that is tied to what was heard. -/
theorem target4 (X : Pub34 Cb.Gl.E) (hρ : X.ρ = Reading.gl)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) (P : MidPar Cb.Gl.E M Xs)
    (hD : X.D = P.D) (htb : X.tb = P.tb) (F0 F : Fork) (w : ℕ → LW Cb.Gl.E) (st : P.ip.St)
    (hα : X.alpha = X.H.fo.alpha) (hθ : X.theta = X.H.fo.theta)
    (hzs : st.z = zAt X.H.fo) (hkT : st.kTg = kTgAt X.H.fo F0)
    (hs : st.s = Reading.gl.val (F.vp.getD X.tT.sCl zeroE))
    (hβ : st.β = Reading.gl.val (X.om.getD 1 zeroE))
    (hf : st.o3.fin = Reading.gl.val X.tT.p.claim) (he : st.o3.eps = Reading.gl.val X.tT.p.eps)
    (hkeep : X.H.fo.cEnd.value Reading.gl (F.worldOf Reading.gl (fun _ => 0) fun _ _ _ => 0) =
      X.H.fo.cEnd.value Reading.gl (F0.worldOf Reading.gl (fun _ => 0) fun _ _ _ => 0))
    (h0 : ∀ j, X.tT.p.first ≤ j → j < X.tT.p.first + X.tT.p.walk.1.length →
      Reading.gl.val (F.vp.getD j zeroE) = 0)
    (htt : Reading.gl.val X.tT.p.target = X.tT.p.start.value Reading.gl
      (F.worldOf Reading.gl (fun _ => 0) fun _ _ _ => 0)) :
    P.ip.inn.tg st = (startOf X.H X.om X.parts).value Reading.gl
      (F.worldOf Reading.gl (fun _ => 0) fun _ _ _ => 0) := by
  have hinv := X.hinv
  rw [hρ] at hinv
  have ho : overTg P.ip.Y3 st.o3 = X.H.KT.value Reading.gl
      (F.worldOf Reading.gl (fun _ => 0) fun _ _ _ => 0) :=
    over_KT Reading.gl _ P.ip.Y3 st.o3 X.tT.p _ X.H.KT X.hKT hinv
      (fun j h1 h2 => by rw [shown_slot]; exact h0 j h1 h2) htt (terms_S0 P _ _ _) hf he
  have hk : st.kTg = keysPub X.H.fo - X.H.fo.cEnd.value Reading.gl
      (F.worldOf Reading.gl (fun _ => 0) fun _ _ _ => 0) := by
    rw [hkT, hkeep]
    rfl
  exact startTg_pub X hρ hscl P hD htb _ (fun _ _ _ => rfl) w st hzs hα hθ hk
    (by rw [hs, shown_slot]) hβ ho

/-- **The fourth claim.** -/
theorem claim4 (X : Pub34 Cb.Gl.E) (hρ : X.ρ = Reading.gl)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) (P : FullPar Cb.Gl.E M Xs)
    (hD : X.D = P.D) (htb : X.tb = P.tb) (F0 F : Fork) (w : ℕ → LW Cb.Gl.E)
    (y : P.own.toOwn.tail.s3.Nx × Cb.Gl.E) (r : Fin 0 → Cb.Gl.E) (st : P.ip.St)
    (hst : (P.own.toOwn.tail.s4.cl y r).2 = st) (t : E)
    (ht : Reading.gl.val t = (startOf X.H X.om X.parts).value Reading.gl
      (F.worldOf Reading.gl (fun _ => 0) fun _ _ _ => 0))
    (hα : X.alpha = X.H.fo.alpha) (hθ : X.theta = X.H.fo.theta)
    (hzs : st.z = zAt X.H.fo) (hkT : st.kTg = kTgAt X.H.fo F0)
    (hs : st.s = Reading.gl.val (F.vp.getD X.tT.sCl zeroE))
    (hβ : st.β = Reading.gl.val (X.om.getD 1 zeroE))
    (hf : st.o3.fin = Reading.gl.val X.tT.p.claim) (he : st.o3.eps = Reading.gl.val X.tT.p.eps)
    (hkeep : X.H.fo.cEnd.value Reading.gl (F.worldOf Reading.gl (fun _ => 0) fun _ _ _ => 0) =
      X.H.fo.cEnd.value Reading.gl (F0.worldOf Reading.gl (fun _ => 0) fun _ _ _ => 0))
    (h0 : ∀ j, X.tT.p.first ≤ j → j < X.tT.p.first + X.tT.p.walk.1.length →
      Reading.gl.val (F.vp.getD j zeroE) = 0)
    (htt : Reading.gl.val X.tT.p.target = X.tT.p.start.value Reading.gl
      (F.worldOf Reading.gl (fun _ => 0) fun _ _ _ => 0)) :
    (P.own.toOwn.tail.s4.cl y r).1 = Reading.gl.val t := by
  rw [cl4, hst, ht]
  exact target4 X hρ hscl P.toMidPar hD htb F0 F w st hα hθ hzs hkT hs hβ hf he hkeep h0 htt

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.cl4
#print axioms OnBytes.Road.K4.target4
#print axioms OnBytes.Road.K4.claim4
