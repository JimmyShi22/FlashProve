-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/StartTarget.lean: THE TARGET OF THE TYPED BATCHED SUMCHECK OF A LAYERS' SUB-PROOF IS
THE VERIFIER's START FORM's VALUE AT WHAT WAS SHOWN: AS A NUMBER. Two theorems. An identity between
values: no draw, no count.

Cb/Pv/Lay/At/Fore.lean's head: "For a tie with the programs it will not be enough that the batched
sumcheck's target less its incoming form has the programs' value: the target itself, and so kTg,
must be the public part of the programs' start form as a number."

  `lnTg_zero`: the constant of the join's affine side is `lineS` at the cells 0, at any weights.
  `startTg_eq`: at every `MidPar` over the challenge field and every state st of the batched
    sumcheck: if, in a world W, (hp) the eight factors are worth what `joinPart_keyVec'` says AT THE
    CELLS 0; (hz, hwc) all eight calls' points and weights read as the library's at st.z; (hk)
    st.kTg is `keysPub` less the lookup's end form's value in W; (hs) st.s is the value under the
    slot of the terms' claimed sum; (hβ) st.β reads om[1]; (ho) the typed public part `overTg` of
    what the terms' sumcheck leaves is KT's value in W: then the typed target `inn.tg st` is the
    value of `startOf H om parts` in W.

How it is meant to be used. W := the ledger's world at the mask row 0 with all entries of virtual
rows 0: there a form's value is its public part, read; hp is paid by `trueAt_noEntry`
(Johnson/Road/K4/StartLine.lean) and `joinPart_keyVec'`; hk by `kTgAt`
(Johnson/Road/K4/LookLeft.lean), if the shown values under the end form's slots have not turned
since the lookup.

Limits. EVERY ONE OF THE SIX CONDITIONS IS A PREMISE, and so are four more binders: the terms'
record is there (hT), there are eight factors (hlen) and eight weights (h8), and D.lT ≤ D.cap
(hcap). ho is shown, from premises of its own, in Johnson/Road/K4/KTShown.lean (`over_KT`). hz and
hwc for all eight calls: see StartLine.lean's limits. That a hearing's record holds this target is
not said here.
-/
import Johnson.Road.K4.StartLine
import Johnson.Road.K4.LookLeft
import Cb.Pv.Lay.At.Mid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset Cb.Pv.Lay.At
open OnBytes.Model (Reading World Aff)
open OnBytes.Model.Layer (Heard)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW aC zc wc keyVec famsIn)

variable [scl : Scl] {M X : Type}

/-- The constant of the join's affine side. -/
theorem lnTg_zero {E : Type} [Field E] [Fintype E] (P : MidPar E M X) (w : ℕ → LW E)
    (z : ℕ → E) : lnTg P.D P.tb P.L0 P.rd z = lineS P.D (fun _ => 0) P.tb P.L0 w z := by
  have h0 : P.rd 0 = fun _ => 0 := by
    funext c
    have h := P.hrd 0 0 0 0 c
    simp only [zero_mul, add_zero] at h
    exact h
  unfold lnTg
  rw [h0]
  exact lineS_w P.D P.tb P.L0 _ w z _

/-- **The typed target is the start form's value at what was shown.** -/
theorem startTg_eq (P : MidPar Cb.Gl.E M X) (st : P.ip.St) (W : World Cb.Gl.E) (H : Heard)
    (om : Array E) (parts : List Aff) {tT : Model.Tsc} (hT : H.tT = some tT)
    (hlen : parts.length = 8) (w : ℕ → LW Cb.Gl.E) (ζ : Fin 8 → ℕ → Cb.Gl.E)
    (hp : ∀ (c : Fin 8) (f : Aff), parts[c.val]? = some f →
      f.value Reading.gl W =
        Reading.gl.val H.fo.alpha - (c.val : Cb.Gl.E) * Reading.gl.val H.fo.theta -
        Blocks.ext (aC P.D c) (keyVec P.D (fun _ => 0) P.tb P.L0 w c) (ζ c) +
        TSP P.D (fun _ => 0) P.tb P.L0 w c (ζ c) +
        ∑ l ∈ range P.D.nl, elP P.D (ζ c) l *
          ((famsIn c l).map fun s => ACCP P.D (fun _ => 0) w (ζ c) s l).sum)
    (hcap : P.D.lT ≤ P.D.cap)
    (hz : ∀ c : Fin 8, ∀ j, j < aC P.D c → ζ c j = zc P.D st.z c j)
    (hwc : ∀ c : Fin 8, Reading.gl.val (H.fo.e.getD c.val zeroE) = wc P.D st.z c)
    (h8 : H.fo.e.size = 8)
    (hk : st.kTg = keysPub H.fo - H.fo.cEnd.value Reading.gl W)
    (hs : st.s = W.slot tT.sCl) (hβ : st.β = Reading.gl.val (om.getD 1 zeroE))
    (ho : overTg P.ip.Y3 st.o3 = H.KT.value Reading.gl W) :
    P.ip.inn.tg st = (startOf H om parts).value Reading.gl W := by
  rw [start_lines P.D (fun _ => 0) P.tb P.L0 w Reading.gl W H om parts hT hlen H.fo.alpha
    H.fo.theta st.z ζ hp hcap hz hwc]
  show startTg P.ip.Y3 (lnTg P.D P.tb P.L0 P.rd) st = _
  unfold startTg
  rw [lnTg_zero P w, hk, hs, hβ, ho]
  unfold keysPub
  rw [h8]
  show _ = _ + Reading.gl.val (padFo H.fo) - _ - _ - _ + _
  ring

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.lnTg_zero
#print axioms OnBytes.Road.K4.startTg_eq
