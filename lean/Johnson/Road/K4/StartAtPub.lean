-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/StartAtPub.lean: Johnson/Road/K4/StartTarget.lean's `startTg_eq` WITH ITS PUBLIC
PREMISES PAID FROM THE RECORD `Pub34` (Johnson/Road/Rows/LayerEnds34.lean: the public lines of a
layers' sub-proof up to the batched sumcheck's end). One theorem. An identity between values: no
draw, no count.

  `startTg_pub`: let X : Pub34 over the challenge field read by `Reading.gl`; P : MidPar at the
    table of scales of X's shape, with X's sizes and tables; W a world all of whose entries of
    virtual rows are 0; st a state of the typed batched sumcheck whose point is the lookup's (`zAt
    X.H.fo`). If X's alpha and theta are the lookup's, and (hk) st.kTg is `keysPub` less the
    lookup's end form's value in W, (hs) st.s is the value under the slot of the terms' claimed sum,
    (hβ) st.β reads om[1], (ho) the typed `overTg` of the terms' output is KT's value in W: then the
    typed target `inn.tg st` is the value in W of `startOf X.H X.om X.parts`.

Paid here, from other files' theorems: the eight factors' worth at the cells 0 (`parts_of_lines` at
`trueAt_noEntry`); all eight calls' points and weights at one z (`look_of_lines`, `e_of_look`);
D.lT ≤ D.cap (`hcap_of_layout`); there are eight weights.

Limits. hk, hs, hβ, ho AND THE TIES OF st AND P TO X ARE PREMISES. A `Pub34` holds hfl for all eight
calls: by LayerEnds34.lean's own words that fails at the small shipped example. That a hearing of
K4's text gives such an X is another file's (Johnson/Road/K4/PubOfHearTied.lean).
-/
import Johnson.Road.K4.StartTarget
import Johnson.Road.Rows.LayerEnds34
import Johnson.Road.FormsKeysCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset Cb.Pv.Lay.At
open OnBytes.Model (Reading World Aff)
open OnBytes.Road.Rows (Pub34)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW)

variable [scl : Scl] {M Xs : Type}

/-- **The typed target is the start form's value at what was shown, at the public record.** -/
theorem startTg_pub (X : Pub34 Cb.Gl.E) (hρ : X.ρ = Reading.gl)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) (P : MidPar Cb.Gl.E M Xs)
    (hD : X.D = P.D) (htb : X.tb = P.tb) (W : World Cb.Gl.E)
    (hW : ∀ a b c, W.entry a b c = 0) (w : ℕ → LW Cb.Gl.E) (st : P.ip.St)
    (hzs : st.z = zAt X.H.fo) (hα : X.alpha = X.H.fo.alpha) (hθ : X.theta = X.H.fo.theta)
    (hk : st.kTg = keysPub X.H.fo - X.H.fo.cEnd.value Reading.gl W)
    (hs : st.s = W.slot X.tT.sCl) (hβ : st.β = Reading.gl.val (X.om.getD 1 zeroE))
    (ho : overTg P.ip.Y3 st.o3 = X.H.KT.value Reading.gl W) :
    P.ip.inn.tg st = (startOf X.H X.om X.parts).value Reading.gl W := by
  subst hscl
  letI : Scl := sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam
  have Z : Sized X.h P.D := hD ▸ X.Z
  have hc : P.D.cap = X.h.lidb := hD ▸ X.hc
  have hfl : ∀ k : Fin 8, X.h.nmin - X.h.ll - X.h.lt ≤
      Nat.clog 2 (Inst.Model.FFSeg.used P.D k) := hD ▸ X.hfl
  have hN : Numerals Reading.gl := hρ ▸ X.hρ
  have hpad := X.hpad
  rw [hρ, htb] at hpad
  obtain ⟨h8, Hc⟩ := lines_calls X.hN
  obtain ⟨Lz, Lw, -, -, -⟩ :=
    look_of_lines (ρ := Reading.gl) X.hy X.S Z hc X.hN hfl X.hsx X.hsy X.hzk
  obtain ⟨hlen, hpv⟩ := parts_of_lines X.hy X.S X.hs X.hg X.hrd X.hl X.ht hN Z X.hZ X.hzt X.hm
    X.ha X.hs0 X.hpt (fun _ _ _ => 0)
    (trueAt_noEntry hW X.p.v X.h.lt (pt Reading.gl X.Zp) (pt Reading.gl X.H.ztF)) P.tb P.L0 w
    X.alpha X.theta X.hw X.hparts h8
    (fun cc cd hcd => by
      obtain ⟨cd', h1, h2⟩ := Hc cc
      rw [h1] at hcd
      exact Option.some.inj hcd ▸ h2) hfl hpad
  have hNC : X.p.v.y.fo.NC = 8 := by
    rw [(fo_of_layout X.hy).2.1, (fo_of_layout X.hy).2.2, h8]
  rw [hα, hθ] at hpv
  have hz' : ∀ c : Fin 8, ∀ j, j < Inst.Model.FFSeg.aC P.D c →
      pt Reading.gl (X.p.v.zk.getD c.val #[]) j = Inst.Model.FFSeg.zc P.D st.z c j := by
    intro c j hj
    rw [hzs]
    exact Lz c j hj
  have hw' : ∀ c : Fin 8, Reading.gl.val (X.H.fo.e.getD c.val zeroE) =
      Inst.Model.FFSeg.wc P.D st.z c := by
    intro c
    rw [hzs, X.hHe, e_of_look X.hy X.hN X.he c]
    exact Lw c
  have h8e : X.H.fo.e.size = 8 := by
    rw [X.hHe, X.he, Array.size_map, Array.size_range, hNC]
  exact startTg_eq P st W X.H X.om X.parts X.hT hlen w
    (fun q => pt Reading.gl (X.p.v.zk.getD q.val #[])) hpv (hcap_of_layout X.hy Z hc) hz' hw' h8e
    hk hs hβ ho

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.startTg_pub
