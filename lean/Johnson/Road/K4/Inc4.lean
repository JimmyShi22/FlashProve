-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/Inc4.lean: THE BATCHED SUMCHECK's TYPED TARGET LESS ITS INCOMING FORM AT THE ENTRIES
m IS THE VALUE OF K4's START FORM IN A WORLD WITH MASKS AND TRUE TABLES. The twin, with masks and
cells, of Johnson/Road/K4/StartTarget.lean and StartAtPub.lean (which stand at what was shown, cells
0). Three theorems. Glue: the library's `start_form` (Cb/Pv/Lay/At/Start.lean) and `lineS_form`
(Cb/Pv/Lay/At/Line.lean) against `start_lines` (StartLine.lean). No draw, no count.

  `start_named`: the library's `start_form` with its four members named.
  `startVal_eq`: for P : MidPar, a state st, entries m, a world W: if the eight calls' parts are
    worth in W what `start_lines` asks at the cells `P.rd m`, and four ties hold (hk: what the
    lookup's end leaves · hs: the sent sum less its mask · hβ · ho: what the terms' sumcheck
    leaves): `P.ip.inn.tg st - ∑ j, P.ip.inn.inc st j * m j = (startOf H om parts).value gl W`.
  `startVal_pub`: the same at a public record X : Pub34, the parts' worth concluded from
    `parts_of_lines` under `TrueAt` at cells cc with `cellsOf P.D cc = P.rd m`.

Limits. hk, hs, hβ, ho, `TrueAt` AND THE TIES OF st AND P TO X ARE PREMISES. A `Pub34` holds hfl for
all eight calls: by LayerEnds34.lean's head that fails at the small shipped example.

-/
import Johnson.Road.K4.StartAtPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset Cb.Pv.Lay Cb.Pv.Lay.At
open OnBytes.Model (Reading World Aff)
open OnBytes.Model.Layer (Heard)
open OnBytes.Road.Rows (Pub34)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW aC zc wc keyVec famsIn)

/-- The library's `start_form`, its four members named. -/
theorem start_named {E : Type} [Field E] (Y : Cb.PscPar E) [DecidableEq Y.J]
    (lnTg : (ℕ → E) → E) (lnInc : (ℕ → E) → Y.J → E) (rT : Y.J) (st : St4 E Y.J Y.Out)
    (m : Y.J → E) (k line s o : E) (hk : st.kTg - ∑ j, st.kInc j * m j = k)
    (hl : lnTg st.z + ∑ j, lnInc st.z j * m j = line) (hs : st.s - m rT = s)
    (ho : overAt Y st.o3 m = o) :
    startTg Y lnTg st - ∑ j, startInc Y lnInc rT st j * m j = k - line - s + st.β * o := by
  rw [start_form, hk, hl, hs, ho]

variable [scl : Scl] {M Xs : Type}

open Classical in
/-- **The typed target less the incoming form is the start form's value.** -/
theorem startVal_eq (P : MidPar Cb.Gl.E M Xs) (st : P.ip.St) (m : P.J → Cb.Gl.E)
    (W : World Cb.Gl.E) (H : Heard) (om : Array E) (parts : List Aff) {tT : Model.Tsc}
    (hT : H.tT = some tT) (hlen : parts.length = 8) (w : ℕ → LW Cb.Gl.E)
    (ζ : Fin 8 → ℕ → Cb.Gl.E)
    (hp : ∀ (c : Fin 8) (f : Aff), parts[c.val]? = some f →
      f.value Reading.gl W =
        Reading.gl.val H.fo.alpha - (c.val : Cb.Gl.E) * Reading.gl.val H.fo.theta -
        Blocks.ext (aC P.D c) (keyVec P.D (P.rd m) P.tb P.L0 w c) (ζ c) +
        TSP P.D (P.rd m) P.tb P.L0 w c (ζ c) +
        ∑ l ∈ range P.D.nl, elP P.D (ζ c) l *
          ((famsIn c l).map fun s => ACCP P.D (P.rd m) w (ζ c) s l).sum)
    (hcap : P.D.lT ≤ P.D.cap)
    (hz : ∀ c : Fin 8, ∀ j, j < aC P.D c → ζ c j = zc P.D st.z c j)
    (hwc : ∀ c : Fin 8, Reading.gl.val (H.fo.e.getD c.val zeroE) = wc P.D st.z c)
    (h8 : H.fo.e.size = 8)
    (hk : st.kTg - ∑ j, st.kInc j * m j = keysPub H.fo - H.fo.cEnd.value Reading.gl W)
    (hs : st.s - m P.rT = W.slot tT.sCl) (hβ : st.β = Reading.gl.val (om.getD 1 zeroE))
    (ho : overAt P.ip.Y3 st.o3 m = H.KT.value Reading.gl W) :
    P.ip.inn.tg st - ∑ j, P.ip.inn.inc st j * m j = (startOf H om parts).value Reading.gl W := by
  rw [start_lines P.D (P.rd m) P.tb P.L0 w Reading.gl W H om parts hT hlen H.fo.alpha
    H.fo.theta st.z ζ hp hcap hz hwc]
  refine (start_named P.ip.Y3 P.ip.lnTg P.ip.lnInc P.rT st m _ _ _ _ hk
    (lineS_form P.D P.tb P.L0 P.rd P.hrd w st.z m).symm hs ho).trans ?_
  rw [hβ]
  unfold keysPub
  rw [h8]
  show _ = _ + Reading.gl.val (padFo H.fo) - _ - _ - _ + _
  ring

/-- **The same at the public record.** -/
theorem startVal_pub (X : Pub34 Cb.Gl.E) (hρ : X.ρ = Reading.gl)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) (P : MidPar Cb.Gl.E M Xs)
    (hD : X.D = P.D) (htb : X.tb = P.tb) (W : World Cb.Gl.E) (cc : Cells Cb.Gl.E)
    (T : TrueAt Reading.gl W X.p.v X.h.lt cc (pt Reading.gl X.Zp) (pt Reading.gl X.H.ztF))
    (w : ℕ → LW Cb.Gl.E) (st : P.ip.St) (m : P.J → Cb.Gl.E) (hcc : cellsOf P.D cc = P.rd m)
    (hzs : st.z = zAt X.H.fo) (hα : X.alpha = X.H.fo.alpha) (hθ : X.theta = X.H.fo.theta)
    (hk : st.kTg - ∑ j, st.kInc j * m j = keysPub X.H.fo - X.H.fo.cEnd.value Reading.gl W)
    (hs : st.s - m P.rT = W.slot X.tT.sCl)
    (hβ : st.β = Reading.gl.val (X.om.getD 1 zeroE))
    (ho : overAt P.ip.Y3 st.o3 m = X.H.KT.value Reading.gl W) :
    P.ip.inn.tg st - ∑ j, P.ip.inn.inc st j * m j =
      (startOf X.H X.om X.parts).value Reading.gl W := by
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
    X.ha X.hs0 X.hpt cc T P.tb P.L0 w
    X.alpha X.theta X.hw X.hparts h8
    (fun cc cd hcd => by
      obtain ⟨cd', h1, h2⟩ := Hc cc
      rw [h1] at hcd
      exact Option.some.inj hcd ▸ h2) hfl hpad
  have hNC : X.p.v.y.fo.NC = 8 := by
    rw [(fo_of_layout X.hy).2.1, (fo_of_layout X.hy).2.2, h8]
  rw [hα, hθ, hcc] at hpv
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
  exact startVal_eq P st m W X.H X.om X.parts X.hT hlen w
    (fun q => pt Reading.gl (X.p.v.zk.getD q.val #[])) hpv (hcap_of_layout X.hy Z hc) hz' hw' h8e
    hk hs hβ ho

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.startVal_eq
#print axioms OnBytes.Road.K4.startVal_pub
