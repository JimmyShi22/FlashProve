-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/PartsOfPub.lean: CONDITIONAL.

What is here. Six hypotheses of JoinOne.lean's `joinWorth_one`, as calls: what one of the library's
public structures `Pub34` (Johnson/Road/Rows/LayerEnds34.lean) gives on the lookup's join, in every
world with the true entries. There are eight factors; each is worth what the library's
`parts_of_lines` (Johnson/Road/FormsKeysWhole.lean) concludes; each call's point and weight are the
library's, and so is the token point (`look_of_lines`, Johnson/Road/FormsKeysCaller.lean); a
position's bits fit the library's cap. The steps are those of the library's `startVal_pub`
(Johnson/Road/K4/Inc4.lean), with the truth of the tables from `worlds_of_holds` and
`reads_true_pub`.

  `parts_of_pub`   **the six**

Limits. At the reading `Reading.gl`. THE FULL SIZE ALONE (X). On the library's letters alone:
nothing here names the honest side. HYPOTHESES: such a structure X is given, at this reading; the
table of scales is X's; the world's entries are the true ones at X's tables and the matrices Mm; its
slots are free. The first layer L0 and the weights w are letters. No example is known.

No property is claimed.
-/
import Johnson.Road.K4.Inc4
import Johnson.Road.K4.EntryTrue
import Johnson.Road.FormsKeysRef

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading World Aff)
open OnBytes.Road (pt sclOf cellsAt cellsOf zOf Mats elP ACCP TSP parts_of_lines look_of_lines
  lines_calls e_of_look hcap_of_layout worlds_of_holds admitted_of_layout)
open OnBytes.Road.K4 (reads_true_pub entryOf)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW aC zc wc zpos keyVec famsIn)

/-- **WHAT A PUBLIC STRUCTURE GIVES ON THE LOOKUP's JOIN, IN EVERY WORLD WITH THE TRUE ENTRIES.**
CONDITIONAL: on every hypothesis named. THE FULL SIZE ALONE (X). -/
theorem parts_of_pub [scl : Scl] (X : OnBytes.Road.Rows.Pub34 Cb.Gl.E) (Xρ : X.ρ = Reading.gl)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) (W : World Cb.Gl.E) (Mm : Mats Cb.Gl.E)
    (hW : W.entry = entryOf X.ρ X.tl X.funs X.p.v.iU3 X.p.v.K3 Mm) (L0 : ℕ)
    (w : ℕ → LW Cb.Gl.E) :
    X.parts.length = 8 ∧
    (∀ (q : Fin 8) (f : Aff), X.parts[q.val]? = some f →
      f.value Reading.gl W =
        Reading.gl.val X.alpha - (q.val : Cb.Gl.E) * Reading.gl.val X.theta -
        Blocks.ext (aC X.D q) (keyVec X.D (cellsOf X.D (cellsAt X.p.v.y Mm)) X.tb L0 w q)
          (pt Reading.gl (X.p.v.zk.getD q.val #[])) +
        TSP X.D (cellsOf X.D (cellsAt X.p.v.y Mm)) X.tb L0 w q
          (pt Reading.gl (X.p.v.zk.getD q.val #[])) +
        ∑ l ∈ Finset.range X.D.nl, elP X.D (pt Reading.gl (X.p.v.zk.getD q.val #[])) l *
          ((famsIn q l).map fun s => ACCP X.D (cellsOf X.D (cellsAt X.p.v.y Mm)) w
            (pt Reading.gl (X.p.v.zk.getD q.val #[])) s l).sum) ∧
    (∀ q : Fin 8, ∀ j, j < aC X.D q → pt Reading.gl (X.p.v.zk.getD q.val #[]) j =
      zc X.D (zOf Reading.gl X.H.fo.zx X.H.fo.zy) q j) ∧
    (∀ q : Fin 8, Reading.gl.val (X.H.fo.e.getD q.val zeroE) =
      wc X.D (zOf Reading.gl X.H.fo.zx X.H.fo.zy) q) ∧
    (∀ j, j < X.D.lT → zpos X.D (zOf Reading.gl X.H.fo.zx X.H.fo.zy) j =
      pt Reading.gl X.H.ztF j) ∧
    X.D.lT ≤ X.D.cap := by
  subst hscl
  letI : Scl := sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam
  obtain ⟨T, -, -, -⟩ := worlds_of_holds X.ρ W X.hy X.S X.hg X.hrd X.hl X.ht X.Z X.hZ X.hzt X.h4
    X.hcrt X.htm X.hNM X.hpts X.hfun X.hT Mm (reads_true_pub X Mm hW)
  obtain ⟨h8, Hc⟩ := lines_calls X.hN
  obtain ⟨Lz, Lw, Lp, -, -⟩ :=
    look_of_lines (ρ := X.ρ) X.hy X.S X.Z X.hc X.hN X.hfl X.hsx X.hsy X.hzk
  obtain ⟨hlen, hpv⟩ := parts_of_lines X.hy X.S X.hs X.hg X.hrd X.hl X.ht X.hρ X.Z X.hZ X.hzt X.hm
    X.ha X.hs0 X.hpt (cellsAt X.p.v.y Mm) T X.tb L0 w X.alpha X.theta X.hw X.hparts h8
    (fun cc cd hcd => by
      obtain ⟨cd', h1, h2⟩ := Hc cc
      rw [h1] at hcd
      exact Option.some.inj hcd ▸ h2) X.hfl X.hpad
  have sh := (admitted_of_layout X.hy X.S.p3).shape
  have hzt' : OnBytes.Model.lastOf X.H.fo.zx X.D.lT = .ok X.H.ztF := by
    rw [X.Z.lT, ← sh]
    exact X.hzt
  rw [Xρ] at hpv Lz Lw Lp
  refine ⟨hlen, hpv, Lz, fun q => ?_, Lp X.H.ztF hzt', hcap_of_layout X.hy X.Z X.hc⟩
  rw [X.hHe, e_of_look X.hy X.hN X.he q]
  exact Lw q

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.parts_of_pub
