-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/PassSig.lean: CONDITIONAL.

What is here. The sums of the batched sumcheck's two passes on the honest side (`passSum`,
StackStart.lean) are the library's two sums over its own panels: the first pass's is `Sig0`; the
second's is the weight of the second claim times `Sig1` (Inst/Model/FF/Objects.lean).

How. The library's law holds at every pair of weights whose first reads 1, and neither a panel's
share nor the two sums read the weights: at the weights 1, 0 it gives the first sum alone.

  `pass_share`   a pass's sum, panel by panel, in the library's shares
  `sum_claim`   the weights 1, 0 pick the first pass's panels
  `stackEnd_any`, `sides_made`   two returns
  `pass0_sig`, `pass1_sig`   **the two passes**

Limits. At the reading `Reading.gl`. THE FULL SIZE ALONE: the library's law that is called
(`port_sig`, Johnson/Road/FormsKeysPortSig.lean) asks its structure `SigFits`, which by that file's
head cannot be met at the small public example. HYPOTHESES: `SigFits` at the honest side's own
environment of the panels; the ties of PanelShare.lean at every panel of the first pass (for the
second statement: at every panel); the calls of the second walk are 0, 1, 2, 5; the verifier's list
of claims returns; the first of the two weights reads 1; the verifier's end function returns on the
panels, at whatever weights; for the second pass: every panel's claim is 0 or 1. The library's sums
stand at its structure `rPort`, which holds what stands in the place of the second token sumcheck's
shown values and the never-sent vectors hv as they are given: it is not the library's true
structure. No example of the hypotheses together is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PanelShare
import Johnson.Desc.ProofFile.Honest.K4.Law.UnitsRead
import Johnson.Road.K4.C.StackPanelsAt
import Johnson.Road.FormsKeysPortSig
import Johnson.Desc.First.K4.Returns.Pub.End

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE)
open OnBytes.Model (Reading Aff World WsShape WsClaim)
open OnBytes.Model.Layer (SBlk ClaimEnv StackEnd stackEnd)
open OnBytes.Road (shareP omK wvOf SigFits port_sig rPort Cells Wm)
open OnBytes.Road.K4.C (sidesEnv stack_panels_at)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Sig0 Sig1 layerR)
open OnBytes.Desc.First.K4.Honest

/-- **A pass's sum, panel by panel, in the library's shares.** CONDITIONAL: on the ties at every
panel; every panel's two sides are made. -/
theorem pass_share (D : StackData) {Wo : World Cb.Gl.E} {hv wv : ℕ → ℕ → Cb.Gl.E} (c : ℕ)
    (T : ∀ b ∈ D.bl.toList, b.claim = c → PanelTies D.S
      (fun a => valAff? D.S.v D.R (fun _ => zeroE) a) D.F D.hZ D.hR Wo hv wv b)
    (hs : ∀ b ∈ D.bl.toList, ∃ x, panelTabs D.S (fun a => valAff? D.S.v D.R (fun _ => zeroE) a)
      D.om D.F D.hZ D.hR b = some x) :
    passSum D c = ((D.bl.toList.filter fun b => b.claim == c).map fun b =>
      omK Reading.gl D.om b * shareP Reading.gl Wo D.S.v.y hv wv b).sum := by
  unfold passSum
  congr 1
  refine List.map_congr_left fun b hb => ?_
  have hb' := List.mem_filter.mp hb
  obtain ⟨x, hx⟩ := hs b hb'.1
  rw [hx]
  exact panel_share (T b hb'.1 (by simpa using hb'.2)) hx

/-- The weights 1, 0 pick the first pass's panels. -/
theorem sum_claim (f : SBlk → Cb.Gl.E) (l : List SBlk) :
    (l.map fun b => omK Reading.gl #[oneE, zeroE] b * f b).sum =
      ((l.filter fun b => b.claim == 0).map f).sum := by
  rw [sum_filter]
  congr 1
  refine List.map_congr_left fun b _ => ?_
  unfold omK
  by_cases h : b.claim = 0
  · rw [if_pos (by rw [h]; rfl), h]
    show Reading.gl.val oneE * _ = _
    rw [Reading.gl.one, one_mul]
  · rw [if_neg (by simpa using h)]
    have e : (#[oneE, zeroE] : Array E).getD b.claim zeroE = zeroE := by
      rcases hc : b.claim with _ | _ | n
      · exact absurd hc h
      · rfl
      · rfl
    rw [e, Reading.gl.zero, zero_mul]

/-- Whether the verifier's end function returns does not hang on the two weights. -/
theorem stackEnd_any {y : OnBytes.Model.Layer.Lay} {bl : Array SBlk} {rs om H1 V : Array E}
    {lam : ℕ} {a b : E} {s' : StackEnd} (om' : Array E)
    (h : stackEnd y bl rs lam om H1 V a b = some s') :
    ∃ s'', stackEnd y bl rs lam om' H1 V a b = some s'' := by
  have e := OnBytes.Desc.First.K4.RtPub.stackEnd_rel y lam om H1 V om' H1 V a b a b
    (OnBytes.Flat.All2.refl OnBytes.Desc.First.K4.RtPub.BlkSkel.refl bl.toList) (rfl : rs.size = _)
  rw [h] at e
  exact Option.isSome_iff_exists.mp e.symm

/-- Every panel's two sides are made, where the function that makes the job's data returns. -/
theorem sides_made {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}
    (h : stackData Q w p shownT = some SD) : ∀ b ∈ SD.bl.toList, ∃ x,
      panelTabs SD.S (fun a => valAff? SD.S.v SD.R (fun _ => zeroE) a) SD.om SD.F SD.hZ SD.hR b =
        some x := by
  obtain ⟨S, _, hD⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, _, _, _, _, _, _, sides, hm, _⟩ := stackDataOn_open hD
  rw [Array.mapM_eq_mapM_toList] at hm
  obtain ⟨L, hL, _⟩ := Option.map_eq_some_iff.mp hm
  exact mapM_at _ _ L hL

variable [scl : Scl]

/-- **THE FIRST PASS's SUM IS THE LIBRARY's Sig0.** CONDITIONAL: on every hypothesis named.
THE FULL SIZE ALONE (SF). -/
theorem pass0_sig {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}
    (h : stackData Q w p shownT = some SD) {Wo : World Cb.Gl.E} {c : ClaimEnv}
    {h' : OnBytes.Model.Layer.Shape} {pc : List (List String)} {s : WsShape} {D : Dim}
    {lk L0 : ℕ} {cc : Cells Cb.Gl.E} {t : Cell → Cb.Gl.E} {low z zh ζ : ℕ → Cb.Gl.E} {tb : Tables}
    (SF : SigFits Reading.gl Wo (sidesEnv SD.S shownT) c h' pc s D lk L0 cc t low z zh ζ tb)
    (M : Wm Cb.Gl.E) (hv : ℕ → ℕ → Cb.Gl.E) (hTS : SD.S.TS = [0, 1, 2, 5]) {cl : List WsClaim}
    (hc : c.weightClaims SD.S.TS = some cl)
    (hom : Reading.gl.val (SD.om.getD 0 zeroE) = 1) {rs H1 V : Array E} {lam : ℕ} {sA sB : E}
    {s' : StackEnd}
    {om : Array E} (hst : stackEnd SD.S.v.y SD.bl rs lam om H1 V sA sB = some s')
    (T : ∀ b ∈ SD.bl.toList, b.claim = 0 → PanelTies SD.S
      (fun a => valAff? SD.S.v SD.R (fun _ => zeroE) a) SD.F SD.hZ SD.hR Wo hv
      (wvOf Reading.gl c.wsLay M cl) b) :
    passSum SD 0 = Sig0 D (rPort Reading.gl SD.S.v.y shownT hv D t z zh) tb L0
      (fun l => layerR D.P lk M (L0 + l)) z zh := by
  obtain ⟨pans, hp, hbl, _⟩ := stack_panels_at h
  have hs := sides_made h
  obtain ⟨s'', hst'⟩ := stackEnd_any #[oneE, zeroE] hst
  have e := port_sig SF M hv hTS hp hc (om := #[oneE, zeroE])
    (show Reading.gl.val oneE = 1 from Reading.gl.one) (by rw [← hbl]; exact hst')
  rw [← hbl, sum_claim] at e
  have e1 : Reading.gl.val ((#[oneE, zeroE] : Array E).getD 1 zeroE) = 0 := Reading.gl.zero
  rw [e1, zero_mul, add_zero] at e
  rw [pass_share SD 0 T hs]
  refine Eq.trans ?_ e
  congr 1
  refine List.map_congr_left fun b hb => ?_
  have hb0 : b.claim = 0 := by simpa using (List.mem_filter.mp hb).2
  unfold omK
  rw [hb0, hom, one_mul]
  rfl

/-- **THE SECOND PASS's SUM IS THE SECOND WEIGHT TIMES THE LIBRARY's Sig1.** CONDITIONAL: on every
hypothesis named. THE FULL SIZE ALONE (SF). -/
theorem pass1_sig {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}
    (h : stackData Q w p shownT = some SD) {Wo : World Cb.Gl.E} {c : ClaimEnv}
    {h' : OnBytes.Model.Layer.Shape} {pc : List (List String)} {s : WsShape} {D : Dim}
    {lk L0 : ℕ} {cc : Cells Cb.Gl.E} {t : Cell → Cb.Gl.E} {low z zh ζ : ℕ → Cb.Gl.E} {tb : Tables}
    (SF : SigFits Reading.gl Wo (sidesEnv SD.S shownT) c h' pc s D lk L0 cc t low z zh ζ tb)
    (M : Wm Cb.Gl.E) (hv : ℕ → ℕ → Cb.Gl.E) (hTS : SD.S.TS = [0, 1, 2, 5]) {cl : List WsClaim}
    (hc : c.weightClaims SD.S.TS = some cl)
    (hom : Reading.gl.val (SD.om.getD 0 zeroE) = 1) {rs H1 V : Array E} {lam : ℕ} {sA sB : E}
    {s' : StackEnd}
    {om : Array E} (hst : stackEnd SD.S.v.y SD.bl rs lam om H1 V sA sB = some s')
    (T : ∀ b ∈ SD.bl.toList, PanelTies SD.S (fun a => valAff? SD.S.v SD.R (fun _ => zeroE) a)
      SD.F SD.hZ SD.hR Wo hv (wvOf Reading.gl c.wsLay M cl) b)
    (h01 : ∀ b ∈ SD.bl.toList, b.claim = 0 ∨ b.claim = 1) :
    passSum SD 1 = Reading.gl.val (SD.om.getD 1 zeroE) *
      Sig1 D (rPort Reading.gl SD.S.v.y shownT hv D t z zh) tb L0
        (fun l => layerR D.P lk M (L0 + l)) z zh := by
  obtain ⟨pans, hp, hbl, _⟩ := stack_panels_at h
  have hs := sides_made h
  obtain ⟨s'', hst'⟩ := stackEnd_any SD.om hst
  have e := port_sig SF M hv hTS hp hc hom (by rw [← hbl]; exact hst')
  rw [← hbl] at e
  have e0 := pass0_sig h SF M hv hTS hc hom hst fun b hb _ => T b hb
  have split : (SD.bl.toList.map fun b => omK Reading.gl SD.om b *
      shareP Reading.gl Wo SD.S.v.y hv (wvOf Reading.gl c.wsLay M cl) b).sum =
      passSum SD 0 + passSum SD 1 := by
    rw [pass_share SD 0 (fun b hb _ => T b hb) hs, pass_share SD 1 (fun b hb _ => T b hb) hs,
      sum_filter, sum_filter, ← List.sum_map_add]
    congr 1
    refine List.map_congr_left fun b hb => ?_
    rcases h01 b hb with k | k
    · rw [k, if_pos (by decide), if_neg (by decide), add_zero]
    · rw [k, if_neg (by decide), if_pos (by decide), zero_add]
  have e' : (SD.bl.toList.map fun b => omK Reading.gl SD.om b *
      shareP Reading.gl Wo SD.S.v.y hv (wvOf Reading.gl c.wsLay M cl) b).sum = _ := e
  rw [split, e0] at e'
  exact add_left_cancel e'

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.pass_share
#print axioms ProofFile.Honest.K4.sum_claim
#print axioms ProofFile.Honest.K4.stackEnd_any
#print axioms ProofFile.Honest.K4.sides_made
#print axioms ProofFile.Honest.K4.pass0_sig
#print axioms ProofFile.Honest.K4.pass1_sig
