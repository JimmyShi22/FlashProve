-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/PassOf.lean: CONDITIONAL.

What is here. PassSig.lean's `pass0_sig` (the honest first pass's sum is the library's `Sig0`) with
its ties at the panels laid in from PanelTiesOf.lean's `panelTies_at` and PanelPubOf.lean's
`panelPub_of`. So of the ties between the two sides' letters at the panels one is left as a
hypothesis, hval (HvalOf.lean has it, conditionally); what else is left on the panels is public. The
letters are fixed but for the world, which is any in which the honest value of each form of a
first-pass panel is the form's value (hval): the never-sent vectors are read off the honest tables,
the matrix is that of the honest input's words, the claims are the verifier's function's at the
honest side's own environment.

  `sides_lay`   the honest side's environment has the public layout of the weights
  `pass0_pub`   **the first pass**

Limits. At the reading `Reading.gl`. THE FULL SIZE ALONE: the library's structure `SigFits`
(Johnson/Road/FormsKeysPortSig.lean) is a hypothesis, AT THE WORLD Wo OF hval; by that file's head
it cannot be met at the small public example. PUBLIC HYPOTHESES: `PanelUnits`
(Law/W/OpensOfUnits.lean; Johnson/Road/K4/C/UnitsOfClaim.lean has it from the layout); the calls of
the second walk are 0, 1, 2, 5; the layout of the weights is what the verifier's `wsLayOf` returns
for a model with routed experts. Beside them: three functions return; the first of the two weights
reads 1. The library's sum stands at its structure `rPort`: it is not the library's true structure.
No example of the hypotheses together is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PassSig
import Johnson.Desc.ProofFile.Honest.K4.Law.PanelPubOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE ceilLog2)
open OnBytes.Model (Reading World WsShape WsClaim wsLayOf)
open OnBytes.Model.Layer (ClaimEnv StackEnd stackEnd)
open OnBytes.Road (SigFits rPort)
open OnBytes.Road.K4.C (sidesEnv)
open ProofFile.Honest.K4.W (PanelUnits)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Sig0 layerR)
open OnBytes.Desc.First.K4.Honest

/-- The honest side's environment has the public layout of the weights. -/
theorem sides_lay {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}
    (h : stackData Q w p shownT = some SD) : SD.S.ce.wsLay = Q.P.wsLay := by
  obtain ⟨S, hS, hD⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨eS, _⟩ := stackDataOn_open hD
  subst eS
  obtain ⟨_, _, _, _, _, e1, _, _⟩ := sides_open hS
  exact e1

variable [scl : Scl]

/-- **THE FIRST PASS's SUM IS THE LIBRARY's Sig0.** CONDITIONAL: on every hypothesis named; on the
panels these are hval and a public one. THE FULL SIZE ALONE (SF). -/
theorem pass0_pub {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}
    (h : stackData Q w p shownT = some SD) {rs : Array E} {cl : List WsClaim}
    (hcl : ({ SD.S.ce with rs := rs, rt := p.rt } : ClaimEnv).weightClaims SD.S.TS = some cl)
    {sw : WsShape} {lkw : ℕ} (hl : wsLayOf sw true lkw = .ok Q.P.wsLay)
    (U : PanelUnits SD Q.P.wsLay cl) (Wo : World Cb.Gl.E)
    (hval : ∀ b ∈ SD.bl.toList, b.claim = 0 → ∀ a, FormOf b a → ∀ y,
      valAff? SD.S.v SD.R (fun _ => zeroE) a = some y → Reading.gl.val y = a.value Reading.gl Wo)
    {h' : OnBytes.Model.Layer.Shape} {pc : List (List String)} {s : WsShape} {D : Dim}
    {lk L0 : ℕ} {cc : OnBytes.Road.Cells Cb.Gl.E} {t : Cell → Cb.Gl.E}
    {low z zh ζ : ℕ → Cb.Gl.E} {tb : Tables}
    (SF : SigFits Reading.gl Wo (sidesEnv SD.S shownT)
      { SD.S.ce with rs := rs, rt := p.rt } h' pc s D lk L0 cc t low z zh ζ tb)
    (hTS : SD.S.TS = [0, 1, 2, 5]) (hom : Reading.gl.val (SD.om.getD 0 zeroE) = 1)
    {rs' H1 V om : Array E} {lam : ℕ} {sA sB : E} {s' : StackEnd}
    (hst : stackEnd SD.S.v.y SD.bl rs' lam om H1 V sA sB = some s') :
    passSum SD 0 = Sig0 D
      (rPort Reading.gl SD.S.v.y shownT (hvOfD SD (ceilLog2 SD.S.v.y.h.f)) D t z zh) tb L0
      (fun l => layerR D.P lk (wmOf w.w) (L0 + l)) z zh :=
  pass0_sig h SF (wmOf w.w) (hvOfD SD (ceilLog2 SD.S.v.y.h.f)) hTS hcl hom hst fun b hb h0 => by
    show PanelTies _ _ _ _ _ _ _ (OnBytes.Road.wvOf Reading.gl SD.S.ce.wsLay (wmOf w.w) cl) b
    rw [sides_lay h]
    exact panelTies_at h hcl hl U _ hb (panelPub_of h b hb) Wo (hval b hb h0)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.sides_lay
#print axioms ProofFile.Honest.K4.pass0_pub
