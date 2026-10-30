-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/JoinPub.lean: CONDITIONAL.

What is here. The hypothesis `JoinWorth` (StackStart.lean: the first pass of the batched sumcheck is
the lookup's join) in one statement, with these payers laid in: JoinLib.lean's `joinWorth_lib`;
PassOf.lean's `pass0_pub` for the first pass's sum; TokGpos.lean's `clT_total` over TokFitsOf.lean's
`tokFits_of` for the second token sumcheck's claimed sum; Johnson/Road/K4/C/UnitsOfClaim.lean's
`panel_units` for the claims' units at the panels. No tie between the honest side's tables of the
weights and the library's vectors is left, and no public clause on a panel: these are shown. The
matrix is that of the honest input's words; the never-sent vectors are read off the honest tables.
NOT LAID IN, though they lie in this folder: GatedOf.lean's `hv0_gated` (it is hH) and `hhAt_gated`
(the second clause of `TokLeft`); HvalOf.lean's `hval_true` (hval); SigOfPub.lean's `sig_of_pub`
(SF).

  `TokAll`   what is left at the tokens
  `joinWorth_pub`   **the one statement**

Limits. At the reading `Reading.gl`. THE FULL SIZE ALONE (the library's `SigFits`; the premise hp
has its payer there alone). NOTHING NEW IS SHOWN: one call of each. LEFT AS HYPOTHESES, ALL:
  on the lookup: (B1) its own part is worth 0 at the library's key vectors;
  on the world W of the start form: the slot of the claimed sum holds the honest job's total (hσ);
  each of the eight factors is worth what the library's `joinPart_keyVec'` concludes (hp, hlen); the
  hearing holds the second token sumcheck's structure (hT);
  on the lookup's points and weights: hz, hwc, hzp, hzs;
  on a world Wo of the first pass's panels: `SigFits` (SF); the honest value of each form of such a
  panel is the form's value there (hval);
  at each token (`TokAll`): a world with `SigFits` and the like of hval for the second pass's
  panels; the true end values are the library's contractions; the honest table of the gated products
  is the library's vector; the verifier's function for the claims returns;
  on the honest table of the gated products under the lookup's token point: it is the library's
  vector (hH);
  public: the layout of the weights is what the verifier's `wsLayOf` returns for a model with routed
  experts, with two equations and four inequalities between its shape and the layer sub-proof's; the
  calls of the second walk are 0, 1, 2, 5; sizes (hf2, hlt, hTT, hcap, hfe2, C, hk);
  returns: the job's data (h), the honest job of the second token sumcheck (hJ), the verifier's
  claims (hcl) and its end function (hst, hstT); the first of the two weights reads 1 (hom).
No example of the hypotheses together is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.JoinLib
import Johnson.Desc.ProofFile.Honest.K4.Law.PassOf
import Johnson.Desc.ProofFile.Honest.K4.Law.TokFitsOf
import Johnson.Road.K4.C.StackSidesOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE ceilLog2)
open OnBytes.Model (Reading Aff World Tsc WsShape WsClaim wsLayOf)
open OnBytes.Model.Layer (Heard ClaimEnv StackEnd stackEnd)
open OnBytes.Road (pt padOf SigFits elP ACCP TSP)
open OnBytes.Road.K4.C (sidesEnv panel_units stack_open jobTermsOn_whole)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell wc famsIn fSh hhU zpos zc aC keyVec layerR)
open OnBytes.Desc.First.K4.Honest

variable [scl : Scl]

/-- **What is left at token number i.** This defines a hypothesis; the definition claims nothing. -/
def TokAll (S : OnBytes.Desc.First.K4.Honest.Sides) (D : Dim) (t : Cell → Cb.Gl.E) (tb : Tables)
    (L0 lk : ℕ) (z : ℕ → Cb.Gl.E) (i : ℕ) : Prop :=
  ∃ (rs : Array E) (cl : List WsClaim) (Wo : World Cb.Gl.E),
    ({ S.ce with rs := rs, rt := OnBytes.Desc.First.K4.Honest.bitsOf S.v.y.h.lt i } :
      ClaimEnv).weightClaims S.TS = some cl ∧
    (∀ R sh bl places,
      S.readsTok (OnBytes.Desc.First.K4.Honest.bitsOf S.v.y.h.lt i) = some R →
      S.panels sh = some (bl, places) → ∀ b ∈ bl.toList, b.claim = 1 → ∀ a, FormOf b a → ∀ y,
      valAff? S.v R (fun _ => zeroE) a = some y → Reading.gl.val y = a.value Reading.gl Wo) ∧
    ∀ R sh, S.readsTok (OnBytes.Desc.First.K4.Honest.bitsOf S.v.y.h.lt i) = some R →
      endsOn S R = some sh →
      TokLeft S { S.ce with rs := rs, rt := OnBytes.Desc.First.K4.Honest.bitsOf S.v.y.h.lt i } D t
        tb L0 lk z i Wo sh

/-- **`JoinWorth`, WITH FIVE PAYERS LAID IN.** CONDITIONAL: on every hypothesis named. THE FULL SIZE
ALONE. W: the world of the start form; Wo: a world of the first pass's panels. -/
theorem joinWorth_pub {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}
    (h : stackData Q w p shownT = some SD) {J : Job} (hJ : jobTermsOn SD.S = some J)
    {rs : Array E} {cl : List WsClaim}
    (hcl : ({ SD.S.ce with rs := rs, rt := p.rt } : ClaimEnv).weightClaims SD.S.TS = some cl)
    {sw : WsShape} {lkw : ℕ} (hl : wsLayOf sw true lkw = .ok Q.P.wsLay)
    (hd : sw.d = SD.S.v.y.h.d) (hfe : sw.fe = SD.S.v.y.h.fe) (hdq : sw.dq ≤ SD.S.v.y.dq)
    (hf : sw.f ≤ SD.S.v.y.h.f) (hfef : sw.fe ≤ SD.S.v.y.h.f) (hNE : sw.NE ≤ SD.S.v.y.h.NE)
    (Wo : World Cb.Gl.E)
    (hval : ∀ b ∈ SD.bl.toList, b.claim = 0 → ∀ a, FormOf b a → ∀ y,
      valAff? SD.S.v SD.R (fun _ => zeroE) a = some y → Reading.gl.val y = a.value Reading.gl Wo)
    {h' : OnBytes.Model.Layer.Shape} {pc : List (List String)} {s : WsShape} {D : Dim}
    {lk L0 : ℕ} {cc : OnBytes.Road.Cells Cb.Gl.E} {t : Cell → Cb.Gl.E}
    {low z zh ζ0 : ℕ → Cb.Gl.E} {tb : Tables}
    (SF : SigFits Reading.gl Wo (sidesEnv SD.S shownT)
      { SD.S.ce with rs := rs, rt := p.rt } h' pc s D lk L0 cc t low z zh ζ0 tb)
    (hTS : SD.S.TS = [0, 1, 2, 5]) (hom : Reading.gl.val (SD.om.getD 0 zeroE) = 1)
    {rs' H1 V om : Array E} {lam : ℕ} {sA sB : E} {s' : StackEnd}
    (hst : stackEnd SD.S.v.y SD.bl rs' lam om H1 V sA sB = some s')
    (hstT : ∀ sh bl places, SD.S.panels sh = some (bl, places) → ∃ rs om H1 V lam sA sB s',
      stackEnd SD.S.v.y bl rs lam om H1 V sA sB = some s')
    (hzs : SD.S.zt.size = SD.S.v.y.h.lt) (hTT : SD.S.v.y.T = 2 ^ SD.S.v.y.h.lt)
    (hf2 : D.f = 2 * D.fe) (hlt : D.lT = SD.S.v.y.h.lt)
    (hzp : ∀ j, j < D.lT → zpos D z j = pt Reading.gl SD.S.zt j) (C : D.ChOK)
    (hk : ∀ l, l < D.nl →
      (D.Pl l).kq = (D.Pl l).kk ∨ (16 ≤ (D.Pl l).kq ∧ 16 ≤ (D.Pl l).kk))
    (Htok : ∀ i, i < 2 ^ D.lT → TokAll SD.S D t tb L0 lk z i)
    (ζ : Fin 8 → ℕ → Cb.Gl.E) (W : World Cb.Gl.E) (H : Heard) (parts : List Aff) {tT : Tsc}
    (hT : H.tT = some tT) (hlen : parts.length = 8) (alpha theta : E)
    (hp : ∀ (q : Fin 8) (f : Aff), parts[q.val]? = some f →
      f.value Reading.gl W = Reading.gl.val alpha - (q.val : Cb.Gl.E) * Reading.gl.val theta -
        Blocks.ext (aC D q)
          (keyVec D t tb L0 (fun l => layerR D.P lk (wmOf w.w) (L0 + l)) q) (ζ q) +
        TSP D t tb L0 (fun l => layerR D.P lk (wmOf w.w) (L0 + l)) q (ζ q) +
        ∑ l ∈ Finset.range D.nl, elP D (ζ q) l * ((famsIn q l).map fun s =>
          ACCP D t (fun l => layerR D.P lk (wmOf w.w) (L0 + l)) (ζ q) s l).sum)
    (hcap : D.lT ≤ D.cap) (hfe2 : D.fe ≤ D.f)
    (hz : ∀ q : Fin 8, q ∈ [(0 : Fin 8), 1, 2, 5] → ∀ j, j < aC D q → ζ q j = zc D z q j)
    (hwc : ∀ q : Fin 8, q ∈ [(0 : Fin 8), 1, 2, 5] →
      Reading.gl.val (H.fo.e.getD q.val zeroE) = wc D z q)
    (hH : ∀ l, l < D.nl → ∀ j, j < fSh D l →
      hvOfD SD (ceilLog2 SD.S.v.y.h.f) 0 (l * 2 ^ ceilLog2 SD.S.v.y.h.f + j) =
        hhU D t l j (zpos D z))
    (hB1 : (∑ q : Fin 8, Reading.gl.val (H.fo.e.getD q.val zeroE) *
        (Reading.gl.val alpha - (q.val : Cb.Gl.E) * Reading.gl.val theta -
          Blocks.ext (aC D q)
            (keyVec D t tb L0 (fun l => layerR D.P lk (wmOf w.w) (L0 + l)) q) (ζ q))) +
      Reading.gl.val (padOf H) - H.fo.cEnd.value Reading.gl W = 0)
    (hσ : W.slot tT.sCl = Reading.gl.val J.cube.total) :
    JoinWorth H tT parts W SD := by
  have hS := (stack_open h).1
  obtain ⟨rows, hrows, _⟩ := jobTermsOn_whole hJ
  have Hf : ∀ i, i < 2 ^ D.lT → TokFits SD.S D t tb L0 lk (wmOf w.w) z i := by
    intro i hi
    obtain ⟨rsi, cli, Wi, c1, c2, c3⟩ := Htok i hi
    exact tokFits_of hS hrows (by rw [hTT, ← hlt]; exact hi) c1 hl hd hfe hdq hf hfef hstT Wi c2 c3
  exact joinWorth_lib SD.S.v.y shownT (hvOfD SD (ceilLog2 SD.S.v.y.h.f)) D t tb L0
    (fun l => layerR D.P lk (wmOf w.w) (L0 + l)) z zh ζ W H parts hT hlen alpha theta hp hcap hfe2
    hz hwc hH hB1
    ((clT_total hJ hzs hTT hTS D t tb L0 lk (wmOf w.w) z hf2 hlt hzp C hk Hf).trans hσ.symm)
    (pass0_pub h hcl hl (panel_units h hcl hl hd hfe hdq hf hfef hNE) Wo hval SF hTS hom hst)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.joinWorth_pub
