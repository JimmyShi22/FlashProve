-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/PanelTiesOf.lean: CONDITIONAL.

What is here. The ties of PanelShare.lean (`PanelTies`: the honest side's letters against the
library's, at one panel of the batched sumcheck) at three chosen letters: in `panelTies_of` from
public hypotheses alone, in `panelTies_at` from these and hval. The world is any in which the honest
value of each of the panel's own forms is the form's value: the world of the honest reads is one
(`readsWorld`, Johnson/Road/K4/C/StackTrue.lean: 0 under every slot); every world with the true
entries is another, whatever it holds under its slots: HvalOf.lean's `hval_true`. The never-sent
vectors are read off the honest tables of the gated products (`hvOfD`). The weight claims' vectors
are the library's, at the matrix of the honest input's words. So the three clauses on forms hold by
hval (in `panelTies_of` by that file's `reads_val`), the two on the never-sent vectors by the
choice, the two on the weight claims' vectors by OpenTabs.lean's `opens_are` and `opens_kk`.

  `hvOfD`   the never-sent vectors, read off the honest tables
  `PanelPub`   the public hypothesis on one panel
  `panelTies_at`   **the ties**, in any world in which the honest values of the panel's own forms
     are the forms' values
  `panelTies_of`   the same in the world of the honest reads

Limits. At the reading `Reading.gl`. PUBLIC HYPOTHESES, SHOWN IN OTHER FILES: `PanelUnits`
(Law/W/OpensOfUnits.lean: the claims' units at each panel; shown by
Johnson/Road/K4/C/UnitsOfClaim.lean's `panel_units`); `PanelPub` (shown by PanelPubOf.lean's
`panelPub_of`): a panel with the selector has a row for each routed expert, and its never-sent
vector is not number 0; the columns fit the bits; a panel whose whole A side is a never-sent vector
has number 0 and wy0 bits of a column. Beside them: the function that makes the job's data returns;
the verifier's list of claims returns at the honest side's environment with the challenges and the
end point laid in; the layout of the weights is what the verifier's `wsLayOf` returns for a model
with routed experts. That the vectors `hvOfD` are the library's vectors of the gated products is not
said here: GatedOf.lean's `hv0_gated` says it of number 0. No example of the hypotheses together is
known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PanelShare
import Johnson.Desc.ProofFile.Honest.K4.Law.W.OpensOfUnits
import Johnson.Road.K4.C.StackTrue

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading World WsClaim WsShape wsLayOf)
open OnBytes.Model.Layer (SBlk ClaimEnv)
open OnBytes.Road (wvOf)
open OnBytes.Road.K4.C (readsWorld reads_val)
open ProofFile.Honest.K4.W (PanelUnits)
open OnBytes.Desc.First.K4.Honest

/-- **The never-sent vectors, read off the honest tables of the gated products.** Number 0, at the
place row times 2 ^ wy0 plus column: the table under the lookup's token point. Number k from 1 on,
at a column: the routed experts' table under the second token sumcheck's end point. -/
noncomputable def hvOfD (SD : StackData) (wy0 k X : ℕ) : Cb.Gl.E :=
  if k = 0 then Reading.gl.val (SD.hZ.getD (X / 2 ^ wy0 * SD.S.v.y.Pf + X % 2 ^ wy0) zeroE)
  else Reading.gl.val (SD.hR.getD (SD.S.routedAt (k - 1) X) zeroE)

/-- **The public hypothesis on one panel.** This defines a hypothesis; the definition claims
nothing. -/
structure PanelPub (SD : StackData) (wy0 : ℕ) (b : SBlk) : Prop where
  /-- a panel with the selector has a row for each routed expert -/
  rows : b.tri = true → b.ni = SD.S.v.y.h.NE
  /-- the columns fit the bits -/
  cols : b.ny ≤ 2 ^ b.wy
  /-- the never-sent vector of a panel with the selector is not number 0 -/
  virtT : b.tri = true → ∀ k, b.virt = some k → k ≠ 0
  /-- a never-sent vector that is a whole A side is number 0, with wy0 bits of a column -/
  virtP : b.tri = false → ∀ k, b.virt = some k → k = 0 ∧ b.wy = wy0

/-- **THE TIES, IN ANY WORLD IN WHICH THE HONEST VALUE OF EACH OF THE PANEL's OWN FORMS IS THE
FORM's VALUE** (hval). CONDITIONAL: on every hypothesis named. -/
theorem panelTies_at {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}
    (h : stackData Q w p shownT = some SD) {rs : Array E} {cl : List WsClaim}
    (hcl : ({ SD.S.ce with rs := rs, rt := p.rt } : ClaimEnv).weightClaims SD.S.TS = some cl)
    {s : WsShape} {lk : ℕ} (hl : wsLayOf s true lk = .ok Q.P.wsLay)
    (U : PanelUnits SD Q.P.wsLay cl) (wy0 : ℕ) {b : SBlk} (hb : b ∈ SD.bl.toList)
    (B : PanelPub SD wy0 b) (Wo : World Cb.Gl.E)
    (hval : ∀ a, FormOf b a → ∀ y, valAff? SD.S.v SD.R (fun _ => zeroE) a = some y →
      Reading.gl.val y = a.value Reading.gl Wo) :
    PanelTies SD.S (fun a => valAff? SD.S.v SD.R (fun _ => zeroE) a) SD.F SD.hZ SD.hR
      Wo (hvOfD SD wy0) (wvOf Reading.gl Q.P.wsLay (wmOf w.w) cl) b where
  valX := fun yv y h1 hy => hval _ (Or.inl ⟨yv, h1, rfl⟩) y hy
  valA := fun A i yv f y h1 h2 hy => hval f (Or.inr (Or.inl ⟨A, i, yv, h1, h2⟩)) y hy
  valB := fun B i yv f y h1 h2 hy => hval f (Or.inr (Or.inr ⟨B, i, yv, h1, h2⟩)) y hy
  rows := B.rows
  cols := B.cols
  hvT := fun ht k hk yv _ => by
    unfold hvOfD
    rw [if_neg (B.virtT ht k hk)]
  hvP := fun ht k hk i yv _ hy => by
    obtain ⟨rfl, hw⟩ := B.virtP ht k hk
    have hy' : yv < 2 ^ wy0 := by
      rw [← hw]
      exact lt_of_lt_of_le hy B.cols
    unfold hvOfD
    rw [if_pos rfl, hw, div_grid i (2 ^ wy0) yv hy', mod_grid i (2 ^ wy0) yv hy']
  wvT := fun ht v0 h0 i yv _ hy => by
    obtain ⟨x, u, hx, hu, hE, hwk, hkk, _⟩ := (U b hb v0 h0).1 ht
    have r := opens_are h hcl hl v0 x u hx hu i yv (Or.inl ⟨hE, by rw [hwk]; exact hy⟩)
    rw [hwk] at r
    rw [← r]
    by_cases cy : yv < b.ny
    · rw [if_pos cy]
    · rw [if_neg cy]
      unfold at2
      rw [if_neg (by
        rw [opens_kk h hcl v0 x u hx hu]
        exact fun c => cy (Nat.lt_of_lt_of_le c hkk))]
      exact Reading.gl.zero
  wvP := fun ht v0 h0 i yv hi _ => by
    obtain ⟨x, u, hx, hu, hE, hkk⟩ := (U b hb v0 h0).2 ht i hi
    have r := opens_are h hcl hl (v0 + i) x u hx hu 0 yv (Or.inr ⟨hE, rfl⟩)
    rw [Nat.zero_mul, Nat.zero_add] at r
    rw [← r]
    by_cases cy : yv < b.ny
    · rw [if_pos cy]
    · rw [if_neg cy]
      unfold at2
      rw [if_neg (by
        rw [opens_kk h hcl (v0 + i) x u hx hu]
        exact fun c => cy (Nat.lt_of_lt_of_le c hkk))]
      exact Reading.gl.zero

/-- **THE TIES, FROM PUBLIC HYPOTHESES**, in the world of the honest reads. CONDITIONAL: on every
hypothesis named. -/
theorem panelTies_of {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}
    (h : stackData Q w p shownT = some SD) {rs : Array E} {cl : List WsClaim}
    (hcl : ({ SD.S.ce with rs := rs, rt := p.rt } : ClaimEnv).weightClaims SD.S.TS = some cl)
    {s : WsShape} {lk : ℕ} (hl : wsLayOf s true lk = .ok Q.P.wsLay)
    (U : PanelUnits SD Q.P.wsLay cl) (wy0 : ℕ) {b : SBlk} (hb : b ∈ SD.bl.toList)
    (B : PanelPub SD wy0 b) :
    PanelTies SD.S (fun a => valAff? SD.S.v SD.R (fun _ => zeroE) a) SD.F SD.hZ SD.hR
      (readsWorld SD.S.v SD.R) (hvOfD SD wy0) (wvOf Reading.gl Q.P.wsLay (wmOf w.w) cl) b :=
  panelTies_at h hcl hl U wy0 hb B _ fun a _ => reads_val SD.S.v SD.R a

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.panelTies_at
#print axioms ProofFile.Honest.K4.panelTies_of
