-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TokFitsOf.lean: CONDITIONAL.

What is here. The ties at one token (`TokFits`, TokGpos.lean) with three of their ten clauses paid:
the reads, the true end values and the ties at the panels. The honest side's reads and true end
values at the token's corner come from the return of `tokenRows`. The ties `TripTies` at the second
pass's panels come from TripTiesOf.lean's `tripTies_at`, PanelPubOf.lean's `tripPub_of` and
UnitsAtOf.lean's `unitsAt_of`. The letters are fixed but for the world Wo, which is any in which the
honest value, on the reads at the corner, of each form of a second-pass panel is the form's value
(hval; HvalOf.lean's `hval_true` has it in every world with the true entries): the never-sent
vectors are read off the honest table of the gated products at that token, the matrix is that of the
honest input's words, the claims are the verifier's function's at the honest side's own environment
with the corner laid in.

  `TokLeft`   what is left at a token
  `tokFits_of`   **the ties at a token**

Limits. At the reading `Reading.gl`. For a token's number below the number of tokens. LEFT AS
HYPOTHESES, gathered in `TokLeft`: the library's `SigFits` at the world Wo (THE FULL SIZE ALONE). IT
ASKS THE TRUTH OF THE TABLES AT THE LOOKUP's POINT TOO: so Wo cannot be the world of the reads at
the corner alone, which hold no such table: its entries must be true at all named points, with the
corner for the second token sumcheck's end point; the true end values read as the library's
contractions of the cells at the corner (three clauses); the honest table of the gated products at
that token reads as the library's vector of the routed gated products at the corner. Beside them:
the verifier's function for the claims and its end function return; the layout of the weights is
what the verifier's `wsLayOf` returns for a model with routed experts, with two equations and three
inequalities between its shape and the layer sub-proof's (public). TokAtY.lean's `tokAll_y` pays
`TokLeft` from a public structure at the corner. No example of the hypotheses together is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TokGpos
import Johnson.Desc.ProofFile.Honest.K4.Law.PanelPubOf
import Johnson.Desc.ProofFile.Honest.K4.Law.UnitsAtOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE ceilLog2)
open OnBytes.Model (Reading World WsShape WsClaim wsLayOf)
open OnBytes.Model.Layer (ClaimEnv stackEnd)
open OnBytes.Road (SigFits sentAt)
open OnBytes.Road.K4.C (sidesEnv tokenRows_trips)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell rdTrue hhU)
open OnBytes.Desc.First.K4.Honest

variable [scl : Scl]

/-- The honest table of the gated products at token i: the layer's number among those with routed
experts, the column. -/
def hhAt (S : OnBytes.Desc.First.K4.Honest.Sides) (i lm yv : ℕ) : E :=
  S.hh.getD (S.routedAt lm yv * S.v.y.T + i) zeroE

/-- **What is left at token number i**, in a world Wo and at the true end values sh there. This
defines a hypothesis; the definition claims nothing. -/
def TokLeft (S : OnBytes.Desc.First.K4.Honest.Sides) (c : ClaimEnv) (D : Dim)
    (t : Cell → Cb.Gl.E) (tb : Tables) (L0 lk : ℕ) (z : ℕ → Cb.Gl.E) (i : ℕ)
    (Wo : World Cb.Gl.E) (sh : Array E) : Prop :=
  (∃ (h' : OnBytes.Model.Layer.Shape) (pc : List (List String)) (s : WsShape)
      (cc : OnBytes.Road.Cells Cb.Gl.E) (low ζ : ℕ → Cb.Gl.E),
    SigFits Reading.gl Wo (sidesEnv S sh) c h' pc s D lk L0 cc t low z
      (zhAt S i) ζ tb) ∧
  (∀ l', l' < D.ne → ∀ j, j < D.fe →
    Reading.gl.val (hhAt S i l' j) = hhU D t (2 * l' + 1) (D.fe + j) (zhAt S i)) ∧
  (∀ ν, ν < 2 * D.nl → sentAt Reading.gl sh ν =
    (rdTrue D t z (zhAt S i)
      (fun l j => hvOfH (hhAt S i) 0 (l * 2 ^ ceilLog2 S.v.y.h.f + j))
      fun l' j => hvOfH (hhAt S i) (1 + l') j).R2 ν) ∧
  (∀ l', l' < D.ne → sentAt Reading.gl sh (S.v.y.NN * S.v.y.Lam + l') =
    (rdTrue D t z (zhAt S i)
      (fun l j => hvOfH (hhAt S i) 0 (l * 2 ^ ceilLog2 S.v.y.h.f + j))
      fun l' j => hvOfH (hhAt S i) (1 + l') j).sc2 l') ∧
  ∀ l' e, l' < D.ne → e < D.nx →
    sentAt Reading.gl sh (S.v.y.NN * S.v.y.Lam + S.v.y.LamM + l' * S.v.y.h.NE + e) =
      (rdTrue D t z (zhAt S i)
        (fun l j => hvOfH (hhAt S i) 0 (l * 2 ^ ceilLog2 S.v.y.h.f + j))
        fun l' j => hvOfH (hhAt S i) (1 + l') j).sel2 l' e

/-- **THE TIES AT A TOKEN.** CONDITIONAL: on every hypothesis named. THE FULL SIZE ALONE (`SigFits`
in `TokLeft`). -/
theorem tokFits_of {Q : K4Pub} {w : K4In} {p : Pts} {S : OnBytes.Desc.First.K4.Honest.Sides}
    (hS : OnBytes.Desc.First.K4.Honest.Sides.of Q w p = some S) {rows : TokRows}
    (hrows : tokenRows S = some rows) {i : ℕ} (hi : i < S.v.y.T) {rs : Array E}
    {cl : List WsClaim}
    (hcl : ({ S.ce with rs := rs, rt := OnBytes.Desc.First.K4.Honest.bitsOf S.v.y.h.lt i } :
      ClaimEnv).weightClaims S.TS = some cl)
    {sw : WsShape} {lkw : ℕ} (hl : wsLayOf sw true lkw = .ok Q.P.wsLay) (hd : sw.d = S.v.y.h.d)
    (hfe : sw.fe = S.v.y.h.fe) (hdq : sw.dq ≤ S.v.y.dq) (hf : sw.f ≤ S.v.y.h.f)
    (hfef : sw.fe ≤ S.v.y.h.f)
    (hst : ∀ sh bl places, S.panels sh = some (bl, places) → ∃ rs om H1 V lam sA sB s',
      stackEnd S.v.y bl rs lam om H1 V sA sB = some s')
    {D : Dim} {t : Cell → Cb.Gl.E} {tb : Tables} {L0 lk : ℕ} {z : ℕ → Cb.Gl.E}
    (Wo : World Cb.Gl.E)
    (hval : ∀ R sh bl places,
      S.readsTok (OnBytes.Desc.First.K4.Honest.bitsOf S.v.y.h.lt i) = some R →
      S.panels sh = some (bl, places) → ∀ b ∈ bl.toList, b.claim = 1 → ∀ a, FormOf b a → ∀ y,
      valAff? S.v R (fun _ => zeroE) a = some y → Reading.gl.val y = a.value Reading.gl Wo)
    (Lf : ∀ R sh, S.readsTok (OnBytes.Desc.First.K4.Honest.bitsOf S.v.y.h.lt i) = some R →
      endsOn S R = some sh →
      TokLeft S { S.ce with rs := rs, rt := OnBytes.Desc.First.K4.Honest.bitsOf S.v.y.h.lt i } D t
        tb L0 lk z i Wo sh) :
    TokFits S D t tb L0 lk (wmOf w.w) z i := by
  obtain ⟨R, sh, tr, hR, hsh, _, _⟩ := tokenRows_trips hrows hi
  obtain ⟨⟨h', pc, s, cc, low, ζ, SF⟩, hH, e1, e2, e3⟩ := Lf R sh hR hsh
  obtain ⟨_, _, _, _, _, ew, _, _⟩ := sides_open hS
  refine ⟨R, sh, Wo, _, h', pc, s, cc, low, ζ, hvOfH (hhAt S i), cl, hR, hsh, SF,
    hcl, hst sh, fun bl places hp b hb h1 => ?_, fun l' hl' j hj => ?_, e1, e2, e3⟩
  · show TripTies _ _ _ _ _ _ (OnBytes.Road.wvOf Reading.gl S.ce.wsLay (wmOf w.w) cl) b
    rw [ew]
    exact tripTies_at hS hcl hl R Wo (hhAt S i) (hval R sh bl places hR hp b hb h1)
      (unitsAt_of hS hp hcl hl hd hfe hdq hf hfef b hb) (tripPub_of hp b hb)
  · show Reading.gl.val (hhAt S i (1 + l' - 1) j) = _
    rw [Nat.add_sub_cancel_left]
    exact hH l' hl' j hj

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.tokFits_of
