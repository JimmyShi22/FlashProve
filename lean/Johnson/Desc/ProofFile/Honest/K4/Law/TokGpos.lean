-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TokGpos.lean: CONDITIONAL.

What is here. The sum that the second token sumcheck's honest job claims is the library's `ClT`
(Inst/Model/FF/Objects.lean), from ties at each token.

  `sig1_true`   the library's Sig1 at `rPort` is its summand `Gpos`, where what stands for the shown
     values is true
  `zhAt`, `TokFits`   a token's corner, read; the ties at one token
  `tok_gpos`   one token's sum of products is `Gpos` at the token's corner
  `clT_total`   **ClT is the claimed sum**

Limits. At the reading `Reading.gl`. THE FULL SIZE ALONE: through TokSig.lean it calls the library's
`port_sig`, whose structure `SigFits` cannot be met at the small public example by that file's head.
ALL TIES AT A TOKEN ARE HYPOTHESES, gathered in `TokFits`: the honest side's reads and true end
values at the token's corner; `SigFits` there, with the corner for the end point; the verifier's
list of claims and its end function return; the ties of TripShare.lean at the second pass's panels;
the true end values read as the library's contractions of the cells at the corner, in the library's
ranges; the routed never-sent vectors are the library's vectors of the routed gated products there.
Beside them: what the library's law on the panel of queries and keys asks of sizes and shifts
(public); the token point reads as the library's; the tokens are two to the bits of a token; f = 2
fe. No example of the hypotheses together is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TokSig
import Johnson.Road.Rows.LayerEnds3Y
import Johnson.Road.FormsKeysSigG
import Johnson.Road.K4.GposSum
import Johnson.Road.K4.C.CornerKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE ceilLog2)
open OnBytes.Model (Reading World WsShape WsClaim eqTab)
open OnBytes.Model.Layer (Lay ClaimEnv stackEnd)
open OnBytes.Road (pt wvOf SigFits rPort sentAt withEnds sig1_gpos Cells Wm)
open OnBytes.Road.Rows (sig1_congr)
open OnBytes.Road.K4.C (sidesEnv firstOf jobTermsOn_whole)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell LW Sig1 Gpos ClT rdTrue hhU zpos layerR)
open OnBytes.Desc.First.K4.Honest

variable [scl : Scl]

/-- **The library's Sig1 at `rPort` is its summand at zh**, where what stands for the shown values
is the library's true contraction of the cells at zh, in the library's ranges, and the routed
never-sent vectors are the honest ones there. -/
theorem sig1_true (y : Lay) (sh : Array E) (hv : ℕ → ℕ → Cb.Gl.E) (D : Dim) (t : Cell → Cb.Gl.E)
    (tb : Tables) (L0 : ℕ) (w : ℕ → LW Cb.Gl.E) (z zh : ℕ → Cb.Gl.E) (C : D.ChOK)
    (hk : ∀ l, l < D.nl →
      (D.Pl l).kq = (D.Pl l).kk ∨ (16 ≤ (D.Pl l).kq ∧ 16 ≤ (D.Pl l).kk))
    (hH : ∀ l', l' < D.ne → ∀ j, j < D.fe → hv (1 + l') j = hhU D t (2 * l' + 1) (D.fe + j) zh)
    (hR : ∀ ν, ν < 2 * D.nl → sentAt Reading.gl sh ν =
      (rdTrue D t z zh (fun l j => hv 0 (l * 2 ^ ceilLog2 y.h.f + j)) fun l' j => hv (1 + l') j).R2
        ν)
    (hsc : ∀ l', l' < D.ne → sentAt Reading.gl sh (y.NN * y.Lam + l') =
      (rdTrue D t z zh (fun l j => hv 0 (l * 2 ^ ceilLog2 y.h.f + j))
        fun l' j => hv (1 + l') j).sc2 l')
    (hsel : ∀ l' e, l' < D.ne → e < D.nx →
      sentAt Reading.gl sh (y.NN * y.Lam + y.LamM + l' * y.h.NE + e) =
        (rdTrue D t z zh (fun l j => hv 0 (l * 2 ^ ceilLog2 y.h.f + j))
          fun l' j => hv (1 + l') j).sel2 l' e) :
    Sig1 D (rPort Reading.gl y sh hv D t z zh) tb L0 w z zh = Gpos D t tb L0 w z zh := by
  unfold rPort
  rw [sig1_congr D _ tb L0 w z zh hR hsc hsel]
  exact sig1_gpos D t tb L0 w z zh (fun l j => hv 0 (l * 2 ^ ceilLog2 y.h.f + j))
    (fun l' j => hv (1 + l') j) C hk hH

/-- Token number i's corner, read: the honest side's array of the token's bits, the highest
first. -/
noncomputable abbrev zhAt (S : OnBytes.Desc.First.K4.Honest.Sides) (i : ℕ) : ℕ → Cb.Gl.E :=
  pt Reading.gl (OnBytes.Desc.First.K4.Honest.bitsOf S.v.y.h.lt i)

/-- **The ties at token number i.** The second token sumcheck's end point is the token's corner,
read: in these letters the library's `sigFits_of_look` (Johnson/Road/FormsKeysCaller.lean) ends;
SigOfPub.lean calls it. -/
def TokFits (S : OnBytes.Desc.First.K4.Honest.Sides) (D : Dim) (t : Cell → Cb.Gl.E) (tb : Tables)
    (L0 lk : ℕ) (M : Wm Cb.Gl.E) (z : ℕ → Cb.Gl.E) (i : ℕ) : Prop :=
  ∃ (R : Reads) (sh : Array E) (Wo : World Cb.Gl.E) (c : ClaimEnv)
    (h' : OnBytes.Model.Layer.Shape) (pc : List (List String)) (s : WsShape) (cc : Cells Cb.Gl.E)
    (low ζ : ℕ → Cb.Gl.E) (hv : ℕ → ℕ → Cb.Gl.E) (cl : List WsClaim),
    S.readsTok (OnBytes.Desc.First.K4.Honest.bitsOf S.v.y.h.lt i) = some R ∧
    endsOn S R = some sh ∧
    SigFits Reading.gl Wo (sidesEnv S sh) c h' pc s D lk L0 cc t low z (zhAt S i) ζ tb ∧
    c.weightClaims S.TS = some cl ∧
    (∀ bl places, S.panels sh = some (bl, places) → ∃ rs om H1 V lam sA sB s',
      stackEnd S.v.y bl rs lam om H1 V sA sB = some s') ∧
    (∀ bl places, S.panels sh = some (bl, places) → ∀ b ∈ bl.toList, b.claim = 1 →
      TripTies S (fun a => valAff? S.v R (fun _ => zeroE) a)
        (S.weights (eqTab (OnBytes.Desc.First.K4.Honest.bitsOf S.v.y.h.lt i)))
        (fun lm yv => S.hh.getD (S.routedAt lm yv * S.v.y.T + i) zeroE) Wo hv
        (wvOf Reading.gl c.wsLay M cl) b) ∧
    (∀ l', l' < D.ne → ∀ j, j < D.fe →
      hv (1 + l') j = hhU D t (2 * l' + 1) (D.fe + j) (zhAt S i)) ∧
    (∀ ν, ν < 2 * D.nl → sentAt Reading.gl sh ν =
      (rdTrue D t z (zhAt S i) (fun l j => hv 0 (l * 2 ^ ceilLog2 S.v.y.h.f + j))
        fun l' j => hv (1 + l') j).R2 ν) ∧
    (∀ l', l' < D.ne → sentAt Reading.gl sh (S.v.y.NN * S.v.y.Lam + l') =
      (rdTrue D t z (zhAt S i) (fun l j => hv 0 (l * 2 ^ ceilLog2 S.v.y.h.f + j))
        fun l' j => hv (1 + l') j).sc2 l') ∧
    ∀ l' e, l' < D.ne → e < D.nx →
      sentAt Reading.gl sh (S.v.y.NN * S.v.y.Lam + S.v.y.LamM + l' * S.v.y.h.NE + e) =
        (rdTrue D t z (zhAt S i) (fun l j => hv 0 (l * 2 ^ ceilLog2 S.v.y.h.f + j))
          fun l' j => hv (1 + l') j).sel2 l' e

/-- **One token's sum of products is the library's summand at the token's corner.** -/
theorem tok_gpos {S : OnBytes.Desc.First.K4.Honest.Sides} {rows : TokRows}
    (hrows : tokenRows S = some rows)
    (hsame : (rows.all fun x => x.2.map (·.1) == (firstOf rows).map (·.1)) = true) {i : ℕ}
    (hi : i < S.v.y.T) (hTS : S.TS = [0, 1, 2, 5]) {D : Dim} {t : Cell → Cb.Gl.E} {tb : Tables}
    {L0 lk : ℕ} {M : Wm Cb.Gl.E} {z : ℕ → Cb.Gl.E} (hlt : D.lT = S.v.y.h.lt)
    (hi2 : i < 2 ^ D.lT) (C : D.ChOK)
    (hk : ∀ l, l < D.nl →
      (D.Pl l).kq = (D.Pl l).kk ∨ (16 ≤ (D.Pl l).kq ∧ 16 ≤ (D.Pl l).kk))
    (H : TokFits S D t tb L0 lk M z i) :
    tokSum rows i =
      Gpos D t tb L0 (fun l => layerR D.P lk M (L0 + l)) z (Blocks.cubePt D.lT i) := by
  obtain ⟨R, sh, Wo, c, h', pc, s, cc, low, ζ, hv, cl, hR, hsh, SF, hc, hst, T, hH, e1, e2, e3⟩ :=
    H
  rw [tok_sig hrows hsame hi hR hsh SF M hv hTS hc hst T,
    sig1_true S.v.y sh hv D t tb L0 _ z _ C hk hH e1 e2 e3]
  refine OnBytes.Road.K4.Gpos_congr D t tb L0 _ z fun v => ?_
  rw [Blocks.ext_cubePt D.lT v hi2]
  show Blocks.ext D.lT v (pt Reading.gl (OnBytes.Desc.First.K4.Honest.bitsOf S.v.y.h.lt i)) = v i
  rw [← hlt]
  exact OnBytes.Road.K4.C.ext_corner D.lT v hi2

/-- **THE LIBRARY's ClT IS THE SUM THAT THE SECOND TOKEN SUMCHECK's HONEST JOB CLAIMS.**
CONDITIONAL: on every hypothesis named. THE FULL SIZE ALONE. -/
theorem clT_total {S : OnBytes.Desc.First.K4.Honest.Sides} {J : Job} (hJ : jobTermsOn S = some J)
    (hz : S.zt.size = S.v.y.h.lt) (hT : S.v.y.T = 2 ^ S.v.y.h.lt) (hTS : S.TS = [0, 1, 2, 5])
    (D : Dim) (t : Cell → Cb.Gl.E) (tb : Tables) (L0 lk : ℕ) (M : Wm Cb.Gl.E) (z : ℕ → Cb.Gl.E)
    (hf : D.f = 2 * D.fe) (hlt : D.lT = S.v.y.h.lt)
    (hzp : ∀ j, j < D.lT → zpos D z j = pt Reading.gl S.zt j) (C : D.ChOK)
    (hk : ∀ l, l < D.nl →
      (D.Pl l).kq = (D.Pl l).kk ∨ (16 ≤ (D.Pl l).kq ∧ 16 ≤ (D.Pl l).kk))
    (H : ∀ i, i < 2 ^ D.lT → TokFits S D t tb L0 lk M z i) :
    ClT D t tb L0 (fun l => layerR D.P lk M (L0 + l)) z = Reading.gl.val J.cube.total := by
  obtain ⟨rows0, h0, _, hsame, _, _⟩ := jobTermsOn_whole hJ
  refine terms_clT hJ hz D t tb L0 _ z hf hlt hzp fun rows hrows i hi => ?_
  obtain rfl : rows0 = rows := Option.some.inj (h0.symm.trans hrows)
  exact tok_gpos hrows hsame (by rw [hT, ← hlt]; exact hi) hTS hlt hi C hk (H i hi)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.sig1_true
#print axioms ProofFile.Honest.K4.tok_gpos
#print axioms ProofFile.Honest.K4.clT_total
