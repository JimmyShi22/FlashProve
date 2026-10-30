-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/EmbEnds.lean: the embedding's identity of the first group of layers, from the
verifier's claim on the embedding's value and the merge's in-claim on it.

In the first group the prover sends one hidden value, the embedding's value, under a slot sVE. Two
claims name it. claimEmbedding (OnBytes/Model/Layer.lean) says that it is the stream that comes in,
at a point of features and positions. The last of the merge's weight claims (claimE,
OnBytes/Model/LayerPanels.lean) says that it is a sum in the committed matrix of weights. The
library's identity Idn.j11 (Inst/Model/FF/Trace.lean) says that the stream that comes in is the
embedding of the tokens, at every feature and position.

Main definitions.
 - embSide: a function of (feature, position), summed under the weights in which claimEmbedding's
   form sums the stream: the blocks' weights, the equality weights inside a block, the equality
   weights of the positions.
 - EmbWeight: a named hypothesis. The sum that the claim claimE speaks of is embSide of the
   library's embedding of the tokens. No theorem concludes it yet. (Meaning.Emb.embWeight in
   Johnson/Meaning/EmbWeightProof.lean concludes it, for any matrix and any array of tokens, at the
   library's reference parameters, of every claim that claimE returns, under public premises: on the
   layout of the weights, on seven numbers of the sub-proof's layout and on the lengths of two
   points. That the matrix is the committed one and that the array holds the request's tokens is not
   claimed there.)
 - EmbStep: a named premise at one point: if embSide of the defects of Idn.j11 is 0 at this point,
   every defect is 0. It is no law for all points: for defects that are not all 0 it fails at some
   points, and what is true of all points is a count of these. Asked for all points it would be
   false, so it belongs in no record of hypotheses; emb_field, which takes it, is a coarse form.
Main theorems. emb_side: embSide of the defects of Idn.j11 is 0, from claimEmbedding's claim, the
merge's in-claim on the slot sVE and EmbWeight. emb_field: the identities Idn.j11, from emb_side and
EmbStep.

What is not claimed. EmbWeight and EmbStep are hypotheses. All else is an identity in a world. The
program does not import this file.


-/
import Johnson.Road.FormsKeysIdnL

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading World Aff WsLay WsClaim eqTab)
open OnBytes.Model.Layer (Env)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell Idn idnVal xS)
open Blocks (ext)

variable {K : Type} [Field K]

/-- A function f of (feature, position), summed as claimEmbedding's form sums the stream: over nb
blocks under the weights w, over the 2^ls features of a block under the equality weights of low, and
over the 2^lT positions under those of u. -/
def embSide (w : ℕ → K) (nb ls lT : ℕ) (low u : ℕ → K) (f : ℕ → ℕ → K) : K :=
  ∑ kh ∈ range nb, w kh *
    ∑ r ∈ range (2 ^ ls), Blocks.eqN ls 0 low r * ext lT (fun p => f (kh * 2 ^ ls + r) p) u

/-- embSide takes differences to differences. -/
theorem embSide_sub (w : ℕ → K) (nb ls lT : ℕ) (low u : ℕ → K) (f g : ℕ → ℕ → K) :
    embSide w nb ls lT low u (fun j p => f j p - g j p) =
      embSide w nb ls lT low u f - embSide w nb ls lT low u g := by
  unfold embSide
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun kh _ => ?_
  rw [← mul_sub, ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun r _ => ?_
  rw [Blocks.ext_sub]
  ring

/-- The sum that the embedding's weight claim y speaks of in the matrix M is embSide of the
embedding emb of the tokens tok. -/
def EmbWeight (ρ : Reading K) (lay : WsLay) (M : Wm K) (y : WsClaim) (w : ℕ → K)
    (nb ls lT : ℕ) (low u : ℕ → K) (emb : ℕ → ℕ → K) (tok : ℕ → ℕ) : Prop :=
  claimVal ρ lay M y = embSide w nb ls lT low u fun j p => emb (tok p) j

/-- At this point, embSide of the defects of Idn.j11 is 0 only if every defect is 0. -/
def EmbStep [scl : Scl] (D : Dim) (t : Cell → K) (emb : ℕ → ℕ → K) (tok : ℕ → ℕ) (w : ℕ → K)
    (nb ls : ℕ) (low u : ℕ → K) : Prop :=
  embSide w nb ls D.lT low u (fun j p => idnVal D t emb tok (.j11 j p)) = 0 →
    ∀ j i, (Idn.j11 j i).Valid D true → idnVal D t emb tok (.j11 j i) = 0

section Field

variable {ρ : Reading K} {W : World K} {v : Env} {c : Cells K} {t : Cell → K} [scl : Scl]
  {D : Dim} {low u lowV uV uP uR lowE uE : ℕ → K}

/-- embSide of the defects of Idn.j11 is 0. F, T3: the ground of Johnson/Road/FormsKeysIdnL.lean; s:
the sum of claimEmbedding's form; hc: that claim; hV: the merge's in-claim on the slot sVE. -/
theorem emb_side (F : Fits ρ W v D c t low u)
    (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE) (h0 : v.g = 0) {tb : ℕ}
    (hb : v.tabAt ("xbI" ++ "@" ++ "Z_E") = some tb) (tkh : Array E) (sVE : ℕ) {s : Aff}
    (hs : embSum v tb tkh = some s)
    (hc : ((Aff.slot sVE).scale (negE oneE) + s).value ρ W = 0)
    {lay : WsLay} {M : Wm K} {y : WsClaim} (hV : W.slot sVE = claimVal ρ lay M y)
    {emb : ℕ → ℕ → K} {tok : ℕ → ℕ}
    (hE : EmbWeight ρ lay M y (fun kh => ρ.val ((eqTab tkh).getD kh zeroE))
      (v.y.h.d / v.y.S2) v.y.ls D.lT lowE uE emb tok) :
    embSide (fun kh => ρ.val ((eqTab tkh).getD kh zeroE)) (v.y.h.d / v.y.S2) v.y.ls D.lT lowE uE
      (fun j p => idnVal D t emb tok (.j11 j p)) = 0 := by
  have e := F.embedding T3 h0 hb tkh sVE hs
  rw [hc, hV, hE] at e
  have e2 : embSide (fun kh => ρ.val ((eqTab tkh).getD kh zeroE)) (v.y.h.d / v.y.S2) v.y.ls D.lT
      lowE uE (fun j p => idnVal D t emb tok (.j11 j p)) =
    embSide (fun kh => ρ.val ((eqTab tkh).getD kh zeroE)) (v.y.h.d / v.y.S2) v.y.ls D.lT
      lowE uE (fun j p => xS D t 0 j p) -
    embSide (fun kh => ρ.val ((eqTab tkh).getD kh zeroE)) (v.y.h.d / v.y.S2) v.y.ls D.lT
      lowE uE (fun j p => emb (tok p) j) :=
    embSide_sub _ _ _ _ _ _ (fun j p => xS D t 0 j p) (fun j p => emb (tok p) j)
  rw [e2]
  exact e.symm

/-- The identities Idn.j11, at a point at which EmbStep holds. -/
theorem emb_field (F : Fits ρ W v D c t low u)
    (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE) (h0 : v.g = 0) {tb : ℕ}
    (hb : v.tabAt ("xbI" ++ "@" ++ "Z_E") = some tb) (tkh : Array E) (sVE : ℕ) {s : Aff}
    (hs : embSum v tb tkh = some s)
    (hc : ((Aff.slot sVE).scale (negE oneE) + s).value ρ W = 0)
    {lay : WsLay} {M : Wm K} {y : WsClaim} (hV : W.slot sVE = claimVal ρ lay M y)
    {emb : ℕ → ℕ → K} {tok : ℕ → ℕ}
    (hE : EmbWeight ρ lay M y (fun kh => ρ.val ((eqTab tkh).getD kh zeroE))
      (v.y.h.d / v.y.S2) v.y.ls D.lT lowE uE emb tok)
    (St : EmbStep D t emb tok (fun kh => ρ.val ((eqTab tkh).getD kh zeroE))
      (v.y.h.d / v.y.S2) v.y.ls lowE uE) :
    ∀ j i, (Idn.j11 j i).Valid D true → idnVal D t emb tok (.j11 j i) = 0 :=
  St (emb_side F T3 h0 hb tkh sVE hs hc hV hE)

end Field

end OnBytes.Road.Rows
