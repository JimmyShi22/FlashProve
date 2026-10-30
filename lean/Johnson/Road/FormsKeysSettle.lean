-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysSettle.lean: the verifier's own settling of a weight claim, summed over the
cells of the committed matrix, is the library's value of the panel's tensor claim.

The verifier settles a weight claim on the committed matrix W of weights by two functions of
OnBytes/Model/Weights.lean: wsGamma of what wsRowPart leaves gives a coefficient to each row of the
claim's unit, and wsEpsT gives the value of the claim's factors on the columns at a point.
Johnson/Road/FormsKeysFac.lean shows that the sum of coefficient times value at the point that
spells the column times the entry of W, over the unit's rows and all columns, is the two scalars
wgt and ka times claimVal, a definition of these files (claim_cells_layout).
Johnson/Road/FormsKeysAim.lean and Johnson/Road/FormsKeysQKF.lean show that claimVal of the
verifier's own claims is the library's Pan.TnRow or Pan.TnPan. This file joins the two.

What is compared with what: on the left the verifier's own functions wsGamma, wsRowPart and wsEpsT
on the verifier's own claims and layout, summed against a free matrix W; on the right the library's
Pan.TnRow and Pan.TnPan at the weights that the library's layout reads in the same W.

Main definitions: settleSum. Main theorems: settle_eq; settle_G, settle_U, settle_V, settle_O,
settle_D, settle_LR, settle_Gr, settle_Ur, settle_Dr, settle_QK.

The hypotheses are those of the theorems that are joined (see their files), and beside them:
 - Numerals ρ: the reading takes the program's numerals to the field's. Met by the reading of the
   program's own field (gl_numerals in Johnson/Road/FormsKeysKit.lean).
 - the layout has a unit under the claim's number: it follows from the way a claim is made
   (claim_inv in Johnson/Road/FormsKeysClaim.lean), and is asked here so that the unit has a name.
 - wsClaimShape returns on the claim. By the text of wsForkEnd (OnBytes/Model/Merge.lean) the
   verifier tests it of every claim that it settles; no theorem here unfolds that text, and that
   the verifier's own claims pass is run at made-up shapes alone (Johnson/Road/FormsKeysRunW.lean).

What is not claimed. The sum runs over the vertices that spell the columns: what the verifier does
with wsEpsT at a random point, and how the rows' coefficients meet the commitment, is not said
here. That the hidden value under a claim's slot is this sum is not shown. See also
Johnson/Road/FormsKeysKit.lean. The program does not import this file.
-/
import Johnson.Road.FormsKeysAim
import Johnson.Road.FormsKeysFac
import Johnson.Road.FormsKeysQKF

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading WsShape WsUnit WsLay WsClaim CallD Seg wsLayOf wsClaimShape wsGamma
  wsRowPart wsEpsT)
open OnBytes.Model.Layer (ClaimEnv)
open Inst.Model (Tables)
open Inst.Model.FFSeg (Dim Fam Pan Rd layerR call aC zc)

variable {K : Type} [Field K]

/-- The verifier's settling of the claim cl on the unit u, summed against the matrix W: over all
columns C and all rows y of the unit, the claim's coefficient on the row (wsGamma of what wsRowPart
leaves, under the scalars ka and wgt), times the value of the claim's factors on the columns at the
point that spells C (wsEpsT), times the entry of W in row u.off + y and column C. -/
def settleSum (ρ : Reading K) (lay : WsLay) (W : Wm K) (cl : WsClaim) (u : WsUnit) (ka wgt : E) :
    K :=
  ∑ C ∈ range (2 ^ lay.lk), ∑ y ∈ range u.rows,
    ρ.val ((wsGamma u (wsRowPart lay cl ka) wgt).getD y zeroE) *
      ρ.val (wsEpsT lay cl (bitsOf lay.lk C)) * W (u.off + y) C

/-- It is the two scalars times the sum that the claim speaks of: claim_cells_layout in these
words. -/
theorem settle_eq {ρ : Reading K} (hρ : Numerals ρ) {s : WsShape} {p3 : Bool} {lk : ℕ}
    {lay : WsLay} (hl : wsLayOf s p3 lk = .ok lay) {cl : WsClaim} {u : WsUnit}
    (hu : lay.U[cl.ui]? = some u) (hs : wsClaimShape lay cl = .ok ()) {W : Wm K} {ka wgt : E} :
    settleSum ρ lay W cl u ka wgt = ρ.val wgt * ρ.val ka * claimVal ρ lay W cl :=
  claim_cells_layout hρ hl hu hs W ka wgt

section Nine

variable {ρ : Reading K} {c : ClaimEnv} {h : Model.Layer.Shape} {pc : List (List String)}
  {s : WsShape} {D : Dim} {lk L0 : ℕ} {z ζ : ℕ → K} (A : AimFits ρ c h pc s D lk L0 ζ)
  (hρ : Numerals ρ) (W : Wm K) (r : Rd K) (tb : Tables) (zh : ℕ → K)

include A hρ

/-- Member number i of the verifier's list of claims of segment G. -/
theorem settle_G (T : CallTie ρ c h D z .G) {l : List WsClaim}
    (hl : c.claimsA "G" = some l) {i : ℕ} {cl : WsClaim} (hi : l[i]? = some cl) {u : WsUnit}
    (hu : c.wsLay.U[cl.ui]? = some u) (hs : wsClaimShape c.wsLay cl = .ok ()) (ka wgt : E) :
    settleSum ρ c.wsLay W cl u ka wgt = ρ.val wgt * ρ.val ka *
      Pan.G.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ i := by
  rw [settle_eq hρ A.claim.lay hu hs, list_G A W r tb zh T hl hi]

/-- Member number i of the verifier's list of claims of segment U. -/
theorem settle_U (T : CallTie ρ c h D z .U) {l : List WsClaim}
    (hl : c.claimsA "U" = some l) {i : ℕ} {cl : WsClaim} (hi : l[i]? = some cl) {u : WsUnit}
    (hu : c.wsLay.U[cl.ui]? = some u) (hs : wsClaimShape c.wsLay cl = .ok ()) (ka wgt : E) :
    settleSum ρ c.wsLay W cl u ka wgt = ρ.val wgt * ρ.val ka *
      Pan.U.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ i := by
  rw [settle_eq hρ A.claim.lay hu hs, list_U A W r tb zh T hl hi]

/-- Member number i of the verifier's list of claims of segment V. -/
theorem settle_V (T : CallTie ρ c h D z .V) {l : List WsClaim}
    (hl : c.claimsA "V" = some l) {i : ℕ} {cl : WsClaim} (hi : l[i]? = some cl) {u : WsUnit}
    (hu : c.wsLay.U[cl.ui]? = some u) (hs : wsClaimShape c.wsLay cl = .ok ()) (ka wgt : E) :
    settleSum ρ c.wsLay W cl u ka wgt = ρ.val wgt * ρ.val ka *
      Pan.V.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ i := by
  rw [settle_eq hρ A.claim.lay hu hs, list_V A W r tb zh T hl hi]

/-- Member number i of the verifier's list of claims of segment O. -/
theorem settle_O (T : CallTie ρ c h D z .O) {l : List WsClaim}
    (hl : c.claimsA "O" = some l) {i : ℕ} {cl : WsClaim} (hi : l[i]? = some cl) {u : WsUnit}
    (hu : c.wsLay.U[cl.ui]? = some u) (hs : wsClaimShape c.wsLay cl = .ok ()) (ka wgt : E) :
    settleSum ρ c.wsLay W cl u ka wgt = ρ.val wgt * ρ.val ka *
      Pan.O.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ i := by
  rw [settle_eq hρ A.claim.lay hu hs, list_O A W r tb zh T hl hi]

/-- Member number i of the verifier's list of claims of segment D. -/
theorem settle_D (T : CallTie ρ c h D z .D) {l : List WsClaim}
    (hl : c.claimsA "D" = some l) {i : ℕ} {cl : WsClaim} (hi : l[i]? = some cl) {u : WsUnit}
    (hu : c.wsLay.U[cl.ui]? = some u) (hs : wsClaimShape c.wsLay cl = .ok ()) (ka wgt : E) :
    settleSum ρ c.wsLay W cl u ka wgt = ρ.val wgt * ρ.val ka *
      Pan.D.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ i := by
  rw [settle_eq hρ A.claim.lay hu hs, list_D A W r tb zh T hl hi]

/-- Member number i of the verifier's list of claims of segment LR. -/
theorem settle_LR (T : CallTie ρ c h D z .LR) {l : List WsClaim}
    (hl : c.claimsA "LR" = some l) {i : ℕ} {cl : WsClaim} (hi : l[i]? = some cl) {u : WsUnit}
    (hu : c.wsLay.U[cl.ui]? = some u) (hs : wsClaimShape c.wsLay cl = .ok ()) (ka wgt : E) :
    settleSum ρ c.wsLay W cl u ka wgt = ρ.val wgt * ρ.val ka *
      Pan.LR.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ i := by
  rw [settle_eq hρ A.claim.lay hu hs, list_LR A W r tb zh T hl hi]

/-- Member number lm of the verifier's list of claims of the routed product G. -/
theorem settle_Gr (T : CallTie ρ c h D z .G) {l : List WsClaim}
    (hl : c.claimsT "G" = some l) {lm : ℕ} {cl : WsClaim} (hi : l[lm]? = some cl) {u : WsUnit}
    (hu : c.wsLay.U[cl.ui]? = some u) (hs : wsClaimShape c.wsLay cl = .ok ()) (ka wgt : E) :
    settleSum ρ c.wsLay W cl u ka wgt = ρ.val wgt * ρ.val ka *
      (Pan.Gr lm).TnPan D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ := by
  rw [settle_eq hρ A.claim.lay hu hs, list_Gr A W r tb zh T hl hi]

/-- Member number lm of the verifier's list of claims of the routed product U. -/
theorem settle_Ur (T : CallTie ρ c h D z .U) {l : List WsClaim}
    (hl : c.claimsT "U" = some l) {lm : ℕ} {cl : WsClaim} (hi : l[lm]? = some cl) {u : WsUnit}
    (hu : c.wsLay.U[cl.ui]? = some u) (hs : wsClaimShape c.wsLay cl = .ok ()) (ka wgt : E) :
    settleSum ρ c.wsLay W cl u ka wgt = ρ.val wgt * ρ.val ka *
      (Pan.Ur lm).TnPan D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ := by
  rw [settle_eq hρ A.claim.lay hu hs, list_Ur A W r tb zh T hl hi]

/-- Member number lm of the verifier's list of claims of the routed product D. -/
theorem settle_Dr (T : CallTie ρ c h D z .D) {l : List WsClaim}
    (hl : c.claimsT "D" = some l) {lm : ℕ} {cl : WsClaim} (hi : l[lm]? = some cl) {u : WsUnit}
    (hu : c.wsLay.U[cl.ui]? = some u) (hs : wsClaimShape c.wsLay cl = .ok ()) (ka wgt : E) :
    settleSum ρ c.wsLay W cl u ka wgt = ρ.val wgt * ρ.val ka *
      (Pan.Dr lm).TnPan D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ := by
  rw [settle_eq hρ A.claim.lay hu hs, list_Dr A W r tb zh T hl hi]

end Nine

/-- Member number lam of the verifier's list of claims of the segment QK. The hypotheses are those
of claims_QK (Johnson/Road/FormsKeysQKF.lean). -/
theorem settle_QK {ρ : Reading K} (hρ : Numerals ρ) {c : ClaimEnv} {sW : WsShape} {D : Dim}
    {lk L0 : ℕ} {ζ : ℕ → K} (C : ClaimFits ρ c sW D lk L0 ζ) {q : ℕ} {cd : CallD} {sg : Seg}
    (F : QKFits c D q cd sg) (hrt : c.rt.size = D.lT) {tb : Tables}
    (R : ∀ lam, lam < c.v.y.Lam → RopeFits ρ c D tb L0 lam) {z zh : ℕ → K}
    (hz : ∀ j < aC D (call .QK), pt ρ (c.v.zk.getD q #[]) j = zc D z (call .QK) j)
    (hzh : ∀ j < D.lT, zh j = pt ρ c.rt j) (r : Rd K) (W : Wm K) {l : List WsClaim}
    (hl : c.claimsT "QK" = some l) {lam : ℕ} (hlam : lam < l.length) {u : WsUnit}
    (hu : c.wsLay.U[l[lam].ui]? = some u) (hs : wsClaimShape c.wsLay l[lam] = .ok ())
    (ka wgt : E) :
    settleSum ρ c.wsLay W l[lam] u ka wgt = ρ.val wgt * ρ.val ka *
      Pan.QK.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ lam := by
  rw [settle_eq hρ C.lay hu hs, (claims_QK ρ C F hrt R hz hzh r W hl).2 lam hlam]

#print axioms settle_eq
#print axioms settle_G
#print axioms settle_U
#print axioms settle_V
#print axioms settle_O
#print axioms settle_D
#print axioms settle_LR
#print axioms settle_Gr
#print axioms settle_Ur
#print axioms settle_Dr
#print axioms settle_QK

end OnBytes.Road
