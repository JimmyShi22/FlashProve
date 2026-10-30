-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoGaps.lean: what each row and the masked claim of a lookup's typed
out-statement lack of holding, as values: equal to the flat function's claims, up to a sign that is
named.

OnBytes/Tie/Pv/Lookup/Forest/FoOutIff.lean, OnBytes/Tie/Pv/Lookup/Forest/FoPlaneRows.lean,
OnBytes/Tie/Pv/Lookup/Forest/FoPin.lean and OnBytes/Tie/Pv/Lookup/Forest/FoJoinOut.lean say of each
typed row, and of the masked claim on the key vector, that it holds exactly if a value of the flat
function is 0. Whoever batches the claims with powers of a draw needs more: that the two values are
equal, sign and scale too. This file states that.

What the file states. rowRes μ r (OnBytes/Tie/Pv/Lookup/Forest/FoEnds.lean) is a sparse row's form
at the reading μ, less its target.
 - res_toRow: a sparse row, renamed along ι and spread: its dense form at μ, less its target, is
   rowRes of the row at the reading p ↦ μ (ι p).
 - rowEnd_res: rowRes of the closing's row is the leaves' claim's left side less its right side.
   rowEnd_claim: so, at the record of plain data rs, it is claimLeaves
   (OnBytes/Tie/Pv/Lookup/Forest/FoClaims.lean) at the columns' sums colsK. Sign +.
 - rowBitE_res, rowBitE_claim: rowRes of the bits' row on the planes is the NEGATIVE of claimBits.
 - rowNum_res, rowNum_claim: rowRes of the row that sums the counts is countK. Sign +.
 - MGap c k f μ: what a masked claim c on a vector f lacks: the extension of f at c's point, plus
   c's form at μ, less c's target. mgap_zero: the claim holds exactly if it is 0. mgap_congr: the
   point enters through the weights alone.
 - join_form_gap: the value of joinK's form (OnBytes/Tie/Pv/Lookup/Port/FoJoin.lean) is the NEGATIVE
   of MGap of the claim on the joint key vector, under the premises of join_form.
 - join_ends_gap: the same in the record's fields, under the premises of join_ends
   (OnBytes/Tie/Pv/Lookup/Forest/FoJoinOut.lean), to the letter. join_claim_gap: so claimJoin, at
   the values of the key forms KF, is the NEGATIVE of MGap of the out-statement's masked claim.

How join_form_gap is had. join_form holds of every claim and every form cEnd that reads it. At the
claim whose target is moved by the claim's own gap, which holds, and the form moved likewise, it
gives that joinK's value is 0 there; and that value is affine in cEnd (val_joinK).

Limits. At the base: nothing on a ledger, a draw or the byte-level verifier's total. The premises of
the four files named above stay: for the three rows: the shape is lawful (FoNums.ok), 5 ≤ lm ≤ kT +
5, and the reading is 0 at the place zero; for join_claim_gap: FoNums.ok, Fo.OutAt of the
out-statement, and that the key forms have the key vectors' extensions as their values (KFokAt).
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoOutOf

set_option autoImplicit false

namespace Fo
open TwV FoNums Finset OnBytes.Model OnBytes.Ends Cb Cb.LdLkp Cb.Fo Tw3 Cb.Fo.Pin

/-! ### rows -/

section
variable {E : Type} [Field E] {J₀ : Type} [Fintype J₀] [DecidableEq J₀]

/-- A sparse row, renamed and spread. -/
theorem res_toRow (ι : Pl → Option J₀) (r : SRow Pl E) (μ : Option J₀ → E) :
    ∑ j, (toRow (rowMap ι r)).cf j * μ j - (toRow (rowMap ι r)).tg =
      rowRes (fun p => μ (ι p)) r := by
  unfold rowRes evalL
  show ∑ j, dense (mapL ι r.cf) j * μ j - r.tg = _
  rw [dense_val]
  unfold mapL
  rw [List.map_map]
  rfl

end

section
variable {K : Type} [CommRing K]

/-- The closing's row. -/
theorem rowEnd_res (h : FoNums.Sh) (hok : ok h = true) (lm jLK : ℕ) (h5 : 5 ≤ lm)
    (hlm : lm ≤ h.kT + 5) (θ : K) (μ : Pl → K) (h0 : μ .zero = 0) (t : Trace K) :
    rowRes μ (rowEnd (numsF h lm jLK θ) t) =
      valS (hide (numsF h lm jLK θ).ledE (dgE (numsF h lm jLK θ)) t.cls.xs) μ +
          t.cls.eps * valS (incTop (numsF h lm jLK θ).ledT (incT0 (numsF h lm jLK θ) t)
              t.tabl.reverse) μ +
          t.cls.eps * (leavesAK h θ t.lam (byVar (ordE h) t.cls.xs).reverse *
            planesK h lm (byVar (ordE h) t.cls.xs).reverse
              (colsK h lm (byVar (ordE h) t.cls.xs).reverse μ)) -
        (t.cls.fin - t.cls.eps) := by
  have hg : (byVar (ordE h) t.cls.xs).length = FoNums.w + h.d := by rw [byVar_len, ordE_len]
  show valS (hide (numsF h lm jLK θ).ledE (dgE (numsF h lm jLK θ)) t.cls.xs ++
        scale t.cls.eps (incTop (numsF h lm jLK θ).ledT (incT0 (numsF h lm jLK θ) t) t.tabl.reverse)
            ++
        scale (t.cls.eps * ((List.range (2 ^ h.d)).map fun r =>
            eqN ((byVar (ordE h) t.cls.xs).drop FoNums.w) r * (t.lam - 1 - tabF h θ r)).sum)
          (bitsForm (numsF h lm jLK θ) (byVar (ordE h) t.cls.xs))) μ - (t.cls.fin - t.cls.eps * 1) =
      _
  rw [valS_append, valS_append, valS_scale, valS_scale, tab_ext_g h hok θ t.lam _ hg,
    plane_sum_g h hok lm jLK h5 hlm θ μ h0 _ hg, mul_one, mul_assoc]
  rfl

/-- The bits' row on the planes: the sign turns. -/
theorem rowBitE_res (h : FoNums.Sh) (hok : ok h = true) (lm jLK : ℕ) (h5 : 5 ≤ lm)
    (hlm : lm ≤ h.kT + 5) (θ : K) (μ : Pl → K) (h0 : μ .zero = 0) (t : Trace K) :
    rowRes μ (rowBitE (numsF h lm jLK θ) t) =
      -((t.bits.v 0 - t.bits.be * μ ((numsF h lm jLK θ).ledB.sh 0)) -
          planesK h lm (byVar (ordB h) t.bits.xs).reverse
            (colsK h lm (byVar (ordB h) t.bits.xs).reverse μ)) := by
  have hg : (byVar (ordB h) t.bits.xs).length = FoNums.w + h.d := by rw [byVar_len, ordB_len]
  show valS (bitsForm (numsF h lm jLK θ) (byVar (ordB h) t.bits.xs) ++
      [((numsF h lm jLK θ).ledB.sh 0, t.bits.be)]) μ - t.bits.v 0 = _
  rw [valS_append, plane_sum_g h hok lm jLK h5 hlm θ μ h0 _ hg]
  have e : valS [((numsF h lm jLK θ).ledB.sh 0, t.bits.be)] μ =
      t.bits.be * μ ((numsF h lm jLK θ).ledB.sh 0) := by
    simp [valS]
  rw [e]
  unfold colsK
  ring

/-- The row that sums the counts. -/
theorem rowNum_res (h : FoNums.Sh) (H : FoNums.ok h = true) (lm jLK : ℕ) (h5 : 5 ≤ lm)
    (hlm : lm ≤ h.kT + 5) (θ : K) (μ : Pl → K) (h0 : μ .zero = 0) :
    rowRes μ (rowNum (numsF h lm jLK θ)) = countK h lm (pinColK lm μ) := by
  show valS (rowNum (numsF h lm jLK θ)).cf μ - (rowNum (numsF h lm jLK θ)).tg = _
  unfold countK
  rw [pin_sum h lm jLK θ μ h0 (ok_parts H).1.2.2.1 h5 hlm, PadFac.pin_target h H, foldl_add_from]
  ring

/-- At the record of plain data: the three claims on the planes. -/
theorem rowEnd_claim (h : FoNums.Sh) (H : ok h = true) (lm jLK : ℕ) (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT +
    5)
    (rs : Rounds K) (ν : Pl → K) (h0 : ν .zero = 0) :
    rowRes ν (rowEnd (forN h lm jLK rs) (forTrace h lm jLK rs)) =
      claimLeaves h lm jLK rs ν (colsK h lm (endsOf h lm jLK rs).zb0 ν) :=
  rowEnd_res h H lm jLK h5 hlm (thetaOf h rs) ν h0 (forTrace h lm jLK rs)

theorem rowBitE_claim (h : FoNums.Sh) (H : ok h = true) (lm jLK : ℕ) (h5 : 5 ≤ lm)
    (hlm : lm ≤ h.kT + 5) (rs : Rounds K) (ν : Pl → K) (h0 : ν .zero = 0) :
    rowRes ν (rowBitE (forN h lm jLK rs) (forTrace h lm jLK rs)) =
      -claimBits h lm jLK rs ν (colsK h lm (endsOf h lm jLK rs).zb1 ν) :=
  rowBitE_res h H lm jLK h5 hlm (thetaOf h rs) ν h0 (forTrace h lm jLK rs)

theorem rowNum_claim (h : FoNums.Sh) (H : ok h = true) (lm jLK : ℕ) (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT +
    5)
    (rs : Rounds K) (ν : Pl → K) (h0 : ν .zero = 0) :
    rowRes ν (rowNum (forN h lm jLK rs)) = countK h lm (pinColK lm ν) :=
  rowNum_res h H lm jLK h5 hlm (thetaOf h rs) ν h0

end

/-! ### the masked claim on the key vector -/

section
variable {E N : Type} [Field E] [Fintype N]

/-- What a masked claim lacks of holding. -/
def MGap (c : MCl E N) (k : ℕ) (f : ℕ → E) (μ : N → E) : E :=
  Blocks.ext k f c.pt + ∑ i, c.mf i * μ i - c.tg

theorem mgap_zero (c : MCl E N) (k : ℕ) (f : ℕ → E) (μ : N → E) :
    c.Holds k f μ ↔ MGap c k f μ = 0 := by
  unfold MCl.Holds MGap
  exact sub_eq_zero.symm

theorem mgap_congr (c c' : MCl E N) (k : ℕ) (f : ℕ → E) (μ : N → E)
    (hw : ∀ X < 2 ^ k, Blocks.eqN k 0 c.pt X = Blocks.eqN k 0 c'.pt X) (hm : c.mf = c'.mf)
    (ht : c.tg = c'.tg) : MGap c k f μ = MGap c' k f μ := by
  unfold MGap Blocks.ext
  rw [hm, ht, Finset.sum_congr rfl fun X hX => by rw [hw X (Finset.mem_range.mp hX)]]

/-- **The value of the join's form is the negative of the claim's gap.** -/
theorem join_form_gap {h : FoNums.Sh} (hp : Prem h) (Kv : (N → E) → ℕ → ℕ → E) (θ α : E) (c : MCl E
    N)
    (KF : ℕ → AffK N E) (cEnd : AffK N E) (μ : N → E) (hKF : KFokAt h Kv (zkOf h c) KF μ)
    (hC : CEok c α cEnd) :
    AffK.val (joinK h θ α (eK h (zyOf h c)) (zyOf h c) KF cEnd) μ =
      -MGap c h.v (jointKey h (Kv μ) θ) μ := by
  have hC' : CEok (⟨c.pt, c.mf, c.tg + MGap c h.v (jointKey h (Kv μ) θ) μ⟩ : MCl E N) α
      (cEnd.1, cEnd.2 - MGap c h.v (jointKey h (Kv μ) θ) μ) := by
    intro μ'
    have := hC μ'
    unfold AffK.val at this ⊢
    show _ + (cEnd.2 - _) = α - (c.tg + _) + _
    linear_combination this
  have hH : (⟨c.pt, c.mf, c.tg + MGap c h.v (jointKey h (Kv μ) θ) μ⟩ : MCl E N).Holds h.v
      (jointKey h (Kv μ) θ) μ := by
    unfold MCl.Holds MGap
    show _ = c.tg + _
    ring
  have hz := (join_form hp Kv θ α
    (⟨c.pt, c.mf, c.tg + MGap c h.v (jointKey h (Kv μ) θ) μ⟩ : MCl E N) KF _ μ hKF hC').1 hH
  have hz' : AffK.val (joinK h θ α (eK h (zyOf h c)) (zyOf h c) KF
      (cEnd.1, cEnd.2 - MGap c h.v (jointKey h (Kv μ) θ) μ)) μ = 0 := hz
  rw [val_joinK] at hz' ⊢
  have e : AffK.val (cEnd.1, cEnd.2 - MGap c h.v (jointKey h (Kv μ) θ) μ) μ =
      AffK.val cEnd μ - MGap c h.v (jointKey h (Kv μ) θ) μ := by
    unfold AffK.val
    show _ + (cEnd.2 - _) = _
    ring
  rw [e] at hz'
  linear_combination hz'

end

section
variable {E : Type} [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]

/-- **The same in the record's fields.** -/
theorem join_ends_gap (h : FoNums.Sh) (H : FoNums.ok h = true) (L : Lay E St₀ J₀) (lm jLK : ℕ)
    (ι : Pl → Option J₀) (rs : Rounds E)
    (st : St₀) (x : TX (St₀ × E) E (Option J₀))
    (h1 : x.1 = (st, (endsOf h lm jLK rs).theta))
    (h4 : ∀ X < 2 ^ (FoNums.v' h + 1), Blocks.eqN (FoNums.v' h + 1) 0 x.2.1.pt X =
      TwV.eqN ((endsOf h lm jLK rs).zy.reverse ++ (endsOf h lm jLK rs).zx.reverse) X)
    (h5 : ∀ j, x.2.1.mf j = dense (mapL ι (endsOf h lm jLK rs).cEndF) j)
    (h6 : x.2.1.tg = (endsOf h lm jLK rs).alpha - (endsOf h lm jLK rs).cEndC)
    (KF : ℕ → AffK (Option J₀) E) (μ : Option J₀ → E)
    (hKF : KFokAt h (forK E L st) (fun c => (endsOf h lm jLK rs).zk.getD c []) KF μ) :
    AffK.val (joinK h (endsOf h lm jLK rs).theta (endsOf h lm jLK rs).alpha
          (eK h (endsOf h lm jLK rs).zy)
        (endsOf h lm jLK rs).zy KF (mapL ι (endsOf h lm jLK rs).cEndF, (endsOf h lm jLK rs).cEndC))
            μ =
      -MGap x.2.1 (FoNums.v' h + 1) ((forA E h L).key x.1 μ) μ := by
  have hx := ends_zx_len h H lm jLK rs
  have hy := ends_zy_len h H lm jLK rs
  have hv : FoNums.v' h + 1 = h.dT + h.rK := (ok_v H).symm
  have hlen : ((endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy).length = h.dT + h.rK := by
    rw [List.length_append, hx, hy]
  -- the claim with the record's lists as its point
  have hrho : rhoP (h.dT + h.rK) (ptL ((endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy)) =
      (endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy := by
    rw [← hlen]; exact rho_ptL _
  have hc := mgap_congr x.2.1 ⟨ptL ((endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy), x.2.1.mf,
      x.2.1.tg⟩
    (FoNums.v' h + 1) ((forA E h L).key x.1 μ) μ (fun X hX => by
      rw [h4 X hX, hv]
      have e := eqN_top (ptL ((endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy)) 0 (h.dT + h.rK) X
      simp only [Nat.zero_add] at e
      rw [← e]
      have e2 : ((List.range (h.dT + h.rK)).map fun i =>
          ptL ((endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy) i) =
          (endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy := hrho
      rw [e2, List.reverse_append]) rfl rfl
  have hzx : zxOf h (⟨ptL ((endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy), x.2.1.mf, x.2.1.tg⟩
      : MCl E (Option J₀)) =
      (endsOf h lm jLK rs).zx := by
    unfold zxOf zx
    rw [hrho, ← hx, List.take_left']
    rfl
  have hzy : zyOf h (⟨ptL ((endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy), x.2.1.mf, x.2.1.tg⟩
      : MCl E (Option J₀)) =
      (endsOf h lm jLK rs).zy := by
    unfold zyOf zy
    rw [hrho, ← hx, List.drop_left']
    rfl
  have hKF' : KFokAt h (forK E L st)
      (zkOf h (⟨ptL ((endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy), x.2.1.mf, x.2.1.tg⟩ : MCl
          E (Option J₀))) KF μ := by
    intro c hcN
    rw [hKF c hcN]
    show extL _ ((endsOf h lm jLK rs).zk.getD c []) = _
    rw [ends_zk h H lm jLK rs c hcN]
    unfold zkOf
    rw [hzx, hzy]
  have hCE : CEok (⟨ptL ((endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy), x.2.1.mf, x.2.1.tg⟩ :
      MCl E (Option J₀))
      (endsOf h lm jLK rs).alpha (mapL ι (endsOf h lm jLK rs).cEndF, (endsOf h lm jLK rs).cEndC) :=
          by
    intro ν
    unfold AffK.val
    simp only [h5, h6]
    rw [dense_val]
    ring
  have hj := join_form_gap (ok_prem H) (forK E L st) (endsOf h lm jLK rs).theta
      (endsOf h lm jLK rs).alpha
    (⟨ptL ((endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy), x.2.1.mf, x.2.1.tg⟩ : MCl E
        (Option J₀)) KF _ μ hKF' hCE
  rw [hzy] at hj
  rw [hj, hc]
  have hk : (forA E h L).key x.1 μ = jointKey h (forK E L st μ) (endsOf h lm jLK rs).theta := by
    rw [h1]; exact forA_key E h L H st _ μ
  rw [← hk]
  have hvv : h.v = FoNums.v' h + 1 := ok_v H
  rw [hvv]

/-- **The join's claim is the negative of the out-statement's masked claim's gap.** -/
theorem join_claim_gap (h : FoNums.Sh) (H : FoNums.ok h = true) (L : Lay E St₀ J₀) (lm jLK : ℕ)
    (ι : Pl → Option J₀) (rs : Rounds E) (st : St₀) (x : TX (St₀ × E) E (Option J₀))
    (hx : OutAt h lm jLK ι rs st x) (KF : ℕ → AffK (Option J₀) E) (μ : Option J₀ → E)
    (hKF : KFokAt h (forK E L st) (fun c => (endsOf h lm jLK rs).zk.getD c []) KF μ) :
    claimJoin h lm jLK rs (fun p => μ (ι p)) (fun c => AffK.val (KF c) μ) =
      -MGap x.2.1 (FoNums.v' h + 1) ((forA E h L).key x.1 μ) μ := by
  rw [← join_ends_gap h H L lm jLK ι rs st x hx.state hx.point hx.form hx.target KF μ hKF]
  unfold claimJoin
  rw [val_joinK, val_joinK]
  simp only [AffK.val_ofConst]
  congr 1
  unfold AffK.val mapL
  simp only [List.map_map]
  rfl

end
end Fo
