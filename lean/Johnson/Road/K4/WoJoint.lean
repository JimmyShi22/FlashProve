-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/WoJoint.lean: THE PENDING ROW's LEFT SIDE, TYPED AND AS THE PROGRAM SPELLS IT: THE
ALGEBRA, GENERAL IN THE CLAIMS. The library writes the merge's summand at a point as a sum over the
claims of a coefficient times `summand` of a pair (γ, ε) (Cb/Pv/Lay/At/FootW.lean), and so the
pending row's row weights as `rowW` (Cb/Pv/Lay/End/WeightsPay.lean). The program's records spell the
same function as `fmAt` (Johnson/Road/FormsKeysMerge.lean), and what `wsPending` returns as
`pendWeight` (Johnson/Road/Rows/PendingPort.lean). Here the two are one number, IF each typed pair
and its claim of the program, both functionals of a matrix, take one value AT ONE MATRIX that is
made of the point (whoever shows that will show it on every matrix). The two factors γ and ε are
never tied apart. Definitions, statements and proofs.

  `starW ρ k rm M`: the matrix whose entry in row r and column C is the equality weight of C at rm
    times row r of M read at rm.
  `eqk_eqN`: the library's two equality weights are one (`Alg.eqk` at a vertex, `Blocks.eqN` at the
    vertex's number).
  `tval_star`: a typed pair's value on `starW` is its `summand` on M at the point.
  `claimVal_star`: what a claim of the program speaks of in `starW` (`claimVal`,
    Johnson/Road/FormsKeysWm.lean) is the claim's share `shareAt` on M at the point.
  `summand_share`: so, under (H) at that one matrix: `summand a (matOf M) ψ = shareAt ρ lay M rm c`.
  `comb_fmAt`: summed over the claims: the typed combination is `fmAt`.
  `rows_pend`: `∑ r, rowW co ten ψ r * Alg.mle (matOf M r) ψ = ∑ j ∈ range (2 ^ S.kRow), pendWeight
    ρ w.g j * rowAt ρ lay.lk o.rm M j`, where `wsPending lay o claims S = .ok w`.

NO NEW ARGUMENT BUT ONE CHOICE OF A MATRIX: `claim_cells`
(Johnson/Road/FormsKeysFac.lean), `eps_multilinear` (FormsKeysMerge.lean), `pending_port_free`
(Johnson/Road/Rows/StretchLaws.lean), `comb_rows` (WeightsPay.lean).

Limits. (H): THAT EACH TYPED PAIR AND ITS CLAIM ARE ONE FUNCTIONAL IS A PREMISE (asked at the one
matrix `starW`); so are: that the layout has each claim's unit, `UnitOK`, that each claim passes
`wsClaimShape`; that the coefficients are the readings of the program's; that the record's `recs`
are made of the claims as the program's text makes them; that `wsPending` returns. Identities on
numbers: no draw. Nothing on the mask entry, the factor and the shown value of the pending row.
Nothing on soundness.
-/
import Johnson.Road.Rows.StretchLaws
import Cb.Pv.Lay.End.WeightsPay
import Inst.Model.LayoutTensor

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset
open OnBytes OnBytes.Road OnBytes.Road.Rows
open OnBytes.Model (Reading WsLay WsUnit WsClaim WsForkOut WsPending wsEpsT wsRowPart wsGamma
  wsClaimShape wsPending)
open Cb.Pv.Lay.At (tval summand)
open Cb.Pv.Lay.End.Gated (rowW comb_rows)
open Inst.Model.Layout.Tensor (matOf)

variable {K : Type} [Field K] (ρ : Reading K)

/-- The matrix made of the point: the equality weight of the column times the row read there. -/
def starW (k : ℕ) (rm : Array E) (M : Wm K) : Wm K :=
  fun r C => Blocks.eqN k 0 (pt ρ rm) C * rowAt ρ k rm M r

/-- The library's two equality weights are one. -/
theorem eqk_eqN (k : ℕ) (a : ℕ → K) (c : Fin k → Bool) :
    Alg.eqk (fun i : Fin k => a i) c = Blocks.eqN k 0 a (Alg.num c) := by
  unfold Alg.eqk Blocks.eqN
  rw [← Fin.prod_univ_eq_prod_range
    (fun t => if (Alg.num c).testBit (k - 1 - t) then a (0 + t) else 1 - a (0 + t)) k]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hb : (Alg.num c).testBit (k - 1 - (v : ℕ)) = c v := congrFun (Alg.bits_num c) v
  rw [hb, Nat.zero_add]

/-- A row of M read at the point, as the library's extension. -/
theorem mle_row {h : ℕ} (k : ℕ) (rm : Array E) (M : Wm K) (r : Fin h) :
    Alg.mle (matOf (h := h) (k := k) M r) (fun i : Fin k => pt ρ rm i) = rowAt ρ k rm M r := by
  unfold Alg.mle rowAt
  rw [← Alg.sum_num fun C => Blocks.eqN k 0 (pt ρ rm) C * M r C]
  exact Finset.sum_congr rfl fun c _ => by rw [eqk_eqN]; rfl

/-- **A typed pair's value on the matrix made of the point is its summand at the point.** -/
theorem tval_star {h k : ℕ} (a : (Fin h → K) × ((Fin k → Bool) → K)) (rm : Array E) (M : Wm K) :
    tval a (matOf (starW ρ k rm M)) = summand a (matOf M) (fun i : Fin k => pt ρ rm i) := by
  rw [Cb.Pv.Lay.End.Gated.summand_rows]
  unfold tval
  have e1 : ∀ c : Fin k → Bool, a.2 c * ∑ r, a.1 r * matOf (starW ρ k rm M) r c =
      (Alg.eqk (fun i : Fin k => pt ρ rm i) c * a.2 c) * ∑ r : Fin h, a.1 r * rowAt ρ k rm M r := by
    intro c
    rw [eqk_eqN, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    show a.2 c * (a.1 r * (Blocks.eqN k 0 (pt ρ rm) (Alg.num c) * rowAt ρ k rm M r)) = _
    ring
  rw [Finset.sum_congr rfl fun c _ => e1 c, ← Finset.sum_mul]
  show Alg.mle a.2 (fun i : Fin k => pt ρ rm i) * _ = _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [mle_row]
  ring

/-- **What a claim speaks of in the matrix made of the point is its share at the point.** -/
theorem claimVal_star (hρ : Numerals ρ) {lay : WsLay} {c : WsClaim} {u : WsUnit}
    (hu : lay.U[c.ui]? = some u) (hs : wsClaimShape lay c = .ok ()) (U : UnitOK lay.lk u)
    (rm : Array E) (M : Wm K) :
    claimVal ρ lay (starW ρ lay.lk rm M) c = shareAt ρ lay M rm c := by
  have h1 := claim_cells hρ hu hs U (starW ρ lay.lk rm M) oneE oneE
  rw [ρ.one, one_mul, one_mul] at h1
  rw [← h1]
  unfold shareAt
  rw [hu]
  show _ = ρ.val (wsEpsT lay c rm) * _
  rw [eps_multilinear ρ hu (shape_of_claim hu hs).1 U rm, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun y _ => ?_
  show _ * _ * (Blocks.eqN lay.lk 0 (pt ρ rm) C * rowAt ρ lay.lk rm M (u.off + y)) = _
  ring

/-- **A typed pair's summand is its claim's share**, if the two are one functional at the matrix
made of the point. -/
theorem summand_share (hρ : Numerals ρ) {lay : WsLay} {c : WsClaim} {u : WsUnit}
    (hu : lay.U[c.ui]? = some u) (hs : wsClaimShape lay c = .ok ()) (U : UnitOK lay.lk u)
    (rm : Array E) (M : Wm K) {h : ℕ} (a : (Fin h → K) × ((Fin lay.lk → Bool) → K))
    (H : tval a (matOf (starW ρ lay.lk rm M)) = claimVal ρ lay (starW ρ lay.lk rm M) c) :
    summand a (matOf M) (fun i : Fin lay.lk => pt ρ rm i) = shareAt ρ lay M rm c := by
  rw [← tval_star, H, claimVal_star ρ hρ hu hs U]

/-- **The typed combination of the claims' summands is the program's function at the point.** -/
theorem comb_fmAt (hρ : Numerals ρ) (lay : WsLay) (rm : Array E) (M : Wm K) {h n : ℕ}
    (co : Fin n → K) (ten : Fin n → (Fin h → K) × ((Fin lay.lk → Bool) → K))
    (cs : Fin n → WsClaim) (rho : Fin n → E) (hco : ∀ a, co a = ρ.val (rho a))
    (hu : ∀ a, ∃ u, lay.U[(cs a).ui]? = some u ∧ UnitOK lay.lk u)
    (hs : ∀ a, wsClaimShape lay (cs a) = .ok ())
    (H : ∀ a, tval (ten a) (matOf (starW ρ lay.lk rm M)) =
      claimVal ρ lay (starW ρ lay.lk rm M) (cs a)) :
    ∑ a, co a * summand (ten a) (matOf M) (fun i : Fin lay.lk => pt ρ rm i) =
      fmAt ρ lay M (List.ofFn fun a => (cs a, rho a)) rm := by
  unfold fmAt
  rw [List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_congr rfl fun a _ => ?_
  obtain ⟨u, hua, Ua⟩ := hu a
  show _ = ρ.val (rho a) * shareAt ρ lay M rm (cs a)
  rw [summand_share ρ hρ hua (hs a) Ua rm M (ten a) (H a), hco a]

/-- **The typed row weights against what `wsPending` returns.** -/
theorem rows_pend (hρ : Numerals ρ) (lay : WsLay) (M : Wm K) (o : WsForkOut) (claims : ℕ)
    (S : Params.LinShape) {h n : ℕ} (co : Fin n → K)
    (ten : Fin n → (Fin h → K) × ((Fin lay.lk → Bool) → K)) (cs : Fin n → WsClaim)
    (rho : Fin n → E) (hco : ∀ a, co a = ρ.val (rho a))
    (hu : ∀ a, ∃ u, lay.U[(cs a).ui]? = some u ∧ UnitOK lay.lk u)
    (hs : ∀ a, wsClaimShape lay (cs a) = .ok ())
    (H : ∀ a, tval (ten a) (matOf (starW ρ lay.lk o.rm M)) =
      claimVal ρ lay (starW ρ lay.lk o.rm M) (cs a))
    (ho : o.recs = (List.ofFn fun a => (cs a, rho a)).map fun y =>
      wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 o.rm)))
    {w : WsPending} (hw : wsPending lay o claims S = .ok w) :
    ∑ r, rowW co ten (fun i : Fin lay.lk => pt ρ o.rm i) r *
        Alg.mle (matOf (h := h) M r) (fun i : Fin lay.lk => pt ρ o.rm i) =
      ∑ j ∈ range (2 ^ S.kRow), pendWeight ρ w.g j * rowAt ρ lay.lk o.rm M j := by
  rw [← comb_rows, comb_fmAt ρ hρ lay o.rm M co ten cs rho hco hu hs H]
  exact (pending_port_free ρ hρ lay M o claims S _ ho hw).2.2.2.symm

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.eqk_eqN
#print axioms OnBytes.Road.K4.tval_star
#print axioms OnBytes.Road.K4.claimVal_star
#print axioms OnBytes.Road.K4.summand_share
#print axioms OnBytes.Road.K4.comb_fmAt
#print axioms OnBytes.Road.K4.rows_pend
