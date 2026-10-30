-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/NormsAt.lean: what the verifier's claims on the norms say on cells, carried to the
records of the norms' stages at the library's description.

Cb/Pv/Lay/At/Norms.lean fills the records of the two stretches on the norms of a layers' sub-proof
(SquaresL, RowsL) at the library's description of a feed-forward segment: P.sq and P.rows, for
letters P : NormPar0 E. What the chain of the sub-proof's own rounds owes at its end for these
stretches are the rows on the sent scalars (SquaresL.B; RowsL.led at the hidden vector), the linear
row RowsL.tie, and the output claims of the two sumchecks. Cb/Pv/Lay/End/NormsCl.lean concludes
NormsLast from the verifier's claims. This file carries NormsLast to these clauses.

The two sides have letters of their own. Each theorem takes as premises the equations between them
that it needs: that a point, a batching element or a hidden value ("what was shown less the factor
times the mask entry") of the one side is that of the other.

Main theorems: sqB_of, rowsLed_of, tie_of (the rows); sqE_of (the two rows on the end values of the
product layer of the squares), rowsE_of (those of the token sumcheck of the row products).

Limits. The first output claim of either sumcheck (the row on the hiding coefficients) is not here.
The equations between the letters are premises. Identities alone: nothing on a distribution of a
challenge and nothing on soundness.


-/
import Cb.Pv.Lay.At.Norms
import Cb.Pv.Lay.End.NormsCl

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Finset Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (led Pv lDd)
open Blocks (ext)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] (P : NormPar0 E) {J : Type}
  {N : NormsNames J} {e : NormsE E} {lNI b s : ℕ} {y : J → E} {m : P.J → E}

/-- The rows on the sent scalars of the sums of squares. -/
theorem sqB_of (L : NormsLast N e P.D (P.rd m) lNI b s y) (p : Fin P.D.lT → E)
    (sW : Fin P.D.nNu × Fin 9 → E) (c : E) (hp : e.pV = Blocks.nat p)
    (hs : ∀ (ν : Fin P.D.nNu) (x : Fin 9),
      e.shW (9 * (ν : ℕ) + (x : ℕ)) - y (N.mW (9 * (ν : ℕ) + (x : ℕ))) =
        sW (ν, x) - m (P.mkS ν x)) :
    P.sq.B ((p, sW), c) m := by
  intro ν x
  show sW (ν, x) - m (P.mkS ν x) = _
  rw [← hs ν x, NormsLast.rowB N e L ν.2 x.2, hp]
  rfl

/-- The claim on the vector of the hidden products. -/
theorem rowsLed_of (L : NormsLast N e P.D (P.rd m) lNI b s y) (p : Fin P.D.lT → E)
    (sP : Fin (P.D.nNu * 7) → E) (hp : e.pV = Blocks.nat p)
    (hs : ∀ n : Fin (P.D.nNu * 7), e.shP (n : ℕ) - y (N.mP (n : ℕ)) = sP n - m (P.mkP n)) :
    P.rows.led p m fun n => sP n - m (P.mkP n) := by
  intro ν k hk
  have h := NormsLast.rowLed N e L ν.2 (P.pvOf (fun n => sP n - m (P.mkP n)) ν) (fun j hj => by
    unfold NormPar0.pvOf
    rw [dif_pos hj]
    beta_reduce
    rw [← hs]
    have e1 : ((finProdFinEquiv (ν, (⟨j, hj⟩ : Fin 7)) : Fin (P.D.nNu * 7)) : ℕ) =
        7 * (ν : ℕ) + j := by
      rw [finProdFinEquiv_apply_val]
      exact Nat.add_comm _ _
    rw [e1]) hk
  rw [hp] at h
  exact h

/-- The linear row that ties the sent sum of the token sumcheck to the sent scalars. -/
theorem tie_of (L : NormsLast N e P.D (P.rd m) lNI b s y) (p : Fin P.D.lT → E)
    (sP : Fin (P.D.nNu * 7) → E) (σ z : E) (hω : e.ω = σ)
    (hs : ∀ n : Fin (P.D.nNu * 7), e.shP (n : ℕ) - y (N.mP (n : ℕ)) = sP n - m (P.mkP n))
    (hz : e.shCl - y N.mCl = z - m P.rP) : P.rows.tie ((p, sP), σ) z m := by
  show (z - m P.rP) - ∑ n : Fin (P.D.nNu * 7), σ ^ (n : ℕ) * (sP n - m (P.mkP n)) = 0
  rw [← hz, L.batch, hω, Nat.mul_comm 7, sub_eq_zero,
    ← Fin.sum_univ_eq_sum_range (fun x => σ ^ x * (e.shP x - y (N.mP x)))]
  exact sum_congr rfl fun n _ => by rw [hs n]

omit [Fintype E] scl in
/-- The four numbers of a ledger by their number, in the two ways of writing. -/
theorem match_rowVal (Dg : ℕ → E) (q : Fin 4) :
    (match (q : ℕ) with
      | 0 => Inst.Model.Ledger.sa
      | 1 => Inst.Model.Ledger.sb
      | 2 => Inst.Model.Ledger.Rlo
      | _ => Inst.Model.Ledger.Rhi) Dg = rowVal Dg q := by
  fin_cases q <;> rfl

/-- The rows on the end values of the token sumcheck of the row products. -/
theorem rowsE_of (L : NormsLast N e P.D (P.rd m) lNI b s y) (o : P.rows.tok.toSum.T.par.Out)
    (hr : e.r2 = Blocks.nat (P.rows.tok.Kp.outPt P.rows.tok.Mk o)) (a : Fin P.D.nNu × Fin 4)
    (hv : e.sh2 (4 * (a.1 : ℕ) + (a.2 : ℕ)) - e.β2 * y (N.m2 (4 * (a.1 : ℕ) + (a.2 : ℕ))) =
      o.vals a - m (P.cP a) * P.rows.tok.Kp.outB P.rows.tok.Mk o) :
    P.rows.tok.toSum.T.par.EHolds o m a := by
  rw [TokL.ev_iff]
  have h := L.shown (4 * (a.1 : ℕ) + (a.2 : ℕ)) (by have := a.1.2; have := a.2.2; omega)
  have q4 : (4 * (a.1 : ℕ) + (a.2 : ℕ)) % 4 = (a.2 : ℕ) := by have := a.2.2; omega
  have d4 : (4 * (a.1 : ℕ) + (a.2 : ℕ)) / 4 = (a.1 : ℕ) := by have := a.2.2; omega
  rw [hv, q4, d4, hr] at h
  have e1 : ext P.D.lT (fun i => rowVal (led (P.rd m) a.1 i) a.2)
      (Blocks.nat (P.rows.tok.Kp.outPt P.rows.tok.Mk o)) =
      o.vals a - m (P.cP a) * P.rows.tok.Kp.outB P.rows.tok.Mk o := by
    rw [h]
    exact Blocks.ext_congr (fun i _ => (match_rowVal _ _).symm) _
  show ext P.D.lT (fun i => rowVal (led (P.rd m) a.1 i) a.2)
      (Blocks.nat (P.rows.tok.Kp.outPt P.rows.tok.Mk o)) +
      m (P.cP a) * P.rows.tok.Kp.outB P.rows.tok.Mk o = o.vals a
  rw [e1]
  ring

/-- Either map of the product layer of the squares has the extension of Pv: nothing is cut, as the
number of norms is a power of two. -/
theorem sq_vm (o : P.sq.R.L.toSum.T.par.Out) (bb : Bool) (z : ℕ → E) :
    ext (P.D.lL + 1 + (lDd P.D + P.D.lT)) (P.sq.R.L.vm o.st m bb) z =
      ext (P.D.lL + 1 + (lDd P.D + P.D.lT)) (Pv P.D (P.rd m) o.st.1.2) z := by
  refine Blocks.ext_congr (fun X hX => ?_) z
  cases bb
  · show (if P.D.nNu * 2 ^ (lDd P.D + P.D.lT) ≤ X then 0 else Pv P.D (P.rd m) o.st.1.2 X) = _
    have hn : P.D.nNu * 2 ^ (lDd P.D + P.D.lT) = 2 ^ (P.D.lL + 1 + (lDd P.D + P.D.lT)) := by
      show 2 * 2 ^ P.D.lL * 2 ^ (lDd P.D + P.D.lT) = _
      ring
    rw [if_neg (by omega)]
  · rfl

/-- The two rows on the end values of the product layer of the squares. -/
theorem sqE_of (L : NormsLast N e P.D (P.rd m) lNI b s y) (o : P.sq.R.L.toSum.T.par.Out)
    (hN : lNI = P.D.lL + 1) (hl : lDd P.D = b + s) (hγ : e.γ = o.st.1.2)
    (hr : e.r1 = Blocks.nat fun i =>
      (noKept P.sq.R.L.Sm).outPt P.sq.R.L.Mk o (P.sq.R.L.e.symm i))
    (hL : e.shL - e.β1 * y N.mL =
      o.vals false - m (P.cS false) * (noKept P.sq.R.L.Sm).outB P.sq.R.L.Mk o)
    (hR : e.shR - e.β1 * y N.mR =
      o.vals true - m (P.cS true) * (noKept P.sq.R.L.Sm).outB P.sq.R.L.Mk o) (bb : Bool) :
    P.sq.R.L.toSum.T.par.EHolds o m bb := by
  rw [ProdL.kval_iff]
  have h := L.endL
  rw [hN, ← hl, hγ, hr] at h
  have k := sq_vm P (m := m) o bb (Blocks.nat fun i =>
    (noKept P.sq.R.L.Sm).outPt P.sq.R.L.Mk o (P.sq.R.L.e.symm i))
  show ext (P.D.lL + 1 + (lDd P.D + P.D.lT)) (P.sq.R.L.vm o.st m bb) _ + _ = _
  rw [k, ← h]
  cases bb
  · show _ + m (P.cS false) * _ = _
    rw [hL]
    ring
  · show _ + m (P.cS true) * _ = _
    rw [← L.endR, hR]
    ring

end Cb.Pv.Lay.End
