-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/NormsPay.lean: from the ledger of the verifier's claims on the norms to what the chain
of a layers' sub-proof's own rounds owes at its end for the norms' two stretches.

The chain owes at its end (Cb/Pv/Lay/End/Last.lean), for the stretch of the sums of squares and the
stretch of the row products: the rows on the sent scalars, the linear row on the sent sum, and all
output claims of the two sumchecks. This file pays these five clauses, at the records of
Cb/Pv/Lay/At/Norms.lean, from three things. The ledger of the claims on the norms
(Cb/Pv/Lay/End/Led.lean) holds of early entries m and late entries u. The late entries are what the
tables of reads are meant to be (TablesTrue). For each sumcheck, the claim which it leaves, a letter
of the ledger, says its first output claim.

Main theorem: norms_pay.

Limits. hU1, hU2 (what the letters u1, u2 say), hst (the state that the first sumcheck's output
carries holds the drawn element) and TablesTrue are premises. That the ledger is a program's is not
said here. Sizes: five limbs; the width of the stream is B blocks of 2^s features.


-/
import Cb.Pv.Lay.End.Led
import Cb.Pv.Lay.End.NormsBill

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (lDd)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] (P : NormPar0 E) {J₂ : Type} [Fintype J₂]
  [DecidableEq P.J] [DecidableEq J₂]

/-- The five clauses that the chain owes at its end for the norms. -/
theorem norms_pay (U : NormsReads J₂) (p : Fin P.D.lT → E) (sW : Fin (P.D.nNu * 9) → E) (c : E)
    (o1 : P.sq.R.L.toSum.T.par.Out) (sP : Fin (P.D.nNu * 7) → E) (σ z : E)
    (o2 : P.rows.tok.toSum.T.par.Out) (zt : ℕ → E) (u1 u2 : Blocks.Form (P.J ⊕ J₂) E)
    (m : P.J → E) (u : J₂ → E) (b s B : ℕ) (hl : lDd P.D = b + s) (hd : P.D.d = B * 2 ^ s)
    (hB : B ≤ 2 ^ b) (hst : o1.st.1.2 = c)
    (T : TablesTrue (namesAt P U) (normsEAt P p sW c o1 sP σ z o2 zt) P.D (P.rd m) (P.D.lL + 1) b s
      B (Sum.elim m u))
    (h : TWhole.Ledger.Holds (normsLed (namesAt P U) (normsEAt P p sW c o1 sP σ z o2 zt) u1 u2 P.D
      (P.D.lL + 1) b B) (Sum.elim m u))
    (hU1 : Blocks.Form.val (Sum.elim m u) u1 = 0 → P.sq.R.L.toSum.T.par.UHolds o1 m)
    (hU2 : Blocks.Form.val (Sum.elim m u) u2 = 0 → P.rows.tok.toSum.T.par.UHolds o2 m) :
    P.sq.B ((p, fun q => sW (finProdFinEquiv q)), c) m ∧
      P.sq.R.L.toSum.T.par.OutHolds o1 m ∧
      (P.rows.led p m fun n => sP n - m (P.mkP n)) ∧ P.rows.tie ((p, sP), σ) z m ∧
      P.rows.tok.toSum.T.par.OutHolds o2 m := by
  have hn : P.D.nNu = 2 ^ (P.D.lL + 1) := by
    show 2 * 2 ^ P.D.lL = _
    rw [pow_succ, Nat.mul_comm]
  have L := norms_led_last _ _ u1 u2 P.D (P.rd m) (P.D.lL + 1) b s B _ hn hl hd hB T h
  obtain ⟨r1, r2⟩ := norms_rows _ _ u1 u2 P.D (P.D.lL + 1) b B _ ((ledOf_holds _ _).1 h)
  obtain ⟨a1, a2, a3, a4, a5⟩ :=
    norms_bill_at P U p sW c o1 sP σ z o2 zt m u (P.D.lL + 1) b s rfl hl hst L
  exact ⟨a1, ⟨hU1 r1, a2⟩, a3, a4, ⟨hU2 r2, a5⟩⟩

end Cb.Pv.Lay.End
