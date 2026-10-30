-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/NormsBill.lean: the letters of the verifier's claims on the norms, read off what the
chain of a layers' sub-proof's own rounds has sent, drawn and put out; and what the claims then pay
of what that chain owes at its end.

Cb/Pv/Lay/End/NormsCl.lean writes the claims from a record NormsE of letters and a record NormsNames
of names of entries. Here both are made from the letters P : NormPar0 E of Cb/Pv/Lay/At/Norms.lean
and from the parts of a last statement of the chain: the token point p, the scalars sW sent for the
sums of squares, the element c drawn behind them, the output o1 of the first sumcheck, the scalars
sP sent for the row products, the element σ, the sent sum z and the output o2 of the second
sumcheck. The entries are P.J, which holds the mask entries, beside a type J₂ of late entries.

Main definitions: NormsReads (names of the late entries), namesAt, normsEAt.
Main theorem: norms_bill_at: NormsLast at these letters gives the rows on the sent scalars of both
stretches, the linear row, and the rows on the end values of both sumchecks.

Limits. The first output claim of either sumcheck (the row on the hiding coefficients) is not here.
The premise hst says that the state which the first sumcheck's output carries holds the drawn
element c. It is meant for the output of a run; that it holds there is not shown here. zt, the tail
of the lookup's point, is a letter.


-/
import Cb.Pv.Lay.End.NormsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Finset Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (lDd)

/-- The names of the late entries that the claims on the norms read. -/
structure NormsReads (J₂ : Type) where
  uXi : ℕ → ℕ → ℕ → J₂
  uP : ℕ → ℕ → J₂
  uR : ℕ → ℕ → J₂
  uSel : ℕ → ℕ → J₂

variable {E : Type} [Field E] [Fintype E] [scl : Scl] (P : NormPar0 E) {J₂ : Type}

/-- The names of the entries. Past the last number of a kind the name is of no account. -/
def namesAt (U : NormsReads J₂) : NormsNames (P.J ⊕ J₂) where
  mW x := if h : x < P.D.nNu * 9 then
    .inl (P.mkS (finProdFinEquiv.symm ⟨x, h⟩).1 (finProdFinEquiv.symm ⟨x, h⟩).2) else .inl P.rP
  mP x := if h : x < P.D.nNu * 7 then .inl (P.mkP ⟨x, h⟩) else .inl P.rP
  mCl := .inl P.rP
  mL := .inl (P.cS false)
  mR := .inl (P.cS true)
  m2 x := if h : x < P.D.nNu * 4 then .inl (P.cP (finProdFinEquiv.symm ⟨x, h⟩)) else .inl P.rP
  uXi ν l kh := .inr (U.uXi ν l kh)
  uP ν n := .inr (U.uP ν n)
  uR ν n := .inr (U.uR ν n)
  uSel l x := .inr (U.uSel l x)

/-- The letters of the claims, off the parts of a last statement. -/
noncomputable def normsEAt (p : Fin P.D.lT → E) (sW : Fin (P.D.nNu * 9) → E) (c : E)
    (o1 : P.sq.R.L.toSum.T.par.Out) (sP : Fin (P.D.nNu * 7) → E) (σ z : E)
    (o2 : P.rows.tok.toSum.T.par.Out) (zt : ℕ → E) : NormsE E where
  pV := Blocks.nat p
  r1 := Blocks.nat fun i => (noKept P.sq.R.L.Sm).outPt P.sq.R.L.Mk o1 (P.sq.R.L.e.symm i)
  r2 := Blocks.nat (P.rows.tok.Kp.outPt P.rows.tok.Mk o2)
  zt := zt
  γ := c
  ω := σ
  β1 := (noKept P.sq.R.L.Sm).outB P.sq.R.L.Mk o1
  β2 := P.rows.tok.Kp.outB P.rows.tok.Mk o2
  shW x := if h : x < P.D.nNu * 9 then sW ⟨x, h⟩ else 0
  shP x := if h : x < P.D.nNu * 7 then sP ⟨x, h⟩ else 0
  shCl := z
  shL := o1.vals false
  shR := o1.vals true
  sh2 x := if h : x < P.D.nNu * 4 then o2.vals (finProdFinEquiv.symm ⟨x, h⟩) else 0

omit scl in
/-- A pair of numbers as one, in the order of finProdFinEquiv. -/
theorem pair_eq {a n : ℕ} (ν : Fin a) (x : Fin n) (h : n * (ν : ℕ) + (x : ℕ) < a * n) :
    (⟨n * (ν : ℕ) + (x : ℕ), h⟩ : Fin (a * n)) = finProdFinEquiv (ν, x) :=
  Fin.ext (by
    rw [finProdFinEquiv_apply_val]
    exact Nat.add_comm _ _)

omit scl in
theorem pair_lt {a n : ℕ} (ν : Fin a) (x : Fin n) : n * (ν : ℕ) + (x : ℕ) < a * n := by
  have h1 := ν.2
  have h2 := x.2
  calc n * (ν : ℕ) + (x : ℕ) < n * (ν : ℕ) + n := by omega
    _ = n * ((ν : ℕ) + 1) := by ring
    _ ≤ n * a := Nat.mul_le_mul_left _ h1
    _ = a * n := Nat.mul_comm _ _

/-- What the claims on the norms pay of what the chain owes at its end. -/
theorem norms_bill_at (U : NormsReads J₂) (p : Fin P.D.lT → E) (sW : Fin (P.D.nNu * 9) → E)
    (c : E) (o1 : P.sq.R.L.toSum.T.par.Out) (sP : Fin (P.D.nNu * 7) → E) (σ z : E)
    (o2 : P.rows.tok.toSum.T.par.Out) (zt : ℕ → E) (m : P.J → E) (u : J₂ → E) (lNI b s : ℕ)
    (hN : lNI = P.D.lL + 1) (hl : lDd P.D = b + s) (hst : o1.st.1.2 = c)
    (L : NormsLast (namesAt P U) (normsEAt P p sW c o1 sP σ z o2 zt) P.D (P.rd m) lNI b s
      (Sum.elim m u)) :
    P.sq.B ((p, fun q => sW (finProdFinEquiv q)), c) m ∧
      (∀ bb, P.sq.R.L.toSum.T.par.EHolds o1 m bb) ∧
      (P.rows.led p m fun n => sP n - m (P.mkP n)) ∧ P.rows.tie ((p, sP), σ) z m ∧
      ∀ a, P.rows.tok.toSum.T.par.EHolds o2 m a := by
  have hP : ∀ n : Fin (P.D.nNu * 7),
      (normsEAt P p sW c o1 sP σ z o2 zt).shP (n : ℕ) -
        Sum.elim m u ((namesAt P U).mP (n : ℕ)) = sP n - m (P.mkP n) := fun n => by
    show (if h : (n : ℕ) < P.D.nNu * 7 then sP ⟨n, h⟩ else 0) -
      Sum.elim m u (if h : (n : ℕ) < P.D.nNu * 7 then .inl (P.mkP ⟨n, h⟩) else .inl P.rP) = _
    rw [dif_pos n.2, dif_pos n.2]
    rfl
  refine ⟨sqB_of P L p _ c rfl fun ν x => ?_, sqE_of P L o1 hN hl hst.symm rfl ?_ ?_,
    rowsLed_of P L p sP rfl hP, tie_of P L p sP σ z rfl hP rfl, fun a => rowsE_of P L o2 rfl a ?_⟩
  · show (if h : 9 * (ν : ℕ) + (x : ℕ) < P.D.nNu * 9 then sW ⟨_, h⟩ else 0) -
      Sum.elim m u (if h : 9 * (ν : ℕ) + (x : ℕ) < P.D.nNu * 9 then
        .inl (P.mkS (finProdFinEquiv.symm ⟨_, h⟩).1 (finProdFinEquiv.symm ⟨_, h⟩).2)
        else .inl P.rP) = _
    rw [dif_pos (pair_lt ν x), dif_pos (pair_lt ν x), pair_eq ν x (pair_lt ν x),
      Equiv.symm_apply_apply]
    rfl
  · show o1.vals false - (noKept P.sq.R.L.Sm).outB P.sq.R.L.Mk o1 * m (P.cS false) =
      o1.vals false - m (P.cS false) * (noKept P.sq.R.L.Sm).outB P.sq.R.L.Mk o1
    ring
  · show o1.vals true - (noKept P.sq.R.L.Sm).outB P.sq.R.L.Mk o1 * m (P.cS true) =
      o1.vals true - m (P.cS true) * (noKept P.sq.R.L.Sm).outB P.sq.R.L.Mk o1
    ring
  · show (if h : 4 * (a.1 : ℕ) + (a.2 : ℕ) < P.D.nNu * 4 then
        o2.vals (finProdFinEquiv.symm ⟨_, h⟩) else 0) - _ *
      Sum.elim m u (if h : 4 * (a.1 : ℕ) + (a.2 : ℕ) < P.D.nNu * 4 then
        .inl (P.cP (finProdFinEquiv.symm ⟨_, h⟩)) else .inl P.rP) = _
    rw [dif_pos (pair_lt a.1 a.2), dif_pos (pair_lt a.1 a.2), pair_eq a.1 a.2 (pair_lt a.1 a.2),
      Equiv.symm_apply_apply]
    show o2.vals a - P.rows.tok.Kp.outB P.rows.tok.Mk o2 * m (P.cP a) =
      o2.vals a - m (P.cP a) * P.rows.tok.Kp.outB P.rows.tok.Mk o2
    ring

end Cb.Pv.Lay.End
