-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/TermsPay.lean: from the verifier's claims on the end values of the sumcheck of the
terms to the rows on end values that the chain of a layers' sub-proof's own rounds owes at its end.

The chain owes at its end, for the sumcheck of the terms, the output rows on its end values. This
file pays them, at the parameters of Cb/Pv/Lay/At/Terms.lean, from two things. Every form of termsCl
(Cb/Pv/Lay/End/TermsCl.lean) is worth 0 on early entries m and late entries u. The late entries are
what the tables of reads are meant to be (TermsTrue).

Main names:
  `tm_ev`: what the output row on an end value says at the parameters of Cb/Pv/Lay/At/Terms.lean.
  `numA`: the number of an end value. `pick`: a function of the end values' names as a function of
  their numbers.
  `TermsReads`, `namesT`, `termsEAt`: the names and letters of termsCl at an output of the sumcheck.
  `terms_pay`: the rows on all end values.
Limits: TermsTrue is a premise. That the list of forms is a program's is not said here. The first
output row of the sumcheck is not paid here: the chain does not owe it at its end. That the drawn
coefficient is not 0 is not paid here either.


-/
import Cb.Pv.Lay.End.TermsCl
import Cb.Pv.Lay.At.Terms

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Cb Finset Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim)

/-- The number of an end value: reciprocals, then scores, then the selectors' entries. -/
def numA (D : Dim) : ShA D → ℕ :=
  Sum.elim (fun ν => ν) (Sum.elim (fun l => D.nNu + l) fun p => D.nNu + D.ne + p.1 * D.nx + p.2)

/-- A function of the end values' names as a function of their numbers; d beyond them. -/
def pick {α : Type} (D : Dim) (f : ShA D → α) (d : α) (x : ℕ) : α :=
  if h : x < D.nNu then f (.inl ⟨x, h⟩)
  else if h2 : x - D.nNu < D.ne then f (.inr (.inl ⟨x - D.nNu, h2⟩))
  else if h3 : (x - D.nNu - D.ne) / D.nx < D.ne ∧ (x - D.nNu - D.ne) % D.nx < D.nx then
    f (.inr (.inr (⟨(x - D.nNu - D.ne) / D.nx, h3.1⟩, ⟨(x - D.nNu - D.ne) % D.nx, h3.2⟩)))
  else d

theorem pick_num {α : Type} (D : Dim) (f : ShA D → α) (d : α) (a : ShA D) :
    pick D f d (numA D a) = f a := by
  rcases a with ν | l | p
  · show pick D f d ν = _
    unfold pick
    rw [dif_pos ν.isLt]
  · show pick D f d (D.nNu + l) = _
    unfold pick
    have e : D.nNu + (l : ℕ) - D.nNu = l := Nat.add_sub_cancel_left _ _
    rw [dif_neg (by omega), dif_pos (by rw [e]; exact l.isLt)]
    congr 3
    exact Fin.ext e
  · show pick D f d (D.nNu + D.ne + p.1 * D.nx + p.2) = _
    unfold pick
    have h2 := p.2.isLt
    have e : D.nNu + D.ne + (p.1 : ℕ) * D.nx + p.2 - D.nNu - D.ne = p.1 * D.nx + p.2 := by omega
    have d1 : ((p.1 : ℕ) * D.nx + p.2) / D.nx = p.1 := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h2, Nat.zero_add]
    have d2 : ((p.1 : ℕ) * D.nx + p.2) % D.nx = p.2 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]
    rw [dif_neg (by omega), dif_neg (by omega),
      dif_pos (by rw [e, d1, d2]; exact ⟨p.1.isLt, h2⟩)]
    congr 3
    exact Prod.ext
      (Fin.ext (show (D.nNu + D.ne + (p.1 : ℕ) * D.nx + p.2 - D.nNu - D.ne) / D.nx = p.1 by
        rw [e, d1]))
      (Fin.ext (show (D.nNu + D.ne + (p.1 : ℕ) * D.nx + p.2 - D.nNu - D.ne) % D.nx = p.2 by
        rw [e, d2]))

variable {E : Type} [Field E] [Fintype E] [scl : Scl] (P : TermPar0 E)

/-- A shown contraction is, as a function of the point, the extension of a vector. -/
theorem sh9_isExt (t : Inst.Model.FFSeg.Cell → E) (z : ℕ → E) (a : ShA P.D) :
    IsExt P.D.lT fun u => sh9 P.D (recAt P.D t z u) a := by
  rcases a with ν | l | p <;> exact IsExt.of _

/-- What the output row on an end value says. -/
theorem tm_ev (o : P.tm.toSum.T.par.Out) (m : P.J → E) (a : ShA P.D) :
    P.tm.toSum.T.par.EHolds o m a ↔
      sh9 P.D (recAt P.D (P.rd m) o.st (Blocks.nat (P.tm.Kp.outPt P.tm.Mk o))) a +
          m (P.cT a) * P.tm.Kp.outB P.tm.Mk o = o.vals a := by
  rw [P.tm.ev_iff o m a, ← (sh9_isExt P (P.rd m) o.st a).cube]
  exact Iff.rfl

variable {J₂ : Type}

/-- The names of the reads at the end point, among the late entries. -/
structure TermsReads (J₂ : Type) where
  uRow : ℕ → ℕ → J₂
  uSc : ℕ → ℕ → J₂
  uSel : ℕ → ℕ → ℕ → J₂

/-- The names of termsCl: the masks among the early entries, the reads among the late ones. -/
def namesT (U : TermsReads J₂) : TermsNames (P.J ⊕ J₂) where
  mT := fun x => .inl (pick P.D P.cT P.rT x)
  uRow := fun ν n => .inr (U.uRow ν n)
  uSc := fun l k => .inr (U.uSc l k)
  uSel := fun l x k => .inr (U.uSel l x k)

/-- The letters of termsCl at an output of the sumcheck. -/
noncomputable def termsEAt (o : P.tm.toSum.T.par.Out) : TermsE E where
  rt := Blocks.nat (P.tm.Kp.outPt P.tm.Mk o)
  β := P.tm.Kp.outB P.tm.Mk o
  sh := pick P.D o.vals 0

variable [Fintype J₂] [DecidableEq P.J] [DecidableEq J₂]

/-- The rows on all end values of the sumcheck of the terms. -/
theorem terms_pay (U : TermsReads J₂) (o : P.tm.toSum.T.par.Out) (m : P.J → E) (u : J₂ → E)
    (T : TermsTrue (namesT P U) (termsEAt P o) P.D (P.rd m) (Sum.elim m u))
    (h : ∀ f ∈ termsCl (namesT P U) (termsEAt P o) P.D, Blocks.Form.val (Sum.elim m u) f = 0) :
    ∀ a, P.tm.toSum.T.par.EHolds o m a := by
  have L := terms_last (namesT P U) (termsEAt P o) P.D (P.rd m) o.st (fun _ _ => 0)
    (fun l' j => Inst.Model.FFSeg.hhU P.D (P.rd m) (2 * l' + 1) (P.D.fe + j)
      (Blocks.nat (P.tm.Kp.outPt P.tm.Mk o))) (Sum.elim m u) T h
  intro a
  rw [tm_ev]
  have key : ∀ x : ShA P.D,
      pick P.D o.vals 0 (numA P.D x) -
          P.tm.Kp.outB P.tm.Mk o * m (pick P.D P.cT P.rT (numA P.D x)) =
        sh9 P.D (recAt P.D (P.rd m) o.st (Blocks.nat (P.tm.Kp.outPt P.tm.Mk o))) x := by
    intro x
    rcases x with ν | l | p
    · exact L.recip ν ν.isLt
    · exact L.sc l l.isLt
    · exact L.sel p.1 p.2 p.1.isLt p.2.isLt
  have k := key a
  rw [pick_num, pick_num] at k
  linear_combination -k

end Cb.Pv.Lay.End

#print axioms Cb.Pv.Lay.End.terms_pay
