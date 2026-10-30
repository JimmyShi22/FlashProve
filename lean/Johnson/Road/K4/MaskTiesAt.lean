-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/MaskTiesAt.lean: the record MaskTies of Johnson/Road/K4/SlotsOfLed.lean: at the
library's own names of the mask entries, the entries are the mask at the hearing's slots' numbers.
First at any letters of the library's chain, from what the messages hold at each typed name; then at
the value of Johnson/Road/K4/Value.lean, from the numbers of its plan.

The library's names of the mask entries are functions of a number (namesAt, namesT, gNamesAt in
Cb/Pv/Lay/End/NormsBill.lean, TermsPay.lean, GatedPay.lean): number n of a kind is the typed name of
a pair or of an end value. Johnson/Road/K4/ValueMasks.lean says what the value's messages hold at
each typed name. Here the two are put together, number by number.

Main names:
  `pair_val`: a number below a c, cut into a pair and put together again.
  `numA_lt`: the number of an end value of the terms is below their number.
  `maskTies_of`: MaskTies at any letters Pf, entries Sum.elim (Pf.msg m) u.
  `SlotNums`: the plan's numbers are the hearing's; the plan's numbering of the terms' end values is
    the library's; the slots lie within the mask row.
  `maskTies_at`: MaskTies at the value Q.full and the mask Q.maskAt m.
Limits. SlotNums is a premise: that a hearing holds the plan's numbers is
Johnson/Road/K4/SlotsTie.lean's matter, at a plan whose numbers are slotsAt's; that the slots lie
within the mask row is asked in eight inequalities. Nothing on what lies under a slot. Nothing on
soundness.


-/
import Johnson.Road.K4.SlotsOfLed
import Johnson.Road.K4.ValueMasks

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes.Model.Layer (Own)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim)

/-- A number below a c, cut into a pair by finProdFinEquiv and put together again. -/
theorem pair_val {a c n : ℕ} (h : n < a * c) :
    c * ((finProdFinEquiv.symm (⟨n, h⟩ : Fin (a * c))).1 : ℕ) +
      ((finProdFinEquiv.symm (⟨n, h⟩ : Fin (a * c))).2 : ℕ) = n := by
  have e := finProdFinEquiv_apply_val (finProdFinEquiv.symm (⟨n, h⟩ : Fin (a * c)))
  rw [Equiv.apply_symm_apply] at e
  exact (e.trans (Nat.add_comm _ _)).symm

/-- The number of an end value of the terms is below their number. -/
theorem numA_lt (D : Dim) (q : ShA D) : numA D q < D.nNu + D.ne + D.ne * D.nx := by
  rcases q with ν | l | p
  · show (ν : ℕ) < _
    have := ν.2
    omega
  · show D.nNu + (l : ℕ) < _
    have := l.2
    omega
  · show D.nNu + D.ne + (p.1 : ℕ) * D.nx + (p.2 : ℕ) < _
    have h1 : (p.1 : ℕ) * D.nx + (p.2 : ℕ) < D.ne * D.nx := by
      calc (p.1 : ℕ) * D.nx + (p.2 : ℕ) < (p.1 : ℕ) * D.nx + D.nx := by
            have := p.2.2
            omega
        _ = ((p.1 : ℕ) + 1) * D.nx := by ring
        _ ≤ D.ne * D.nx := Nat.mul_le_mul_right _ p.1.2
    omega

theorem ite_le_one (b : Bool) : (if b then 1 else 0) ≤ 1 := by cases b <;> simp

variable {E' : Type} [Field E'] [Fintype E'] [scl : Scl] {M X : Type}

/-- **MaskTies at any letters of the library's chain**, from what the messages hold at each typed
name of a mask entry. -/
theorem maskTies_of (Pf : FullPar E' M X) (m : M) {J₂ : Type} (u : J₂ → E') (mask : ℕ → E')
    (o : Own) (UN : NormsReads J₂) (UT : TermsReads J₂) (UG : GatedReads J₂)
    (cS : ∀ b : Bool, Pf.msg m (Pf.cS b) = mask (o.H.wpl.sL + (if b then 1 else 0)))
    (hsR : o.H.wpl.sR = o.H.wpl.sL + 1) (rP : Pf.msg m Pf.rP = mask o.H.tV.sCl)
    (cP : ∀ q : Fin Pf.D.nNu × Fin 4,
      Pf.msg m (Pf.cP q) = mask (o.H.tV.sEnd + 4 * (q.1 : ℕ) + (q.2 : ℕ)))
    (mkS : ∀ (i : Fin Pf.D.nNu) (s : Fin 9),
      Pf.msg m (Pf.mkS i s) = mask (o.H.sW + 9 * (i : ℕ) + (s : ℕ)))
    (mkP : ∀ i : Fin (Pf.D.nNu * 7), Pf.msg m (Pf.mkP i) = mask (o.H.sPv + (i : ℕ)))
    (cT : ∀ tT, o.H.tT = some tT → ∀ q : ShA Pf.D,
      Pf.msg m (Pf.cT q) = mask (tT.sEnd + numA Pf.D q))
    (c5 : ∀ b : Bool, Pf.msg m (Pf.c5 b) = mask (o.hd.sL + (if b then 1 else 0)))
    (h5R : o.hd.sR = o.hd.sL + 1)
    (c6 : ∀ o2, o.hd2 = some o2 → ∀ b : Bool,
      Pf.msg m (Pf.c6 b) = mask (o2.sL + (if b then 1 else 0)))
    (h6R : ∀ o2, o.hd2 = some o2 → o2.sR = o2.sL + 1) :
    MaskTies mask o Pf.D (namesAt Pf.nr UN) (namesT Pf.tp UT) (gNamesAt Pf.fp UG)
      (Sum.elim (Pf.msg m) u) where
  mL := cS false
  mR := (cS true).trans (congrArg mask hsR.symm)
  mCl := rP
  m2 := fun n hn => by
    have hn' : n < Pf.D.nNu * 4 := by omega
    have e : (namesAt Pf.nr UN).m2 n = .inl (Pf.cP (finProdFinEquiv.symm ⟨n, hn'⟩)) :=
      dif_pos hn'
    rw [e]
    show Pf.msg m (Pf.cP _) = _
    rw [cP, Nat.add_assoc, pair_val hn']
  mW := fun n hn => by
    have hn' : n < Pf.D.nNu * 9 := by omega
    have e : (namesAt Pf.nr UN).mW n = .inl (Pf.mkS (finProdFinEquiv.symm ⟨n, hn'⟩).1
        (finProdFinEquiv.symm ⟨n, hn'⟩).2) := dif_pos hn'
    rw [e]
    show Pf.msg m (Pf.mkS _ _) = _
    rw [mkS, Nat.add_assoc, pair_val hn']
  mP := fun n hn => by
    have hn' : n < Pf.D.nNu * 7 := by omega
    have e : (namesAt Pf.nr UN).mP n = .inl (Pf.mkP ⟨n, hn'⟩) := dif_pos hn'
    rw [e]
    show Pf.msg m (Pf.mkP _) = _
    rw [mkP]
  mT := fun tT hT n hn => by
    obtain ⟨q, rfl⟩ := numA_surj hn
    show Pf.msg m (pick Pf.D Pf.cT Pf.rT (numA Pf.D q)) = _
    rw [pick_num]
    exact cT tT hT q
  m5L := c5 false
  m5R := (c5 true).trans (congrArg mask h5R.symm)
  m6L := fun o2 h2 => c6 o2 h2 false
  m6R := fun o2 h2 => (c6 o2 h2 true).trans (congrArg mask (h6R o2 h2).symm)

/-- The plan's numbers are the hearing's; its numbering of the terms' end values is the library's;
the slots lie within the mask row. -/
structure SlotNums (Q : Plan4 E' M X) (o : Own) : Prop where
  sW : Q.sW = o.H.sW
  vS : Q.vS = o.H.wpl.sL
  sR : o.H.wpl.sR = o.H.wpl.sL + 1
  sP : Q.sP = o.H.sPv
  cP0 : Q.cP0 = o.H.tV.sCl
  vP : Q.vP = o.H.tV.sEnd
  vT : ∀ tT, o.H.tT = some tT → Q.vT = tT.sEnd
  numT : ∀ q, Q.numT q = numA Q.D q
  v5 : Q.v5 = o.hd.sL
  s5R : o.hd.sR = o.hd.sL + 1
  v6 : ∀ o2, o.hd2 = some o2 → Q.v6 = o2.sL
  s6R : ∀ o2, o.hd2 = some o2 → o2.sR = o2.sL + 1
  rW : Q.sW + 9 * Q.D.nNu ≤ Q.ns
  rS : Q.vS + 1 ≤ Q.ns
  rP : Q.sP + Q.D.nNu * 7 ≤ Q.ns
  rCl : Q.cP0 ≤ Q.ns
  r2 : Q.vP + 4 * Q.D.nNu ≤ Q.ns
  rT : Q.vT + (Q.D.nNu + Q.D.ne + Q.D.ne * Q.D.nx) ≤ Q.ns
  r5 : Q.v5 + 1 ≤ Q.ns
  r6 : Q.v6 + 1 ≤ Q.ns

/-- **MaskTies at the value.** -/
theorem maskTies_at (Q : Plan4 E' M X) (m : M) {J₂ : Type} (u : J₂ → E') {o : Own}
    (S : SlotNums Q o) (UN : NormsReads J₂) (UT : TermsReads J₂) (UG : GatedReads J₂) :
    MaskTies (Q.maskAt m) o Q.full.D (namesAt Q.full.nr UN) (namesT Q.full.tp UT)
      (gNamesAt Q.full.fp UG) (Sum.elim (Q.full.msg m) u) :=
  maskTies_of Q.full m u (Q.maskAt m) o UN UT UG
    (fun b => (Q.msg_cS m b (Nat.le_trans (Nat.add_le_add_left (ite_le_one b) _) S.rS)).trans
      (congrArg (fun s => Q.maskAt m (s + (if b then 1 else 0))) S.vS))
    S.sR ((Q.msg_rP m S.rCl).trans (congrArg (Q.maskAt m) S.cP0))
    (fun q => (Q.msg_cP m q (by
        have h1 : (q.1 : ℕ) < Q.D.nNu := q.1.2
        have h2 := q.2.2
        have h3 := S.r2
        omega)).trans
      (congrArg (fun s => Q.maskAt m (s + 4 * (q.1 : ℕ) + (q.2 : ℕ))) S.vP))
    (fun i s => (Q.msg_mkS m i s (by
        have h1 : (i : ℕ) < Q.D.nNu := i.2
        have h2 := s.2
        have h3 := S.rW
        omega)).trans
      (congrArg (fun w => Q.maskAt m (w + 9 * (i : ℕ) + (s : ℕ))) S.sW))
    (fun i => (Q.msg_mkP m i (by
        have h1 : (i : ℕ) < Q.D.nNu * 7 := i.2
        have h3 := S.rP
        omega)).trans
      (congrArg (fun w => Q.maskAt m (w + (i : ℕ))) S.sP))
    (fun tT hT q => (Q.msg_cT m q (by
        have h1 := numA_lt Q.D q
        have h3 := S.rT
        rw [S.numT]
        omega)).trans (by rw [S.numT, S.vT tT hT]; rfl))
    (fun b => (Q.msg_c5 m b (Nat.le_trans (Nat.add_le_add_left (ite_le_one b) _) S.r5)).trans
      (congrArg (fun s => Q.maskAt m (s + (if b then 1 else 0))) S.v5))
    S.s5R
    (fun o2 h2 b =>
      (Q.msg_c6 m b (Nat.le_trans (Nat.add_le_add_left (ite_le_one b) _) S.r6)).trans
        (congrArg (fun s => Q.maskAt m (s + (if b then 1 else 0))) (S.v6 o2 h2)))
    S.s6R

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.pair_val
#print axioms OnBytes.Road.K4.numA_lt
#print axioms OnBytes.Road.K4.ite_le_one
#print axioms OnBytes.Road.K4.maskTies_of
#print axioms OnBytes.Road.K4.maskTies_at
