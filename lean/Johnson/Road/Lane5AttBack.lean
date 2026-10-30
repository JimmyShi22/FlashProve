-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttBack.lean

The way back, at the reference sizes: from the library's matrices to a list of the attention link
that is in order. It gives "AttOrd" (Johnson/Road/Lane5AttDef.lean) of the list that is READ OUT of
the matrices. It is no converse at one list: that is
Johnson/Road/Lane5AttIff.lean [not in this library]. It is the road to a value of AttOrd at the
reference sizes (Johnson/Road/Lane5AttMet.lean).

* "zsOf S g M": the list of the attention link of group g, read out of the library's matrices M: the
  parts of "as", ah, ao from the slots 0, 1, 2 of segment 2 g + 1; qa from slot 5 of segment 2 g;
  the matrix bA, which holds no cell, is 0.
* "agreeBack": the library reads in M, at every valid name, the cell that the verifier's rule reads
  in zsOf S g M.
* "ord_of_holds": if the conditions of segment 2 g + 1 hold at M and M is below 2^18 at the places
  of ALL valid names of the segment, the borrowed ones too, then AttOrd S (zsOf S g M).
* "ord_of_premise": under the premise, AttOrd S (zsOf S g (A (2 g + 1))): the bound on the borrowed
  cells comes from link 2 g through the seam.

Beside the hypotheses of Johnson/Road/Lane5AttLink.lean: hw: the parts of "as" have together at
least the library's 7,200 columns (from the verifier's own call: wide_of_shaped,
Johnson/Road/Lane5AttShape.lean).
-/
import Johnson.Road.Lane5AttLink

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model
open Inst.Model.All (DA KA DF SFK DAK)

/-- **The list of the attention link of group g, read out of the library's matrices.** -/
def zsOf (S : Attention.Shape) (g : ℕ) (M : Mx) : Zs := fun a r c =>
  if a < S.cf.NAs then M (2 * g + 1) (0 * 65536 + r) (a * (S.kAs / S.cf.NAs) + c)
  else if a = S.cf.NAs then M (2 * g + 1) (1 * 65536 + r) c
  else if a = S.cf.NAs + 1 then M (2 * g + 1) (2 * 65536 + r) c
  else if a = S.cf.NAs + 3 then M (2 * g) (5 * 65536 + r) c
  else 0

variable (S : Attention.Shape) (g : ℕ) (M : Mx)

theorem zsOf_as {a : ℕ} (ha : a < S.cf.NAs) (r c : ℕ) :
    zsOf S g M a r c = M (2 * g + 1) (0 * 65536 + r) (a * (S.kAs / S.cf.NAs) + c) := by
  unfold zsOf
  rw [if_pos ha]

theorem zsOf_ah (r c : ℕ) : zsOf S g M S.cf.NAs r c = M (2 * g + 1) (1 * 65536 + r) c := by
  unfold zsOf
  rw [if_neg (Nat.lt_irrefl _), if_pos rfl]

theorem zsOf_ao (r c : ℕ) : zsOf S g M (S.cf.NAs + 1) r c = M (2 * g + 1) (2 * 65536 + r) c := by
  unfold zsOf
  rw [if_neg (show ¬ S.cf.NAs + 1 < S.cf.NAs by omega),
    if_neg (show ¬ S.cf.NAs + 1 = S.cf.NAs by omega), if_pos rfl]

theorem zsOf_qa (r c : ℕ) : zsOf S g M (S.cf.NAs + 3) r c = M (2 * g) (5 * 65536 + r) c := by
  unfold zsOf
  rw [if_neg (show ¬ S.cf.NAs + 3 < S.cf.NAs by omega),
    if_neg (show ¬ S.cf.NAs + 3 = S.cf.NAs by omega),
    if_neg (show ¬ S.cf.NAs + 3 = S.cf.NAs + 1 by omega), if_pos rfl]

/-- An own cell. -/
theorem back_own (hw : 7200 ≤ S.kAs / S.cf.NAs * S.cf.NAs) (c : AttSeg.Raw) (hc : c.Valid DA)
    (ho : c.Own = true) :
    zAt (zsOf S g M) (portOf S (AttSeg.addr DA KA c)) =
      Cm.Seg.at' M (Cm.Seg.Name.att g c).place := by
  have B := Cm.Seg.att_addr c hc ho
  show _ = M (2 * g + 1) (Cm.Seg.plAtt c).1 (Cm.Seg.plAtt c).2
  unfold Cm.Seg.plAtt Cm.Seg.stack
  rw [Cm.Seg.hSlot_eq, Cm.Seg.colsAtt_eq]
  generalize AttSeg.addr DA KA c = a at B ⊢
  obtain ⟨μ, r, col⟩ := a
  rcases B with ⟨e, b1, b2⟩ | ⟨e, b1, b2⟩ | ⟨e, b1, b2⟩
  · simp only at e b1 b2
    subst e
    have h0 : col / 7200 = 0 := Nat.div_eq_of_lt b2
    have h1 : col % 7200 = col := Nat.mod_eq_of_lt b2
    have ha : col / (S.kAs / S.cf.NAs) < S.cf.NAs :=
      Nat.div_lt_of_lt_mul (lt_of_lt_of_le b2 hw)
    show zsOf S g M (col / (S.kAs / S.cf.NAs)) r (col % (S.kAs / S.cf.NAs)) =
      M (2 * g + 1) ((0 + col / 7200) * 65536 + r) (col % 7200)
    rw [h0, h1, Nat.add_zero, zsOf_as S g M ha, Nat.div_add_mod']
  · simp only at e b1 b2
    subst e
    have h0 : col / 7200 = 0 := Nat.div_eq_of_lt (by omega)
    have h1 : col % 7200 = col := Nat.mod_eq_of_lt (by omega)
    show zsOf S g M S.cf.NAs r col = M (2 * g + 1) ((1 + col / 7200) * 65536 + r) (col % 7200)
    rw [h0, h1, Nat.add_zero, zsOf_ah]
  · simp only at e b1 b2
    subst e
    have h0 : col / 7200 = 0 := Nat.div_eq_of_lt (by omega)
    have h1 : col % 7200 = col := Nat.mod_eq_of_lt (by omega)
    show zsOf S g M (S.cf.NAs + 1) r col =
      M (2 * g + 1) ((2 + col / 7200) * 65536 + r) (col % 7200)
    rw [h0, h1, Nat.add_zero, zsOf_ao]

/-- A borrowed cell. -/
theorem back_bor (q : FFSeg.Cell) (c : AttSeg.Raw) (hc : c.Valid DA)
    (hq : (AttSeg.addr DA KA c).1 = .qa) (h1 : (FFSeg.addr DF q).1 = .qa)
    (h2 : (FFSeg.addr DF q).2 = (AttSeg.addr DA KA c).2) :
    zAt (zsOf S g M) (portOf S (AttSeg.addr DA KA c)) =
      Cm.Seg.at' M (Cm.Seg.Name.ff g q).place := by
  obtain ⟨b1, b2⟩ := qa_range c hc hq
  show _ = M (2 * g) (Cm.Seg.plFF q).1 (Cm.Seg.plFF q).2
  unfold Cm.Seg.plFF Cm.Seg.stack
  rw [Cm.Seg.hSlot_eq, Cm.Seg.colsFF_eq, h1, h2]
  generalize AttSeg.addr DA KA c = a at hq b1 b2 ⊢
  obtain ⟨μ, r, col⟩ := a
  simp only at hq b1 b2
  subst hq
  have h0 : col / 5990 = 0 := Nat.div_eq_of_lt (by omega)
  have h3 : col % 5990 = col := Nat.mod_eq_of_lt (by omega)
  show zsOf S g M (S.cf.NAs + 3) r col = M (2 * g) ((5 + col / 5990) * 65536 + r) (col % 5990)
  rw [h0, h3, Nat.add_zero, zsOf_qa]

variable {S}

/-- **At every valid name the library reads in M the cell that the verifier's rule reads in the list
that is read out of M.** -/
theorem agreeBack (hS : AttSized S) (hw : 7200 ≤ S.kAs / S.cf.NAs * S.cf.NAs) :
    Cm.Seg.Agree (Cm.Seg.TS.tMA g M) (cellsA S (zsOf S g M)) := by
  intro c hc
  show Cm.Seg.at' M (Cm.Seg.ownAtt g c).place = zAt (zsOf S g M) (addrA S c)
  rw [addrA_ref hS c]
  cases c with
  | c ρ jj b x => exact (back_own S g M hw _ hc rfl).symm
  | mx k b g' i => exact (back_own S g M hw _ hc rfl).symm
  | den k b g' i => exact (back_own S g M hw _ hc rfl).symm
  | ib k b g' i => exact (back_own S g M hw _ hc rfl).symm
  | qh b g' i n => exact (back_own S g M hw _ hc rfl).symm
  | qh' b g' i n => exact (back_own S g M hw _ hc rfl).symm
  | qry k b g' i n =>
    exact (back_bor S g M _ _ hc rfl rfl (Inst.Model.All.addr_qry k b g' i n)).symm
  | out k b g' i n =>
    exact (back_bor S g M _ _ hc rfl rfl (Inst.Model.All.addr_out k b g' i n)).symm
  | key k lam g' j n =>
    exact (back_bor S g M _ _ hc rfl rfl (Inst.Model.All.addr_key k lam g' j n)).symm
  | val k lam g' j n =>
    exact (back_bor S g M _ _ hc rfl rfl (Inst.Model.All.addr_val k lam g' j n)).symm

variable {g M}

/-- **From the conditions of segment 2 g + 1 to AttOrd.** -/
theorem ord_of_holds (hg : g < 12) (hS : AttSized S)
    (hw : 7200 ≤ S.kAs / S.cf.NAs * S.cf.NAs) {s : Cm.Scales}
    (hsh : (s.kap (4 * g)).sh = S.cf.sh.getD 0 0)
    (hE : ∀ ι : ℕ, ι < S.u0 → ((S.Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι)
    (hb : ∀ c : AttSeg.Raw, c.Valid DA → |Cm.Seg.at' M (Cm.Seg.ownAtt g c).place| < 2 ^ 18)
    {Wz : Mat} {x : Instance ppref}
    (H : (Cm.Seg.TS.segM s (2 * g + 1)).Holds Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wz)
      (Cm.Seg.TS.cM M)) :
    AttOrd S (zsOf S g M) := by
  have Ag := agreeBack g M hS hw
  have R1 : AttSeg.RFraw (scl := SFK s.kap s.nf g) (DAK s.kap g) tbRef Cb.Gl.F
      (cellsA S (zsOf S g M)) := by
    refine ⟨fun c hc => ?_, (holdsA_iff hg s x Wz M _ Ag).1 H⟩
    have hc' : c.Valid DA := ((Cm.lay_valid_refK _).1 c).1 hc
    rw [← Ag c hc']
    exact hb c hc'
  have e : dimOf S = DAK s.kap g :=
    (dimOf_ref hS).trans (congrArg AttSeg.Dim.refK (hS.u0.trans (kap_rows_nat s (4 * g)).symm))
  rw [← e] at R1
  have h0 : ((sclOf S).κ 0).sh = ((SFK s.kap s.nf g).κ 0).sh := hsh.symm
  have R2 : AttSeg.RFraw (scl := sclOf S) (dimOf S) tbRef Cb.Gl.F (cellsA S (zsOf S g M)) :=
    Eq.mpr (rfraw_sh h0 (dimOf S) tbRef Cb.Gl.F (cellsA S (zsOf S g M))) R1
  exact ⟨rfraw_exp (scl := sclOf S) (D := dimOf S) (tb := tbRef) (tb' := tbOf S)
    (fun ι hι => ((tbOf_exp S ι).trans (hE ι hι)).symm) R2⟩

/-- **Under the premise the attention link's list, read out of link 2 g + 1's matrices, is in
order.** -/
theorem ord_of_premise (hg : g < 12) (hS : AttSized S)
    (hw : 7200 ≤ S.kAs / S.cf.NAs * S.cf.NAs) {s : Cm.Scales}
    (hsh : (s.kap (4 * g)).sh = S.cf.sh.getD 0 0)
    (hE : ∀ ι : ℕ, ι < S.u0 → ((S.Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι)
    {Wz : Mat} {x : Instance ppref} {A : ℕ → Mx}
    (P : Premise Cm.Seg.Hd.plain (Cm.Seg.TS.segM s) Wz x A) :
    AttOrd S (zsOf S g (A (2 * g + 1))) := by
  have hk : 2 * g + 1 < Cm.Seg.nSeg := by
    show 2 * g + 1 < 25
    omega
  refine ord_of_holds hg hS hw hsh hE (fun c hc => ?_) (P.link (2 * g + 1) hk).holds
  have hn := (Cm.lay_own_valid Cm.Seg.Hd.plain).2.1 g hg c hc
  have hq : (Cm.Seg.ownAtt g c).place ∈ Cm.Seg.reads Cm.Seg.Hd.plain (2 * g + 1) :=
    Or.inr (Or.inl ⟨g, c, rfl, hg, hc, rfl⟩)
  rw [P.seam (2 * g + 1) hk _ hq]
  exact (P.link _ (Cm.lay_inShape _ Cm.lay_figures.2.2.2.2.2 _ hn).1).small _ hn rfl

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.agreeBack
#print axioms OnBytes.Road.L5.ord_of_holds
#print axioms OnBytes.Road.L5.ord_of_premise
