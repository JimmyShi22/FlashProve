-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttMx.lean

The library's family of matrices, filled from the list of one attention link; and: at the reference
sizes the library reads in it, at every valid name of the attention segment, the cell that the
verifier's rule of addresses reads in the list.

* "attMx S g Z": in segment 2 g + 1 the slots 0, 1, 2 hold the link's own matrices "as" (its parts
  side by side), ah, ao; in segment 2 g the slot 5 holds the link's copy of qa; 0 elsewhere. The
  matrix bA of the list holds no cell and is not read. Nothing is said of the stream (slot 7 of
  segment 2 g): it is no member of the link's list, and no condition of the segment reads it.
  An entry of attMx is an entry of Z or 0. The matrices are not cut to the rows and columns that the
  verifier's matrices have.
* "agreeA": Cm.Seg.Agree (Cm.Seg.TS.tMA g (attMx S g Z)) (cellsA S Z): the hypothesis of the
  library's lever Cm.Seg.TS.attSpec_holds_iff.

What is compared with what: the library's reading tMA (Cm/TargetSegAtt.lean) of a family of matrices
of ours, against cellsA of ours (Johnson/Road/Lane5AttDef.lean).
-/
import Johnson.Road.Lane5AttAddr
import Johnson.Road.Lane5
import Cm.SegLayoutProofs
import Cm.TargetSegAtt

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model.All (DA KA DF)
open Inst.Model

/-- **The library's matrices, filled from the list of the attention link of group g.** -/
def attMx (S : Attention.Shape) (g : ℕ) (Z : Zs) : Mx := fun s r c =>
  if s = 2 * g + 1 then
    if r / 65536 = 0 then Z (c / (S.kAs / S.cf.NAs)) (r % 65536) (c % (S.kAs / S.cf.NAs))
    else if r / 65536 = 1 then Z S.cf.NAs (r % 65536) c
    else if r / 65536 = 2 then Z (S.cf.NAs + 1) (r % 65536) c
    else 0
  else if s = 2 * g ∧ r / 65536 = 5 then Z (S.cf.NAs + 3) (r % 65536) c
  else 0

variable (S : Attention.Shape) (g : ℕ) (Z : Zs)

/-- The arithmetic of a slot. -/
theorem slot_dm {σ r : ℕ} (hr : r < 65536) :
    (σ * 65536 + r) / 65536 = σ ∧ (σ * 65536 + r) % 65536 = r := by
  constructor <;> omega

theorem attMx_as {r : ℕ} (hr : r < 65536) (c : ℕ) :
    attMx S g Z (2 * g + 1) (0 * 65536 + r) c =
      Z (c / (S.kAs / S.cf.NAs)) r (c % (S.kAs / S.cf.NAs)) := by
  unfold attMx
  rw [if_pos rfl, (slot_dm hr).1, (slot_dm hr).2, if_pos rfl]

theorem attMx_ah {r : ℕ} (hr : r < 65536) (c : ℕ) :
    attMx S g Z (2 * g + 1) (1 * 65536 + r) c = Z S.cf.NAs r c := by
  unfold attMx
  rw [if_pos rfl, (slot_dm hr).1, (slot_dm hr).2, if_neg (show ¬ (1 : ℕ) = 0 by decide), if_pos rfl]

theorem attMx_ao {r : ℕ} (hr : r < 65536) (c : ℕ) :
    attMx S g Z (2 * g + 1) (2 * 65536 + r) c = Z (S.cf.NAs + 1) r c := by
  unfold attMx
  rw [if_pos rfl, (slot_dm hr).1, (slot_dm hr).2, if_neg (show ¬ (2 : ℕ) = 0 by decide),
    if_neg (show ¬ (2 : ℕ) = 1 by decide), if_pos rfl]

theorem attMx_qa {r : ℕ} (hr : r < 65536) (c : ℕ) :
    attMx S g Z (2 * g) (5 * 65536 + r) c = Z (S.cf.NAs + 3) r c := by
  unfold attMx
  rw [if_neg (show ¬ 2 * g = 2 * g + 1 by omega), (slot_dm hr).1, (slot_dm hr).2,
    if_pos (show 2 * g = 2 * g ∧ (5 : ℕ) = 5 from ⟨rfl, rfl⟩)]

/-- At the place of an own cell the matrices hold the entry of the list at the library's address. -/
theorem attMx_own (c : AttSeg.Raw) (hc : c.Valid DA) (ho : c.Own = true) :
    Cm.Seg.at' (attMx S g Z) (Cm.Seg.Name.att g c).place =
      zAt Z (portOf S (AttSeg.addr DA KA c)) := by
  have B := Cm.Seg.att_addr c hc ho
  show attMx S g Z (2 * g + 1) (Cm.Seg.plAtt c).1 (Cm.Seg.plAtt c).2 = _
  unfold Cm.Seg.plAtt Cm.Seg.stack
  rw [Cm.Seg.hSlot_eq, Cm.Seg.colsAtt_eq]
  generalize AttSeg.addr DA KA c = a at B ⊢
  obtain ⟨μ, r, col⟩ := a
  rcases B with ⟨e, b1, b2⟩ | ⟨e, b1, b2⟩ | ⟨e, b1, b2⟩
  · simp only at e b1 b2
    subst e
    have h0 : col / 7200 = 0 := Nat.div_eq_of_lt b2
    have h1 : col % 7200 = col := Nat.mod_eq_of_lt b2
    show attMx S g Z (2 * g + 1) ((0 + col / 7200) * 65536 + r) (col % 7200) =
      Z (col / (S.kAs / S.cf.NAs)) r (col % (S.kAs / S.cf.NAs))
    rw [h0, h1, Nat.add_zero]
    exact attMx_as S g Z b1 col
  · simp only at e b1 b2
    subst e
    have h0 : col / 7200 = 0 := Nat.div_eq_of_lt (by omega)
    have h1 : col % 7200 = col := Nat.mod_eq_of_lt (by omega)
    show attMx S g Z (2 * g + 1) ((1 + col / 7200) * 65536 + r) (col % 7200) = Z S.cf.NAs r col
    rw [h0, h1, Nat.add_zero]
    exact attMx_ah S g Z b1 col
  · simp only at e b1 b2
    subst e
    have h0 : col / 7200 = 0 := Nat.div_eq_of_lt (by omega)
    have h1 : col % 7200 = col := Nat.mod_eq_of_lt (by omega)
    show attMx S g Z (2 * g + 1) ((2 + col / 7200) * 65536 + r) (col % 7200) =
      Z (S.cf.NAs + 1) r col
    rw [h0, h1, Nat.add_zero]
    exact attMx_ao S g Z b1 col

theorem attRow_qa : 2 ^ AttSeg.lRow DA KA .qa = 65536 := by decide

/-- A borrowed cell stands inside the matrix qa. -/
theorem qa_range (c : AttSeg.Raw) (hc : c.Valid DA) (hq : (AttSeg.addr DA KA c).1 = .qa) :
    (AttSeg.addr DA KA c).2.1 < 65536 ∧ (AttSeg.addr DA KA c).2.2 < 1536 := by
  obtain ⟨h1, h2⟩ := AttSeg.AddrFacts.addrRange DA KA AttSeg.Calls.ref AttSeg.ref_dim_ok c hc
  rw [hq] at h1 h2
  rw [attRow_qa] at h1
  rw [AttSeg.ref_cols.2.2.2.2] at h2
  exact ⟨h1, h2⟩

/-- At the owner's place of a borrowed cell the matrices hold the entry of the link's copy of qa at
the library's address. -/
theorem attMx_bor (q : FFSeg.Cell) (c : AttSeg.Raw) (hc : c.Valid DA)
    (hq : (AttSeg.addr DA KA c).1 = .qa) (h1 : (FFSeg.addr DF q).1 = .qa)
    (h2 : (FFSeg.addr DF q).2 = (AttSeg.addr DA KA c).2) :
    Cm.Seg.at' (attMx S g Z) (Cm.Seg.Name.ff g q).place =
      zAt Z (portOf S (AttSeg.addr DA KA c)) := by
  obtain ⟨b1, b2⟩ := qa_range c hc hq
  show attMx S g Z (2 * g) (Cm.Seg.plFF q).1 (Cm.Seg.plFF q).2 = _
  unfold Cm.Seg.plFF Cm.Seg.stack
  rw [Cm.Seg.hSlot_eq, Cm.Seg.colsFF_eq, h1, h2]
  generalize AttSeg.addr DA KA c = a at hq b1 b2 ⊢
  obtain ⟨μ, r, col⟩ := a
  simp only at hq b1 b2
  subst hq
  have h0 : col / 5990 = 0 := Nat.div_eq_of_lt (by omega)
  have h3 : col % 5990 = col := Nat.mod_eq_of_lt (by omega)
  show attMx S g Z (2 * g) ((5 + col / 5990) * 65536 + r) (col % 5990) = Z (S.cf.NAs + 3) r col
  rw [h0, h3, Nat.add_zero]
  exact attMx_qa S g Z b1 col

variable {S}

/-- **At every valid name the library reads in attMx the cell of the verifier's rule.** -/
theorem agreeA (hS : AttSized S) :
    Cm.Seg.Agree (Cm.Seg.TS.tMA g (attMx S g Z)) (cellsA S Z) := by
  intro c hc
  show Cm.Seg.at' (attMx S g Z) (Cm.Seg.ownAtt g c).place = zAt Z (addrA S c)
  rw [addrA_ref hS c]
  cases c with
  | c ρ jj b x => exact attMx_own S g Z _ hc rfl
  | mx k b g' i => exact attMx_own S g Z _ hc rfl
  | den k b g' i => exact attMx_own S g Z _ hc rfl
  | ib k b g' i => exact attMx_own S g Z _ hc rfl
  | qh b g' i n => exact attMx_own S g Z _ hc rfl
  | qh' b g' i n => exact attMx_own S g Z _ hc rfl
  | qry k b g' i n =>
    exact attMx_bor S g Z _ _ hc rfl rfl (Inst.Model.All.addr_qry k b g' i n)
  | out k b g' i n =>
    exact attMx_bor S g Z _ _ hc rfl rfl (Inst.Model.All.addr_out k b g' i n)
  | key k lam g' j n =>
    exact attMx_bor S g Z _ _ hc rfl rfl (Inst.Model.All.addr_key k lam g' j n)
  | val k lam g' j n =>
    exact attMx_bor S g Z _ _ hc rfl rfl (Inst.Model.All.addr_val k lam g' j n)

/-- An own cell of the segment, read in attMx, is the cell of the verifier's rule. -/
theorem attMx_cell (hS : AttSized S) (c : AttSeg.Raw) (hc : c.Valid DA) (ho : c.Own = true) :
    Cm.Seg.at' (attMx S g Z) (Cm.Seg.Name.att g c).place = cellsA S Z c :=
  (attMx_own S g Z c hc ho).trans (congrArg (zAt Z) (addrA_ref hS c).symm)

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.agreeA
#print axioms OnBytes.Road.L5.attMx_cell
