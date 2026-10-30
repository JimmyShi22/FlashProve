-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/NormsIff.lean: the converse of norms_last: on entries with true tables, what the
claims on the norms say on cells gives the claims.

Cb/Pv/Lay/End/NormsCl.lean shows that, on entries with true tables, the claims on the norms give the
record NormsLast. This file shows the converse. So nothing is lost between the list of forms and the
record, and whoever has cells, points and shown values that meet the record has a ledger that holds,
on entries with true tables and with the two claims that the sumchecks leave.

Main theorems: norms_cl_of_last; norms_cl_iff.

Limits: as Cb/Pv/Lay/End/NormsCl.lean. Nothing on an honest prover: the record is a premise.


-/
import Cb.Pv.Lay.End.NormsCl

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Finset
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell led npOf lDd)
open Inst.Model.Ledger (saF sbF RloF RhiF)
open Blocks (ext Form)

variable {E J : Type} [Field E] [Fintype J] [DecidableEq J] (N : NormsNames J) (e : NormsE E)

/-- On entries with true tables, NormsLast and the two claims that the sumchecks leave give every
form of the list. -/
theorem norms_cl_of_last [Scl] (u1 u2 : Form J E) (D : Dim) (t : Cell → E) (lNI b s B : ℕ)
    (y : J → E) (hn : D.nNu = 2 ^ lNI) (hl : lDd D = b + s) (hd : D.d = B * 2 ^ s)
    (hB : B ≤ 2 ^ b) (T : TablesTrue N e D t lNI b s B y) (L : NormsLast N e D t lNI b s y)
    (h1 : Form.val y u1 = 0) (h2 : Form.val y u2 = 0) :
    ∀ f ∈ normsCl N e u1 u2 D lNI b B, Form.val y f = 0 := by
  intro f hf
  unfold normsCl clNorms clLedger clHot at hf
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false] at hf
  rcases hf with (rfl | rfl | rfl) | rfl | (rfl | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) |
    ⟨l, hl', rfl⟩
  · exact h1
  · unfold cSame
    rw [map_sub, val_hL, val_hR, L.endR, sub_self]
  · unfold cEnd
    rw [map_sub, val_hL, map_sum, L.endL, ext_Pv_point D t e.γ e.r1 lNI b s B hl hd hB, hn,
      sub_eq_zero]
    refine sum_congr rfl fun i hi => ?_
    have h5 : i / 5 < 2 ^ lNI * B :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact mem_range.mp hi)
    have hν : i / 5 / B < D.nNu := by
      rw [hn]
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h5)
    have hB0 : 0 < B := by
      rcases Nat.eq_zero_or_pos B with h0 | h0
      · rw [h0, Nat.mul_zero] at h5
        exact absurd h5 (Nat.not_lt_zero _)
      · exact h0
    rw [map_smul, Form.val_ent, smul_eq_mul,
      T.xi _ _ _ hν (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ hB0)]
  · unfold cBatch hCl
    rw [map_sub, Form.val_masked, map_sum, L.batch, sub_eq_zero]
    exact sum_congr rfl fun x _ => by rw [map_smul, val_hP, smul_eq_mul]
  · exact h2
  · unfold cShown
    rw [map_sub, val_h2, L.shown x hx, sub_eq_zero]
    have hb : ∀ n, n < 99 → Form.val y (byteF (E := E) N.uR (x / 4) n) =
        ext D.lT (fun i => led t (x / 4) i n) e.r2 := fun n hn' => by
      rw [val_byteF, T.atR _ _ (Nat.div_lt_of_lt_mul hx) hn']
    rcases (by omega : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3) with q | q | q | q
    · rw [q]
      show ext D.lT (fun i => Inst.Model.Ledger.sa (led t (x / 4) i)) e.r2 = Form.val y (saF _)
      rw [Inst.Model.Ledger.val_saF, (rows_congr hb).1]
      exact Inst.Model.Ledger.ext_sa D.lT (fun m i => led t (x / 4) i m) e.r2
    · rw [q]
      show ext D.lT (fun i => Inst.Model.Ledger.sb (led t (x / 4) i)) e.r2 = Form.val y (sbF _)
      rw [Inst.Model.Ledger.val_sbF, (rows_congr hb).2.1]
      exact Inst.Model.Ledger.ext_sb D.lT (fun m i => led t (x / 4) i m) e.r2
    · rw [q]
      show ext D.lT (fun i => Inst.Model.Ledger.Rlo (led t (x / 4) i)) e.r2 = Form.val y (RloF _)
      rw [Inst.Model.Ledger.val_RloF, (rows_congr hb).2.2.1]
      exact Inst.Model.Ledger.ext_Rlo D.lT (fun m i => led t (x / 4) i m) e.r2
    · rw [q]
      show ext D.lT (fun i => Inst.Model.Ledger.Rhi (led t (x / 4) i)) e.r2 = Form.val y (RhiF _)
      rw [Inst.Model.Ledger.val_RhiF, (rows_congr hb).2.2.2]
      exact Inst.Model.Ledger.ext_Rhi D.lT (fun m i => led t (x / 4) i m) e.r2
  · have hν : x / 9 < D.nNu := Nat.div_lt_of_lt_mul hx
    unfold cIdn
    rw [Inst.Model.Ledger.val_idnForm]
    simp only [val_hW, val_hP]
    exact (idnP_congr_D (npOf D (x / 9)) _ _
      (fun n hn' => by rw [val_byteF, T.atP _ _ hν hn']) (x % 9)).symm.trans
      (L.lines (x / 9) hν (x % 9) (by omega))
  · have hν : x / 8 < D.nNu := Nat.div_lt_of_lt_mul hx
    unfold cIdn
    rw [Inst.Model.Ledger.val_idnForm]
    simp only [val_hW, val_hP]
    exact (idnP_congr_D (npOf D (x / 8)) _ _
      (fun n hn' => by rw [val_byteF, T.atP _ _ hν hn']) (9 + x % 8)).symm.trans
      (L.lines (x / 8) hν (9 + x % 8) (by omega))
  · have k := L.hot l hl'
    unfold Inst.Model.FFSeg.d10 at k
    rw [Blocks.ext_sub, Blocks.ext_sum, Blocks.ext_const] at k
    unfold cHot
    rw [map_sub, map_sum, Form.val_const, ← k]
    congr 1
    exact sum_congr rfl fun x hx => by rw [Form.val_ent, T.sel _ _ hl' (mem_range.mp hx)]

/-- On entries with true tables the list of forms and the record say the same. -/
theorem norms_cl_iff [Scl] (u1 u2 : Form J E) (D : Dim) (t : Cell → E) (lNI b s B : ℕ)
    (y : J → E) (hn : D.nNu = 2 ^ lNI) (hl : lDd D = b + s) (hd : D.d = B * 2 ^ s)
    (hB : B ≤ 2 ^ b) (T : TablesTrue N e D t lNI b s B y) :
    (∀ f ∈ normsCl N e u1 u2 D lNI b B, Form.val y f = 0) ↔
      NormsLast N e D t lNI b s y ∧ Form.val y u1 = 0 ∧ Form.val y u2 = 0 :=
  ⟨fun h => ⟨norms_last N e u1 u2 D t lNI b s B y hn hl hd hB T h,
    norms_rows N e u1 u2 D lNI b B y h⟩,
    fun h => norms_cl_of_last N e u1 u2 D t lNI b s B y hn hl hd hB T h.1 h.2.1 h.2.2⟩

end Cb.Pv.Lay.End
