-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/LedPort.lean: where the claims of the layers' own rounds on the norms' rows are all
worth 0, the library-side claims behind the token sumcheck of the row products are all worth 0, but
for the one that the sumcheck itself leaves; in every world and at all entries that the dictionary
LedDict ties to each other.

OnBytes/Desc/First/K4/Claims.lean lists, for each norm of a group, four claims on the shown end
values, nine carries and eight lines (rowsForms; the formulas: OnBytes/Desc/First/P6/NormRow.lean).
Cb/Pv/Lay/End/NormsCl.lean lists claims on the same values in the library's names (clLedger: the
letter u2, then cShown, then cIdn). This file holds the two against each other on values, after the
pattern of Johnson/Road/Rows/LayerTermsPort.lean. Both sides were already read as the library's
identities with letters, idnP: the verifier's in OnBytes/Desc/First/P6/NormRowLaw.lean and
PositionBridge.lean (fields_value, forms_zero), the library's in
Inst/Model/Common/LedgerForms.lean (val_idnForm). So here only the letters are compared: slot by
slot, digit by digit. End value number 4 i + k is field number k of norm i in the order a, b, Rlo,
Rhi on both sides; sum number 9 i + s and product number 7 i + j likewise.

Main names:
  `LedDict`: the dictionary: the number of norms; the hidden values under three runs of slots; the
    entries of the reads that hold the cells of the norms' rows at two token points; two constants
    of each norm.
  `digits_read`: a digit that digitsAt hands out is worth the entry of the reads plus 128.
  `shown_port`, `idn_port`: one library-side claim is worth 0.
  `led_port`: all of clLedger but its head; `led_port_all`: with the head, if it is worth 0.
Limits. The dictionary is a premise: no world and no entries are shown at which it holds, nor that
its three runs of slots are apart. The claim that the token sumcheck itself leaves (the library's
u2) is not compared with anything. Nothing is said on whether the reads are true, on a digit's range
or on soundness. Equations in the field K at two token points, not at a position.


-/
import Johnson.Road.Rows.LayerTermsPort
import OnBytes.Desc.First.K4.RowsLaws
import OnBytes.Desc.First.P6.PositionBridge
import Cb.Pv.Lay.End.NormsCl

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Model (Reading World Aff)
open OnBytes.Model.Layer (Env Heard aff0 epsOf twoM)
open OnBytes.Road.Rows (readAtW U3at_read)
open OnBytes.Desc.First.K4 (rowsForms digitsAt rowsForms_mem)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim npOf)
open Inst.Model.Ledger (saF sbF RloF RhiF)
open Cb.Pv.Lay.End (NormsNames NormsE byteF cShown cIdn clLedger val_h2 val_hW val_hP val_byteF
  rows_congr idnP_congr_D)
open Blocks (Form)

variable {K : Type} [Field K] {J : Type} [Fintype J] [DecidableEq J]

/-- The dictionary between the verifier's letters and the library-side letters of the claims on the
norms' rows. -/
structure LedDict [scl : Scl] (ρ : Reading K) (W : World K) (v : Env) (H : Heard) (D : Dim)
    (N : NormsNames J) (e : NormsE K) (y : J → K) : Prop where
  /-- the norms of the group -/
  nNu : v.y.NI = D.nNu
  /-- the hidden value under the slot of end value number x of the token sumcheck of the row
  products: what was shown less the challenge times the mask entry -/
  slot2 : ∀ x, x < 4 * D.nNu → W.slot (H.tV.sEnd + x) = e.sh2 x - e.β2 * y (N.m2 x)
  /-- the hidden value under the slot of sum number x: what was shown less the mask entry -/
  slotW : ∀ x, x < 9 * D.nNu → W.slot (H.sW + x) = e.shW x - y (N.mW x)
  /-- the hidden value under the slot of row product number x: the same -/
  slotP : ∀ x, x < 7 * D.nNu → W.slot (H.sPv + x) = e.shP x - y (N.mP x)
  /-- the cells of the norms' rows at the end point of that token sumcheck -/
  rowR : ∀ t tr, v.tabAt ("ar@" ++ "r_tV") = some t → v.y.T_ "row" = some tr →
    ∀ ν n, ν < D.nNu → n < 99 → readAtW W v t (tr.OFF + ν * 99 + n) = y (N.uR ν n)
  /-- the cells of the norms' rows at the norms' token point -/
  rowP : ∀ t tr, v.tabAt ("ar@" ++ "P_V") = some t → v.y.T_ "row" = some tr →
    ∀ ν n, ν < D.nNu → n < 99 → readAtW W v t (tr.OFF + ν * 99 + n) = y (N.uP ν n)
  /-- the constant under the root of norm i -/
  eps : ∀ i, i < D.nNu → ρ.val (epsOf v.y i) = ((npOf D i).eps : K)
  /-- 2^(M + 1) of norm i -/
  two : ∀ i, i < D.nNu → (twoM v i).value ρ W = 2 ^ ((npOf D i).M + 1)

variable {ρ : Reading K} {W : World K} {v : Env} {H : Heard} {N : NormsNames J} {e : NormsE K}
  {y : J → K}

/-- Digit n of row i at the token point P, as digitsAt hands it out, is worth 128 more than the
entry of the reads that holds the cell; c: what that entry is worth. -/
theorem digits_read {P : String} {i : ℕ} {c : ℕ → K}
    (hrow : ∀ t tr, v.tabAt ("ar@" ++ P) = some t → v.y.T_ "row" = some tr →
      ∀ n, n < 99 → readAtW W v t (tr.OFF + i * 99 + n) = c n)
    {Dg : ℕ → Aff} (hD : digitsAt v P i = some Dg) {n : ℕ} (hn : n < 99) :
    (Dg n).value ρ W = c n + 128 := by
  unfold digitsAt at hD
  obtain ⟨cells, hc, rfl⟩ := Option.map_eq_some_iff.mp hD
  unfold Env.rowCells at hc
  obtain ⟨t, ht, hc⟩ := bind_some hc
  obtain ⟨tr, htr, hc⟩ := bind_some hc
  have h1 := range_mapM_get aff0 hc hn
  show (cells.getD n aff0 + Desc.First.P6.nat 128).value ρ W = _
  rw [Aff.value_add, Desc.First.P6.nat_value ρ W, U3at_read h1, hrow t tr ht htr n hn]
  norm_num

section Port

variable [scl : Scl] {D : Dim} (Dc : LedDict ρ W v H D N e y) {l : List Aff}
  (h : rowsForms v H = some l) (hz : ∀ f ∈ l, f.value ρ W = 0)
include Dc h hz

/-- End value number x of the token sumcheck of the row products against the reads of the row at
its end point: the library-side claim is worth 0. -/
theorem shown_port {x : ℕ} (hx : x < 4 * D.nNu) : Form.val y (cShown N e x) = 0 := by
  have hi : x / 4 < D.nNu := by omega
  obtain ⟨Dr, _, hDr, _, m1, _, _⟩ := rowsForms_mem h (i := x / 4) (by rw [Dc.nNu]; exact hi)
  have m1' : ∀ f ∈ [Aff.slot (H.tV.sEnd + 4 * (x / 4) + 0) - (Desc.First.P6.Row.ofDigits Dr).a,
      Aff.slot (H.tV.sEnd + 4 * (x / 4) + 1) - (Desc.First.P6.Row.ofDigits Dr).b,
      Aff.slot (H.tV.sEnd + 4 * (x / 4) + 2) - (Desc.First.P6.Row.ofDigits Dr).Rlo,
      Aff.slot (H.tV.sEnd + 4 * (x / 4) + 3) - (Desc.First.P6.Row.ofDigits Dr).Rhi], f ∈ l := m1
  have hb : ∀ n, n < 99 → Form.val y (byteF (E := K) N.uR (x / 4) n) = (Dr n).value ρ W :=
    fun n hn => by
      rw [val_byteF, digits_read (fun t tr ht htr n hn => Dc.rowR t tr ht htr (x / 4) n hi hn) hDr
        hn]
  obtain ⟨fa, fb, fl, fh⟩ := Desc.First.P6.fields_value ρ W Dr
  unfold cShown
  rw [map_sub, val_h2, ← Dc.slot2 x hx]
  rcases (by omega : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3) with c | c | c | c
  · have z := hz _ (m1' _ List.mem_cons_self)
    rw [Aff.value_sub, Aff.value_slot, fa,
      (by omega : H.tV.sEnd + 4 * (x / 4) + 0 = H.tV.sEnd + x)] at z
    rw [c]
    show W.slot (H.tV.sEnd + x) - Form.val y (saF (byteF (E := K) N.uR (x / 4))) = 0
    rw [Inst.Model.Ledger.val_saF, (rows_congr hb).1]
    exact z
  · have z := hz _ (m1' _ (List.mem_cons_of_mem _ List.mem_cons_self))
    rw [Aff.value_sub, Aff.value_slot, fb,
      (by omega : H.tV.sEnd + 4 * (x / 4) + 1 = H.tV.sEnd + x)] at z
    rw [c]
    show W.slot (H.tV.sEnd + x) - Form.val y (sbF (byteF (E := K) N.uR (x / 4))) = 0
    rw [Inst.Model.Ledger.val_sbF, (rows_congr hb).2.1]
    exact z
  · have z := hz _ (m1' _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    rw [Aff.value_sub, Aff.value_slot, fl,
      (by omega : H.tV.sEnd + 4 * (x / 4) + 2 = H.tV.sEnd + x)] at z
    rw [c]
    show W.slot (H.tV.sEnd + x) - Form.val y (RloF (byteF (E := K) N.uR (x / 4))) = 0
    rw [Inst.Model.Ledger.val_RloF, (rows_congr hb).2.2.1]
    exact z
  · have z := hz _ (m1' _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))))
    rw [Aff.value_sub, Aff.value_slot, fh,
      (by omega : H.tV.sEnd + 4 * (x / 4) + 3 = H.tV.sEnd + x)] at z
    rw [c]
    show W.slot (H.tV.sEnd + x) - Form.val y (RhiF (byteF (E := K) N.uR (x / 4))) = 0
    rw [Inst.Model.Ledger.val_RhiF, (rows_congr hb).2.2.2]
    exact z

/-- Identity number k of norm i, with the hidden sums and products in the places of the sums and of
the products, on the reads of the row at the norms' token point: the library-side claim is worth 0.
k: any number (from 17 on the claim is the form 0). -/
theorem idn_port {i : ℕ} (hi : i < D.nNu) (k : ℕ) : Form.val y (cIdn N e D i k) = 0 := by
  obtain ⟨_, Dp, _, hDp, _, mC, mL⟩ := rowsForms_mem h (i := i) (by rw [Dc.nNu]; exact hi)
  have z := Desc.First.P6.forms_zero ρ W Dp (fun s => Aff.slot (H.sW + 9 * i + s))
    (fun j => Aff.slot (H.sPv + 7 * i + j)) (npOf D i) (epsOf v.y i) (twoM v i) (Dc.eps i hi)
    (Dc.two i hi) (fun f hf => hz f (mC f hf)) (fun f hf => hz f (mL f hf)) k
  unfold cIdn
  rw [Inst.Model.Ledger.val_idnForm]
  simp only [val_hW, val_hP]
  refine Eq.trans ?_ z
  refine (idnP_congr_D (npOf D i) _ _ (Dg' := Desc.First.P6.dv ρ W Dp) (fun n hn => ?_) k).trans
    (Cb.Pv.Lay.End.idnP_congr (npOf D i) _ (fun s hs => ?_) (fun j hj => ?_) k)
  · show (Dp n).value ρ W = Form.val y (byteF (E := K) N.uP i n)
    rw [val_byteF]
    exact digits_read (fun t tr ht htr n hn => Dc.rowP t tr ht htr i n hi hn) hDp hn
  · show e.shW (9 * i + s) - y (N.mW (9 * i + s)) = (Aff.slot (H.sW + 9 * i + s)).value ρ W
    rw [Aff.value_slot, Nat.add_assoc, Dc.slotW _ (by omega)]
  · show e.shP (7 * i + j) - y (N.mP (7 * i + j)) = (Aff.slot (H.sPv + 7 * i + j)).value ρ W
    rw [Aff.value_slot, Nat.add_assoc, Dc.slotP _ (by omega)]

/-- **The port of the norms' rows.** Under the dictionary: if rowsForms returns a list and all its
forms are worth 0 in the world, then every form of clLedger but its head, the letter u2, is worth 0
at the entries. -/
theorem led_port (u2 : Blocks.Form J K) : ∀ q ∈ (clLedger N e u2 D).tail, Form.val y q = 0 := by
  intro q hq
  have hq' : q ∈ (List.range (4 * D.nNu)).map (cShown N e) ++
      ((List.range (9 * D.nNu)).map (fun x => cIdn N e D (x / 9) (x % 9)) ++
        (List.range (8 * D.nNu)).map fun x => cIdn N e D (x / 8) (9 + x % 8)) := hq
  simp only [List.mem_append, List.mem_map, List.mem_range] at hq'
  rcases hq' with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
  · exact shown_port Dc h hz hx
  · exact idn_port Dc h hz (by omega) _
  · exact idn_port Dc h hz (by omega) _

/-- The same with the head: if the letter u2 is worth 0 too, every form of clLedger is. -/
theorem led_port_all {u2 : Blocks.Form J K} (hu : Form.val y u2 = 0) :
    ∀ q ∈ clLedger N e u2 D, Form.val y q = 0 := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq'
  · exact hu
  · exact led_port Dc h hz u2 q hq'

end Port

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.digits_read
#print axioms OnBytes.Road.K4.shown_port
#print axioms OnBytes.Road.K4.idn_port
#print axioms OnBytes.Road.K4.led_port
#print axioms OnBytes.Road.K4.led_port_all
