-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Ends/HeadIn.lean: from "the keys of every call of the output head's lookup lie in the
call's table" to the library's clause "every key of the nine families is an entry of its table".

The key vectors are kvH (OnBytes/Tie/Pv/Lookup/Ends/H.lean), written for this library over the
verifier's records: no function of the verifier's returns them. Call q's key number j T + i is the
key of the entry that stands in column j, at position i. The tables have the rows of the verifier's
records of the calls (tauN, OnBytes/Tie/Pv/Lookup/Ends/Joint.lean).

Main theorems:
  col_unique: where the verifier's marking of a call's columns does not refuse, a column is listed
    by one entry of one name.
  colH_of_marks: so colH finds, in the column of entry x of a segment, that segment's name and x.
  kvH_at: call q's key number j T + i is segH of what colH finds in column j.
  word_castH: the word of a number reads in the extension field as the number.
  headKeys_of_inTable: under TiesH at the library's sizes (Johnson/Road/Ends/HeadSeg.lean),
    CallsFitL (Johnson/Road/HeadSumL.lean), the marking of each call's columns, "each segment lists
    one column for each entry", "the factor under HD0 times 2^23 is 1", the library's number of
    positions, and CallAt for each call that has a segment: if all keys of kvH of each call lie in
    the table of that call's record (Cb.Lkp.InTable), then every key of the library's nine families,
    over the base field, on the integer cells tz and the integer output matrix Hz, is an entry of
    the family's table.
How: key_segH; IsLut (Johnson/Road/HeadTabs.lean); at HD0 the key in kvH is the library's divided by
2^23 (Down.hd0_ledger); from the extension field down to the base field by Down.ledgerKey_map and
Down.inLut_iff (Johnson/Road/HeadDown.lean).

Limits: that the keys do lie in their tables is a premise. No value of TiesH or CallAt is given
here. Nothing on identities, on smallness, on a form or on a protocol.

-/
import Cb.Gen.LkpAlg
import Johnson.Road.HeadSumL
import Johnson.Road.HeadFn
import Johnson.Road.HeadDown
import Johnson.Road.HeadTabs
import Johnson.Road.Ends.HeadSeg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset
open OnBytes.Ends
open OnBytes.Model (Seg Call)
open Inst.Model (NormPar Lut Mat)
open Inst.Model.Head (Fam Req InLut nT)

/-! ## Columns -/

/-- Where the marking does not refuse, a column is listed by one entry of one name. -/
theorem col_unique {R : Model.Head.Run} {J : ℕ} {l : List Seg} {w : Array ℕ}
    (h : l.foldlM (fun w g => Model.Head.markColumns R w g) (Array.replicate J 0) = some w)
    {g g' : Seg} (hg : g ∈ l) (hg' : g' ∈ l) {x x' : ℕ} (hx : x < g.n) (hx' : x' < g'.n)
    (e : g.pos.getD x 0 = g'.pos.getD x' 0) : g'.name = g.name ∧ x' = x := by
  obtain ⟨f, Kf⟩ := exists_keyFn (K := ℚ) h
    (fun n a _ => if n = g.name ∧ a = x then 1 else 0) 0
  have h1 := Kf.seg g hg x hx
  have h2 := Kf.seg g' hg' x' hx'
  rw [e] at h1
  have h4 : (if g.name = g.name ∧ x = x then (1 : ℚ) else 0) =
      if g'.name = g.name ∧ x' = x then 1 else 0 := congrFun (h1.symm.trans h2) 0
  rw [if_pos ⟨rfl, rfl⟩] at h4
  by_cases c : g'.name = g.name ∧ x' = x
  · exact c
  · rw [if_neg c] at h4
    exact absurd h4 one_ne_zero

/-- In the column of entry x of a segment colH finds the segment's name and x. -/
theorem colH_of_marks {R : Model.Head.Run} {q : ℕ} {w : Array ℕ}
    (h : (R.L.calls.getD q default).segs.foldlM (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some w)
    (hsz : ∀ g ∈ (R.L.calls.getD q default).segs, g.pos.size = g.n) {g : Seg}
    (hg : g ∈ (R.L.calls.getD q default).segs) {x : ℕ} (hx : x < g.n) :
    H.colH R.L q (g.pos.getD x 0) = some (g.name, x) := by
  have hxs : x < g.pos.size := by rw [hsz g hg]; exact hx
  cases hc : H.colH R.L q (g.pos.getD x 0) with
  | none =>
    exfalso
    unfold H.colH at hc
    have h4 := List.findSome?_eq_none_iff.mp hc g hg
    have h5 : g.pos.findIdx? (· == g.pos.getD x 0) = none := by
      cases h : g.pos.findIdx? (· == g.pos.getD x 0) with
      | none => rfl
      | some a =>
        rw [h] at h4
        cases h4
    have h6 := Array.findIdx?_eq_none_iff.1 h5 g.pos[x] (Array.getElem_mem hxs)
    have h8 : g.pos.getD x 0 = g.pos[x] := by simp [Array.getD, hxs]
    simp [h8] at h6
  | some a =>
    unfold H.colH at hc
    obtain ⟨g0, hg0, h0⟩ := List.exists_of_findSome?_eq_some hc
    cases hx0 : g0.pos.findIdx? (· == g.pos.getD x 0) with
    | none =>
      rw [hx0] at h0
      cases h0
    | some x0 =>
      rw [hx0] at h0
      have e : (g0.name, x0) = a := Option.some.inj h0
      obtain ⟨hi, hp0, _⟩ := Array.findIdx?_eq_some_iff_getElem.1 hx0
      have hp : g.pos.getD x 0 = g0.pos.getD x0 0 := by
        have h9 : g0.pos[x0] = g.pos.getD x 0 := by simpa using hp0
        have h10 : g0.pos.getD x0 0 = g0.pos[x0] := by simp [Array.getD, hi]
        rw [h10, h9]
      obtain ⟨e1, e2⟩ := col_unique h hg hg0 hx (by rw [← hsz g0 hg0]; exact hi) hp
      rw [← e, e1, e2]

section Kv

variable {K : Type} [Field K]

/-- Call q's key number j T + i is the key of what stands in column j, at position i. -/
theorem kvH_at (P : H.PubH) (cell : H.NameH → K) {q j a i : ℕ} {sn : String}
    (hc : H.colH P.L q j = some (sn, a)) (hi : i < P.h.T) :
    H.kvH P cell q (j * P.h.T + i) = H.segH P cell sn a i := by
  have hT : 0 < P.h.T := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
  have e1 : (j * P.h.T + i) / P.h.T = j := by
    rw [Nat.mul_comm, Nat.mul_add_div hT, Nat.div_eq_of_lt hi, Nat.add_zero]
  have e2 : (j * P.h.T + i) % P.h.T = i := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  unfold H.kvH H.kvOf
  rw [e1, e2, hc]

end Kv

/-! ## Tables -/

/-- The word of a number, as a number, reads in the library's extension field as the number. -/
theorem word_castH (n : ℕ) :
    (((Model.fOfNat n).toNat : ℕ) : Cb.Gl.E) = ((n : ℕ) : Cb.Gl.E) := by
  have e : Model.fOfNat n = Fmt.Fld.two.red n := rfl
  have h : Slice.toF (Model.fOfNat n) = (n : Cb.Gl.F) := by rw [e, Slice.toF_red]
  have h' : (((Model.fOfNat n).toNat : ℕ) : Cb.Gl.F) = (n : Cb.Gl.F) := h
  calc (((Model.fOfNat n).toNat : ℕ) : Cb.Gl.E)
      = algebraMap Cb.Gl.F Cb.Gl.E (((Model.fOfNat n).toNat : ℕ) : Cb.Gl.F) :=
        (map_natCast _ _).symm
    _ = algebraMap Cb.Gl.F Cb.Gl.E (n : Cb.Gl.F) := by rw [h']
    _ = ((n : ℕ) : Cb.Gl.E) := map_natCast _ _

/-- What is asked of call number q: it is one of the NC calls; the lookup's shape has a record c0
for it, with the library's table T; the call's table has 2^k rows; its key vector has room for all
columns and positions. -/
structure CallAt (R : Model.Head.Run) (NC : ℕ) (n k : ℕ → ℕ) (T : ℕ → Lut) (q : ℕ) : Prop where
  lt : q < NC
  has : ∃ c0 : Call, R.L.fs.calls[q]? = some c0 ∧ IsLut c0 (T q) ∧ k q = c0.k
  room : (R.L.calls.getD q default).J * R.h.T ≤ 2 ^ n q

/-- **From the calls' tables to the library's clause on keys.** -/
theorem headKeys_of_inTable {R : Model.Head.Run} {P : H.PubH} (hPh : P.h = R.h) (hPL : P.L = R.L)
    {cell : H.NameH → Cb.Gl.E} {np : NormPar} {tz : Inst.Model.Head.Cells ℤ} {Hz : Mat} {y : Req}
    (hT : R.h.T = nT)
    (Ti : TiesH P cell HeadSizes.ref np (tz.cast Cb.Gl.E) (fun j v => ((Hz j v : ℤ) : Cb.Gl.E)) y)
    (hc : H.iw P * (2 : Cb.Gl.E) ^ 23 = 1) {T : ℕ → Lut}
    (A : CallsFitL R (kvOf (H.iw P) HeadSizes.ref np (tz.cast Cb.Gl.E)
        (fun j v => ((Hz j v : ℤ) : Cb.Gl.E)) y) T (H.iw P) np (tz.cast Cb.Gl.E)
      (fun j v => ((Hz j v : ℤ) : Cb.Gl.E)) y)
    {w : ℕ → Array ℕ}
    (hw : ∀ q, (R.L.calls.getD q default).segs.foldlM
      (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some (w q))
    (hsz : ∀ q, ∀ g ∈ (R.L.calls.getD q default).segs, g.pos.size = g.n)
    {NC : ℕ} {n k : ℕ → ℕ}
    (CA : ∀ q, (∃ g, g ∈ (R.L.calls.getD q default).segs) → CallAt R NC n k T q)
    (hin : ∀ q < NC, Cb.Lkp.InTable (n q) (k q) (H.kvH P cell q)
      (fun u => ((tauN P.L.fs q u : ℕ) : Cb.Gl.E)))
    (s : Fam) (a i : ℕ) (ha : a < Inst.Model.Head.len s) (hi : i < nT) :
    InLut (Policy.LedgerHead.tableOf s)
      (Policy.LedgerHead.key np (tz.cast Cb.Gl.F) (fun j v => ((Hz j v : ℤ) : Cb.Gl.F)) y s a
        i) := by
  obtain ⟨q, g, hg, hname, hn, hTq, hkv⟩ := A s
  have ha' : a < g.n := Nat.lt_of_lt_of_le ha hn
  have hcol := colH_of_marks (hw q) (hsz q) hg ha'
  obtain ⟨_, _, pj⟩ := marks_sum (K := ℚ) (J := (R.L.calls.getD q default).J) (fun _ => 0)
    (R.L.calls.getD q default).segs (Array.replicate (R.L.calls.getD q default).J 0) (w q)
    (by simp) (hw q)
  have hj := pj g hg a ha'
  obtain ⟨hq, ⟨c0, hc0, hl, hk⟩, hroom⟩ := CA q ⟨g, hg⟩
  have hiT : i < R.h.T := by rw [hT]; exact hi
  have hX : g.pos.getD a 0 * P.h.T + i < 2 ^ n q := by
    rw [hPh]
    refine Nat.lt_of_lt_of_le ?_ hroom
    calc g.pos.getD a 0 * R.h.T + i < g.pos.getD a 0 * R.h.T + R.h.T := by omega
      _ = (g.pos.getD a 0 + 1) * R.h.T := by ring
      _ ≤ (R.L.calls.getD q default).J * R.h.T := Nat.mul_le_mul_right _ hj
  obtain ⟨u, hu, e⟩ := hin q hq _ hX
  rw [← hPL] at hcol
  rw [kvH_at P cell hcol (by rw [hPh]; exact hiT), hname,
    Ti.key_segH s a i (by cases s <;> exact ha) hi] at e
  -- the row of the verifier's table is the library's
  have ht : tauN P.L.fs q u = (c0.tauAt u).toNat := by
    unfold tauN
    rw [hPL, hc0]
    rfl
  have hu' : u < (T q).rows := by
    rw [← hl.rows, ← hk]
    exact hu
  obtain ⟨m, hm1, hm2⟩ := hl.row u hu'
  have e' : keyC (H.iw P) HeadSizes.ref np (tz.cast Cb.Gl.E)
      (fun j v => ((Hz j v : ℤ) : Cb.Gl.E)) y s a i = (((T q).row u : ℤ) : Cb.Gl.E) := by
    rw [e]
    show ((tauN P.L.fs q u : ℕ) : Cb.Gl.E) = _
    rw [ht, hm1, word_castH, ← hm2, Int.cast_natCast]
  have h1 : InLut (lutOfL s) (keyOfL (H.iw P) np (tz.cast Cb.Gl.E)
      (fun j v => ((Hz j v : ℤ) : Cb.Gl.E)) y s a i) := by
    rw [← hTq, ← hkv, kvOf_name]
    exact ⟨u, hu', e'⟩
  have hE : InLut (Policy.LedgerHead.tableOf s) (Policy.LedgerHead.key np (tz.cast Cb.Gl.E)
      (fun j v => ((Hz j v : ℤ) : Cb.Gl.E)) y s a i) := by
    cases s
    case HD0 => exact (Down.hd0_ledger hc np (tz.cast Cb.Gl.E) _ y a i).2 h1
    all_goals exact h1
  exact (Down.inLut_iff (algebraMap Cb.Gl.F Cb.Gl.E) (algebraMap Cb.Gl.F Cb.Gl.E).injective
    (Policy.LedgerHead.tableOf s)
    (Down.ledgerKey_map (algebraMap Cb.Gl.F Cb.Gl.E) np Hz y tz s a i)).1 hE

end OnBytes.Road.Hd

#print axioms OnBytes.Road.Hd.col_unique
#print axioms OnBytes.Road.Hd.colH_of_marks
#print axioms OnBytes.Road.Hd.kvH_at
#print axioms OnBytes.Road.Hd.headKeys_of_inTable
