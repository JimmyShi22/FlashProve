-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadTabL.lean: the table of each family's call is the family's: public facts on the
layout of the output head's sub-proof, for the head with the cost ledger.

Johnson/Road/HeadSumL.lean goes from "every value in every column of every call is an entry of the
call's table" to the library's relation of the head with the cost ledger. It asks that the table of
the call in which a family's segment stands is the table in which the verifier looks the family's
keys up (the hypothesis hT of callsFitL_of_layout). This file shows that, for the library's tables
by the calls' kinds (tabL, Johnson/Road/HeadSumMet.lean), of every layout that the verifier's
function returns. It reads no routine of the check and no claim.

Main theorems: tabL_of_layout; small_cellsHL (small matrices have small cells); two_ne_gl.

What is not claimed. That the verifier's own table of a call is the library's table for the call's
kind is another file's (isLut_of_layout, Johnson/Road/HeadTabs.lean). The program does not import
this file.
-/
import Johnson.Road.HeadSumL
import Johnson.Road.HeadCallsLaid
import Johnson.Road.HeadPlace

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model Inst.Model.Head

/-- If every entry of the matrices is below 2^18 in absolute value, so is every cell that the head
with the ledger reads. -/
theorem small_cellsHL (h : Model.Head.Shape) (L : Model.Head.HL) (b : Model.Head.Border)
    {Mz : Mats ℤ} (hM : ∀ a r c, |Mz a r c| < 2 ^ 18) : Head.Small (cellsH h L b Mz) :=
  fun _ _ => ⟨fun _ _ => hM _ _ _, fun _ _ => hM _ _ _, fun _ _ => hM _ _ _, fun _ _ => hM _ _ _⟩

/-- The two lists of the nine names agree, and a name belongs to one family. -/
theorem nameH_inj {s' s : Head.Fam} (e : nameH s' = nameOf s) : s' = s := by
  cases s' <;> cases s <;> first | rfl | (simp [nameH, nameOf] at e)

/-- The library's table for the kind of a family's call is the table in which the verifier looks the
family's keys up. -/
theorem lutOfL_kind (s : Head.Fam) : lutOfKind (famKind s) = lutOfL s := by
  cases s <;> simp [famKind, lutOfKind, lutOfL, Policy.LedgerHead.tableOf]

/-- Each family's name stands in the verifier's list of segments. -/
theorem nameOf_listed (h : Model.Head.Shape) (L : Model.Head.HL) (s : Head.Fam) :
    ∃ x ∈ Model.Head.segments h L, x.1 = nameOf s := by
  cases s
  case NF => exact ⟨("NF", "R16", h.d), by simp [Model.Head.segments], rfl⟩
  case NFH => exact ⟨("NFH", "R16", h.d), by simp [Model.Head.segments], rfl⟩
  case HD0 => exact ⟨("HD0", "R16", L.JV), by simp [Model.Head.segments], rfl⟩
  case HD1 => exact ⟨("HD1", "R16", L.JV), by simp [Model.Head.segments], rfl⟩
  case ROW => exact ⟨("ROW", "R8", Model.ledNRH h.XL), by simp [Model.Head.segments], rfl⟩
  case HD2 => exact ⟨("HD2", "R8", L.JV), by simp [Model.Head.segments], rfl⟩
  case HE0 => exact ⟨("HE0", "FE", L.JVa), by simp [Model.Head.segments], rfl⟩
  case HE1 => exact ⟨("HE1", "FE", L.JV - L.JVa), by simp [Model.Head.segments], rfl⟩
  case CNF => exact ⟨("CNF", "FC", h.d), by simp [Model.Head.segments], rfl⟩

/-- **The table of each family's call is the family's**, in a layout that the verifier's function
returns: the library's table for the kind of the call that a family's name finds is the table in
which the verifier looks the family's keys up. -/
theorem tabL_of_layout {R : Model.Head.Run} {tauFC : Array F}
    (hy : Model.Head.layout R.h tauFC = .ok R.L) (Sf : SegsFit R) (s : Head.Fam) (q : ℕ)
    (hq : Model.Head.callNo R.L (nameOf s) = some q) : tabL R q = lutOfL s := by
  obtain ⟨x, hx, hn⟩ := nameOf_listed R.h R.L s
  obtain ⟨q', g, hq', hg, hgn, _⟩ := mem_of_segHas (segHas_of_layout hy (R := R) rfl rfl x hx)
  rw [hn, hq] at hq'
  obtain rfl := Option.some.inj hq'
  obtain ⟨s', e1, _, e3⟩ := Sf q g hg
  obtain rfl := nameH_inj (e1.symm.trans (hgn.trans hn))
  unfold tabL
  rw [e3]
  exact lutOfL_kind s'

/-- 2 is not 0 in the challenge field. -/
theorem two_ne_gl : (2 : Cb.Gl.E) ≠ 0 := by
  obtain ⟨c, hc⟩ := Down.exists_inv23 (K := Cb.Gl.E) (p := Cb.Gl.p)
    (algebraMap Cb.Gl.F Cb.Gl.E) (by have h := Down.gl_big; omega)
  intro h0
  rw [h0, zero_pow (by decide), mul_zero] at hc
  exact zero_ne_one hc

#print axioms small_cellsHL
#print axioms tabL_of_layout
#print axioms two_ne_gl

end OnBytes.Road.Hd
