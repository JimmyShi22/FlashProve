-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttCallsH.lean

The tables of the calls in the lookup's own record. Beside the shape, shapeHid returns the record of
"the one lookup in which all its calls run" (its docstring; Model.Forest.Shape). It takes the calls
of shape, sets the number iota of each, and puts their records into that record's field calls. So
each of them has the library's table (Johnson/Road/Lane5AttCalls.lean: isLut_ord).

* "hid_calls": what shapeHid returns: the shape of shape with two fields set; its calls are shape's
  with iota set; the lookup's calls are their records.
* "isLut_hid": every call of the shape that shapeHid returns has the table that AttOrd's relation
  asks of its kind; and the lookup's calls are these calls' records, in their order.
* "isLut_group": the same for the plan that group returns.

Conditions, as in isLut_ord: AttFit (one shift, ldh = 7), kFD = 16, S = 12, rx = 8.
Not claimed: what the lookup shows; that the run's lookup reads its tables from that field (the
texts of the run and of the lookup are not looked at here).
-/
import Johnson.Road.Lane5AttCalls

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model
open Attention (ACall Cfg Shape shape shapeHid)

/-- **What shapeHid returns.** -/
theorem hid_calls {lid : ℕ} {cf : Cfg} {S : Shape} {fs : Model.Forest.Shape}
    (h : shapeHid lid cf = Except.ok (S, fs)) :
    ∃ (A : Shape) (io : ℕ → ℕ) (kbA : ℕ), shape cf = Except.ok A ∧
      S = { A with
        kbA := kbA
        calls := A.calls.mapIdx fun q c => { c with call := { c.call with iota := io q } } } ∧
      fs.calls = S.calls.map (fun k => k.call) := by
  unfold Attention.shapeHid at h
  obtain ⟨A, hA, h⟩ := bind_ok h
  obtain ⟨f, -, h⟩ := bind_ok h
  obtain ⟨-, h⟩ := refuse_ok h
  obtain ⟨kbA, -, h⟩ := bind_ok h
  obtain ⟨counted, -, h⟩ := bind_ok h
  obtain ⟨-, -, h⟩ := bind_ok h
  have e := Except.ok.inj h
  obtain ⟨e1, e2⟩ := Prod.mk.inj e
  subst e1
  subst e2
  exact ⟨A, fun q => f.iota.getD q 0, kbA, hA, rfl, rfl⟩

/-- **Every call of the shape that shapeHid returns has the table that AttOrd's relation asks of its
kind, and the lookup's calls are these calls' records.** -/
theorem isLut_hid {lid : ℕ} {cf : Cfg} {S : Shape} {fs : Model.Forest.Shape}
    (h : shapeHid lid cf = Except.ok (S, fs)) (F : AttFit S) (hkF : cf.kFD = 16)
    (h12 : cf.S = 12) (h8 : cf.rx = 8) :
    (∀ k ∈ S.calls.toList,
      Hd.IsLut k.call (AttSeg.lut (scl := sclOf S) (dimOf S) (tbOf S) (noK k.kind))) ∧
      fs.calls = S.calls.map (fun k => k.call) := by
  obtain ⟨A, io, kbA, hA, eS, ef⟩ := hid_calls h
  refine ⟨fun k hk => ?_, ef⟩
  subst eS
  have FA : AttFit A := ⟨F.one, F.ldh⟩
  have hk' : k ∈ (A.calls.mapIdx fun q c =>
      ({ c with call := { c.call with iota := io q } } : ACall)).toList := hk
  rw [Array.toList_mapIdx, List.mem_mapIdx] at hk'
  obtain ⟨i, hi, rfl⟩ := hk'
  exact (isLut_ord hA FA hkF h12 h8 _ (List.getElem_mem hi)).iota (io i)

/-- The same for the plan that group returns. -/
theorem isLut_group {P : Model.PolScan} {y : Model.Layer.Lay} {sc : Model.Layer.Scales}
    {midQ : ℕ → ℕ} {lines : List Attention.Line} {g : ℕ} {X : Attention.Plan}
    (h : Attention.group P y sc midQ lines g = Except.ok X) (F : AttFit X.S)
    (hkF : X.S.cf.kFD = 16) (h12 : X.S.cf.S = 12) (h8 : X.S.cf.rx = 8) :
    (∀ k ∈ X.S.calls.toList,
      Hd.IsLut k.call (AttSeg.lut (scl := sclOf X.S) (dimOf X.S) (tbOf X.S) (noK k.kind))) ∧
      X.fs.calls = X.S.calls.map (fun k => k.call) := by
  obtain ⟨cf, -, hp, -⟩ := group_plan h
  have hh := (plan_shape hp).1
  have ec := (shaped_of_hid hh).cfg
  rw [ec] at hkF h12 h8
  exact isLut_hid hh F hkF h12 h8

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.hid_calls
#print axioms OnBytes.Road.L5.isLut_hid
#print axioms OnBytes.Road.L5.isLut_group
