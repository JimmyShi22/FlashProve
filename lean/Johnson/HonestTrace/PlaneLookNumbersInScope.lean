-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/PlaneLookNumbersInScope.lean

On public data alone. Five theorems.

A HOME OUTSIDE THE EXECUTABLE MODEL's FOLDER FOR THREE LAWS ON THE VERIFIER's PLANS.
They serve whoever needs the planes' numbers in scope (K3/Term/PlaneNumbersInScope.lean, and so
"the planes' matrices have the filling's sizes"). Here they are proved over modules of the
library's public side alone. The number of groups is the plans' own.

* "largest_table_of_accepted_lookup": a lookup's record that passes "FoNums.ok" and has a call with 2^16 rows has kT = 16.
* "laid_call_has_sixteen_bits": a call that "Attention.layCall" lays has 2^16 rows, where the table of kind KFD has.
* "attention_configuration_is_the_fills": the plan's configuration is what the verifier's "Attention.fill" returns; the group's number
  is below the layout's number of groups.
* "attention_lookup_numbers_in_scope": in scope every attention plan's lookup has four calls, and its largest table 2^16 rows.
* "layers_largest_table_in_scope": in scope the layers' lookup has kT = 16.

Limits. In scope alone but for the third. Nothing on cells, on a Script, on a prover or on any property.
-/
import Johnson.Goal.Meaning.OkScope
import Johnson.Goal.Meaning.TabsScope
import Johnson.Goal.Meaning.AttForInScope
import Johnson.Goal.Meaning.ScopeCore
import Johnson.Meaning.PublicCore
import Johnson.Road.Lane5AttPlan
import Johnson.Road.Lane5AttLaid
import Johnson.Road.Lane5AttCallsH
import Johnson.Road.Lane5AttCalls
import Johnson.Road.Lane5AttShape
import Johnson.Road.Lane5AttPub
import Johnson.Road.FormsKeysShape
import Johnson.Road.HeadL5Grp
import Johnson.Road.HeadPub
import Johnson.HonestTrace.CountsAttention
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPubA
import OnBytes.Tie.Pv.Lookup.Ends.FoPublic

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.PlaneLook

open OnBytes OnBytes.Model OnBytes.Ends
open OnBytes.Road (shape_calls)
open OnBytes.Road.Hd (config_groups layerLayout_of_polLayout)
open OnBytes.Road.L5 (hid_calls calls_of_shape refuse_ok four_of_hid group_plan plan_shape shaped_of_hid)
open OnBytes.HonestTrace.Att (mapM_mem)

/-- The largest table of a lookup whose record passes FoNums.ok, and one of whose calls has 2^16 rows. -/
theorem largest_table_of_accepted_lookup {h : Forest.Shape} (hok : FoNums.ok h = true) {q : Nat} {c : Call}
    (hq : h.calls[q]? = some c) (hk : c.k = 16) : h.kT = 16 := by
  unfold FoNums.ok at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hsz⟩, -⟩, hall⟩, -⟩, -⟩, h16⟩, -⟩, -⟩ := hok
  have hlt : q < h.NC := by
    rw [← hsz]
    exact (Array.getElem?_eq_some_iff.1 hq).1
  have h1 := (hall q hlt).1.1.2
  have e : FoNums.kOf h q = 16 := by
    unfold FoNums.kOf
    rw [hq]
    exact hk
  omega

/-- A call that layCall lays has 2^16 rows, where the table of kind KFD has. -/
theorem laid_call_has_sixteen_bits {cf : Attention.Cfg} {HA Sm : Nat} {Tt : Array Nat} {x : Attention.Listed}
    {k : Attention.ACall} (h : Attention.layCall cf HA Sm Tt x = Except.ok k) (hk : cf.kFD = 16) :
    k.call.k = 16 := by
  obtain ⟨name, kind, sh, segs⟩ := x
  unfold Attention.layCall at h
  obtain ⟨-, h⟩ := refuse_ok h
  have e := Except.ok.inj h
  subst e
  cases kind
  · rfl
  · exact hk
  · rfl
  · rfl

variable {X : Verify.Public} {g : Nat} {P : Attention.Plan}

/-- **The plan's configuration is what the verifier's fill returns**, and the group's number is below the layout's number of groups. -/
theorem attention_configuration_is_the_fills {pol KL : ByteArray} {lay : Option ByteArray}
    (h : Verify.publicOf pol KL lay = .ok X) (hP : X.A[g]? = some P) :
    ∃ (sc : Layer.Scales) (midQ : Nat → Nat) (lines : List Attention.Line) (c : Attention.Config),
      Attention.config X.P X.y sc midQ = .ok c ∧
      Layer.layout (Verify.layerShape X.P) X.P.polCalls = .ok X.y ∧
      Attention.fill X.P X.y sc lines g = .ok P.S.cf ∧ g < X.y.NGr := by
  obtain ⟨hpl, -, -, -, -, sc, A0, seen, -, harm, -, eA⟩ := Fo.Pub.publicOf_cut pol KL lay X h
  rw [eA] at hP
  obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.1 hP
  have hlt' := hlt
  rw [Array.size_zipWith] at hlt'
  have hgA : g < A0.size := by omega
  rw [Array.getElem_zipWith] at hget
  have eS : P.S = (A0[g]'hgA).S := by rw [← hget]
  rcases harm with ⟨-, c, hC, eA0⟩ | ⟨-, eA0⟩
  · subst eA0
    obtain ⟨lines, hsz, hall⟩ := config_groups hC
    have hgN : g < X.layers.y.NGr := by rw [← hsz]; exact hgA
    obtain ⟨Xg, hX, hG⟩ := hall g hgN
    obtain ⟨hX', eX⟩ := Array.getElem?_eq_some_iff.1 hX
    obtain ⟨cf, hf, hp, -⟩ := group_plan hG
    have hcf := (shaped_of_hid (plan_shape hp).1).cfg
    refine ⟨sc, _, lines, c, hC, layerLayout_of_polLayout hpl, ?_, hgN⟩
    rw [eS, eX, hcf]
    exact hf
  · subst eA0
    simp at hgA

variable {F : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}

/-- **In scope every attention plan's lookup has four calls, and its largest table 2^16 rows.** -/
theorem attention_lookup_numbers_in_scope (hC : VerifierAndGoals.InScope F = true) (hF : VerifierAndGoals.readFiles F = .ok pp)
    (hX : Verify.publicOf F.pol F.KL lay = .ok X) (hP : X.A[g]? = some P) :
    P.fs.NC = 4 ∧ P.fs.kT = 16 := by
  have hg : g < 12 := by
    obtain ⟨-, -, -, -, -, -, -, h1⟩ := attention_configuration_is_the_fills hX hP
    exact lt_of_lt_of_eq h1 (Road.Hd.public_of_core hX (Road.Hd.core_of_scope hC hF hX)).groups
  obtain ⟨cf, hh, -, hk, -, -, U⟩ := Meaning.Att.hid_in_scope hC hF hX hg
  have eS : Road.Hd.shapeA X g = P.S := by
    unfold Road.Hd.shapeA
    rw [hP]
    rfl
  have ef : Meaning.Att.fsA X g = P.fs := by
    unfold Meaning.Att.fsA
    rw [hP]
    rfl
  have hok := Meaning.P34.ok_att_in_scope hC hF hX hg
  rw [eS, ef] at hh
  rw [ef] at hok
  have F4 := four_of_hid hh U
  obtain ⟨A, io, kbA, hA, eSA, efc⟩ := hid_calls hh
  obtain ⟨⟨h0, hs0, -, e0⟩, -⟩ := Fo.Pub2.shapeOf_shapeHid hh
  have hNC : P.fs.NC = 4 := by
    rw [e0]
    show h0.NC = 4
    rw [(shape_calls hs0).2, Array.size_map, F4.size]
  refine ⟨hNC, ?_⟩
  have h0lt : 0 < P.S.calls.size := by rw [F4.size]; norm_num
  have hq : P.fs.calls[0]? = some (P.S.calls[0]).call := by
    rw [efc]
    simp [h0lt]
  refine largest_table_of_accepted_lookup hok hq ?_
  obtain ⟨calls, hM, hcs, -, -⟩ := calls_of_shape hA
  have hm : P.S.calls[0] ∈ P.S.calls.toList := by simp
  generalize P.S.calls[0] = k0 at hm ⊢
  rw [eSA] at hm
  have hm' : k0 ∈ (A.calls.mapIdx fun q c =>
      ({ c with call := { c.call with iota := io q } } : Attention.ACall)).toList := hm
  rw [Array.toList_mapIdx, List.mem_mapIdx] at hm'
  obtain ⟨i, hi, e⟩ := hm'
  rw [← e]
  show (A.calls.toList[i]).call.k = 16
  have hmem : A.calls.toList[i] ∈ calls := by
    have el : A.calls.toList = calls := by rw [hcs]
    rw [← el]
    exact List.getElem_mem hi
  obtain ⟨x, -, hl⟩ := mapM_mem hM _ hmem
  exact laid_call_has_sixteen_bits hl hk

/-- **In scope the layers' lookup has its largest table at 2^16 rows.** -/
theorem layers_largest_table_in_scope (hC : VerifierAndGoals.InScope F = true) (hF : VerifierAndGoals.readFiles F = .ok pp)
    (hX : Verify.publicOf F.pol F.KL lay = .ok X) : X.y.fo.kT = 16 := by
  obtain ⟨c0, h0, -, hk⟩ := Meaning.P34.hL_in_scope hC hF hX 0
  exact largest_table_of_accepted_lookup (Meaning.P34.ok_layers hX) h0 (by simpa using hk)

end OnBytes.HonestTrace.PlaneLook

#print axioms OnBytes.HonestTrace.PlaneLook.largest_table_of_accepted_lookup
#print axioms OnBytes.HonestTrace.PlaneLook.laid_call_has_sixteen_bits
#print axioms OnBytes.HonestTrace.PlaneLook.attention_configuration_is_the_fills
#print axioms OnBytes.HonestTrace.PlaneLook.attention_lookup_numbers_in_scope
#print axioms OnBytes.HonestTrace.PlaneLook.layers_largest_table_in_scope
