-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ForestAtHead.lean: AT ALL PUBLIC FILES IN THE GOALS' SCOPE, AND
SO UNDER THE LIBRARY's HEAD: THE SIZES OF THE LOOKUP OF AN ATTENTION SUB-PROOF ARE WRITTEN NUMBERS:
`forestSize a.fs = { v := 29, d := 18, shifted := true }`, AND `Forest.elems a.fs = 1812`. Facts on
public parameters alone. Statements with their proofs; no definition.

Why. The number of scalars that the lookup sends, `Forest.elems a.fs`, is where K5's stretch begins
in the segment's mask row. It reads two numbers of the lookup's record: v = dT + rK and d = kT + cK.
The library has dT = 25 and rK = 4 in scope (`Meaning.Att.att_nums_in_scope`,
Johnson/Goal/Meaning/AttNumsScope.lean) and the number of calls, 4 (`sameCalls_in_scope`,
Johnson/Goal/Meaning/AttForInScope.lean). Here kT = 16 and cK = 2 come beside them, by the makers'
texts.

  `layCall_k`         where the table of kind KFD has 2^16 rows, every call that `layCall` lays has
                      k = 16: by its text
  `calls_k`           so every call of what `Attention.shape` returns
  `hid_forest_more`   `shapeHid`'s record of the lookup has the kT and cK that `Forest.shape`
                      returns on shape's calls: the twin of the library's `hid_forest`, which
                      keeps dT and rK
  `kc_of_hid`         kT = 16 and cK = 2, under the usual call list and kFD = 16
  `att_kc_in_scope`   the same at `fsA X g`, in scope
  `forestSize_in_scope`, `elems_in_scope`   MAIN, in scope, at the plan a of group g
  `forestSize_head`, `elems_head`           MAIN, under the head

By: `Cb.Fo.shape_more` (OnBytes/Tie/Pv/Lookup/Port/FoShape.lean): kT is the largest k of the calls ·
`Fo.ZPlan.shape_cK` (OnBytes/Tie/Pv/Lookup/Ends/FoZRec.lean): cK is the rounded-up logarithm of
their number · `ns_of_list` (AttNumsScope.lean): the calls are four · `calls_of_shape`, `mapM_mem`
(Johnson/Road/Lane5AttCalls.lean): each call is one that `layCall` has laid · `hid_in_scope`
(AttForInScope.lean): in scope the plan's record is what `shapeHid` returns at a configuration with
kFD = 16 and the usual call list. The like for the output head's lookup:
Johnson/Desc/Kinds/Law/HeadFsWritten.lean.

Limits. Numbers of a public plan: nothing on a run, an input or a book. g < 12. The scope, and under
it the head, are hypotheses. Nothing on the plan's other fields: of `armsB` (Johnson/AtFull/Rows/)
this gives one of an attention arm's three values. The full size alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Goal.Meaning.AttNumsScope
import OnBytes.Tie.Pv.Lookup.Port.FoShape
import OnBytes.Tie.Pv.Lookup.Ends.FoZRec
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5

open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Verify (publicOf Public)
open Attention (ACall Cfg Shape Listed shape shapeHid layCall)
open Meaning.Att (fsA hid_in_scope sameCalls_in_scope att_nums_in_scope ns_of_list)

/-! ## 1 The calls' table bits, by the makers' texts -/

/-- CONDITIONAL: hk: the table of kind KFD has 2^16 rows. **Every call that `layCall` lays has
k = 16.** -/
theorem layCall_k {cf : Cfg} {HA Sm : ℕ} {Tt : Array ℕ} {x : Listed} {k : ACall}
    (hk : cf.kFD = 16) (h : layCall cf HA Sm Tt x = Except.ok k) : k.call.k = 16 := by
  obtain ⟨name, kind, sh, segs⟩ := x
  unfold Attention.layCall at h
  obtain ⟨-, h⟩ := refuse_ok h
  have e := Except.ok.inj h
  subst e
  cases kind <;> first | rfl | exact hk

/-- CONDITIONAL: hk. The same at every call of what `Attention.shape` returns. -/
theorem calls_k {cf : Cfg} {A : Shape} (hA : shape cf = Except.ok A) (hk : cf.kFD = 16) :
    ∀ c ∈ A.calls.toList, c.call.k = 16 := by
  obtain ⟨calls, hM, hc, -, -⟩ := calls_of_shape hA
  intro c hcm
  rw [hc] at hcm
  obtain ⟨x, -, hx⟩ := OnBytes.Road.L5.mapM_mem _ _ _ hM c hcm
  exact layCall_k hk hx

/-- `shapeHid`'s record of the lookup has the kT and cK that `Forest.shape` returns on shape's
calls. -/
theorem hid_forest_more {lid : ℕ} {cf : Cfg} {S : Shape} {fs : Forest.Shape}
    (h : shapeHid lid cf = Except.ok (S, fs)) :
    ∃ (A : Shape) (fo : Forest.Shape), shape cf = Except.ok A ∧
      Forest.shape (A.calls.map (·.call)) lid = .ok fo ∧ fs.kT = fo.kT ∧ fs.cK = fo.cK := by
  unfold Attention.shapeHid at h
  obtain ⟨A, hA, h⟩ := bind_ok h
  obtain ⟨fo, hfo, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨e1, e2⟩ := Prod.mk.inj (Except.ok.inj h)
  subst e1
  subst e2
  exact ⟨A, fo, hA, hfo, rfl, rfl⟩

/-- CONDITIONAL: the usual call list; kFD = 16. **The largest table has 2^16 rows, and a call's
number has 2 bits.** -/
theorem kc_of_hid {lid : ℕ} {cf : Cfg} {S : Shape} {fs : Forest.Shape}
    (h : shapeHid lid cf = Except.ok (S, fs)) (U : UsualCalls cf) (hk : cf.kFD = 16) :
    fs.kT = 16 ∧ fs.cK = 2 := by
  obtain ⟨A, fo, hA, hfo, e1, e2⟩ := hid_forest_more h
  obtain ⟨hT, -⟩ := ns_of_list (S := A) hA U (fun _ k => k) (fun _ _ => rfl) (mapIdx_keep _).symm
  have K := calls_k hA hk
  have k0 : (callAt A 0).call.k = 16 := K _ (by rw [hT]; simp)
  have k1 : (callAt A 1).call.k = 16 := K _ (by rw [hT]; simp)
  have k2 : (callAt A 2).call.k = 16 := K _ (by rw [hT]; simp)
  have k3 : (callAt A 3).call.k = 16 := K _ (by rw [hT]; simp)
  have hkT : fo.kT = 16 := by
    rw [(Cb.Fo.shape_more hfo).2.2.2.1, ← Array.foldl_toList, Array.toList_map, hT]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [k0, k1, k2, k3]
    rfl
  have hcK : fo.cK = 2 := by
    rw [Fo.ZPlan.shape_cK hfo, Array.size_map, ← Array.length_toList, hT]
    show clog2 4 = 2
    decide
  exact ⟨e1.trans hkT, e2.trans hcK⟩

/-! ## 2 In scope -/

section
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- CONDITIONAL: the scope. The two numbers at the lookup's record of group g. -/
theorem att_kc_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) :
    (fsA X g).kT = 16 ∧ (fsA X g).cK = 2 := by
  obtain ⟨cf, hh, -, hk, -, -, U⟩ := hid_in_scope hZ hR h hg
  exact kc_of_hid hh U hk

/-- CONDITIONAL: the scope; a is the plan of group g. **THE SIZES OF THE LOOKUP OF AN ATTENTION
SUB-PROOF ARE WRITTEN NUMBERS.** -/
theorem forestSize_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ha : X.A[g]? = some a) : forestSize a.fs = { v := 29, d := 18, shifted := true } := by
  have ef : fsA X g = a.fs := by
    unfold fsA
    rw [ha]
    rfl
  obtain ⟨-, d1, d2⟩ := att_nums_in_scope hZ hR h hg
  obtain ⟨d3, d4⟩ := att_kc_in_scope hZ hR h hg
  have d5 := (sameCalls_in_scope hZ hR h hg).NC
  rw [ef] at d1 d2 d3 d4 d5
  unfold forestSize Forest.Shape.v Forest.Shape.d
  rw [d1, d2, d3, d4, d5]
  rfl

/-- CONDITIONAL: as `forestSize_in_scope`. **The lookup sends 1812 scalars.** -/
theorem elems_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ha : X.A[g]? = some a) : Forest.elems a.fs = 1812 := by
  have e := forestSize_in_scope hZ hR h hg ha
  have hv : a.fs.v = 29 := congrArg (·.v) e
  have hd : a.fs.d = 18 := congrArg (·.d) e
  unfold Forest.elems
  rw [hv, hd]
  rfl

end

/-! ## 3 Under the head -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: h: the head; hg; ea. **Under the head the sizes are the written ones.** -/
theorem forestSize_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) :
    forestSize a.fs = { v := 29, d := 18, shifted := true } :=
  forestSize_in_scope h.scope h.reads h.pubOne hg ea

/-- CONDITIONAL: h: the head; hg; ea. **Under the head the lookup sends 1812 scalars.** -/
theorem elems_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) : Forest.elems a.fs = 1812 :=
  elems_in_scope h.scope h.reads h.pubOne hg ea

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.layCall_k
#print axioms ProofFile.Honest.K5.calls_k
#print axioms ProofFile.Honest.K5.hid_forest_more
#print axioms ProofFile.Honest.K5.kc_of_hid
#print axioms ProofFile.Honest.K5.att_kc_in_scope
#print axioms ProofFile.Honest.K5.forestSize_in_scope
#print axioms ProofFile.Honest.K5.elems_in_scope
#print axioms ProofFile.Honest.K5.forestSize_head
#print axioms ProofFile.Honest.K5.elems_head
