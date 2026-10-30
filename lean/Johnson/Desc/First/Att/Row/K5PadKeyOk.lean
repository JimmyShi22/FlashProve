-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5PadKeyOk.lean: **THE TEST ON THE PADDING KEYS ACCEPTS AT EVERY
SHAPE THAT THE MAKER RETURNS: A GENERAL LAW,
NO EVALUATION.** padKeyOk g (Johnson/Desc/First/Att/ClaimsOk.lean) asks
of each call of g whose table is not of the kind kfd that its padding key is 0. It is the first
conjunct of claimsOk, and paddingLaid's first test (Johnson/Desc/First/Att/RunsP.lean) is the same.
WHY IT HOLDS, BY THE MAKER's TEXT (layCall, OnBytes/Model/AttentionShape.lean): the row t0 to which
padding keys point is set at the kind kfd alone; at the three other kinds it is the default, 0
(OnBytes/Model/Frame.lean); and row 0 has the value 0: rowKR sh 0 = 0, since 0 < 2 ^ sh;
rowWH 0 = 0;
a call of the kind r16 has no table, and there row t has the value t. No table is built: the entry
comes off the table's own definition (padKey_tableOf, padKey_none: Row/K5PadKey.lean).

Main names (namespace H2K5.Row):
  padOkA a: padKeyOk's own test at one call of the maker's. padKeyOk_calls: padKeyOk (geoOf S) is
    that test at all calls of S.
  padOkA_layCall: it accepts at whatever layCall returns: all four kinds; at kfd by its first arm.
  padOkA_iota: it does not read the number iota, which shapeHid sets afterwards.
  padOkA_shape: it accepts at each call of a shape that Attention.shape returns.
  **padKeyOk_shapeHid**: padKeyOk (geoOf S) = true where Attention.shapeHid returns (S, fs).
  **padKeyOk_plan**: the like at a.S where Attention.plan returns a.
  **padKeyOk_ofPlan**: the like at A.S under K5Law.OfPlan A
    (Johnson/Desc/First/Att/Claims/OfPlan.lean): the form that public_ofPlan hands out of the public
    part's own attention segments.
  **padKeyOk_row**: in the row's own letters: from hZ (the front, at the second hash function, has
    returned Z) and ha (Z.p.X.A[g]? = some a): padKeyOk (geoOf a.S) = true. No ground is asked.
CALLED, NOT TYPED ANEW (OnBytes.Road.L5): calls_of_shape and mapM_mem
(Johnson/Road/Lane5AttCalls.lean): the walk through shape's steps; hid_calls
(Johnson/Road/Lane5AttCallsH.lean): what shapeHid returns; plan_shape
(Johnson/Road/Lane5AttPlan.lean); K5Law.ofPlan_shape and public_ofPlan; ProofFile.Law.pub_public
(Johnson/Desc/ProofFile/Law/MakerPublic.lean); publicOfO_older
(Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean).
NEIGHBOURS IN THE LIBRARY, NOT CALLED HERE (OnBytes.Road.L5, Johnson/Road/Lane5AttTabs.lean):
tableOf_at: a row of a table that tableOf makes, read by Model.Call.tauAt, as a field element, under
a bound on the row; isLut_KR and isLut_WH: their clause on padding shows over the integers that row
0 has the value 0. padKey_tableOf gives the machine word itself, at CallG, with no bound.
Limits. It says nothing of padKey at the calls of the kind kfd, which padTerm reads
(Johnson/Desc/First/Att/RunsP.lean). At a copy of the maker with another name (a twin) it does not
apply until that copy's value is tied to the maker's.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Row.K5PadKey
import Johnson.Desc.First.Att.ClaimsOk
import Johnson.Desc.First.Att.Claims.OfPlan
import Johnson.Road.Lane5AttCallsH
import Johnson.Road.Lane5AttPlan
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open OnBytes
open VerifiableInference.Desc.First.Att.P (CallG callOf geoOf padKeyOk)
open OnBytes.Attention (ACall Cfg Listed layCall tableOf rowKR rowWH)
open OnBytes.Road.L5 (calls_of_shape mapM_mem hid_calls plan_shape refuse_ok)

/-- padKeyOk's own test at one call of the maker's. -/
def padOkA (a : ACall) : Bool := (callOf a).tab == .kfd || (callOf a).padKey == 0

theorem padKeyOk_calls (S : Attention.Shape) : padKeyOk (geoOf S) = S.calls.all padOkA := by
  show ((S.calls.map callOf).all fun c => c.tab == .kfd || c.padKey == 0) = _
  rw [Array.all_map]
  rfl

theorem rowKR_zero (sh : Nat) : rowKR sh 0 = 0 := by
  have hp : ¬ (0 ≥ 2 ^ sh) := Nat.not_le.2 (Nat.two_pow_pos sh)
  unfold rowKR
  rw [if_neg hp]

/-- **The test accepts at whatever layCall returns.** -/
theorem padOkA_layCall {cf : Cfg} {HA Smax : Nat} {Tt : Array Nat} {x : Listed} {a : ACall}
    (h : layCall cf HA Smax Tt x = .ok a) : padOkA a = true := by
  obtain ⟨name, kind, sh, segs⟩ := x
  unfold Attention.layCall at h
  obtain ⟨-, h⟩ := refuse_ok h
  have e := Except.ok.inj h
  subst e
  unfold padOkA
  cases kind with
  | kfd => rfl
  | kr =>
    rw [Bool.or_eq_true]
    refine Or.inr ?_
    rw [beq_iff_eq, padKey_tableOf _ (k := 16) (row := rowKR sh) rfl (Nat.two_pow_pos 16)]
    show UInt64.ofNat (rowKR sh 0) = 0
    rw [rowKR_zero]
    rfl
  | wh =>
    rw [Bool.or_eq_true]
    refine Or.inr ?_
    rw [beq_iff_eq, padKey_tableOf _ (k := 16) (row := rowWH) rfl (Nat.two_pow_pos 16)]
    show UInt64.ofNat (rowWH 0) = 0
    rfl
  | r16 =>
    rw [Bool.or_eq_true]
    refine Or.inr ?_
    rw [beq_iff_eq, padKey_none _ rfl]
    rfl

/-- The test does not read iota. -/
theorem padOkA_iota (c : ACall) (i : Nat) :
    padOkA { c with call := { c.call with iota := i } } = padOkA c := rfl

theorem padOkA_shape {cf : Cfg} {S : Attention.Shape} (h : Attention.shape cf = .ok S) (a : ACall)
    (ha : a ∈ S.calls.toList) : padOkA a = true := by
  obtain ⟨calls, hM, hc, -, -⟩ := calls_of_shape h
  rw [hc] at ha
  obtain ⟨x, -, hx⟩ := mapM_mem _ _ _ hM a ha
  exact padOkA_layCall hx

/-- **AT EVERY SHAPE THAT shapeHid RETURNS THE TEST ON THE PADDING KEYS ACCEPTS.** -/
theorem padKeyOk_shapeHid {lid : Nat} {cf : Cfg} {S : Attention.Shape}
    {fs : Model.Forest.Shape} (h : Attention.shapeHid lid cf = .ok (S, fs)) :
    padKeyOk (geoOf S) = true := by
  obtain ⟨A, io, kbA, hA, eS, -⟩ := hid_calls h
  subst eS
  rw [padKeyOk_calls, ← Array.all_toList]
  refine List.all_eq_true.2 fun k hk => ?_
  have hk' : k ∈ (A.calls.mapIdx fun q c =>
      ({ c with call := { c.call with iota := io q } } : ACall)).toList := hk
  rw [Array.toList_mapIdx, List.mem_mapIdx] at hk'
  obtain ⟨i, hi, rfl⟩ := hk'
  exact (padOkA_iota _ _).trans (padOkA_shape hA _ (List.getElem_mem hi))

/-- **At every value of Attention.plan.** -/
theorem padKeyOk_plan {settings : Model.Settings} {i : Attention.In} {cf : Cfg}
    {a : Attention.Plan} (h : Attention.plan settings i cf = .ok a) :
    padKeyOk (geoOf a.S) = true :=
  padKeyOk_shapeHid (plan_shape h).1

/-- **In the form that the public part's own attention segments have.** -/
theorem padKeyOk_ofPlan {A : Attention.Plan} (h : K5Law.OfPlan A) :
    padKeyOk (geoOf A.S) = true := by
  obtain ⟨_, _, hh⟩ := K5Law.ofPlan_shape h
  exact padKeyOk_shapeHid hh

/-- **IN THE ROW's OWN LETTERS: where the front has returned Z, at each attention segment of its
public part.** -/
theorem padKeyOk_row {pol lay KL : ByteArray} {Z : ProofFile.Pub} {g : Nat} {a : Attention.Plan}
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction pol lay KL = .ok Z) (ha : Z.p.X.A[g]? = some a) :
    padKeyOk (geoOf a.S) = true := by
  have hX : Model.Verify.publicOf pol KL (some lay) = .ok Z.p.X :=
    (VerifiableInference.PlanWritten.publicOfO_older pol KL (some lay)).symm.trans
      (ProofFile.Law.pub_public hZ)
  exact padKeyOk_ofPlan (K5Law.public_ofPlan hX g a ha)

end H2K5.Row

#print axioms H2K5.Row.padKeyOk_calls
#print axioms H2K5.Row.rowKR_zero
#print axioms H2K5.Row.padOkA_layCall
#print axioms H2K5.Row.padOkA_iota
#print axioms H2K5.Row.padOkA_shape
#print axioms H2K5.Row.padKeyOk_shapeHid
#print axioms H2K5.Row.padKeyOk_plan
#print axioms H2K5.Row.padKeyOk_ofPlan
#print axioms H2K5.Row.padKeyOk_row
