-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/PlanRAtHead.lean: CONDITIONAL: THE FACTS ON THE PLAN THAT valsTS_of_R
TAKES (PlanR, Johnson/Desc/K5/Honest/Law/LookR.lean) HOLD AT EACH OF THE TWELVE ATTENTION SEGMENTS
UNDER THE HEAD; AND, WHERE THE ONE BOOL ON THE SHAPE SAYS YES AND THE SENTENCE ON THE LOOKUP HOLDS,
THE TWO TESTS ON VALUES SAY YES. A joining of the library's lemmas.

Main names:
  planR_at_head   **PlanR at the group's plan**: under the head at any of the format's hashes (the
    letter o), g below 12
  LookOn A s      the chain stands in an attention link whose field g meets lookR A (the same clause
    as riderAtt, Johnson/Desc/ProofFile/Honest/Thread/RidersAtt.lean, unfolded)
  valsTS_of_tabsGC    **the one Bool tabsGC at the state's shape, LookOn, the facts on the plan: then
    valsTS A s**: of valsTS_of_R's other premises the Bool gives heard5 and the return of the
    function of the points

Limits. The head is a hypothesis. valsTS_of_tabsGC is conditional on its three premises; nothing here
says that tabsGC or LookOn holds at any state. Nothing is claimed on soundness, completeness or
hiding.
-/
import Johnson.Desc.K5.Honest.Law.RunsPreR
import Johnson.Desc.K5.Honest.Law.PublicAtHead
import Johnson.Desc.K5.Honest.Law.TabsChain
import Johnson.Road.Rows.AttReadLong

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att.P (UnitG)
open VerifiableInference.Desc.First.Shape (chainSh heardAll heard5Sh ledSh)
open OnBytes.Road.L5 (dimOf)
open P5J (AtMgA TS)

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}

/-- **THE FACTS ON THE PLAN, AT THE GROUP's PLAN.** Conditional: the head; g is below 12; the group's
plan. -/
theorem planR_at_head (h : AtMgA o Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {a : Attention.Plan}
    (ea : (P5J.At.X Zp).A[g]? = some a) :
    ∃ r1 r2 u1 u2 wl ix wh, PlanR a r1 r2 u1 u2 wl ix wh := by
  obtain ⟨hid, PL⟩ := law_at_head h hg ea
  obtain ⟨r1, r2, u1, u2, wl, ix, wh, U, -⟩ := (public_at_head h hg ea).units
  have Nn := OnBytes.Road.Rows.norm_of_hid hid
  have Zs := OnBytes.Road.Rows.sizes_of_hid hid
  have hlm : ∀ f : Inst.Model.AttSeg.Fam, Cb.Pv.Att.End.IsPlane f →
      a.S.cf.lmS ≤ f.l (dimOf a.S) := by
    intro f hf
    have z := Zs.lmS
    have n1 := Nn.nD
    have n2 := Nn.nM
    cases f with
    | m1 =>
      show a.S.cf.lmS ≤ a.S.cf.lgk + (a.S.lnT - 1) + (a.S.lnT - 1 + 1) + a.S.cf.lB + a.S.cf.lB
      omega
    | d1 =>
      show a.S.cf.lmS ≤ a.S.cf.lgk + (a.S.lnT - 1 + 1) + a.S.cf.lB + a.S.cf.lB
      omega
    | m2 =>
      show a.S.cf.lmS ≤ a.S.cf.lgk + (a.S.lnT - 1) + (a.S.lnT - 1 + 1) + a.S.cf.lB + a.S.cf.lB
      omega
    | d2 =>
      show a.S.cf.lmS ≤ a.S.cf.lgk + (a.S.lnT - 1 + 1) + a.S.cf.lB + a.S.cf.lB
      omega
    | w3 => exact False.elim hf
    | x3 => exact False.elim hf
    | f4 => exact False.elim hf
  obtain ⟨_, _, _, _, _, _, ⟨_, fD, fW, _, _⟩, _⟩ := PL.fit
  refine ⟨r1, r2, u1, u2, wl, ix, wh, U, Nn, Nat.le_of_succ_le Zs.lnT, hlm, PL.fit,
    le_trans (hlm .d1 trivial) fD, ?_⟩
  refine le_trans ?_ fW
  show _ ≤ 1 + a.S.cf.lgk + (a.S.lnT - 1 + 1 + a.S.cf.lB) + a.S.cf.ldh
  have := Nn.lt
  omega

end

/-- The chain stands in an attention link whose field g meets the sentence on what the lookup
returned. A definition: a premise's form. -/
def LookOn (A : Attention.Plan) (s : First.S) : Prop :=
  ∃ a, s.here = .att a ∧ lookR A a.g

/-- **THE ONE BOOL ON THE SHAPE, THE SENTENCE ON THE LOOKUP AND THE FACTS ON THE PLAN GIVE THE TWO
TESTS ON VALUES.** CONDITIONAL on all three. -/
theorem valsTS_of_tabsGC (A : Attention.Plan) {r1 r2 u1 u2 wl ix wh : UnitG}
    (Q : PlanR A r1 r2 u1 u2 wl ix wh) {s : First.S}
    (hG : tabsGC A (chainSh s) = true) (hL : LookOn A s) : valsTS A s = true := by
  obtain ⟨a, h, gl, hh, h5, hgl, hT⟩ := parts_of_GC A hG
  obtain ⟨a', ha', hR⟩ := hL
  obtain rfl : a = a' := by
    rw [hh] at ha'
    injection ha' with e
  have hB : ptsB (Att.P.parCOf A).geo (heardAll gl).zk (heard5Sh h) (ledSh a.F) = true := by
    unfold tabsG at hT
    rw [Bool.and_eq_true, Bool.and_eq_true] at hT
    exact hT.1.1
  exact valsTS_of_R A Q hh hR h5
    (fun gl' e => by
      obtain rfl : gl = gl' := Option.some.inj (hgl.symm.trans e)
      exact pts_returns hB) 0

end H2K5.Honest

#print axioms H2K5.Honest.planR_at_head
#print axioms H2K5.Honest.valsTS_of_tabsGC
