-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.MemberO
import Johnson.Desc.K12.Law.LitOFull
/-
Johnson/Desc/K12/Law/MemberOFull.lean: A MEMBER OF PayK, NOT OF THE PROMISE, AT THE FULL SIZE: at the proximity test O of the full-size stored proof (LitOFull.lean). As MemberO.lean, whose head's limits hold here word for word: of a twin (FixesP | PayKP; over the true names: Coin/MemberPromFull.lean); that tOFull is the record which the verifier reaches on the stored file is not proved; (a) (b) read no field element. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  piOFull | rOFull: Johnson/Desc/K12/Law/PlacesFull.lean. rOFull: the planner's own radii at the four stages: 3131972 · 196271 · 12180 · 26843 (from a print, at the full size, of a program of ours, not in this repository), keyed by the main code's a (22 · 18 · 14 · 15; 0 elsewhere).
  member_OFull: no premise, no free letter; batV0 = 474 (= 237 · 2; the same print says so). By Lean's kernel alone.
  oF_below: PayKP fails at 473.

-/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace H2K.Member
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (johOk batV0 spendOk pubOk)
open H2K.First (batOneOk)

theorem oF_memberB : memberB piOFull rOFull tOFull = true := by decide +kernel
theorem oF_publicB : publicB piOFull rOFull tOFull.st.codes = true := by decide +kernel
theorem oF_v0 : batV0 piOFull rOFull = 474 := by decide +kernel

/-- **A member of PayK at a real place of the full-size proof.** -/
theorem member_OFull :
    (∃ a rest G0 Ly D, FixesP piOFull tOFull a rest G0 Ly D) ∧
    PayKP piOFull (fun s => rOFull s.st) (batV0 piOFull rOFull) tOFull ∧
    (proximityTestKind guardedProximityTestParts piOFull : Block T12 Unit).planOk = true ∧ piOFull.early = true ∧
    piOFull.answers = 1 ∧ piOFull.nums.ownMask = true ∧ johOk piOFull rOFull = true ∧
    batOneOk piOFull = true ∧ spendOk piOFull = true ∧ pubOk piOFull tOFull.st.codes = true ∧
    batV0 piOFull rOFull = 474 := by
  obtain ⟨m1, m2⟩ := member_of_B piOFull rOFull tOFull oF_memberB
  have h := oF_publicB
  simp only [publicB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨m1, m2, h1, h2, h3, rfl, h4, h5, h6, h7, oF_v0⟩

theorem oF_below : ¬ PayKP piOFull (fun s => rOFull s.st) 473 tOFull :=
  not_pay_below piOFull rOFull tOFull oF_memberB 473 (by rw [oF_v0]; decide)

theorem oF_roots : tOFull.roots = piOFull.nums.free := rfl

end H2K.Member

#print axioms H2K.Member.member_OFull
#print axioms H2K.Member.oF_below
