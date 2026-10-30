-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastStretch.lean: THE ONE FACT OF MAKE THAT `last_list_of_flat` AND
`eachOwn_pure` ASK (hds: the third stretch of the data of the written rounds is dB :: dt), PAID AT
THE PROOF FILE's OWN DESCRIPTION.
  `third_owed`: where FL's road to its data says D and its sealing test says yes, the third stretch
    has as many rounds as the third block declares: by `paidAtDesc`
    (Johnson/Desc/Sound/PaidAtDesc.lean: the maker's pieces tile the chain) read at the third of the
    four pieces.
  `c2_rounds`: where the third block's own test on the plan says yes, it declares at least one
    round: `proximityTestKind`'s test asks that its rounds are `roundsIn` of the stages, which is 1 + … + 2
    (Johnson/Desc/K12/Frame.lean).
  `hds_pure`: **so there are dB and dt with `ds₂ D.ds₃ (held c0) (held c1) (held c2) = dB :: dt`.**
  `hds_of_planOk`: the same from the data's yes and FL's tests on the plan alone: they ask the
    sealing test, and of every block of the last chain its own test (`last_ok_of_planOk`: the fourth
    clause of `planOkCore`, by position).
Every "there is": dB, dt: the head and the tail of a list that is shown not to be empty; whoever
spends them hands them to `eachOwn_pure`, whose debts at row 2 are then said at them.
Limits. The three premises (the data's yes, the sealing test, the third block's test on the plan)
are what the laid value's own tests ask; that they say yes at any files is an evaluation. Nothing on
soundness.
-/
import Johnson.LLT25R.LastSeat
import Johnson.Desc.K12.FrameLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace LLT25
open OnBytes OnBytes.Maker
open _root_.Run
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (A : SharedSeat) (N : H2U.Places4)
  (c : Chain S Cl)

/-- Where the proximity test's block's test on the plan says yes, it declares a round. -/
theorem k12_rounds_ne {T Cl' : Type} (X : Parts T) (p : P12)
    (h : (proximityTestKind X p : Block T Cl').planOk = true) : (proximityTestKind X p : Block T Cl').rounds ≠ [] := by
  have hr := k12_rounds X p h
  intro e
  rw [e] at hr
  unfold proximityTestKind at h
  split at h
  · rename_i first rest rs os hs hr' ho
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have hl : rs.length = roundsIn p.nums.stages := h.1.1.1.2
    rw [hr'] at hr
    cases hr
    unfold roundsIn at hl
    simp only [List.length_nil] at hl
    omega
  · simp at h

/-- Where the third block's own test on the plan says yes, it declares a round. -/
theorem c2_rounds (hp : (c2 N).planOk = true) : (c2 N).rounds ≠ [] := by
  rw [c2_is] at hp ⊢
  have hk : (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 Cl).planOk = true := by
    have h' : ((proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 Cl).planOk &&
      (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 Cl).claims.isEmpty &&
      (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 Cl).after.isEmpty) = true := hp
    simp only [Bool.and_eq_true] at h'
    exact h'.1.1
  exact k12_rounds_ne guardedProximityTestParts _ hk

section
variable {W : Type} (D : WholeD)
  (a₁ : Block (FL o mk Z A N c).S₁ (FL o mk Z A N c).Cl) (k₁ : List (Block (FL o mk Z A N c).S₁ (FL
      o mk Z A N c).Cl))
  (a₂ : Block (FL o mk Z A N c).S₂ (FL o mk Z A N c).Cl) (k₂ : List (Block (FL o mk Z A N c).S₂ (FL
      o mk Z A N c).Cl))

/-- **The third stretch has as many rounds as the third block declares.** -/
theorem third_owed (file : String) (hD : (FL o mk Z A N c).data file = .ok D)
    (hS : (FL o mk Z A N c).sealLast = true) (q₁ : (FL o mk Z A N c).first.blocksInOrder = a₁ :: k₁)
    (q₂ : (FL o mk Z A N c).shared.blocksInOrder = a₂ :: k₂) :
    (ds₂ D.ds₃ (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂)
        (c0 Z)) (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂)
        (c1 N)) (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂)
        (c2 N))).length = (c2 N).rounds.length := by
  obtain ⟨-, hf, -⟩ := paidAtDesc _ Unit (FL o mk Z A N c) file D hD hS (ckP .two) a₁ k₁ a₂ k₂ (c0
      Z) [c1 N, c2 N, c3 Z N] q₁ q₂ (last_flat_pure o mk Z A N c) (fun _ _ => ⟨fun _ _ w => w,
      Iop.Err.cap 128 _⟩) (fun _ _ => ⟨fun _ _ w => w, Iop.Err.cap 128 _⟩) (fun _ _ => ⟨fun _ _ w =>
      w, Iop.Err.cap 128 _⟩) () ()
  have ht := hf.tiled₃
  exact ht.2.2.2.2.2.2.2.2.1.1

/-- **The one fact of make.** -/
theorem hds_pure (file : String) (hD : (FL o mk Z A N c).data file = .ok D)
    (hS : (FL o mk Z A N c).sealLast = true) (q₁ : (FL o mk Z A N c).first.blocksInOrder = a₁ :: k₁)
    (q₂ : (FL o mk Z A N c).shared.blocksInOrder = a₂ :: k₂) (hp : (c2 N).planOk = true) :
    ∃ dB dt, ds₂ D.ds₃ (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N
        c).S₂) (c0 Z)) (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N
        c).S₂) (c1 N)) (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N
        c).S₂) (c2 N)) = dB :: dt := by
  have hl := third_owed o mk Z A N c D a₁ k₁ a₂ k₂ file hD hS q₁ q₂
  have hr := c2_rounds N hp
  cases hx : ds₂ D.ds₃ (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N
      c).S₂) (c0 Z)) (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N
      c).S₂) (c1 N)) (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N
      c).S₂) (c2 N)) with
  | nil =>
    rw [hx] at hl
    exact absurd (List.length_eq_zero_iff.1 hl.symm) hr
  | cons dB dt => exact ⟨dB, dt, rfl⟩

/-- The tests on the plan ask that the last chain's blocks pass their own: the fourth clause. -/
theorem last_ok_of_planOk {Xi : Type} (F : FileDescription Xi) (h : F.planOk = true) :
    blocksOk F.second.blocksInOrder = true := by
  unfold FileDescription.planOk FileDescription.planOkCore at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1.1.2

/-- **The one fact of make, from the data's yes and the tests on the plan.** -/
theorem hds_of_planOk (file : String) (hD : (FL o mk Z A N c).data file = .ok D) (hP : (FL o mk Z A
    N c).planOk = true)
    (q₁ : (FL o mk Z A N c).first.blocksInOrder = a₁ :: k₁) (q₂ : (FL o mk Z A N c).shared.blocksInOrder = a₂ :: k₂) :
    ∃ dB dt, ds₂ D.ds₃ (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N
        c).S₂) (c0 Z)) (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N
        c).S₂) (c1 N)) (held (P := (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N
        c).S₂) (c2 N)) = dB :: dt := by
  have hb := last_ok_of_planOk (FL o mk Z A N c) hP
  rw [last_flat_pure] at hb
  have hS : (FL o mk Z A N c).sealLast = true := by
    unfold FileDescription.planOk at hP
    simp only [Bool.and_eq_true] at hP
    exact hP.2
  have hp : (c2 N).planOk = true := by
    have hb' : ([c0 Z, c1 N, c2 N, c3 Z N].all fun b => b.planOk && b.shaped) = true := hb
    have h2 := List.all_eq_true.1 hb' (c2 N)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    exact (Bool.and_eq_true_iff.1 h2).1
  exact hds_pure o mk Z A N c D a₁ k₁ a₂ k₂ file hD hS q₁ q₂ hp

end

end LLT25

#print axioms LLT25.k12_rounds_ne
#print axioms LLT25.c2_rounds
#print axioms LLT25.third_owed
#print axioms LLT25.hds_pure
#print axioms LLT25.last_ok_of_planOk
#print axioms LLT25.hds_of_planOk
