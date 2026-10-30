-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyOn2Tests.lean:
«on₂_of_tests»: THE SHARED CHAIN's WHOLE PROMISE On₂ … k AT THE KEY FILE's OWN DESCRIPTION AND THE
FILLING OF THE READING, FROM TESTS ON THE STATE, ONE LAW's FACT AND THE STORED TABLE's SIDE: ONE
SKELETON IN THE FIRST CHAIN's SHAPE: on₁_of_tests (Johnson/RunOne/KeyFillOn.lean) IS THE
PATTERN, COPIED, NOT RE-DERIVED.
THE THREE HEAPS (Johnson/RunOne/KeyOn2Parts.lean: on₂_of_parts):
 (α) T : Tests₂ … k z: sixteen facts on the state alone: PREMISES: run
   at the honest walk, each with a control.
 (β) arr | reads: CALLS of arrOk_six₂ | readsPinned_h₂.
 (γ) the strings' side: shown · hasSmp · NoColl at the open pins: A CALL of
   member_of_record₂ (Johnson/RunOne/KeyFillChains.lean) with its shownK; record: L2 | L2' as
   in on₁_of_tests (at a stored table of code words L2' is
   OnBytes.K.Oracle.not_coll_words' matter).
 L1, «BY A TERM»: at every open pin the sending kind's own sample row lies in the record: L1lo: at
   the elder pins 0 | 2 in the HANDED first state (from the first chain's member, through the seam)
   · L1hi: at the chain's own pins 3 | 4 | 5 in the own statement: Johnson/RunOne/KeySeedIs2.lean's
   seedIs_send2 | seedIs_send5 conclude it behind the held sendings' own yes.
 PUBLIC TESTS, as in on₁_of_tests: no fault at the seats (seatFaultAt … = none) · the frame holds
   the trees (holdsB): EACH IS ASKED ONLY WHERE ITS PIN IS OPEN AT k (pinned (open₂ k)
   = [0, 2] at k ≤ 2 · [0, 2, 3] at 3 … 5 · [0, 2, 3, 4, 5] from 6: by evaluation).
  on₂_of_tests_lo   at k ≤ 2 (the guards of rows 2.0 | 2.1 | 2.2): the chain's own pins are not
    open: L1hi and six of the ten public tests FALL.
AN IMPLICATION: NO MEMBER IS SHOWN HERE. y' IS BUILT (the pull of a family of code words
onto y₀'s stored side): NO RUN's OWN ORACLES: as at the first chain.
OBJECT: on₂ (Fk X N P) (fr₂ D) (baseK csKey six numSix atSix decT recOf (plan₁ (oneAt X)).orc).h₂
atSix (shapeAt X) (plan₁ (oneAt X)) (kreadFam csKey six numSix atSix tab) enc rad (oneAt
X).given.plan.samples coll (last₁At (oneAt X)) off₂ k (z, y') [= On₂ at these letters] ·
USER: the member's column of rows 2.0 … 2.8 · LETTERS: X N P D; decT recOf tab coll enc rad off₂; k
z y₀.
Nothing on soundness.
-/
import Johnson.RunOne.KeyOn2Parts
import Johnson.RunOne.KeyFillChains

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState)
open VerifiableInference.Desc.K1 (SeedIs Tie)
open Johnson.RunOne.KeyRows1 (plan₁)
open Cb Johnson.Pack OnBytes.Maker OnBytes.Slice
open OnBytes.Params VerifiableInference.Desc.Sound

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD)
  {Cells Rec : Type} [Inhabited Cells] (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells)
      (recOf : Xi → Option Rec) (tab : Cells → ℕ → ℕ → OnBytes.F) (coll : Strs → Rec → Prop)
  (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (off₂ : ℕ → ℕ)

/-- **THE SHARED CHAIN's WHOLE PROMISE AT A BORDER, FROM TESTS ON THE STATE, ONE LAW's FACT AND THE
STORED TABLE's SIDE.** -/
theorem on₂_of_tests (k : ℕ) (t0 t2 t3 t4 t5 : String)
    (n0 : 0 ∈ pinned (open₂ k) → seatFaultAt (Fk X N P) Johnson.Top.H.csKey t0 Johnson.Top.H.shIdx 0
        0 = none)
    (n2 : 2 ∈ pinned (open₂ k) → seatFaultAt (Fk X N P) Johnson.Top.H.csKey t2 Johnson.Top.H.shW 5 0
        = none)
    (n3 : 3 ∈ pinned (open₂ k) → seatFaultAt (Fk X N P) Johnson.Top.H.csKey t3 Johnson.Top.H.shU 6 0
        = none)
    (n4 : 4 ∈ pinned (open₂ k) → seatFaultAt (Fk X N P) Johnson.Top.H.csKey t4 Johnson.Top.H.shO 7 0
        = none)
    (n5 : 5 ∈ pinned (open₂ k) → seatFaultAt (Fk X N P) Johnson.Top.H.csKey t5 Johnson.Top.H.shSp 8
        0 = none)
    (f0 : 0 ∈ pinned (open₂ k) → holdsB (fr₂ D) 0 (aOf Johnson.Top.H.csKey Johnson.Top.H.shIdx) =
        true)
    (f2 : 2 ∈ pinned (open₂ k) → holdsB (fr₂ D) 5 (aOf Johnson.Top.H.csKey Johnson.Top.H.shW) =
        true)
    (f3 : 3 ∈ pinned (open₂ k) → holdsB (fr₂ D) 6 (aOf Johnson.Top.H.csKey Johnson.Top.H.shU) =
        true)
    (f4 : 4 ∈ pinned (open₂ k) → holdsB (fr₂ D) 7 (aOf Johnson.Top.H.csKey Johnson.Top.H.shO) =
        true)
    (f5 : 5 ∈ pinned (open₂ k) → holdsB (fr₂ D) 8 (aOf Johnson.Top.H.csKey Johnson.Top.H.shSp) =
        true)
    (y₀ : (fr₂ D).E.Str) (z : P₂ × St₂)
    (T : Tests₂ atSix (shapeAt X) (plan₁ (oneAt X)) (oneAt X).given.plan.samples (last₁At (oneAt X))
        off₂ k z)
    (L1lo : ∀ i : Fin six.length, numSix i ∈ pinned (open₂ k) → numSix i < 3 →
      ∃ o ρ y, (plan₁ (oneAt X)).orc (numSix i) = some o ∧ SeedIs Johnson.Top.H.csKey (six.get i).1
          z.1.2.d.st o ρ y)
    (L1hi : ∀ i : Fin six.length, numSix i ∈ pinned (open₂ k) → ¬ numSix i < 3 →
      ∃ o ρ y, orc₂ (numSix i) = some o ∧ SeedIs Johnson.Top.H.csKey (six.get i).1 z.2.st o ρ y)
    (r : Rec) (L2 : recOf z.1.1 = some r) (L2' : ∀ y' : (fr₂ D).E.Str, y'.1 = y₀.1 → ¬ coll (strsOf
        (fr₂ D) y') r) :
    ∃ y' : (fr₂ D).E.Str, y'.1 = y₀.1 ∧
      on₂ (Fk X N P) (fr₂ D) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (plan₁ (oneAt
          X)).orc).h₂ atSix (shapeAt X) (plan₁ (oneAt X))
        (kreadFam Johnson.Top.H.csKey six numSix atSix tab) enc rad (oneAt X).given.plan.samples
            coll (last₁At (oneAt X)) off₂ k (z, y') := by
  have hIn := open₂_in k
  have hFit : ∀ i : Fin six.length, numSix i ∈ pinned (open₂ k) → FitsAt Johnson.Top.H.csKey six
      (seatAt six numSix atSix) (Fk X N P) i := by
    intro i hi
    have h5 := hIn _ hi
    obtain ⟨q, hq⟩ := i
    have h6 : q < 6 := hq
    interval_cases q
    · exact fitsAt_of_noFault _ six _ _ _ t0 (n0 hi)
    · exact absurd (show (1 : ℕ) ∈ [0, 2, 3, 4, 5] from h5) (by decide)
    · exact fitsAt_of_noFault _ six _ _ _ t2 (n2 hi)
    · exact fitsAt_of_noFault _ six _ _ _ t3 (n3 hi)
    · exact fitsAt_of_noFault _ six _ _ _ t4 (n4 hi)
    · exact fitsAt_of_noFault _ six _ _ _ t5 (n5 hi)
  have hHold : ∀ i : Fin six.length, numSix i ∈ pinned (open₂ k) → HoldsAt Johnson.Top.H.csKey six
      (seatAt six numSix atSix) (fr₂ D) i := by
    intro i hi
    have h5 := hIn _ hi
    obtain ⟨q, hq⟩ := i
    have h6 : q < 6 := hq
    interval_cases q
    · exact holdsAt_of_B _ six _ _ _ (f0 hi)
    · exact absurd (show (1 : ℕ) ∈ [0, 2, 3, 4, 5] from h5) (by decide)
    · exact holdsAt_of_B _ six _ _ _ (f2 hi)
    · exact holdsAt_of_B _ six _ _ _ (f3 hi)
    · exact holdsAt_of_B _ six _ _ _ (f4 hi)
    · exact holdsAt_of_B _ six _ _ _ (f5 hi)
  have hrec : ∀ i : Fin six.length, numSix i ∈ pinned (open₂ k) →
      ∃ ρ y, seedIsS Johnson.Top.H.csKey six numSix (rowIsK Johnson.Top.H.csKey six) (src₂ (plan₁
          (oneAt X)).orc) i z ρ (fun _ => y) := by
    intro i hi
    by_cases h : numSix i < 3
    · obtain ⟨o, ρ, y, ho, hy⟩ := L1lo i hi h
      exact ⟨ρ, y, (seedIsS_iff₂_lo Johnson.Top.H.csKey six numSix (plan₁ (oneAt X)).orc i h z ρ
          _).2 ⟨o, ho, y, hy, rfl⟩⟩
    · obtain ⟨o, ρ, y, ho, hy⟩ := L1hi i hi h
      exact ⟨ρ, y, (seedIsS_iff₂_hi Johnson.Top.H.csKey six numSix (plan₁ (oneAt X)).orc i h z ρ
          _).2 ⟨o, ho, y, hy, rfl⟩⟩
  obtain ⟨W, y', hy, h⟩ := member_of_record₂ Johnson.Top.H.csKey six numSix atSix decT recOf (plan₁
      (oneAt X)).orc (Fk X N P) (fun i => numSix i ∈ pinned (open₂ k)) (fr₂ D)
    seat_inj_six shapesApart_six (fun a b h => Fin.ext h) hFit hHold (fun i _ => tie_six i) (fun i _
        => List.all_eq_true.1 meets_six _ (List.get_mem six i))
    (fun i _ => of_decide_eq_true (List.all_eq_true.1 caseE_six _ (List.get_mem six i))) (fun i _ =>
        List.all_eq_true.1 hasPad_six _ (List.get_mem six i)) y₀ z hrec default
  have at' : ∀ q ∈ pinned (open₂ k), ∃ i : Fin six.length, numSix i = q := fun q hq =>
    ⟨⟨q, by
      have h5 := hIn q hq
      have h6 : ∀ q ∈ [0, 2, 3, 4, 5], q < six.length := by decide
      exact h6 q h5⟩, rfl⟩
  refine ⟨y', hy, on₂_of_parts (Fk X N P) (fr₂ D) _ atSix (shapeAt X) (plan₁ (oneAt X)) _ enc rad _
      coll _ off₂ k z y' T
    (arrOk_six₂ _ decT recOf _) (readsPinned_h₂ _ six numSix atSix _ decT recOf _ _ rfl _) ⟨⟨r, L2,
        L2' y' hy⟩, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩⟩
  · obtain ⟨i, rfl⟩ := at' q hq
    exact shownK _ six numSix atSix (Fk X N P) i (hFit i hq) _ (h i hq).1
  · obtain ⟨i, rfl⟩ := at' q hq
    exact (h i hq).2.2.1
  · obtain ⟨i, rfl⟩ := at' q hq
    exact (h i hq).2.2.2

/-- At the first three borders the elder pins alone are open. -/
theorem pins₂_lo (k : ℕ) (hk : k ≤ 2) : pinned (open₂ k) = [0, 2] := by
  interval_cases k <;> decide

/-- **AT k ≤ 2: THE GUARDS OF ROWS 2.0 | 2.1 | 2.2**: nothing of the chain's own pins is asked. -/
theorem on₂_of_tests_lo (k : ℕ) (hk : k ≤ 2) (t0 t2 : String)
    (n0 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t0 Johnson.Top.H.shIdx 0 0 = none)
    (n2 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t2 Johnson.Top.H.shW 5 0 = none)
    (f0 : holdsB (fr₂ D) 0 (aOf Johnson.Top.H.csKey Johnson.Top.H.shIdx) = true)
    (f2 : holdsB (fr₂ D) 5 (aOf Johnson.Top.H.csKey Johnson.Top.H.shW) = true)
    (y₀ : (fr₂ D).E.Str) (z : P₂ × St₂)
    (T : Tests₂ atSix (shapeAt X) (plan₁ (oneAt X)) (oneAt X).given.plan.samples (last₁At (oneAt X))
        off₂ k z)
    (L1lo : ∀ i : Fin six.length, numSix i ∈ [0, 2] →
      ∃ o ρ y, (plan₁ (oneAt X)).orc (numSix i) = some o ∧ SeedIs Johnson.Top.H.csKey (six.get i).1
          z.1.2.d.st o ρ y)
    (r : Rec) (L2 : recOf z.1.1 = some r) (L2' : ∀ y' : (fr₂ D).E.Str, y'.1 = y₀.1 → ¬ coll (strsOf
        (fr₂ D) y') r) :
    ∃ y' : (fr₂ D).E.Str, y'.1 = y₀.1 ∧
      on₂ (Fk X N P) (fr₂ D) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (plan₁ (oneAt
          X)).orc).h₂ atSix (shapeAt X) (plan₁ (oneAt X))
        (kreadFam Johnson.Top.H.csKey six numSix atSix tab) enc rad (oneAt X).given.plan.samples
            coll (last₁At (oneAt X)) off₂ k (z, y') := by
  have e := pins₂_lo k hk
  have no : ∀ q, q ∈ pinned (open₂ k) → q < 3 := fun q hq => by
    rw [e] at hq
    have h : ∀ q ∈ [0, 2], q < 3 := by decide
    exact h q hq
  exact on₂_of_tests X N P D decT recOf tab coll enc rad off₂ k t0 t2 "" "" "" (fun _ => n0) (fun _
      => n2)
    (fun h => absurd (no 3 h) (by decide)) (fun h => absurd (no 4 h) (by decide)) (fun h => absurd
        (no 5 h) (by decide))
    (fun _ => f0) (fun _ => f2)
    (fun h => absurd (no 3 h) (by decide)) (fun h => absurd (no 4 h) (by decide)) (fun h => absurd
        (no 5 h) (by decide))
    y₀ z T (fun i hi _ => L1lo i (e ▸ hi)) (fun i hi h => absurd (no _ hi) h) r L2 L2'

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.on₂_of_tests
#print axioms Johnson.RunOne.KeyRows23.on₂_of_tests_lo
