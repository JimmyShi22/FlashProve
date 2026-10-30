-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/KeyOfData.lean: at the data that a description's declared rounds give
(`FileDescription.data`, Johnson/Desc/BlockSlot.lean), a tree of the first chain stands, in the first
chain's view, under its own number; so each tree below the first chain's number of trees is the
first of all the file's trees with its key: the premise hFirst of `colsOf_first`
(ColsAtStageFirst.lean) at the frame that the rule of composition has for a file's first chain.
Statements and proofs; no definition.

  `data_parts`     what `FileDescription.data`'s yes holds: the written rounds, and the makers' tests' yes
  `key_of_data`    ∀ j < D.t₁, D.key₁ j = j
  `t₁_le_all`      D.t₁ ≤ nAll D
  `first_of_data`  THE STATEMENT, at the stage ⟨a, base, allOf D, ds, D.key₁, allOf D⟩, base ≤ D.t₁
  `keys_meet_data` where the first two chains each send a tree, tree 0 and tree D.t₁ have one key
                   there: the keys of `allOf D` are not apart
Limits. Nothing says of which description a file's data are. `WholeD.at` turns the depth alone, so
all of this holds of `D.at a` too (`first_of_data_at`). No soundness is claimed.

-/
import Johnson.Top.H0.K2Hears.KeyOfFits
import Johnson.Top.H0.K2Hears.FirstAtFrame
import Johnson.Desc.BlockSlot
import Johnson.EntryRec.OkcFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Maker
open OnBytes.Params (Rounds)
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Sound (allOf nAll)

variable {Xi : Type}

/-- What `FileDescription.data`'s yes holds. -/
theorem data_parts {F : FileDescription Xi} {file : String} {D : WholeD} (h : F.data file = .ok D) :
    ∃ R : Rounds × Rounds × Rounds, okAt F.tableDepth (some R) = true ∧
      D = WholeD.of F.tableDepth (Three.Whole.of R.1 R.2.1 R.2.2) := by
  unfold FileDescription.data at h
  cases hR : Johnson.G.OfPlan.writtenOf file F.roundsDeclaredByBlocks with
  | error e =>
    rw [hR] at h
    cases h
  | ok R =>
    rw [hR] at h
    by_cases hk : okAt F.tableDepth (some R) = true
    · refine ⟨R, hk, ?_⟩
      simp only [hk, bind, Except.bind, pure, Except.pure] at h
      exact (Except.ok.inj h).symm
    · simp only [hk, bind, Except.bind, pure, Except.pure] at h
      cases h

/-- **A tree of the first chain stands under its own number.** -/
theorem key_of_data {F : FileDescription Xi} {file : String} {D : WholeD} (h : F.data file = .ok D) :
    ∀ j, j < D.t₁ → D.key₁ j = j := by
  obtain ⟨R, hk, rfl⟩ := data_parts h
  have P := okAt_parts hk
  have hc : (WholeD.of F.tableDepth (Three.Whole.of R.1 R.2.1 R.2.2)).t₁ = Three.rootsIn R.1 := by
    have := P.counts
    unfold countsFit at this
    rw [Bool.and_eq_true] at this
    exact eq_of_beq this.1
  intro j hj
  rw [hc] at hj
  exact key_first P.fits j hj

theorem t₁_le_all (D : WholeD) : D.t₁ ≤ nAll D := by
  unfold nAll
  omega

/-- **hFirst at the frame of a file's first chain.** -/
theorem first_of_data {F : FileDescription Xi} {file : String} {D : WholeD} (h : F.data file = .ok D)
    (a base : Nat) (ds : List RDT) (hb : base ≤ D.t₁) :
    ∀ j, j < (⟨a, base, allOf D, ds, D.key₁, allOf D⟩ : StageD).base →
      ((⟨a, base, allOf D, ds, D.key₁, allOf D⟩ : StageD).Lin.find? fun L =>
        (⟨a, base, allOf D, ds, D.key₁, allOf D⟩ : StageD).key L.no ==
          (⟨a, base, allOf D, ds, D.key₁, allOf D⟩ : StageD).key j).map (·.no) = some j :=
  first_at_stage D a base ds D.t₁ hb (t₁_le_all D) (key_of_data h)

/-- The same at the data with another depth of the stored table laid. -/
theorem first_of_data_at {F : FileDescription Xi} {file : String} {D : WholeD} (h : F.data file = .ok D)
    (a' a base : Nat) (ds : List RDT) (hb : base ≤ D.t₁) :
    ∀ j, j < (⟨a, base, allOf (D.at a'), ds, (D.at a').key₁, allOf (D.at a')⟩ : StageD).base →
      ((⟨a, base, allOf (D.at a'), ds, (D.at a').key₁, allOf (D.at a')⟩ : StageD).Lin.find? fun L =>
        (⟨a, base, allOf (D.at a'), ds, (D.at a').key₁, allOf (D.at a')⟩ : StageD).key L.no ==
          (⟨a, base, allOf (D.at a'), ds, (D.at a').key₁, allOf (D.at a')⟩ : StageD).key j).map
            (·.no) = some j :=
  first_at_stage (D.at a') a base ds D.t₁ hb (t₁_le_all (D.at a')) (key_of_data h)

/-- **Where the first two chains each send a tree, the keys of all the file's trees are not
apart.** -/
theorem keys_meet_data {F : FileDescription Xi} {file : String} {D : WholeD} (h : F.data file = .ok D)
    (h1 : 0 < D.t₁) (h2 : 0 < D.t₂) : D.key₁ 0 = D.key₁ D.t₁ ∧ 0 ≠ D.t₁ := by
  obtain ⟨R, hk, rfl⟩ := data_parts h
  have P := okAt_parts hk
  have hc := P.counts
  unfold countsFit at hc
  rw [Bool.and_eq_true] at hc
  have c1 : (WholeD.of F.tableDepth (Three.Whole.of R.1 R.2.1 R.2.2)).t₁ = Three.rootsIn R.1 :=
    eq_of_beq hc.1
  have c2 : (WholeD.of F.tableDepth (Three.Whole.of R.1 R.2.1 R.2.2)).t₂ = Three.rootsIn R.2.1 :=
    eq_of_beq hc.2
  rw [c1] at h1 ⊢
  rw [c2] at h2
  exact keys_meet P.fits h1 h2

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.data_parts
#print axioms VerifiableInference.Desc.First.K2.key_of_data
#print axioms VerifiableInference.Desc.First.K2.first_of_data
#print axioms VerifiableInference.Desc.First.K2.first_of_data_at
#print axioms VerifiableInference.Desc.First.K2.keys_meet_data
