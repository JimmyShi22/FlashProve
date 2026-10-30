-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/BatchDoorProofs.lean: the proofs of Run/BatchDoor.lean: the generic protocol, as the Batch
protocol of an interface, meets formal side conditions of the library's compilation theorems (the
record `Met`: `metB`), under the hypotheses of its statements. (`metB`: states, under two hypotheses
on Batch's wiring, `Met` with the generic construction's protocol as Batch: Run/BatchDoor.lean.
`Met`: a record of twelve conditions on an interface and its wiring, listed in Run/M1Door.lean's
head.)

The law on verifier messages at constant state functions is proved by induction on the shape. All
else goes clause by clause, as in Run/M1Door.lean. The last field of the record is `bcsSoundBatchG`
of Compile/Batch/Sound.lean.

Main names (statements and hypotheses: Run/BatchDoor.lean):
  `joint_true`: the law on verifier messages at state functions that are constantly 1.
  `lb_sound`: `Sound` of `Lb B` at the relation "everything", with error 0. True and empty (Limits,
    below).
  `okgWb`: the laws of the whole wiring `Wb K wB`.
  `metB`: the record `Met` at `LbS C ds dec` and `Wb K wB`.

Notation:
  `LbS`: the interface whose Batch is the protocol of `PSof` (Run/PlanQS.lean);
  `Lb B`: the interface with a given batch `B` (Run/PlanQS.lean);
  `zErr s`: the list of errors 0 (Run/M1Door.lean);
  _N, _M at the end of a name: Run/M1RunTieTheirs.lean's descriptions, N at tiny, M at full
    parameters;
  _T, _R, _F at the end of a name: Run/M1RunTiePF.lean's descriptions, T and R at tiny, F at full
    parameters.

Limits: the conditions with content are not met. `lb_sound` is true and empty. At the relation
"everything" (`All`, Run/M1Door.lean: every instance is in the relation) every string decodes too,
so no statement lies outside Batch's language. There the state function that is constantly 1 serves,
and nothing is asked of any round. No statement on soundness follows. The library's clause on an
accepted Batch string is "the external string does not decode, or the instance is in the relation".
At "everything" this is true of everything. What is not claimed is told in the head of
Run/BatchDoor.lean, under 4.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.BatchDoor

set_option autoImplicit false

namespace Run.BatchDoor
open Iop Rom Compile Compile.Batch Prob Run.PQ Run.M1Door
open scoped ENNReal

theorem joint_true' (N : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (Sf : Fin N → Option (PTr s → Bool)),
      (∀ j S, Sf j = some S → ∀ τ, S τ = true) → JointLaw N s A (zErr s) Sf
  | [], _, _, _ => trivial
  | r :: s, (a, A), Sf, h => by
      obtain ⟨k, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
      intro m0 m
      refine ⟨?_, fun v => joint_true' N s A _ ?_⟩
      · cases k with
        | lo =>
            intro j S hS hf
            rw [h j S hS] at hf
            cases hf
        | sh =>
            refine le_of_eq (cnt_false fun c hc => ?_)
            obtain ⟨j, S, hS, hf, -⟩ := hc
            rw [h j S hS] at hf
            cases hf
      · intro j S' hS' τ
        cases hj : Sf j with
        | none => rw [hj] at hS'; cases hS'
        | some S =>
            rw [hj] at hS'
            cases hS'
            exact h j S hj _

theorem joint_true : Spec.joint_true := joint_true'

theorem lb_sound : Spec.lb_sound := fun B =>
  { sndT := ⟨(), trivial,
      fun _ _ h => absurd (fun e : (some () : Option Unit) = none => by cases e) h⟩
    sndL := ⟨(), trivial, fun _ _ h => absurd (Or.inr rfl) h⟩
    sndB := by
      have lang : ∀ _ : Fin 0 → Unit,
          (some () : Option Unit) = none ∨ ∃ i, (some () : Option Unit) = some i ∧ All i () :=
        fun _ => Or.inr ⟨(), rfl, trivial⟩
      refine ⟨zErr _, zErr_below _ _, fun n h => ?_, fun _ _ _ => true, ?_, ?_, ?_, ?_, ?_⟩
      · exact absurd h (by show (none : Option ℕ) ≠ some n; exact fun e => by cases e)
      · intro y x h
        exact absurd (lang y) h
      · intro y x τ m h
        cases h
      · intro y x τ h
        exact absurd (lang y) h
      · intro y x τ h
        exact absurd (lang y) h
      · intro y x
        refine joint_true 1 _ _ _ fun j S hS τ => ?_
        cases hx : x j with
        | none => rw [hx] at hS; cases hS
        | some u =>
            rw [hx] at hS
            cases hS
            rfl }

theorem okgWb : Spec.okgWb := fun B K wB h he =>
  { T := { sh := trivial, ext := we0_ok, opens := fun _ _ _ => le_refl 0, depth := trivial }
    Lk := { sh := trivial, ext := weL_ok, opens := fun _ _ _ => le_refl 0, depth := trivial }
    B := h
    fits := Nat.zero_le _
    slots := rfl
    extDepth := ⟨rfl, rfl, by show wB.ext.depth = 0; rw [he]; rfl⟩
    depthT := le_refl 0, depthL := le_refl 0, depthB := Nat.zero_le _
    extT := fun p => p.elim0
    extB := fun p => p.elim0
    extL := ⟨fun p => p.elim0, fun p => p.elim0⟩ }

theorem lbs_reads (C : CK) (ds : List RD) (dec : View → Bool) : (LbS C ds dec).Reads 0 0 0 0 0 where
  cntT := fun _ _ => le_refl 0
  cntLp := fun _ _ => le_refl 0
  cntLc := fun _ _ => le_refl 0
  cntB := fun x _ => by
    simp only [BatchInteractiveOracleProof.allReads]
    simp
    cases x 0 <;> rfl
  hidE := fun _ _ _ _ => rfl

theorem metB : Spec.metB := fun C ds dec K wB h he =>
  { okg := okgWb _ K wB h he
    wired := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩
    reads := lbs_reads C ds dec
    localT := fun _ _ _ _ _ _ _ _ _ => rfl
    localL := fun _ _ _ _ _ _ _ _ _ => rfl
    localB := psof_local C ds dec
    cohB := BatchOne.BAnn.allLocal_coherent _
    pointT := ⟨()⟩
    pointL := ⟨()⟩
    pointB := lts_pointT C ds dec
    sound := lb_sound _
    low := bcsSoundBatchG Unit Unit 256 _ (Wb K wB) All 0 (lb_sound _)
      (fun _ _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ _ => rfl) (psof_local C ds dec)
      (BatchOne.BAnn.allLocal_coherent _) (okgWb _ K wB h he) }

theorem metB_N : Spec.metB_N := metB _ _ _ _ M1RunTieTheirs.WN.T M1RunTieTheirs.met_N.okg.T rfl
theorem metB_M : Spec.metB_M := metB _ _ _ _ M1RunTieTheirs.WM.T M1RunTieTheirs.met_M.okg.T rfl
theorem metBF_T : Spec.metBF_T := metB _ _ _ _ M1RunTiePF.WT.T M1RunTiePF.okgPF_T rfl
theorem metBF_R : Spec.metBF_R := metB _ _ _ _ M1RunTiePF.WR.T M1RunTiePF.okgPF_R rfl
theorem metBF_F : Spec.metBF_F := metB _ _ _ _ M1RunTiePF.WF.T M1RunTiePF.okgPF_F rfl

end Run.BatchDoor
