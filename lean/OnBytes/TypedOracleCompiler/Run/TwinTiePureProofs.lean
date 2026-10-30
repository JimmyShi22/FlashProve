-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/TwinTiePureProofs.lean.
Run/TwinTiePureProofs.lean: the proofs of the statements of Run/TwinTiePure.lean: each by recursion
on the list of skeleton rounds; a step unfolds both sides once.

Terms: lean/GLOSSARY.md.

-/
import Run.TwinTiePureProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDefs
import OnBytes.TypedOracleCompiler.Run.TwinTiePure

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Twin
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.Twin

theorem effPlainT_eq : Spec.effPlainT_eq := fun _ _ _ _ _ => rfl

theorem effPlainsT_eq : Spec.effPlainsT_eq := by
  intro lam S
  induction S with
  | nil => intro _ _ _; rfl
  | cons r S ih =>
    rintro ⟨a, A⟩ ⟨rt, rts⟩ ⟨pl, pls⟩
    show (effPlainT r a rt pl, effPlainsT S A rts pls) =
      (effPlain (r := r.up) a rt pl, effPlains (up S) A rts pls)
    rw [ih]
    rfl

theorem mkTrT_eq : Spec.mkTrT_eq := by
  intro lam K S
  induction S with
  | nil => intro _ _ _ _ _ _; rfl
  | cons r S ih =>
    rintro ⟨a, A⟩ ⟨w, W⟩ ⟨rt, rts⟩ ⟨pl, pls⟩ ⟨c, ρ⟩ f
    simp only [mkTrT, TypedOracleCompiler.Compile.Batch.mkTr, ih]
    refine Prod.ext (Prod.ext (congrArg w.pt.ofSyms (funext fun p => ?_)) rfl) rfl
    generalize rootAt w rt p = b
    generalize f (.inl p) = o
    cases b <;> cases o <;> rfl

theorem countT_eq : Spec.countT_eq := by
  intro lam S
  induction S with
  | nil => intro _; rfl
  | cons r S ih =>
    rintro ⟨rt, rts⟩
    simp only [countT, RootsOfChain.count, ih]

theorem strictST_eq : Spec.strictST_eq := by
  intro lam K sMT S
  induction S with
  | nil => intro _ _ _ _ _; rfl
  | cons r S ih =>
    rintro ⟨a, A⟩ ⟨w, W⟩ ⟨rt, rts⟩ isRead f
    simp only [strictST, strictSB, ih]

theorem forestsT_eq : Spec.forestsT_eq := by
  intro I X lam K L S
  induction S with
  | nil => intro _ _ _ _ _ _; rfl
  | cons r S ih =>
    rintro ⟨a, A⟩ ⟨w, W⟩ emb ⟨rt, rts⟩ isRead f
    simp only [forestsT, forestsB, ih]
    generalize checksTrees w.posAt0 (fun p => emb (.inl p))
        (fun p => isRead (.inl p)) (fun p => f (.inl p)) 0 w.depth0 (rt.1.getD []) = x
    generalize checksTrees w.posAtJ (fun p => emb (.inl p))
        (fun p => isRead (.inl p)) (fun p => f (.inl p)) 0 w.depthJ (rt.2.getD []) = y
    generalize forestsB (up S) A W (fun p => emb (.inr p)) rts
        (fun p => isRead (.inr p)) (fun p => f (.inr p)) = z
    cases x <;> cases y <;> cases z <;> rfl

end TypedOracleCompiler.Run.Twin
