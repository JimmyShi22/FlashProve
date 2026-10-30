-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/KnowBindingUp.lean: index binding with a witness extractor, from the base scheme up to the
scheme with the links in the key.

This file is about index binding, the soundness notion of a commit-and-prove argument, with a
witness extractor: it is carried from one form of the compiled scheme to another.
Statement and proof; an assembly, no mathematics.
The compiler's base scheme with batches, `argB`, carries the link in every proof. The scheme of the
top theorem, `argBKE`, has the links in the verification key, proofs without the two fields of a
link, and a prover that does no work for empty slots.
For languages the way from the one to the other is that of the proof of `bindingKEGr`
(Compile/Batch/MainKEGr.lean). Here is the same way in the syntax with witnesses, for any witness
map and any bound.

Main names:
  `Spec.bindingUp`: index binding of `withW Wn (argB W WP p)` with the extractor
    `extractorBW W wit w0` and the bound ε gives index binding of `withW Wn (argBKE W WP p)` with
    `extractorBKW W wit w0` and the same ε.

Why no cost: the cheating committer hands the links to its prover, which writes them back into its
proof; neither asks a query more. Index binding reads a scheme only through its verifier, so the
changed prover does not matter.

Limits: it is an implication. This file says nothing on the base scheme itself
(CompileK/KnowBinding.lean). It says nothing on completeness or privacy.

Terms: lean/GLOSSARY.md.
-/
import CompileK.KnowExt
import CompileK.GenWitProofs
import Compile.Batch.StarKE

set_option autoImplicit false

noncomputable section

namespace Compile.GenMap
open Rom ZKCP ZKCP.Gen

variable {S : OSpec} {I X IVK ISK ISK' Pf Pf' : Type}

/-- Reading a scheme through maps on proving keys and proofs is kept when both schemes are put into
the syntax with witnesses. -/
theorem via_withW (Wn : Type) {A : Arg S I X Unit IVK ISK Pf} {A' : Arg S I X Unit IVK ISK' Pf'}
    {φ : ISK' → ISK} {τ : Pf → Pf'} (h : Via A A' φ τ) :
    Via (withW Wn A) (withW Wn A') φ τ where
  C := h.C
  P := fun k b => by
    show ((A'.P k (forgetW b)).bind fun l =>
        OComp.pure (⟨l.val, l.property.trans (List.length_map _)⟩ : Slots Pf' b)) =
      ((A.P (φ k) (forgetW b)).bind fun l =>
          OComp.pure (⟨l.val, l.property.trans (List.length_map _)⟩ : Slots Pf b)).bind
        fun l => .pure (mapS τ l)
    rw [h.P, OComp.bind_assoc, OComp.bind_assoc]
    rfl
  V := h.V

end Compile.GenMap

namespace Compile.GenPub
open Rom ZKCP ZKCP.Gen

variable {S : OSpec} {I X IVK ISK Pf Λ : Type}

/-- Publishing a datum in the key commutes with the passage to the syntax with witnesses. -/
theorem pubArg_withW (Wn : Type) (A : Arg S I X Unit IVK ISK Pf) (u : Pub IVK ISK Pf Λ) :
    pubArg (withW Wn A) u = withW Wn (pubArg A u) := rfl

end Compile.GenPub

namespace Compile.Batch
open Iop Rom ZKCP Compile.GenMap Compile.GenPub
open scoped ENNReal

namespace Spec

/-- States: index binding with a witness extractor goes up from the base scheme to the scheme with
the links in the key, at the same bound. -/
def bindingUp : Prop :=
  ∀ (I X Wn PP : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L)
      (p : Params) (R : Gen.RelPair I X Wn PP) (wit : X → Orcs L.onlineBatch.loc.shape → Wn)
      (w0 : Wn) (ε : ℕ → ℕ → ℝ≥0∞),
    Gen.HasIndexBindingWith R (Gen.withW Wn (argB W WP p)) (extractorBW W wit w0) ε →
    Gen.HasIndexBindingWith R (Gen.withW Wn (argBKE W WP p)) (extractorBKW W wit w0) ε

end Spec

/-- The scheme with free empty slots has the verifier of the scheme with the links in the key. -/
theorem V_KE {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params) :
    (argBKE W WP p).V = (argBK W WP p).V := rfl

theorem bindingUp : Spec.bindingUp := by
  intro I X Wn PP lam L W WP p R wit w0 ε hb
  have h1 := GenPub.binding (A := Gen.withW Wn (argB W WP p)) pubK R hb
  rw [pubArg_withW] at h1
  have h2 := GenMap.binding (via_withW Wn (via_K W WP p)) stripK_liftK R h1
  unfold extractorBKW
  exact Gen.binding_congr_V R (A := Gen.withW Wn (argBK W WP p))
    (A' := Gen.withW Wn (argBKE W WP p))
    (fun v x π => congrFun (congrFun (congrFun (V_KE W WP p).symm v) x) π) h2

end Compile.Batch
