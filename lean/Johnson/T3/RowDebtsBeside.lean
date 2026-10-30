-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/T3/RowDebtsBeside.lean: RowDebtsAt without its field on the input, so that the key file's input can
stand as one named line (SendersTestTheRange, AtFullSide/T3/TheOneTheorem.lean). This file proves zero
knowledge of nothing.
-/
import Johnson.T3.OwedOfKindsAt


set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section

namespace VerifiableInference.Compilation
open ProofFile.Honest (Prover ProverCoinCounts Sides Owed AtHonest OnlineProverWithDescription OnlineProverParts BudDebts ThreadsP OnAtRun₁ OnAtRun₂ OnAtRun₃
  silentAt runC ready Committer sealPlain rootedAll)
open VerifiableInference.Desc (FileDescription Chain)

section General
variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- **What RowDebtsAt asks beside the input.** -/
structure RowDebtsBeside (F : FileDescription Xi) (Bk : ProverCoinCounts) (G : Sides F Bk W₀ Rc Ky Tr X₀ X)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (Rel : W₀ → Rc → Xi → Prop) : Prop where
  kinds : ∀ κ, KindPays G κ
  hst : ∀ w₀ rc x, Rel w₀ rc x → ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored,
    ∀ y, y < 2 ^ t.sh.a → ∃ u, H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W
  hbud : BudDebts F Bk G
  threads : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
    ∃ T : ThreadsP F Bk (G.prover H) w₀ rc x k R, ∀ ρ r, ρ.due F = true →
      silentAt F (G.prover H) w₀ rc x ρ = none →
      runC F Bk (G.prover H) w₀ rc x k ρ = .ok r →
      (∀ L ∈ G.first, OnAtRun₁ (G := G) (H := H) T ρ r L) ∧
      (∀ L ∈ G.shared, OnAtRun₂ (G := G) (H := H) T ρ r L) ∧
      ∀ L ∈ G.second, OnAtRun₃ (G := G) (H := H) T ρ r L
  plan : F.planOk = true
  book : Bk.word F = none
  seats : G.seated = true
  plainSeal : sealPlain F = true
  rooted : rootedAll F (G.prover H) = true
  returns : ∀ w₀ rc x, Rel w₀ rc x → ∀ k, ∃ R, ready F Bk (G.prover H) w₀ rc x k = .ok R

/-- With the input it is RowDebtsAt. -/
theorem RowDebtsBeside.toAt {F : FileDescription Xi} {Bk : ProverCoinCounts} {G : Sides F Bk W₀ Rc Ky Tr X₀ X}
    {H : Prover W₀ Rc Xi Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop} (h : RowDebtsBeside F Bk G H Rel)
    (input : ∀ w₀ rc x, Rel w₀ rc x → H.inRange w₀ = true ∧ (H.trace w₀ x).isSome = true) :
    RowDebtsAt F Bk G H Rel :=
  ⟨h.kinds, input, h.hst, h.hbud, h.threads, h.plan, h.book, h.seats, h.plainSeal, h.rooted,
    h.returns⟩

end General

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.RowDebtsBeside.toAt
