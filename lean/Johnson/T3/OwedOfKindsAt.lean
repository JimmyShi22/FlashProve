-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/T3/OwedOfKindsAt.lean: Owed from the kinds, general in the description.

1.  RowDebtsAt: what RowDebtsP asks, at any description, book and prover, with the six that the head
    gives online as fields by name: plan, book, seats, plainSeal, rooted and returns.
2.  owed_of_kindsAt: Owed at the muted rows from these.
3.  RowDebtsP.toAt: the online head gives the six, so RowDebtsP is a case of it.
4.  No value of any premise is given here: this file proves zero knowledge of nothing.
-/
import Johnson.T3.OwedOfKinds

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

/-- **What stays beside any description's rows**: the kinds, the threads and the six that a head gives. -/
structure RowDebtsAt (F : FileDescription Xi) (Bk : ProverCoinCounts) (G : Sides F Bk W₀ Rc Ky Tr X₀ X)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (Rel : W₀ → Rc → Xi → Prop) : Prop where
  kinds : ∀ κ, KindPays G κ
  input : ∀ w₀ rc x, Rel w₀ rc x → H.inRange w₀ = true ∧ (H.trace w₀ x).isSome = true
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

variable {F : FileDescription Xi} {Bk : ProverCoinCounts} {G : Sides F Bk W₀ Rc Ky Tr X₀ X}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop}

/-- **Owed at the muted rows from the kinds**, at any description. -/
theorem owed_of_kindsAt (debts : RowDebtsAt F Bk G H Rel) : Owed F Bk H G.mute Rel :=
  have hand₁ := fun L hL σ hσ => (debts.kinds L.place.kind).1 L hL rfl σ hσ
  have hand₂ := fun L hL σ hσ => (debts.kinds L.place.kind).2.1 L hL rfl σ hσ
  have hand₃ := fun L hL σ hσ => (debts.kinds L.place.kind).2.2 L hL rfl σ hσ
  ProofFile.Honest.owed_mute_of_threads_at_run debts.plan debts.book debts.seats debts.plainSeal debts.rooted
    hand₁ hand₂ hand₃ debts.input debts.hst debts.returns
    (fun w₀ rc x h k R hR => Classical.choose (debts.threads w₀ rc x h k R hR))
    (fun _ _ _ _ _ _ hR =>
      ProofFile.Honest.partsStand_of_hand debts.plan debts.book debts.seats hand₁ hand₂ hand₃ hR)
    debts.hbud
    (fun w₀ rc x h k R hR => Classical.choose_spec (debts.threads w₀ rc x h k R hR))

end General

section Online
variable {W₀ Rc Tr X₀ X : Type} {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
  {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {P : OnlineProverParts W₀ Rc Tr X₀ X}
  {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} {G : Sides A.F A.B W₀ Rc OnBytes.TableKey Tr X₀ X}
  {more : List (String × Bool)} {Rel : W₀ → Rc → ProofFile.Inst → Prop}

/-- **RowDebtsP is a case of it**: the online head gives the six. -/
theorem RowDebtsP.toAt (hd : AtHonest o Z D r Zp Np cF x P A G more) {Sd Xc : Type}
    (Cm : Committer W₀ Rc Sd Xc ProofFile.Inst OnBytes.TableKey) (item : Nat)
    (debts : RowDebtsP A G (Cm.proverAt item A.H) Rel) :
    RowDebtsAt A.F A.B G (Cm.proverAt item A.H) Rel :=
  ⟨debts.kinds, debts.input, debts.hst, debts.hbud, debts.threads, hd.plan, hd.book, hd.seats, hd.seal,
    hd.rooted, ready_of_head hd Cm item debts.input⟩

end Online

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.RowDebtsAt
#print axioms VerifiableInference.Compilation.owed_of_kindsAt
#print axioms VerifiableInference.Compilation.RowDebtsP.toAt
