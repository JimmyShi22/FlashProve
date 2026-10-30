-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineThreadsOfPays.lean: A SOCKET: a member of `ThreadsP` (Johnson/Desc/ProofFile/Honest/Law/OwedParts.lean) WHOSE
INVARIANTS ARE THE THREADS' OWN (`ThrS`, Honest/Thread/Said.lean: a thread's sentence together with what is said), from the
premises on the pairs that the rule for a file's acceptance takes too (`threadsC_ofS`, E2E/DebtsOfPairs.lean), WITHOUT
those that say yes. General in the description, the book, the prover, the three threads and their letters.

  `threadsOfPays`   the member: from `Sits`, the description's test on its plan, `OwesS` and `SaidNext` at the three threads,
                    `Enters₁`, `Enters₂`, the letters at the two starts, and `DoorBehindS` (Honest/Thread/FileD.lean)
  `threadsOfPays_first`, `_shared`, `_second`   its three families of invariants are `ThrS`: by unfolding

Why. The frame's laws on a run that has returned (`OnAtRun₁`, `OnAtRun₂`, `OnAtRun₃`, `owed_at_run`:
Honest/Law/OwedAtRun.lean) take a member of `ThreadsP` by type and hand `InsideOf` at its invariants to whoever pays On. At
the invariants of form (E2E/OfflineRunsThreads.lean) that says the form alone; at this member it says the threads' own
sentence at the called part. Beside `threadsS` (Honest/Thread/FileOwed.lean), which asks the door of the threads' sentences
and the letters apart: here the door is asked from the pair to the pair, as the rule for acceptance asks it, so that
one set of premises serves both.

What is NOT spent: `YesS`, `DoorYesS`, `FinYesS`: no sub-protocol's, door's or last test's acceptance.
Every premise is a premise: no thread is shown here to meet any of them. Nothing on any property.
-/
import E2E.DebtsOfPairs
import Johnson.Desc.ProofFile.Honest.Law.OwedParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (FileDescription)
open AtPublicFiles.KeyLink (playsS₁ playsS₂ playsS₃)

variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts} {F : FileDescription Xi}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X}
  {T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
  {T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
  {S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop}
  {S₃ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
  {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}

/-- **The threads' own invariants as a member of `ThreadsP`**, from the premises on the pairs that say no yes. -/
def threadsOfPays (hS : Sits F H T₁ T₂ T₃) (hp : F.planOk = true) (o₁ : OwesS T₁ S₁)
    (o₂ : OwesS T₂ S₂) (o₃ : OwesS T₃ S₃) (n₁ : ∀ b, SaidNext T₁ S₁ b)
    (n₂ : ∀ b, SaidNext T₂ S₂ b) (n₃ : ∀ b, SaidNext T₃ S₃ b)
    (a₁ : Enters₁ F H T₁ w₀ rc x k R) (a₂ : Enters₂ F H T₂ w₀ rc x k R)
    (e₁ : S₁ 0 k { R.start₁ H with opened := some [] })
    (e₂ : S₂ 0 k { R.start₂ H with opened := some [] })
    (a₃ : DoorBehindS F H T₁ T₂ T₃ S₁ S₂ S₃ x k R) : ThreadsP F Bk H w₀ rc x k R where
  I₁ := ThrS T₁ S₁
  I₂ := ThrS T₂ S₂
  I₃ := ThrS T₃ S₃
  h₁ := playsS₁ hS hp o₁ n₁
  h₂ := playsS₂ hS hp o₂ n₂
  h₃ := playsS₃ hS hp o₃ n₃
  a₁ := ⟨a₁, e₁⟩
  a₂ := ⟨a₂, e₂⟩
  a₃ := a₃

section
variable (hS : Sits F H T₁ T₂ T₃) (hp : F.planOk = true) (o₁ : OwesS T₁ S₁) (o₂ : OwesS T₂ S₂)
  (o₃ : OwesS T₃ S₃) (n₁ : ∀ b, SaidNext T₁ S₁ b) (n₂ : ∀ b, SaidNext T₂ S₂ b)
  (n₃ : ∀ b, SaidNext T₃ S₃ b) (a₁ : Enters₁ F H T₁ w₀ rc x k R)
  (a₂ : Enters₂ F H T₂ w₀ rc x k R) (e₁ : S₁ 0 k { R.start₁ H with opened := some [] })
  (e₂ : S₂ 0 k { R.start₂ H with opened := some [] })
  (a₃ : DoorBehindS F H T₁ T₂ T₃ S₁ S₂ S₃ x k R)

/-- Its first family of invariants. -/
theorem threadsOfPays_first :
    (threadsOfPays hS hp o₁ o₂ o₃ n₁ n₂ n₃ a₁ a₂ e₁ e₂ a₃).I₁ = ThrS T₁ S₁ := rfl

/-- Its second. -/
theorem threadsOfPays_shared :
    (threadsOfPays hS hp o₁ o₂ o₃ n₁ n₂ n₃ a₁ a₂ e₁ e₂ a₃).I₂ = ThrS T₂ S₂ := rfl

/-- Its third. -/
theorem threadsOfPays_second :
    (threadsOfPays hS hp o₁ o₂ o₃ n₁ n₂ n₃ a₁ a₂ e₁ e₂ a₃).I₃ = ThrS T₃ S₃ := rfl

end

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.threadsOfPays
#print axioms AtPublicFiles.OfflineRows.threadsOfPays_first
#print axioms AtPublicFiles.OfflineRows.threadsOfPays_shared
#print axioms AtPublicFiles.OfflineRows.threadsOfPays_second
