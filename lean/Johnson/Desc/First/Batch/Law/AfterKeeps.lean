-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/AfterKeeps.lean
(kind K9's soundness lemma): THEOREMS: what the law of a whole segment asks of a
run behind the batching (Johnson/Desc/LinkLaw2.lean: the clause of LinkSem.AfterKeeps), at the
meaning semOf (Law/BatchAdds.lean), for a run that keeps the ledger's core.
  afterKeeps_of_core   for ANY run r of which it is known that, where it returns, the ledger behind
                       has the core (Law/Stages.lean: the sums, chi, the count of claims, the plan's
                       number) of the ledger in front: behind stays; the state behind is later; and
                       the one equation's value, read at any later state, is unturned.
  coefRun              the step coefficientsP (it sets the virtual rows' weights), lifted through
                       K9's lens; which tail it reads is a letter.
  afterKeeps_coefRun   the clause at that run.
The hypotheses are on the lens and on the other kinds' letters alone.

-/
import Johnson.Desc.First.Batch.Law.BatchAdds
import Johnson.Desc.First.Batch.Law.Layout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Lens)
open VerifiableInference.Desc.First.TailClaims (coefficientsP)

variable {T P K : Type} [Field K]

/-- **A run that keeps the ledger's core meets the clause of AfterKeeps.** -/
theorem afterKeeps_of_core (ρ : Reading K) (X : Lens T) (O : Others T P K)
    (r : T → Except String T)
    (hr : ∀ s s', r s = .ok s' →
      ∃ a a', X.get? s = some a ∧ X.get? s' = some a' ∧ core a'.F = core a.F)
    (hO : ∀ s s', O.behind s → r s = .ok s' → O.behind s' ∧ O.more s s') :
    ∀ s s', (semOf ρ X O).behind s → r s = .ok s' →
      (semOf ρ X O).behind s' ∧ (semOf ρ X O).later s s' ∧
        ∀ t y, (semOf ρ X O).later s' t →
          (semOf ρ X O).one t s' y = (semOf ρ X O).one t s y := by
  intro s s' hb hs
  obtain ⟨a, a', ha, ha', hc⟩ := hr s s' hs
  obtain ⟨o1, o2⟩ := hO s s' hb hs
  have hp : a'.F.planClaimsF = a.F.planClaimsF := congrArg (fun x => x.2.2.2) hc
  refine ⟨o1, ⟨?_, o2⟩, fun t y _ => oneK_of_core X ρ s s' a a' ha ha' hc t y⟩
  simp only [planOf, ha, ha', Option.map_some, hp]

/-- The step that sets the virtual rows' weights, through K9's lens. tailOf: which tail it reads. -/
def coefRun (X : Lens T) (tailOf : T → HTailF2) : T → Except String T := fun s => do
  let a ← X.part s
  let G ← coefficientsP (tailOf s) a.F
  pure (X.set s { a with F := G })

/-- **The clause of AfterKeeps at that run.** -/
theorem afterKeeps_coefRun (ρ : Reading K) (X : Lens T) (O : Others T P K)
    (tailOf : T → HTailF2)
    (lens : ∀ s a, (X.get? s).isSome = true → ∃ a', X.get? (X.set s a) = some a' ∧ a'.F = a.F)
    (hO : ∀ s s', O.behind s → coefRun X tailOf s = .ok s' → O.behind s' ∧ O.more s s') :
    ∀ s s', (semOf ρ X O).behind s → coefRun X tailOf s = .ok s' →
      (semOf ρ X O).behind s' ∧ (semOf ρ X O).later s s' ∧
        ∀ t y, (semOf ρ X O).later s' t →
          (semOf ρ X O).one t s' y = (semOf ρ X O).one t s y := by
  refine afterKeeps_of_core ρ X O (coefRun X tailOf) (fun s s' hs => ?_) hO
  unfold coefRun at hs
  obtain ⟨a, ha, hs⟩ := ok_bind hs
  obtain ⟨G, hG, hs⟩ := ok_bind hs
  have ha' := there_ok ha
  have e : X.set s { a with F := G } = s' := Except.ok.inj hs
  obtain ⟨a', h1, h2⟩ := lens s { a with F := G } (by simp [ha'])
  refine ⟨a, a', ha', by rw [← e]; exact h1, ?_⟩
  have h2' : a'.F = G := h2
  rw [h2']
  exact coefficientsP_core _ _ _ hG

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.afterKeeps_of_core
#print axioms VerifiableInference.Desc.K9L.afterKeeps_coefRun
