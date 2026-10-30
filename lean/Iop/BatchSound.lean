-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchSound.lean: a fact on (Snd-B), `BatchInteractiveOracleProof.SndB` of Iop/Batch.lean: a shared round's joint
error is at most N times one slot's. (Words of this library: lean/GLOSSARY.md.) In a protocol with N
slots an annotation says for each round whether its challenge is shared by all slots or local to
each.
`BatchH4.jointLaw_of_verLaw`: if the state function of every non-empty slot satisfies the condition
on challenges, `VerLaw`, with the errors ε, then the condition on challenges for all slots,
`JointLaw`, holds, for every annotation and every N, with the errors of the shared rounds multiplied
by N (`Err.timesShared`).

Notation: `St : Fin N → Option (PTr s → Bool)` in `JointLaw` (Iop/Batch.lean): St j is the state
function of slot j on what is left of the protocol (none: the slot is empty); `Kind`
(Iop/Batch.lean): a round is called shared (`sh`) or local (`lo`) after its verifier message;
`BRho N s A : Type` (Iop/Batch.lean): the verifier's randomness of a whole execution of the batch: ρ
= (ρ_0, ρ_1, .., ρ_N); `cnt P : ℕ` (Prob/Cnt.lean): the number of elements of a finite type with the
property P; `PTr s : Type` (Iop/State.lean): partial transcripts: at the prover (`atP`), at the
verifier (`atV`), or full (`full`); `AtP s`, `AtV s : Type` (Iop/State.lean): transcripts at the
prover; transcripts at the verifier.

Limits: this file does not prove the form of this fact with "a slot that the prover names", nor that
every annotation of a round-by-round sound IOP has (Snd-B).
Helpers: namespace `Iop.BatchH4`.
-/
import Iop.Batch

namespace Iop
open Prob
open scoped ENNReal


namespace BatchH4

/-- "A prover message never changes 0 to 1", for a state function S on the remaining rounds. -/
def ProverLaw (s : Shape) (S : PTr s → Bool) : Prop :=
  ∀ (τ : AtP s) (m : τ.round.Msg), S (.atP τ) = false → S (.atV (τ.snoc m)) = false

theorem ProverLaw.tail {r : Round} {s : Shape} {S : PTr (r :: s) → Bool} (h : ProverLaw (r :: s) S)
    (m : r.Msg) (c : r.Chal) :
    ProverLaw s fun τ => S (PTr.cons m c τ) :=
  fun τ m' h0 => h (Sum.inr (m, c, τ)) m' h0

theorem unif_cons (N : ℕ) (r : Round) (s : Shape) (a : RAnn r) (A : RoundSplits s) :
    unif (BRho N (r :: s) (a, A)) = Prob.prod (unif (a.kind.All N r.Chal)) (unif (BRho N s A)) :=
  unif_prod


end BatchH4

variable {X : Type} {E : ExtSpec}

/-! ## The joint error is at most N times the error for a single slot -/

/-- The errors of the shared rounds multiplied by N. -/
def Err.timesShared (N : ℕ) : {s : Shape} → RoundSplits s → Err s → Err s
  | [], _, _ => ()
  | _ :: _, (a, A), (e, ε) => ((match a.kind with | .lo => e | .sh => N * e), Err.timesShared N A ε)

namespace BatchH4

/-- The condition on challenges: from state 0, at most as many challenge values as the round's error
count lead to state 1; for a state function on the remaining rounds. -/
def VerLaw (s : Shape) (ε : Err s) (S : PTr s → Bool) : Prop :=
  ∀ τ : AtV s, S (.atV τ) = false → cnt (fun c : τ.round.Chal => S (τ.snoc c) = true) ≤ τ.err ε

theorem jointLaw_of_verLaw (N : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (ε : Err s) (St : Fin N → Option (PTr s → Bool)),
      (∀ j S, St j = some S → VerLaw s ε S) → JointLaw N s A (Err.timesShared N A ε) St
  | [], _, _, _, _ => trivial
  | r :: s, (a, A), (e, ε), St, h => by
      intro m0 m
      refine ⟨?_, fun v => jointLaw_of_verLaw N s A ε _ ?_⟩
      · obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pl, own⟩ := a
        cases k
        · show cnt _ ≤ N * e
          have := cnt_exists_le_mul (C := r.Chal) (ι := Fin N) (fun j c => ∃ S, St j = some S ∧
            S (.atV (Sum.inl (sp.symm (m0, m j)))) = false ∧ S (PTr.cons (sp.symm (m0, m j)) c (PTr.empty s)) = true) e
            (by
              intro j
              cases hS : St j with
              | none =>
                rw [cnt_false]
                · exact Nat.zero_le _
                · rintro c ⟨S, hS', -⟩
                  rw [hS] at hS'
                  cases hS'
              | some S =>
                by_cases h0 : S (.atV (Sum.inl (sp.symm (m0, m j)))) = false
                · refine le_trans (cnt_mono ?_) (h j S hS (Sum.inl (sp.symm (m0, m j))) h0)
                  rintro c ⟨S', hS', -, h1⟩
                  obtain rfl : S = S' := Option.some.inj (hS.symm.trans hS')
                  exact h1
                · rw [cnt_false]
                  · exact Nat.zero_le _
                  · rintro c ⟨S', hS', h0', -⟩
                    obtain rfl : S = S' := Option.some.inj (hS.symm.trans hS')
                    exact h0 h0')
          rw [Fintype.card_fin] at this
          exact this
        · intro j S hS h0
          exact h j S hS (Sum.inl (sp.symm (m0, m j))) h0
      · intro j S' hS'
        cases hS : St j with
        | none => rw [hS] at hS'; cases hS'
        | some S =>
          rw [hS] at hS'
          obtain rfl := Option.some.inj hS'
          exact fun τ h0 => h j S hS (Sum.inr (_, _, τ)) h0

end BatchH4

end Iop
