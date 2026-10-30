-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WTreesSentBeforeTest.lean: the clause `old` of `StandAtW` (WAccepted.lean): the
trees that the last chain's test opens and has not sent are in hand at the declared widths; the law
that takes two blocks of a fold apart.

  `wideLast`       the declared width of each tree taken over
  `oldLineB`, `old_line`, `old_line_bent`   a closed line on the written place: every opening of a
                   tree that is not the test's own names one of the three sources, at its width;
                   one width changed: no
  `old_at_W`       the clause, at every stand whose table has these widths
  `fold_two`       two blocks behind one another: each one's yes

Limits.
- hw is a premise on the thread's table. `lastTable` (LastTerm.lean) reads it off the two earlier
  threads' tables.
- NOT IN FRONT OF A LAW OVER COINS: `old_at_W` stands behind `Thr`.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFive

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open OnBytes
open VerifiableInference.Desc (Block OpenedColumn foldBlocks foldBlocks_cons step_inv)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open H2K.Member (piWFull)
open ProofFile.Honest.K12.AtProof (fourOf)

/-- The declared width of a tree taken over. -/
def wideLast : Fmt.TreeSource → ℕ
  | .taken 0 1 => 3
  | .taken 0 82 => 12
  | .taken 1 1 => 36
  | _ => 0

/-- Every opening of a tree that is not the test's own names a source taken over, at its width. -/
def oldLineB (w : Fmt.TreeSource → ℕ) (ds : List Fmt.DeclaredRound) : Bool :=
  ds.all fun d => d.opens.all fun o =>
    match o.2 with
    | .own _ => true
    | .taken a b => decide (Fmt.TreeSource.taken a b ∈ takenLast) &&
        decide (o.1.W = w (.taken a b))

-- THE LINE. Foretold: yes.
#guard oldLineB wideLast (proximityTestKind guardedProximityTestParts piWFull : Block T12 Unit).rounds

-- CONTROL. Foretold: no.
#guard !oldLineB (fun σ => wideLast σ + 1) (proximityTestKind guardedProximityTestParts piWFull : Block T12 Unit).rounds

theorem old_line : oldLineB wideLast (proximityTestKind guardedProximityTestParts piWFull : Block T12 Unit).rounds = true := by
  decide +kernel

theorem old_line_bent :
    oldLineB (fun σ => wideLast σ + 1) (proximityTestKind guardedProximityTestParts piWFull : Block T12 Unit).rounds = false := by
  decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **The clause `old`.** -/
theorem old_at_W (h : P5J.AtMg o Z D r Zp Np cF) (T : Thread Bk S Cl V W X Pb) {b : ℕ}
    (ht : T.taken = takenLast) (hsent : treesTo T.bs b = 0)
    (hw : ∀ σ ∈ takenLast, ∀ k w hd, (T.table σ k w hd).2.words = wideLast σ)
    {k : Coins Bk} {s : S} {m : Mid W X} {E : Env} (u : Thr T b k s m E) :
    ∀ d ∈ (proximityTestKind guardedProximityTestParts (fourOf Np).W : Block T12 Unit).rounds, ∀ q ∈ d.opens,
      oldSrc E.sent q.2 = true → ∃ pt, E.tree q.2 = some pt ∧ pt.2.words = q.1.W := by
  refine old_of_hand T _ (fun d hd q hq hO => ?_) u
  rw [rounds_head_W h] at hd
  have a2 := List.all_eq_true.1 (List.all_eq_true.1 old_line d hd) q hq
  rw [hsent] at hO
  cases hσ : q.2 with
  | own n =>
    rw [hσ] at hO
    simp [oldSrc] at hO
  | taken a c =>
    rw [hσ] at a2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at a2
    refine ⟨?_, fun k' w' h' => ?_⟩
    · show _ ∈ T.taken ++ _
      rw [ht]
      exact List.mem_append_left _ a2.1
    · rw [hw _ a2.1]
      exact a2.2.symm

/-- **Two blocks behind one another: each one's yes.** -/
theorem fold_two (ft : ℕ) (a b : Block S Cl) (s₀ s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (h : foldBlocks ft [a, b] s₀ rs cols = .ok (s, [], [])) :
    ∃ s₁ r₁ g₁ r₂ g₂, a.decide s₀ r₁ g₁ = .ok s₁ ∧ b.decide s₁ r₂ g₂ = .ok s := by
  obtain ⟨s₁, k, -, h1, h⟩ := foldBlocks_cons ft a [b] s₀ rs cols _ h
  obtain ⟨s₂, k', -, h2, h⟩ := foldBlocks_cons ft b [] s₁ _ _ _ h
  have e : s₂ = s := congrArg (·.1) (Except.ok.inj h)
  subst e
  exact ⟨s₁, _, _, _, _, (step_inv _ _ _ _ _ _ _ h1).2.2.2, (step_inv _ _ _ _ _ _ _ h2).2.2.2⟩

end

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.wideLast
#print axioms ProofFile.Honest.K12.AtFile.oldLineB
#print axioms ProofFile.Honest.K12.AtFile.old_line
#print axioms ProofFile.Honest.K12.AtFile.old_line_bent
#print axioms ProofFile.Honest.K12.AtFile.old_at_W
#print axioms ProofFile.Honest.K12.AtFile.fold_two
