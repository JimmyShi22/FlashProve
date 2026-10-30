-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Law/CountF.lean: HOW MANY HASH CALLS THE COMPILED PROVER ASKS AT MOST, ON EVERY PATH,
WHERE A TRY ASKS ITS FIRST BLOCK FIRST (Rom/OverOneF.lean): the numbers.

Main names.
  `fsF`      a Fiat-Shamir query in hash calls: K + 1 without a test; n + (K + 1) with one and the
             cap n (n + 1 tries): at most n tries that fail, one call each, and one whole answer.
  `chainF`   the sum over the rounds: chainN (Johnson/Prover/Law/Count.lean) with fsF for fsN.
  `small_cost`, `cost_of_small`   the trees and the request tree's path: a typed query is one call.
  `costBound_searchO`, `costBound_fsO`, `costBound_onFs`   the search.
  `costBound_chainO`, `costBound_proveX`   the weighted bound (OComp.CostBoundR, Rom/OverOneF.lean).
  `hashCalls_proveX`   THE STATEMENT: the compiled prover, unturned, by the third exit, asks the
             hash function at most chainF times, on every path.

Limits. AN UPPER BOUND AT LETTERS: chainF is a sum over a wire record, the caps and the length of
the slot's path: NO NUMERAL STANDS HERE, and no cap is a value. Loose as chainN is (its head names
four ways): every round counts both components' Fiat-Shamir numbers: that adds K + 1 calls a round
for the component that is not asked. pass is a letter, TestsAt and FirstIs are premises. One slot,
one chain.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Law.Count
import Johnson.Prover.Law.FirstBlockLaws

set_option autoImplicit false

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The second form's names of oracles, type of a Fiat-Shamir answer and type of programs. (The
first form's are in sight too.) -/
local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName
local notation "FsAns₂" => TypedOracleCompiler.Compile.Batch.FsAns
local notation "OC₂" => TypedOracleCompiler.Compile.Batch.TypedOracleComputation

/-- A Fiat-Shamir query in hash calls. B: the blocks of a whole answer. -/
def fsF {C P : Type} (B : ℕ) : Option (GrW C P) → ℕ → ℕ
  | none, _ => B
  | some _, n => n + B

/-- The sum over the rounds, in hash calls. i: the number of the first of the rounds s; p: the
length of the slot's path in the request tree. -/
def chainF : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → (ℕ → ℕ) → ℕ → ℕ → ℕ
  | [], _, _, _, _, _ => 0
  | _ :: s, (_, A), (w, W), cap, i, p =>
      treesN w.depthJ + treesN w.depth0 + (2 + p) +
        (fsF (K + 1) w.grJ (cap i) + fsF (K + 1) w.gr0 (cap i)) + chainF s A W cap (i + 1) p

/-! ## Queries of one call -/

/-- At the four tree oracles a typed query is one hash call. -/
theorem small_cost (hK : 0 < K) (pass : Pass lam L) :
    Small (lam := lam) (L := L) fun o q => ∀ r, costP hK pass o q r ≤ 1 :=
  ⟨fun _ _ => le_refl 1, fun _ _ => le_refl 1, fun _ _ => le_refl 1, fun _ _ => le_refl 1⟩

/-- A bound in typed queries is one in hash calls, where each query that is asked is one call. -/
theorem cost_of_small (hK : 0 < K) (pass : Pass lam L) {α : Type} {c : OC₂ lam K L α} {t : ℕ}
    (h : c.QueryBound t) (ha : c.AsksIn fun o q => ∀ r, costP hK pass o q r ≤ 1) :
    c.CostBoundR (costP hK pass) t := OComp.CostBoundR.of_queryBound h ha

/-! ## The search -/

section Search
variable (hK : 0 < K) (pass : Pass lam L) {C P : Type} (chal : (Fin K → Dig lam) → C) (t : Tag)
  (qOf : P → FbIn lam L t)

/-- fuel + 1 tries: at most fuel calls for tries that fail, and one whole answer. -/
theorem costBound_searchO (gr : GrW C P)
    (hT : ∀ β u, gr.ok (chal u) = pass t (qOf β) (u ⟨0, hK⟩)) (α : P) :
    ∀ fuel n : ℕ, (searchO gr chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qOf β)) α
      (fuel + 1) n).CostBoundR (costP hK pass) (fuel + (K + 1))
  | fuel, n => by
    show (OComp.query (S := typedOracleFamily lam K L) (OracleName.fb t) (qOf (gr.put n α)) fun a =>
      if gr.ok (chal a.1) then OComp.pure (some (gr.put n α, a))
      else searchO gr chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qOf β)) α fuel
        (n + 1)).CostBoundR (costP hK pass) (fuel + (K + 1))
    intro r
    by_cases hk : gr.ok (chal r.1) = true
    · have hp : pass t (qOf (gr.put n α)) (r.1 ⟨0, hK⟩) = true := by
        rw [← hT (gr.put n α)]
        exact hk
      refine ⟨fuel, ?_, ?_⟩
      · show fuel + (K + 1) = (if pass t (qOf (gr.put n α)) (r.1 ⟨0, hK⟩) = true then K + 1
          else 1) + fuel
        rw [if_pos hp]
        omega
      · simp only [if_pos hk]
        trivial
    · have hp : ¬ pass t (qOf (gr.put n α)) (r.1 ⟨0, hK⟩) = true := by
        rw [← hT (gr.put n α)]
        exact hk
      refine ⟨fuel + K, ?_, ?_⟩
      · show fuel + (K + 1) = (if pass t (qOf (gr.put n α)) (r.1 ⟨0, hK⟩) = true then K + 1
          else 1) + (fuel + K)
        rw [if_neg hp]
        omega
      · simp only [if_neg hk]
        cases fuel with
        | zero => trivial
        | succ f =>
          exact (costBound_searchO gr hT α f (n + 1)).mono (by omega)

/-- A Fiat-Shamir query, with a test or without. -/
theorem costBound_fsO (gr : Option (GrW C P)) (cap : ℕ) (hT : TestQ hK pass chal t qOf gr)
    (α : P) :
    (fsO gr cap chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qOf β)) α).CostBoundR
      (costP hK pass) (fsF (K + 1) gr cap) := by
  cases gr with
  | none =>
    show (OComp.query (S := typedOracleFamily lam K L) (OracleName.fb t) (qOf α) fun a =>
      OComp.pure (some (α, a))).CostBoundR (costP hK pass) (K + 1)
    intro r
    refine ⟨0, ?_, trivial⟩
    show K + 1 = (if pass t (qOf α) (r.1 ⟨0, hK⟩) = true then K + 1 else 1) + 0
    rw [if_pos (hT α _)]
  | some g => exact costBound_searchO hK pass chal t qOf g hT α cap 0

end Search

theorem costBound_onFs {w : (o : ON₂) → domOf lam L o → rngOf lam K o → ℕ} {P β : Type} (i n : ℕ)
    (k : P × FsAns₂ lam K → OC₂ lam K L (Res β)) (hk : ∀ p, (k p).CostBoundR w n) :
    ∀ o, (onFs i k o).CostBoundR w n
  | none => trivial
  | some p => hk p

/-! ## The chain -/

/-- **THE CHAIN's HASH CALLS.** -/
theorem costBound_chainO (hK : 0 < K) (pass : Pass lam L) (t : Tag) (cms : List (Dig lam))
    (x : Option X) (co : Coins lam L) (cap : ℕ → ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
      (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam) (σ : Strat s Unit),
      TestsAt hK pass t i s A W embP →
      (chainO t cms x co cap s A W embS embP i ph σ).CostBoundR (costP hK pass)
        (chainF s A W cap i co.path.length)
  | [], _, _, _, _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m, k), H => by
    have sm := small_cost (lam := lam) (L := L) hK pass
    have tail : ∀ {β : Type} (ph' σ') (f : Res (OutP lam L s) → OC₂ lam K L β),
        (∀ r, (f r).CostBoundR (costP hK pass) 0) →
        ((chainO t cms x co cap s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
          ph' σ').bind f).CostBoundR (costP hK pass)
            (chainF s A W cap (i + 1) co.path.length + 0) :=
      fun ph' σ' f hf =>
        OComp.CostBoundR.bind hf (costBound_chainO hK pass t cms x co cap s A W _ _ _ ph' σ' H.2)
    have one : ∀ (o : ON₂) (q : domOf lam L o), (∀ r, costP hK pass o q r ≤ 1) →
        (askTypedOracle (L := L) (K := K) o q).CostBoundR (costP hK pass) 1 := fun o q h =>
      cost_of_small hK pass (queryBound_askV o q) ⟨h, fun _ => trivial⟩
    simp only [chainO]
    cases e : actOf cms (x.map L.early) co.salt a.kind ph with
    | none => trivial
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          have hT : TestIs hK pass t i w.chal (fun α => embP (.inl (.inr α))) w.grJ := by
            have h1 := H.1
            rw [(act_own e).1] at h1
            exact h1
          exact (OComp.CostBoundR.bind (fun _ => OComp.CostBoundR.bind
              (costBound_onFs _ _ _ fun _ => tail _ _ _ (by intro _; trivial))
              (costBound_fsO hK pass w.chal t _ w.grJ (cap i)
                (testIs_at hK pass t i w.chal _ w.grJ hT _ _) _))
            (cost_of_small hK pass (queryBound_treesO _ _ _ _ _ _ _)
              (asksIn_treesO sm _ _ _ _ _ _ _))).mono (by
                show _ ≤ treesN w.depthJ + treesN w.depth0 + (2 + co.path.length) +
                  (fsF (K + 1) w.grJ (cap i) + fsF (K + 1) w.gr0 (cap i)) +
                    chainF s A W cap (i + 1) co.path.length
                omega)
        | false =>
          have hT : TestIs hK pass t i w.chal (fun α => embP (.inl (.inl α))) w.gr0 := by
            have h1 := H.1
            rw [(act_shared e).1] at h1
            exact h1
          exact (OComp.CostBoundR.bind (fun _ => OComp.CostBoundR.bind
              (costBound_onFs _ _ _ fun _ => tail _ _ _ (by intro _; trivial))
              (costBound_fsO hK pass w.chal t _ w.gr0 (cap i)
                (testIs_at hK pass t i w.chal _ w.gr0 hT _ _) _))
            (cost_of_small hK pass (queryBound_treesO _ _ _ _ _ _ _)
              (asksIn_treesO sm _ _ _ _ _ _ _))).mono (by
                show _ ≤ treesN w.depthJ + treesN w.depth0 + (2 + co.path.length) +
                  (fsF (K + 1) w.grJ (cap i) + fsF (K + 1) w.gr0 (cap i)) +
                    chainF s A W cap (i + 1) co.path.length
                omega)
      | join ρ =>
        have hT : TestIs hK pass t i w.chal (fun α => embP (.inl (.inl α))) w.gr0 := by
          have h1 := H.1
          rw [(act_join e).1] at h1
          exact h1
        exact (OComp.CostBoundR.bind (fun _ => OComp.CostBoundR.bind (fun _ =>
            OComp.CostBoundR.bind (fun _ => OComp.CostBoundR.bind (fun _ =>
            OComp.CostBoundR.bind (fun _ => OComp.CostBoundR.bind
              (costBound_onFs _ _ _ fun _ => tail _ _ _ (by intro _; trivial))
              (costBound_fsO hK pass w.chal t _ w.gr0 (cap i)
                (testIs_at hK pass t i w.chal _ w.gr0 hT _ _) _))
            (cost_of_small hK pass (queryBound_climbO _ _ _) (asksIn_climbO sm _ _ _)))
            (one _ _ fun _ => le_refl 1)) (one _ _ fun _ => le_refl 1))
            (cost_of_small hK pass (queryBound_treesO _ _ _ _ _ _ _)
              (asksIn_treesO sm _ _ _ _ _ _ _)))
            (cost_of_small hK pass (queryBound_treesO _ _ _ _ _ _ _)
              (asksIn_treesO sm _ _ _ _ _ _ _))).mono (by
                show _ ≤ treesN w.depthJ + treesN w.depth0 + (2 + co.path.length) +
                  (fsF (K + 1) w.grJ (cap i) + fsF (K + 1) w.gr0 (cap i)) +
                    chainF s A W cap (i + 1) co.path.length
                omega)

section Prove
variable (hK : 0 < K) (pass : Pass lam L) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
  (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeK lam L)
  (σ : Strat Q.loc.shape Unit) (co : Coins lam L) (cap : ℕ → ℕ)

/-- The compiled prover of one slot. -/
theorem costBound_proveX (H : TestsAt hK pass t 0 Q.loc.shape Q.ann wq.sh embP) :
    (proveX t Q wq embS embP xin cms x y xt σ co cap).CostBoundR (costP hK pass)
      (chainF Q.loc.shape Q.ann wq.sh cap 0 co.path.length) :=
  (OComp.CostBoundR.bind (t := 0) (by intro _; trivial)
    (costBound_chainO hK pass t cms (xin x) co cap Q.loc.shape Q.ann wq.sh embS embP 0 .first σ
      H)).mono (by omega)

/-- **THE COMPILED PROVER, UNTURNED, BY THE THIRD EXIT, ASKS THE HASH FUNCTION AT MOST chainF TIMES,
ON EVERY PATH.** -/
theorem hashCalls_proveX (m : OracleCoding (typedOracleFamily lam K L) lam) (F : FirstIs hK m)
    (H : TestsAt hK pass t 0 Q.loc.shape Q.ann wq.sh embP) :
    ((proveX t Q wq embS embP xin cms x y xt σ co cap).overOneF m (moreP pass)).QueryBound
      (chainF Q.loc.shape Q.ann wq.sh cap 0 co.path.length) := by
  refine queryBound_overOneF m (moreP pass) _ _ ?_
  have e : costF m (moreP pass) = costP hK pass := by
    funext o q r
    exact costF_eq_costP hK pass m F o q r
  rw [e]
  exact costBound_proveX hK pass t Q wq embS embP xin cms x y xt σ co cap H

end Prove

end OnBytes.Prover

#print axioms OnBytes.Prover.small_cost
#print axioms OnBytes.Prover.cost_of_small
#print axioms OnBytes.Prover.costBound_searchO
#print axioms OnBytes.Prover.costBound_fsO
#print axioms OnBytes.Prover.costBound_onFs
#print axioms OnBytes.Prover.costBound_chainO
#print axioms OnBytes.Prover.costBound_proveX
#print axioms OnBytes.Prover.hashCalls_proveX
