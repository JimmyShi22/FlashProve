-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CutLinks.lean: the state-expansion step ("state first", Rom/StateFirst.lean) after the
splitting step (Compile/Batch/CutFit.lean): which oracles have their answers expanded from a state,
and what the step needs of the split scheme. Generic in the number K of hash blocks and in the
scheme (words of this library: lean/GLOSSARY.md).

  `restLink`, `linksS`  For K = K' + 2 the rest of a Fiat-Shamir answer is K' blocks, the chaining
                        value, and the last block, which no algorithm of the scheme may read
                        (`Link.agH`, `Rom.HidFree`); the K' blocks are expanded from a state of two
                        hash blocks, the chaining value and the last block. Every other oracle is
                        unchanged.
  `agree_join`, `hidFree_cut`  If all nb t i < K: two answers with the same first part whose rests
                               agree except for the unread block agree on what is needed
                               (`Need.agree nb`, Compile/Batch/NeedTable.lean). So, if a scheme's
                               algorithms depend on an answer only up to `Need.agree nb`, those of
                               the split scheme do not read the unread block (`Rom.HidFree`),
                               whatever the three rules (`NeedCut`).
  `cutState_of_facOK`  the two steps at a scheme: `Rom.cutState` with its hypotheses `PlainOnly` and
                       `HidFree` discharged

Limits: that nb t i < K holds is a hypothesis: the wire record must have one block more than the
largest number that a round reads (this file gives none). The bounds kC, kP, kV on queries to
expanded oracles are hypotheses. Nothing on the one hash function.
-/
import Compile.Batch.CutFit

set_option autoImplicit false

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP
open scoped ENNReal

variable {I X : Type} {lam : ℕ}

/-- how the rest of a Fiat-Shamir answer is treated -/
def restLink (lam : ℕ) : (K : ℕ) → Link lam (cutFb lam K).Rest
  | 0 => .plain
  | 1 => .plain
  | K + 2 => .chain K (Equiv.refl _)

/-- How each oracle of the split family is treated. -/
def linksS (lam K : ℕ) (L : BatchProtocol I X) :
    ∀ x : (cutSpec (spec lam K L) (cutFS lam K L)).ι,
      Link lam ((cutSpec (spec lam K L) (cutFS lam K L)).Rng x)
  | .inl _ => .plain
  | .inr (.fb _) => restLink lam K
  | .inr .leaf => .plain
  | .inr .node => .plain
  | .inr .rleaf => .plain
  | .inr .rnode => .plain
  | .inr (.fbw _ _) => .plain
  | .inr (.g _) => .plain
  | .inr .ann => .plain
  | .inr .other => .plain

variable {K : ℕ} {L : BatchProtocol I X}

/-- two Fiat-Shamir answers with the same first part whose rests agree except for the unread block
(not all hypotheses are named here: see the statement below) -/
theorem agree_joinFb :
    ∀ (K n : ℕ), n < K →
      ∀ (a : (cutFb lam K).Front) (b b' : (cutFb lam K).Rest), (restLink lam K).agH b b' →
        ((cutFb lam K).join a b).2 = ((cutFb lam K).join a b').2 ∧
        ∀ j : Fin K, j.val < n → ((cutFb lam K).join a b).1 j = ((cutFb lam K).join a b').1 j
  | 0, _, _, _, _, _, _ => ⟨rfl, fun _ _ => rfl⟩
  | 1, _, _, _, _, _, _ => ⟨rfl, fun _ _ => rfl⟩
  | K + 2, n, hn, a, b, b', h => by
    have h' : b.1 = b'.1 ∧ b.2.1 = b'.2.1 := h
    refine ⟨h'.2, fun j hj => ?_⟩
    show (Fin.cons (α := fun _ => Dig lam) a
        (Fin.snoc (α := fun _ => Dig lam) b.1 b.2.2) : Fin (K + 2) → Dig lam) j =
      (Fin.cons (α := fun _ => Dig lam) a
        (Fin.snoc (α := fun _ => Dig lam) b'.1 b'.2.2) : Fin (K + 2) → Dig lam) j
    revert hj
    refine Fin.cases (fun _ => rfl) (fun i hi => ?_) j
    rw [Fin.cons_succ, Fin.cons_succ]
    have hi' : i.val < K := by
      have : i.val + 1 < n := hi
      omega
    have e : i = Fin.castSucc ⟨i.val, hi'⟩ := rfl
    rw [e, Fin.snoc_castSucc, Fin.snoc_castSucc, h'.1]

/-- Answers with the same first part whose rests agree except for the unread block agree on what is
needed, if every round needs fewer than K blocks. -/
theorem agree_join (nb : Tag → ℕ → ℕ) (hnb : ∀ t i, nb t i < K) (o : OracleName) (q : domOf lam L o)
    (a : (cutFS lam K L o).Front) (b b' : (cutFS lam K L o).Rest)
    (h : (linksS lam K L (.inr o)).agH b b') :
    Need.agree nb o q ((cutFS lam K L o).join a b) ((cutFS lam K L o).join a b') := by
  cases o with
  | fb t => exact agree_joinFb K (nb t (q : FbIn lam L t).round) (hnb t _) a b b' h
  | fbw t j => exact ⟨rfl, fun _ _ => rfl⟩
  | leaf => rfl
  | node => rfl
  | rleaf => rfl
  | rnode => rfl
  | g t => rfl
  | ann => rfl
  | other => rfl

variable {Wt IVK' ISK' Pf' : Type}

/-- Under the hypotheses below: the three algorithms of the split scheme do not read the unread
block. -/
theorem hidFree_cut {nb : Tag → ℕ → ℕ} (hnb : ∀ t i, nb t i < K)
    {A : Gen.Arg (spec lam K L) I X Wt IVK' ISK' Pf'}
    (h : FacOK (Need.agree nb) A) (nC nP nV : NeedCut (cutFS lam K L)) :
    HidFree (linksS lam K L) (cutArg (cutFS lam K L) nC nP nV A) where
  C := fun i => factorsBy_cut _ (fun _ _ _ _ e => e) (agree_join nb hnb) _ (h.C i)
  P := fun k b => factorsBy_cut _ (fun _ _ _ _ e => e) (agree_join nb hnb) _ (h.P k b)
  V := fun v x π => factorsBy_cut _ (fun _ _ _ _ e => e) (agree_join nb hnb) _ (h.V v x π)

theorem plainOnly_cut (E : Gen.Extractor (spec lam K L) I X Wt IVK' Pf') :
    PlainOnly (linksS lam K L) (extCut (cutFS lam K L) E) :=
  plainOnly_extCut _ _ (fun _ _ => rfl) E

theorem wCh_inl (o : OracleName) (q : domOf lam L o) : wCh (linksS lam K L) (.inl o) q = 0 := rfl

theorem wCh_inr_le (o : OracleName) (q : domOf lam L o) : wCh (linksS lam K L) (.inr o) q ≤ 1 := by
  unfold wCh
  split <;> omega

/-- The two steps at a scheme: `Rom.cutState` (Rom/CutTop.lean; its statement: `Spec.cutState`,
Rom/SpecCut.lean) with its hypotheses `PlainOnly` and `HidFree` discharged. (`collP`, `hitP` in the
statement below: Rom/StateFirst.lean.)
(not all hypotheses are named here: see the statement below) -/
theorem cutState_of_facOK {PP : Type} {nb : Tag → ℕ → ℕ} (hnb : ∀ t i, nb t i < K)
    (R : Gen.RelPair I X Wt PP) (A : Gen.Arg (spec lam K L) I X Wt IVK' ISK' Pf') (B : ℕ)
    (E : Gen.Extractor (spec lam K L) I X Wt IVK' Pf')
    (Sim : Gen.Simulator (spec lam K L) PP IVK' X Pf') (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞)
    (nC nP nV : NeedCut (cutFS lam K L)) (kC kP kV : ℕ) (hN : NeedOKCut (cutFS lam K L) A nC nP nV)
    (hE : WholeOnly (cutFS lam K L) E) (hA : FacOK (Need.agree nb) A)
    (cC : ∀ i, (A.C i).CostBoundV (wCut (cutFS lam K L) nC (wCh (linksS lam K L))) kC)
    (cP : ∀ k b,
      b.length ≤ B → (A.P k b).CostBoundV (wCut (cutFS lam K L) nP (wCh (linksS lam K L))) kP)
    (cV : ∀ v x π, (A.V v x π).CostBoundV (wCut (cutFS lam K L) nV (wCh (linksS lam K L))) kV)
    (h : Gen.IsZKCPArgWith R A B E Sim α ε ζ) :
    Gen.IsZKCPArgWith R (stateFirstArg (linksS lam K L) (cutArg (cutFS lam K L) nC nP nV A)) B
      (extSt (linksS lam K L) (extCut (cutFS lam K L) E))
      (simSt (linksS lam K L) (simCut (cutFS lam K L) Sim))
      (α + collP lam (kC + kP + B * kV) (kC + kP + B * kV))
      (fun tC tP => ε tC tP + collP lam (tC + tP + kV) (tC + tP + kV)) (fun t N =>
        ζ t N + collP lam (t + (kC + N * kP)) (t + (kC + N * kP)) + hitP lam t (kC + N * kP)) :=
  cutState _ _ lam (linksS lam K L) _ _ _ _ _ _ _ R A B E Sim α ε ζ nC nP nV kC kP kV hN hE cC cP cV
    (plainOnly_cut E) (hidFree_cut hnb hA nC nP nV) h

end Compile.Batch
