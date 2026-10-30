-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CutDraws.lean: which hash blocks of a Fiat-Shamir answer are expanded from the state.

Two steps change the typed oracles of the compiled scheme: a Fiat-Shamir answer is split into its
first block and the rest (Rom/SpecCut.lean, Compile/Batch/CutFit.lean), and the middle hash blocks
of the answer, which are in the rest, are expanded from a state, which is its chaining value and its
last block, by queries to the oracle dr (Rom/StateFirst.lean, Compile/Batch/CutLinks.lean).
`OComp.stateFirst` then queries all K - 2 expanded hash blocks in every round. This file gives the
rule of Rom/StateFirstLazy.lean under which only those that the round's number `nb t i` names are
queried (`nb t i`: how many hash blocks of its answer round i of the protocol t needs: `Need.agree`,
Compile/Batch/NeedTable.lean). Expanded hash block j of the rest is hash block j + 1 of the typed
answer.

  `needD nb`    The rule: expanded hash block j of the rest of a Fiat-Shamir answer is queried if
                and only if j + 1 < `nb t i`. It does not look at earlier hash blocks, and queries
                nothing from the index `nb t i` - 1 on (`needD_below`).
  `readOK_cut`  Let `nb t i` < K in every round, and let the algorithms of a scheme `A` read an
                answer only up to `Need.agree nb`. Then the split scheme meets the condition
                `ReadOK` of the rule, whatever the three rules of the split.

Limits: nothing is said about one hash function, and no query is counted (but for `nDraws`, the
rule's own number for one answer: `needD_below`).
-/
import Compile.Batch.CutLinks
import Rom.StateFirstLazy
import Rom.OverOneA

set_option autoImplicit false

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP

variable {I X : Type} {lam : ℕ}

/-- two rests have the same chaining value and the same expanded hash blocks j with j + 1 < n -/
def restAg (lam : ℕ) : (K n : ℕ) → (cutFb lam K).Rest → (cutFb lam K).Rest → Prop
  | 0, _, _, _ => True
  | 1, _, _, _ => True
  | K + 2, n, b, b' => b.2.1 = b'.2.1 ∧ ∀ j : Fin K, j.val + 1 < n → b.1 j = b'.1 j

/-- the relation on the parts -/
def agParts {K : ℕ} {L : BatchProtocol I X} (nb : Tag → ℕ → ℕ) :
    ∀ x, (cutSpec (spec lam K L) (cutFS lam K L)).Dom x →
      (cutSpec (spec lam K L) (cutFS lam K L)).Rng x →
      (cutSpec (spec lam K L) (cutFS lam K L)).Rng x → Prop
  | .inl _, _, a, a' => a = a'
  | .inr (.fb t), q, b, b' => restAg lam K (nb t (q : FbIn lam L t).round) b b'
  | .inr .leaf, _, _, _ => True
  | .inr .node, _, _, _ => True
  | .inr .rleaf, _, _, _ => True
  | .inr .rnode, _, _, _ => True
  | .inr (.fbw _ _), _, _, _ => True
  | .inr (.g _), _, _, _ => True
  | .inr .ann, _, _, _ => True
  | .inr .other, _, _, _ => True

theorem agree_joinFbR :
    ∀ (K n : ℕ), n < K →
      ∀ (a : (cutFb lam K).Front) (b b' : (cutFb lam K).Rest), restAg lam K n b b' →
        ((cutFb lam K).join a b).2 = ((cutFb lam K).join a b').2 ∧
        ∀ j : Fin K, j.val < n → ((cutFb lam K).join a b).1 j = ((cutFb lam K).join a b').1 j
  | 0, _, _, _, _, _, _ => ⟨rfl, fun _ _ => rfl⟩
  | 1, _, _, _, _, _, _ => ⟨rfl, fun _ _ => rfl⟩
  | K + 2, n, hn, a, b, b', h => by
    have h' : b.2.1 = b'.2.1 ∧ ∀ j : Fin K, j.val + 1 < n → b.1 j = b'.1 j := h
    refine ⟨h'.1, fun j hj => ?_⟩
    show (Fin.cons (α := fun _ => Dig lam) a
        (Fin.snoc (α := fun _ => Dig lam) b.1 b.2.2) : Fin (K + 2) → Dig lam) j =
      (Fin.cons (α := fun _ => Dig lam) a
        (Fin.snoc (α := fun _ => Dig lam) b'.1 b'.2.2) : Fin (K + 2) → Dig lam) j
    revert hj
    refine Fin.cases (fun _ => rfl) (fun i hi => ?_) j
    rw [Fin.cons_succ, Fin.cons_succ]
    have hi1 : i.val + 1 < n := hi
    have hi' : i.val < K := by omega
    have e : i = Fin.castSucc ⟨i.val, hi'⟩ := rfl
    rw [e, Fin.snoc_castSucc, Fin.snoc_castSucc, h'.2 ⟨i.val, hi'⟩ hi1]

variable {K : ℕ} {L : BatchProtocol I X}

/-- Answers with the same first part whose rests are related agree on what is needed, if every
round needs fewer than K hash blocks. -/
theorem agree_joinR (nb : Tag → ℕ → ℕ) (hnb : ∀ t i, nb t i < K) (o : OracleName) (q : domOf lam L o)
    (a : (cutFS lam K L o).Front) (b b' : (cutFS lam K L o).Rest) (h : agParts nb (.inr o) q b b') :
    Need.agree nb o q ((cutFS lam K L o).join a b) ((cutFS lam K L o).join a b') := by
  cases o with
  | fb t => exact agree_joinFbR K (nb t (q : FbIn lam L t).round) (hnb t _) a b b' h
  | fbw t j => exact ⟨rfl, fun _ _ => rfl⟩
  | leaf => rfl
  | node => rfl
  | rleaf => rfl
  | rnode => rfl
  | g t => rfl
  | ann => rfl
  | other => rfl

/-- The rule for the queries to dr. -/
def needD (nb : Tag → ℕ → ℕ) : NeedA (cutSpec (spec lam K L) (cutFS lam K L)) lam
  | .inr (.fb t), q, j, _ => decide (j + 1 < nb t (q : FbIn lam L t).round)
  | .inl _, _, _, _ => false
  | .inr .leaf, _, _, _ => false
  | .inr .node, _, _, _ => false
  | .inr .rleaf, _, _, _ => false
  | .inr .rnode, _, _, _ => false
  | .inr (.fbw _ _), _, _, _ => false
  | .inr (.g _), _, _, _ => false
  | .inr .ann, _, _, _ => false
  | .inr .other, _, _, _ => false

/-- how many queries to dr the rule makes at most -/
def nDraws (nb : Tag → ℕ → ℕ) :
    (x : (cutSpec (spec lam K L) (cutFS lam K L)).ι) →
    (cutSpec (spec lam K L) (cutFS lam K L)).Dom x → ℕ
  | .inr (.fb t), q => nb t (q : FbIn lam L t).round - 1
  | .inl _, _ => 0
  | .inr .leaf, _ => 0
  | .inr .node, _ => 0
  | .inr .rleaf, _ => 0
  | .inr .rnode, _ => 0
  | .inr (.fbw _ _), _ => 0
  | .inr (.g _), _ => 0
  | .inr .ann, _ => 0
  | .inr .other, _ => 0

theorem needD_below (nb : Tag → ℕ → ℕ) :
    (needD (lam := lam) (K := K) (L := L) nb).Below (nDraws nb) := by
  intro x q j acc h
  cases x with
  | inl o => rfl
  | inr o =>
    cases o with
    | fb t =>
      have h' : nb t (q : FbIn lam L t).round - 1 ≤ j := h
      exact decide_eq_false (by omega)
    | _ => rfl

theorem restAg_mask :
    ∀ (K n : ℕ) (b : (cutFb lam K).Rest),
      restAg lam K n b ((restLink lam K).mask (fun j _ => decide (j + 1 < n)) b)
  | 0, _, _ => trivial
  | 1, _, _ => trivial
  | K + 2, n, b => by
    refine ⟨rfl, fun j hj => ?_⟩
    show b.1 j = maskFrom (fun j _ => decide (j + 1 < n)) (extBl b.1) K 0 (acc0 lam) j.val
    rw [maskFrom_static (fun j => decide (j + 1 < n)),
      if_pos ⟨Nat.zero_le _, by have := j.isLt; omega, decide_eq_true hj⟩]
    unfold extBl
    rw [dif_pos j.isLt]

/-- a part and `Link.mask` of it under the rule are related -/
theorem agParts_mask (nb : Tag → ℕ → ℕ) (x : (cutSpec (spec lam K L) (cutFS lam K L)).ι)
    (q : (cutSpec (spec lam K L) (cutFS lam K L)).Dom x)
    (r : (cutSpec (spec lam K L) (cutFS lam K L)).Rng x) :
    agParts nb x q r ((linksS lam K L x).mask (needD nb x q) r) := by
  cases x with
  | inl o => rfl
  | inr o =>
    cases o with
    | fb t => exact restAg_mask K (nb t (q : FbIn lam L t).round) r
    | _ => trivial

variable {Wt IVK' ISK' Pf' : Type}

/-- If every `nb t i` is below K and A reads answers only up to `Need.agree nb`, the split scheme
meets `ReadOK` of the rule `needD nb`. -/
theorem readOK_cut {nb : Tag → ℕ → ℕ} (hnb : ∀ t i, nb t i < K)
    {A : Gen.Arg (spec lam K L) I X Wt IVK' ISK' Pf'}
    (h : FacOK (Need.agree nb) A) (nC nP nV : NeedCut (cutFS lam K L)) :
    ReadOK (linksS lam K L) (needD nb) (cutArg (cutFS lam K L) nC nP nV A) :=
  readOK_of_facOK (ag := agParts nb)
    ⟨fun i => factorsBy_cut _ (fun _ _ _ _ e => e) (agree_joinR nb hnb) _ (h.C i),
      fun k b => factorsBy_cut _ (fun _ _ _ _ e => e) (agree_joinR nb hnb) _ (h.P k b),
      fun v x π => factorsBy_cut _ (fun _ _ _ _ e => e) (agree_joinR nb hnb) _ (h.V v x π)⟩
    (agParts_mask nb)

end Compile.Batch
