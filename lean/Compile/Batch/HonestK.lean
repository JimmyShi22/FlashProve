-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/HonestK.lean: the scheme `argBK` with the entries in the verification key
(Compile/Batch/StarK.lean): facts on its honest committer and prover. For every wire record; the
rounds may have proof-of-work bits (words of this library: lean/GLOSSARY.md). V' is its verifier, V
that of `argB`. The scheme encodes the index once and `p.M` + 1 more times (the copies); the entry
of a copy is the root of its tree and Link's proof string (`Links`: the published entries).
  `allOut_realQ`      A property of all outputs of an algorithm also holds of the algorithm with the
                      ghost names written back (`realQ`, Compile/Batch/Oracles.lean). Written back:
                      queries to `fbw` become queries to `fb`. C and P are of this form
                      (Compile/Batch/Star.lean).
  `honestK`           Take a proof that the prover of `argB` can output, and overwrite its entry
                      from the published list: for V this changes nothing (`GenPub.Pub.Honest`,
                      Compile/GenPub.lean). The reason: such a proof either has no slot's proof
                      string, and then V rejects whatever its other fields are; or it carries the
                      entry of its copy as isk holds it, and a copy number that is at most M.
  `length_links_honest`, `VK_eq_of_length_le`, `V_of_leaf_gt`
                      sanity lemmas: the honest key has exactly M + 1 entries; what V' is on a key
                      with at most M + 1 entries, and what V is at a copy number beyond M (for V' on
                      a longer, cheating key: the docstring of `V_of_leaf_gt`)
Limits: none of the three properties of a scheme (completeness, index binding, index privacy:
ZKCP/Gen.lean).
-/
import Compile.Batch.StarK
import Compile.Batch.PubChall
import Compile.Batch.RealQ

noncomputable section

namespace Compile.Batch
open Iop Rom Prob ZKCP Compile.GenMap Compile.GenPub
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- What holds of all outputs still holds with the ghost names written back (`realQ`). -/
theorem allOut_realQ {K : ℕ} {α : Type} {Q : α → Prop} :
    ∀ (c : OComp (spec lam K L) α), AllOut Q c → AllOut Q (realQ c) := by
  intro c
  induction c with
  | pure a => exact fun h => h
  | sample m k ih => exact fun h r => ih r (h r)
  | query o q k ih =>
    intro h
    cases o <;> exact fun r => ih r (h r)

instance : Inhabited (PrfK lam L) := ⟨⟨0, none⟩⟩

/-! ## `Pub.Honest`: for V, overwriting an honest proof's entry from the key changes nothing -/

section Honest
variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

/-- V rejects a proof without a slot's proof string, whatever its other fields are -/
theorem V_of_piB_none (v : IVK lam L) (x : X) (π : Prf lam L) (h : π.piB = none) :
    V W p v x π = pure false := by
  obtain ⟨c0, piT⟩ := v
  obtain ⟨j, cm, piL, piB⟩ := π
  subst h
  cases piT <;> cases piL <;> rfl

/-- V uses the number of the copy for one check only: every j ≤ M gives the same as 0 -/
theorem V_leaf (v : IVK lam L) (x : X) (j : ℕ) (hj : j ≤ p.M) (cm : Dig lam)
    (piL : Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link))) (piB : Option (OneProtocolProof lam L.onlineBatch)) :
    V W p v x ⟨0, cm, piL, piB⟩ = V W p v x ⟨j, cm, piL, piB⟩ := by
  obtain ⟨c0, piT⟩ := v
  cases piT with
  | none => rfl
  | some a =>
    cases piL with
    | none => rfl
    | some b =>
      cases piB with
      | none => rfl
      | some c =>
        unfold V
        dsimp only
        rw [if_pos (Nat.zero_le _), if_pos hj]

theorem reK_piB (ℓ : Links lam L) (π : Prf lam L) : (reK ℓ π).piB = π.piB := by
  unfold reK
  split <;> rfl

/-- what every proof of the honest prover is like -/
def GoodK (k : IskH lam L) (π : Prf lam L) : Prop :=
  π.piB = none ∨
  (π.leaf ≤ p.M ∧ ∃ lf, k.leaves[π.leaf]? = some lf ∧ π.cm = lf.node.tree.root ∧ π.piL = lf.piL)

theorem V_reK_of_good {k : IskH lam L} {π : Prf lam L} (h : GoodK p k π) (v : IVK lam L) (x : X) :
    V W p v x (reK (linksOf (keyOf k)) π) = V W p v x π := by
  rcases h with h | ⟨hj, lf, hl, hc, hp⟩
  · rw [V_of_piB_none W p v x π h, V_of_piB_none W p v x _ ((reK_piB _ π).trans h)]
  · obtain ⟨j, cm, piL, piB⟩ := π
    have e : (linksOf (keyOf k))[j]? = some (lf.node.tree.root, lf.piL) := by
      simp only [linksOf, keyOf, List.getElem?_map]
      rw [show k.leaves[j]? = some lf from hl]
      rfl
    have e2 : reK (linksOf (keyOf k)) ⟨j, cm, piL, piB⟩ = ⟨0, lf.node.tree.root, lf.piL, piB⟩ := by
      unfold reK
      simp only [e]
    rw [e2, show cm = lf.node.tree.root from hc, show piL = lf.piL from hp]
    exact V_leaf W p v x j hj _ _ _

theorem allOut_PpJ (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (j : Fin (p.M + 1))
    (σ : Equiv.Perm (Fin L.maxBatchSize)) (vs : List Bits) :
    AllOut (fun o : List (Prf lam L) × List Bits => ∀ π ∈ o.1, GoodK p k π)
      (erase (PpJ W WP p k fr xs j.val σ) vs) := by
  unfold PpJ
  rcases hl : k.leaves[j.val]? with _ | lf
  · show AllOut _ (OComp.pure (_, vs))
    intro π hπ
    obtain ⟨_, -, rfl⟩ := List.mem_map.1 hπ
    exact Or.inl rfl
  · dsimp only
    rw [erase_bind]
    refine AllOut.bind (allOut_true _) fun o _ => ?_
    show AllOut _ (OComp.pure (_, o.2))
    intro π hπ
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hπ
    exact Or.inr ⟨Nat.lt_succ_iff.1 j.isLt, lf, hl, rfl, rfl⟩

theorem allOut_P (k : ISK lam L) (b : List (X × Unit)) :
    AllOut (fun πs : Gen.Slots (Prf lam L) b => ∀ π ∈ πs.val, GoodK p k.1 π) (P W WP p k b) := by
  unfold P Ptok
  refine allOut_realQ _
    (AllOut.bind (Q' := fun o : List (Prf lam L) × List Bits => ∀ π ∈ o.1, GoodK p k.1 π) ?_
      fun o ho => ?_)
  · unfold Pp
    rw [erase_sample]
    intro j
    dsimp only
    rw [erase_bind]
    exact AllOut.bind (allOut_true _) fun o _ => allOut_PpJ W WP p k.1 _ _ j o.1 o.2
  · show ∀ π ∈ (fitLen (⟨0, default, none, none⟩ : Prf lam L) b.length o.1).val, GoodK p k.1 π
    intro π hπ
    rcases List.mem_append.1 (List.mem_of_mem_take hπ) with h | h
    · exact ho π h
    · rw [(List.mem_replicate.1 h).2]
      exact Or.inl rfl

/-- For V, overwriting from the key the entry of a proof that the honest prover can output changes
nothing (`Pub.Honest`). -/
theorem honestK :
    (pubK : Pub (IVK lam L) (ISK lam L) (Prf lam L) (Links lam L)).Honest (argB W WP p) :=
  fun v k b => (allOut_P W WP p k b).mono fun _ h π hπ x => V_reK_of_good W p (h π hπ) v x

end Honest

/-! ## Sanity lemmas: the honest key has M + 1 entries; on a key with at most M + 1 entries V' reads
entry j, then runs V -/

section Guards
variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

theorem allOut_leavesC (i : I) (root : Node lam L) :
    ∀ (n : ℕ) (vs : List Bits), AllOut (fun o : List (LeafRec lam L) × List Bits => o.1.length = n)
      (erase (leavesC W WP p i root n) vs)
  | 0, vs => by
      show AllOut _ (OComp.pure (_, vs))
      rfl
  | n + 1, vs => by
      unfold leavesC
      rw [erase_bind]
      refine AllOut.bind (allOut_true _) fun a _ => ?_
      rw [erase_bind]
      refine AllOut.bind (allOut_true _) fun b _ => ?_
      rw [erase_bind]
      refine AllOut.bind (allOut_leavesC i root n _) fun c hc => ?_
      show AllOut _ (OComp.pure (_, c.2))
      show (_ :: c.1).length = n + 1
      rw [List.length_cons, hc]

/-- On every path the honest committer's key has exactly M + 1 entries. -/
theorem length_links_honest (i : I) :
    AllOut (fun o : IVKK lam L × ISK lam L => o.1.2.length = p.M + 1) ((argBK W WP p).C i) := by
  show AllOut _ ((C W WP p i).bind fun o => OComp.pure ((o.1, linksOf (keyOf o.2.1)), o.2))
  refine AllOut.bind (Q' := fun o : IVK lam L × ISK lam L => o.2.1.leaves.length = p.M + 1) ?_
    fun o ho => ?_
  · unfold C Ctok
    refine allOut_realQ _
      (AllOut.bind
        (Q' := fun o : (IVK lam L × IskH lam L) × List Bits => o.1.2.leaves.length = p.M + 1) ?_
        fun o ho => ho)
    unfold Cp
    rw [erase_bind]
    refine AllOut.bind (allOut_true _) fun a _ => ?_
    rw [erase_bind]
    refine AllOut.bind (allOut_true _) fun b _ => ?_
    rw [erase_bind]
    exact AllOut.bind (allOut_leavesC W WP p i _ _ _) fun c hc => hc
  · show (linksOf (keyOf o.2.1)).length = p.M + 1
    simp only [linksOf, keyOf, List.length_map]
    exact ho

/-- On a key with at most M + 1 entries, the honest key among them, V' reads entry j, then runs V on
(j, cm_j, piL_j, piB); without an entry number j it returns false. -/
theorem VK_eq_of_length_le (v : IVK lam L) (ℓ : Links lam L) (hℓ : ℓ.length ≤ p.M + 1) (x : X)
    (j : ℕ) (piB : Option (OneProtocolProof lam L.onlineBatch)) :
    (argBK W WP p).V (v, ℓ) x ⟨j, piB⟩ = match ℓ[j]? with
      | some e => V W p v x ⟨j, e.1, e.2, piB⟩
      | none => pure false := by
  rcases h : ℓ[j]? with _ | e
  · exact VK_of_none W WP p (v := (v, ℓ)) (π := ⟨j, piB⟩) h x
  · have hj : j < ℓ.length := (List.getElem?_eq_some_iff.1 h).1
    rw [VK_of_some W WP p (v := (v, ℓ)) (π := ⟨j, piB⟩) h x]
    exact V_leaf W p v x j (by omega) _ _ _

/-- V returns false, without a query, on a copy number beyond M. So on a cheating key with more than
M + 1 entries V' is more generous than reading entry j and then running V (`VK_eq_of_length_le`): at
j > M it still runs the verifiers of Test, Link and the slot (`VK_of_some`). -/
theorem V_of_leaf_gt (v : IVK lam L) (x : X) (j : ℕ) (hj : p.M < j) (cm : Dig lam)
    (piL : Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link))) (piB : Option (OneProtocolProof lam L.onlineBatch)) :
    V W p v x ⟨j, cm, piL, piB⟩ = pure false := by
  obtain ⟨c0, piT⟩ := v
  cases piT <;> cases piL <;> cases piB <;> first | rfl | (unfold V; dsimp only; rw [if_neg (by omega)])

end Guards

end Compile.Batch
