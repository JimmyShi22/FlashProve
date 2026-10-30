-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/ReadsCountAt.lean: where the public test readsWithinAtB accepts, the positions
that a description's rounds read of a sending's trees are within the sender's bound, on any of the
three chains.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. F is any description, ch the number of a chain (from 0), P the public numbers of
a sending, n₀ the number of its first tree in that chain.
  budAt_of_testAt    If readsWithinAtB F ch P n₀ accepts, then at every due list of challenges the
                     positions that are read of that chain's trees from n₀ on
                     (asksFrom (treeAsks F ρ ch) rs n₀) meet budAt P, the bound on queried positions
                     that stands as a premise inside exact and fresh.
  readsCountAt       At every due list of challenges, the tree number n of the chain number ch is
                     read at no more positions than drawnForAt F ch n.
  ReadsWithinAt      The bound written out on the description's own reads; ReadsWithin (Bud.lean) is
                     its value at ch = 0 (readsWithinAt_zero, by definition).
  readsWithinAtOf    The test implies ReadsWithinAt.
  budAt_of_readsAt   ReadsWithinAt implies budAt at those positions.
  count_chainAt      The step for one chain's rounds.

How it fits. The statements and proofs are those of ReadsCount.lean, ReadsCountProof.lean and
BudProof.lean, with the first chain's number 0 turned into the parameter ch; those files and their
names are unchanged. They serve whoever seats the sender at a place of the kind K1 on the shared or
the second chain: the fields bud₂ and bud₃ of the rule's premise BudDebts
(Johnson/Desc/ProofFile/Honest/Law/OwedRule.lean) read treeAsks F ρ 1 and treeAsks F ρ 2. Counting
lemmas: no distribution is named. Not one of the release's goal statements.

Limits. The clause of BudDebts at a row of another chain is not stated here. All limits of
ReadsTestAt.lean.
-/
import Johnson.SendSim.Seat.ReadsTestAt
import Johnson.SendSim.Seat.ReadsCountProof

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc OnBytes.SendSim.At
open Johnson.Prover.Send (shapeAt)

variable {Xi : Type}

/-- The bound on the description's own reads of the trees that the chain number ch sends. -/
def ReadsWithinAt (F : FileDescription Xi) (ch : Nat) (P : K1.Par) (n₀ : Nat) : Prop :=
  ∀ ρ : Draws, ρ.due F = true → ∀ k τ, k < P.sent.size →
    ((Own.treesMade P.codes P.sent).getD {}).tree[k]? = some τ →
    ((shapeAt P k).mainRows ≠ 0 →
      ((treeAsks F ρ ch (n₀ + τ)).map
          (· % 2 ^ (P.codes.base.getD (shapeAt P k).code default).logN)).toFinset.card
        ≤ (P.codes.base.getD (shapeAt P k).code default).r) ∧
    ((shapeAt P k).maskRows ≠ 0 →
      ((treeAsks F ρ ch (n₀ + τ)).map
          (· % 2 ^ (P.codes.mask.getD (shapeAt P k).maskCode default).logN)).toFinset.card
        ≤ (P.codes.mask.getD (shapeAt P k).maskCode default).r)

theorem readsWithinAt_zero (F : FileDescription Xi) (P : K1.Par) (n₀ : Nat) :
    ReadsWithinAt F 0 P n₀ = ReadsWithin F P n₀ := rfl

/-- One chain's rounds read the tree number n of the chain number ch at no more positions than
opensInAt counts. -/
theorem count_chainAt (ch c ft n : Nat) : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    drawsFit ds Rs = true →
    ((readsOf c ft (fun _ _ => none) (fun _ => none) ds Rs).filter fun q =>
      q.src == some (ch, n)).length ≤ opensInAt ch c n ds
  | [], _, _ => by simp [readsOf]
  | _ :: _, [], h => by simp [drawsFit] at h
  | d :: ds, R :: Rs, h => by
    have h' : (drawFit d R && drawsFit ds Rs) = true := h
    rw [Bool.and_eq_true] at h'
    have ih := count_chainAt ch c ft n ds Rs h'.2
    have hp : R.poss.length = d.entry.poss := by
      by_contra hne
      have hb : (R.poss.length == d.entry.poss) = false := by simpa using hne
      have := h'.1
      simp [drawFit, hb] at this
    have hA : ((d.stored.flatMap fun s =>
        (Fmt.listOf ((Fmt.partOf s R.poss).map (· % 2 ^ s.sh.a))).map fun x =>
          (⟨Fmt.storedKey s.item, x, some s.item, none, none, none, s.sh.W⟩ : Read)).filter
        fun q => q.src == some (ch, n)).length ≤ (d.stored.filter fun _ => false).length * 0 :=
      len_flat _ _ _ 0 (fun s => by
        rw [len_filter_const _ _ _ false fun _ => rfl]
        simp) d.stored
    have hB : ((d.opens.flatMap fun o =>
        (Fmt.listOf (R.poss.map (· % 2 ^ o.1.a))).map fun x =>
          (⟨o.1.tree - ft, x, none, some (srcOf c o.2), none, none, o.1.W⟩ : Read)).filter
        fun q => q.src == some (ch, n)).length ≤
        (d.opens.filter fun o => srcOf c o.2 == (ch, n)).length * d.entry.poss :=
      len_flat _ _ _ _ (fun o => by
        rw [len_filter_const _ _ _ (srcOf c o.2 == (ch, n)) fun _ => by simp]
        split
        · exact le_trans (Fmt.listOf_len _) (by rw [List.length_map, hp])
        · exact Nat.le_refl _) d.opens
    show ((_ ++ _ ++ readsOf c ft _ _ ds Rs).filter _).length ≤
      ((d.opens.filter fun o => srcOf c o.2 == (ch, n)).length * d.entry.poss ::
        ds.map fun d =>
          (d.opens.filter fun o => srcOf c o.2 == (ch, n)).length * d.entry.poss).sum
    rw [List.filter_append, List.filter_append, List.length_append, List.length_append,
      List.sum_cons]
    have ih' : ((readsOf c ft (fun _ _ => none) (fun _ => none) ds Rs).filter fun q =>
      q.src == some (ch, n)).length ≤
        (ds.map fun d => (d.opens.filter fun o => srcOf c o.2 == (ch, n)).length *
          d.entry.poss).sum := ih
    rw [Nat.mul_zero] at hA
    exact Nat.add_le_add (by
      have hA0 := Nat.le_zero.1 hA
      exact (Nat.add_le_add (Nat.le_of_eq hA0) hB).trans (by rw [Nat.zero_add])) ih'

/-- The tree number n of the chain number ch is read at no more positions than are sampled for
it. -/
theorem readsCountAt (F : FileDescription Xi) (ρ : Draws) (ch n : Nat) (hρ : ρ.due F = true) :
    (treeAsks F ρ ch n).length ≤ drawnForAt F ch n := by
  simp only [Draws.due, Bool.and_eq_true] at hρ
  unfold treeAsks allBare bareReads drawnForAt
  rw [List.length_map, List.filter_append, List.filter_append, List.length_append,
    List.length_append]
  exact Nat.add_le_add (Nat.add_le_add (count_chainAt ch 0 0 n _ _ hρ.1.1.1)
    (count_chainAt ch 1 0 n _ _ hρ.1.1.2)) (count_chainAt ch 2 _ n _ _ hρ.1.2)

/-- The test implies the bound on the description's own reads. -/
theorem readsWithinAtOf (F : FileDescription Xi) (ch : Nat) (P : K1.Par) (n₀ : Nat)
    (hB : readsWithinAtB F ch P n₀ = true) : ReadsWithinAt F ch P n₀ := by
  intro ρ hρ k τ hk hτ
  have h := List.all_eq_true.1 hB k (List.mem_range.2 hk)
  rw [hτ] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  have hc := readsCountAt F ρ ch (n₀ + τ) hρ
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · exact le_trans (List.toFinset_card_le _) (by
      rw [List.length_map]
      exact le_trans hc (h.1.resolve_left hm))
  · exact le_trans (List.toFinset_card_le _) (by
      rw [List.length_map]
      exact le_trans hc (h.2.resolve_left hm))

/-- The bound on the reads gives the sender's bound on queried positions. -/
theorem budAt_of_readsAt {F : FileDescription Xi} {ch : Nat} {P : K1.Par} {n₀ : Nat}
    (h : ReadsWithinAt F ch P n₀) (ρ : Draws) (hρ : ρ.due F = true) (rs : List Nat) :
    budAt P (asksFrom (treeAsks F ρ ch) rs n₀) := by
  intro k τ hk hτ
  rcases asked_asksFrom (treeAsks F ρ ch) rs n₀ τ with e | e
  · rw [e]
    exact h ρ hρ k τ hk hτ
  · rw [e]
    exact ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩

/-- **Where the test accepts, the positions read of the sending's trees meet the sender's
bound.** -/
theorem budAt_of_testAt {F : FileDescription Xi} {ch : Nat} {P : K1.Par} {n₀ : Nat}
    (hB : readsWithinAtB F ch P n₀ = true) (ρ : Draws) (hρ : ρ.due F = true) (rs : List Nat) :
    budAt P (asksFrom (treeAsks F ρ ch) rs n₀) :=
  budAt_of_readsAt (readsWithinAtOf F ch P n₀ hB) ρ hρ rs

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.readsCountAt
#print axioms OnBytes.SendSim.Seat.readsWithinAtOf
#print axioms OnBytes.SendSim.Seat.budAt_of_readsAt
#print axioms OnBytes.SendSim.Seat.budAt_of_testAt
