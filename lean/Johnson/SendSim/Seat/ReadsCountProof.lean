-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/ReadsCountProof.lean: the proofs of the two statements of ReadsCount.lean,
where each is written out; and so, where the executable test readsWithinB accepts at every split of
the first chain's list at the place a, the rule's clause on queried positions for the sender's row
(sendRow, "our row") at a (BudClause).
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file proves.
  readsCount          Spec.readsCount.
  readsWithinOf       Spec.readsWithinOf.
  budClause_of_test   If readsWithinB F J.P (treesTo F pre) accepts for every way to split
                      F.first.blocksInOrder into pre, a sub-protocol at the place a, and a rest, then
                      BudClause F a J holds.
  count_chain         The step for one chain: what its rounds query of the first chain's tree number
                      n is at most opensIn.
  len_filter_const    Of the image of a list under a function on whose values a test is constant,
                      the test keeps all or nothing.
  len_flat            A bound, member by member, on what a test keeps of a concatenation of lists.

Limits. The test is evaluated at no description in this file, so BudClause is proved at none here.
Where each premise is proved for the release's files: the table of premises in
Johnson/SendSim/Defs.lean. The statements cover only the first chain's trees. They are lemmas on
lists and numbers of the description's declared rounds: no input, no coin and no execution; no
distribution is named.

How it fits. The proofs use Fmt.listOf_len (Fmt/Rules6Laws.lean) and budClause_of_reads
(BudProof.lean). budClause_of_test serves budClause_of_light (ReadsTestTie.lean), and through it
budAtLots (AtDescLots.lean). ReadsCountAt.lean reuses the two lemmas on lists for the other chains.
-/
import Fmt.Rules6Laws
import Johnson.SendSim.Seat.ReadsCount
import Johnson.SendSim.Seat.BudProof

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc OnBytes.SendSim.At
open Johnson.Prover.Send (shapeAt)

/-- Of the image of a list under f, a test p that is constant on the values of f keeps all or
nothing. -/
theorem len_filter_const {α β : Type} (l : List α) (f : α → β) (p : β → Bool) (b : Bool)
    (h : ∀ x, p (f x) = b) : ((l.map f).filter p).length = if b then l.length else 0 := by
  induction l with
  | nil => cases b <;> rfl
  | cons a l ih =>
    rw [List.map_cons, List.filter_cons, h a]
    cases b
    · simpa using ih
    · simpa using ih

/-- If p keeps at most N entries of g o where m o holds, and none elsewhere, it keeps at most
(l.filter m).length * N entries of the concatenation of the lists g o. -/
theorem len_flat {α β : Type} (g : α → List β) (p : β → Bool) (m : α → Bool) (N : ℕ)
    (h : ∀ o, ((g o).filter p).length ≤ if m o then N else 0) :
    ∀ l : List α, ((l.flatMap g).filter p).length ≤ (l.filter m).length * N
  | [] => Nat.zero_le _
  | o :: l => by
    have ih := len_flat g p m N h l
    have ho := h o
    rw [List.flatMap_cons, List.filter_append, List.length_append, List.filter_cons]
    cases hm : m o
    · rw [hm] at ho
      simp only [Bool.false_eq_true, if_false] at ho ⊢
      omega
    · rw [hm] at ho
      simp only [if_true, List.length_cons] at ho ⊢
      rw [Nat.succ_mul]
      omega

/-- One chain: at challenges that its declared rounds can sample (drawsFit), the queries whose
source is the first chain's tree number n are at most opensIn c n ds. -/
theorem count_chain (c ft n : Nat) : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    drawsFit ds Rs = true →
    ((readsOf c ft (fun _ _ => none) (fun _ => none) ds Rs).filter fun q =>
      q.src == some (0, n)).length ≤ opensIn c n ds
  | [], _, _ => by simp [readsOf]
  | _ :: _, [], h => by simp [drawsFit] at h
  | d :: ds, R :: Rs, h => by
    have h' : (drawFit d R && drawsFit ds Rs) = true := h
    rw [Bool.and_eq_true] at h'
    have ih := count_chain c ft n ds Rs h'.2
    have hp : R.poss.length = d.entry.poss := by
      by_contra hne
      have hb : (R.poss.length == d.entry.poss) = false := by simpa using hne
      have := h'.1
      simp [drawFit, hb] at this
    have hA : ((d.stored.flatMap fun s =>
        (Fmt.listOf ((Fmt.partOf s R.poss).map (· % 2 ^ s.sh.a))).map fun x =>
          (⟨Fmt.storedKey s.item, x, some s.item, none, none, none, s.sh.W⟩ : Read)).filter
        fun q => q.src == some (0, n)).length ≤ (d.stored.filter fun _ => false).length * 0 :=
      len_flat _ _ _ 0 (fun s => by
        rw [len_filter_const _ _ _ false fun _ => rfl]
        simp) d.stored
    have hB : ((d.opens.flatMap fun o =>
        (Fmt.listOf (R.poss.map (· % 2 ^ o.1.a))).map fun x =>
          (⟨o.1.tree - ft, x, none, some (srcOf c o.2), none, none, o.1.W⟩ : Read)).filter
        fun q => q.src == some (0, n)).length ≤
        (d.opens.filter fun o => srcOf c o.2 == (0, n)).length * d.entry.poss :=
      len_flat _ _ _ _ (fun o => by
        rw [len_filter_const _ _ _ (srcOf c o.2 == (0, n)) fun _ => by simp]
        split
        · exact le_trans (Fmt.listOf_len _) (by rw [List.length_map, hp])
        · exact Nat.le_refl _) d.opens
    show ((_ ++ _ ++ readsOf c ft _ _ ds Rs).filter _).length ≤
      ((d.opens.filter fun o => srcOf c o.2 == (0, n)).length * d.entry.poss ::
        ds.map fun d => (d.opens.filter fun o => srcOf c o.2 == (0, n)).length * d.entry.poss).sum
    rw [List.filter_append, List.filter_append, List.length_append, List.length_append,
      List.sum_cons]
    have ih' : ((readsOf c ft (fun _ _ => none) (fun _ => none) ds Rs).filter fun q =>
      q.src == some (0, n)).length ≤
        (ds.map fun d => (d.opens.filter fun o => srcOf c o.2 == (0, n)).length *
          d.entry.poss).sum := ih
    rw [Nat.mul_zero] at hA
    exact Nat.add_le_add (by
      have hA0 := Nat.le_zero.1 hA
      exact (Nat.add_le_add (Nat.le_of_eq hA0) hB).trans (by rw [Nat.zero_add])) ih'

/-- Proof of Spec.readsCount (Johnson/SendSim/Seat/ReadsCount.lean), under the premise stated there.
-/
theorem readsCount : Spec.readsCount := by
  intro Xi F ρ n hρ
  simp only [Draws.due, Bool.and_eq_true] at hρ
  unfold treeAsks allBare bareReads drawnFor
  rw [List.length_map, List.filter_append, List.filter_append, List.length_append,
    List.length_append]
  exact Nat.add_le_add (Nat.add_le_add (count_chain 0 0 n _ _ hρ.1.1.1)
    (count_chain 1 0 n _ _ hρ.1.1.2)) (count_chain 2 _ n _ _ hρ.1.2)

/-- Proof of Spec.readsWithinOf (Johnson/SendSim/Seat/ReadsCount.lean): if the test accepts,
ReadsWithin holds. -/
theorem readsWithinOf : Spec.readsWithinOf := by
  intro Xi F P n₀ hB ρ hρ k τ hk hτ
  have h := List.all_eq_true.1 hB k (List.mem_range.2 hk)
  rw [hτ] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  have hc := readsCount Xi F ρ (n₀ + τ) hρ
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · exact le_trans (List.toFinset_card_le _) (by
      rw [List.length_map]
      exact le_trans hc (h.1.resolve_left hm))
  · exact le_trans (List.toFinset_card_le _) (by
      rw [List.length_map]
      exact le_trans hc (h.2.resolve_left hm))

/-- If readsWithinB F J.P (treesTo F pre) accepts for every way to split the first chain's list into
pre, a sub-protocol at the place a and a rest, then BudClause F a J holds. -/
theorem budClause_of_test {Xi V W X Pb : Type} (F : FileDescription Xi) (a : Place) (J : SendJob W X)
    (h : ∀ pre b t, F.first.blocksInOrder = pre ++ b :: t → b.place = a →
      readsWithinB F J.P (treesTo F pre) = true) : BudClause (V := V) (Pb := Pb) F a J :=
  budClause_of_reads F a J fun pre b t hc hb => readsWithinOf Xi F J.P _ (h pre b t hc hb)

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.readsCount
#print axioms OnBytes.SendSim.Seat.readsWithinOf
#print axioms OnBytes.SendSim.Seat.budClause_of_test
