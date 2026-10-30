-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/BudCount.lean: HOW LONG THE FRAME's LIST OF THE POSITIONS READ OF
A TREE IS, AT ONE REQUEST's CHALLENGES, HELD AGAINST THE LIBRARY's COUNT OF THE DECLARED ROUNDS:
general in the IOP as written in Lean (below: the description F), the chain ch and the tree's number
k in that chain. No kind is named. Counting lemmas on public numbers: no distribution, no coin, no
input. Statements with their proofs; no definition.

Two counts lie, each in a file of its own, and nothing tied them:
  drawnForAt F ch k   (Johnson/SendSim/Seat/ReadsTestAt.lean) adds up, over the three chains'
                  declared rounds, each round's number of sampled positions once for each opening
                  whose SOURCE is the k-th tree that the chain ch sends. readsCountAt
                  (Johnson/SendSim/Seat/ReadsCountAt.lean): at every due list of challenges the
                  frame's treeAsks F ρ ch k (Honest/Law/Rule/Bare.lean) is no longer than that
  (declOpens F).inBatch N j   (E2E/TreeReads.lean, E2E/TreeReadsDeclared.lean) adds up the same
                  numbers once for each opening whose NUMBER OVER THE FILE is j; at a tree of the
                  shared chain: that chain's rounds once and the other two chains' N times

  filter_le_count   in one list: as many members as pass a test, at most so many have the value j
                  under a function that sends all who pass to j
  numAt_of_src    an opening whose source is (ch, k) has the number treeNo F ch k over the file
  opensInAt_le    one chain's declared rounds: the first count is at most the second
  drawnForAt_le   the three chains', the first chain's rounds taken whole
  drawnForAt_inBatch   **drawnForAt F ch k ≤ (declOpens F).inBatch 1 (treeNo F ch k)**, where the
                  library makes the rounds' data of the description (F.data file = .ok D): the
                  first chain's last declared round, which the library's count leaves out, samples
                  no position there (readsOn_first_whole)
  asks_inBatch    **so the frame's treeAsks F ρ ch k is no longer than that**: the half that the
                  head of E2E/TreeReadsDeclared.lean names as not shown there

Only "at most": treeNo is not shown to be injective, and an upper bound wants no more.
What is not claimed. N = 1: ONE REQUEST's CHALLENGES. Nothing on the union of the positions that the
requests of a batch read. treeAsks is computed off the declared rounds and the challenges: no input,
no coin, no run: THAT A RUN ASKS FOR NO POSITION BEYOND WHAT THAT LIST HOLDS is not said here.
Nothing on any property.
-/
import Johnson.SendSim.Seat.ReadsCountAt
import E2E.TreeReadsDeclared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (FileDescription numAt)
open OnBytes.SendSim.Seat (opensInAt drawnForAt readsCountAt)
open AtPublicFiles.TreeReads (readsOn readsOn_cons declPairs declOpens treeNo readsOn_first_whole)

variable {Xi : Type}

/-- As many members as pass a test, at most so many have the value j under a function that sends
all who pass to j. -/
theorem filter_le_count {α : Type} (l : List α) (p : α → Bool) (f : α → Nat) (j : Nat)
    (h : ∀ x ∈ l, p x = true → f x = j) : (l.filter p).length ≤ (l.map f).count j := by
  rw [← List.countP_eq_length_filter, List.count, List.countP_map]
  exact List.countP_mono_left fun x hx hp => by
    show (f x == j) = true
    rw [h x hx hp]
    exact beq_self_eq_true _

/-- An opening whose source is the k-th tree of the chain ch has that tree's number over the
file. -/
theorem numAt_of_src (t₁ t₂ c ch k : Nat) (s : Fmt.TreeSource) (h : (srcOf c s == (ch, k)) = true) :
    numAt t₁ t₂ c s = numAt t₁ t₂ ch (.own k) := by
  have e := beq_iff_eq.1 h
  cases s with
  | own n =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    rfl
  | taken c' n =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    rfl

/-- One chain's declared rounds. -/
theorem opensInAt_le (t₁ t₂ ch c k : Nat) : ∀ ds : List Fmt.DeclaredRound,
    opensInAt ch c k ds ≤ readsOn (declPairs t₁ t₂ c ds) (numAt t₁ t₂ ch (.own k))
  | [] => Nat.le_refl _
  | d :: ds => by
    have ih := opensInAt_le t₁ t₂ ch c k ds
    have h1 : (d.opens.filter fun o => srcOf c o.2 == (ch, k)).length ≤
        (d.opens.map fun o => numAt t₁ t₂ c o.2).count (numAt t₁ t₂ ch (.own k)) :=
      filter_le_count _ _ _ _ fun o _ ho => numAt_of_src t₁ t₂ c ch k o.2 ho
    show (d.opens.filter fun o => srcOf c o.2 == (ch, k)).length * d.entry.poss +
        opensInAt ch c k ds ≤
      readsOn ((d.entry.poss, d.opens.map fun o => numAt t₁ t₂ c o.2) :: declPairs t₁ t₂ c ds)
        (numAt t₁ t₂ ch (.own k))
    rw [readsOn_cons, Nat.mul_comm]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ h1) ih

/-- The three chains' declared rounds, the first chain's taken whole. -/
theorem drawnForAt_le (F : FileDescription Xi) (ch k : Nat) :
    drawnForAt F ch k ≤ readsOn (declPairs F.t₁ F.t₂ 0 F.roundsDeclaredByBlocks.1) (treeNo F ch k) +
      readsOn (declPairs F.t₁ F.t₂ 1 F.roundsDeclaredByBlocks.2.1) (treeNo F ch k) +
      readsOn (declPairs F.t₁ F.t₂ 2 F.roundsDeclaredByBlocks.2.2) (treeNo F ch k) :=
  Nat.add_le_add
    (Nat.add_le_add (opensInAt_le F.t₁ F.t₂ ch 0 k _) (opensInAt_le F.t₁ F.t₂ ch 1 k _))
    (opensInAt_le F.t₁ F.t₂ ch 2 k _)

/-- **The count by sources is at most the library's count by numbers**, in a batch of one
request. -/
theorem drawnForAt_inBatch {F : FileDescription Xi} {file : String} {D : OnBytes.Maker.WholeD}
    (h : F.data file = .ok D) (ch k : Nat) :
    drawnForAt F ch k ≤ (declOpens F).inBatch 1 (treeNo F ch k) := by
  have h1 := drawnForAt_le F ch k
  rw [readsOn_first_whole h] at h1
  have h2 : readsOn (declPairs F.t₁ F.t₂ 1 F.roundsDeclaredByBlocks.2.1) (treeNo F ch k) =
      readsOn (declOpens F).shared (treeNo F ch k) := rfl
  have h3 : readsOn (declPairs F.t₁ F.t₂ 2 F.roundsDeclaredByBlocks.2.2) (treeNo F ch k) =
      readsOn (declOpens F).second (treeNo F ch k) := rfl
  rw [h2, h3] at h1
  unfold AtPublicFiles.TreeReads.Opens.inBatch
  split <;> omega

/-- **At every due list of challenges the frame's list of the positions read of a tree is no longer
than the library's count in a batch of one request.** -/
theorem asks_inBatch {F : FileDescription Xi} {file : String} {D : OnBytes.Maker.WholeD}
    (h : F.data file = .ok D) (ρ : Draws) (hρ : ρ.due F = true) (ch k : Nat) :
    (treeAsks F ρ ch k).length ≤ (declOpens F).inBatch 1 (treeNo F ch k) :=
  Nat.le_trans (readsCountAt F ρ ch k hρ) (drawnForAt_inBatch h ch k)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.filter_le_count
#print axioms ProofFile.Honest.K14.numAt_of_src
#print axioms ProofFile.Honest.K14.opensInAt_le
#print axioms ProofFile.Honest.K14.drawnForAt_le
#print axioms ProofFile.Honest.K14.drawnForAt_inBatch
#print axioms ProofFile.Honest.K14.asks_inBatch
