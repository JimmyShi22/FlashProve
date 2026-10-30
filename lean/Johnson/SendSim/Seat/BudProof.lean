-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/BudProof.lean: if the bound on the positions that a description's own rounds
query (ReadsWithin) holds wherever the first chain's list is split at a sub-protocol at the place a,
then the rule's clause on queried positions holds for the sender's row (sendRow, "our row") at a
(BudClause).
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file proves.
  budClause_of_reads  If ReadsWithin F J.P (treesTo F pre) holds for every way to split F.first.blocksInOrder
                      into pre, a sub-protocol at the place a, and a rest, then BudClause F a J
                      holds.
  budAt_of_reads      If ReadsWithin F P n₀ holds, then at every due list of challenges the
                      positions queried of the first chain's trees from number n₀ on (asksFrom) are
                      within the bound budAt P, whatever the rounds' numbers of roots.
  asked_asksFrom      The positions asked (asksFrom tree rs n) τ for tree τ of a part's first round
                      are tree (n + τ), or there are none. The statement does not say which of the
                      two holds where.
  number_zero         A side whose row is one part has no member but number 0.
  treesTo             The number of trees (the description declares one Oracle for each root) that
                      the first chain's declared rounds announce before a given split of its list.

Limits.
An implication only: neither ReadsWithin nor BudClause is proved in this file. ReadsWithin follows
where the executable test readsWithinB accepts (readsWithinOf, ReadsCountProof.lean). Where each
premise is proved for the release's files: the table of premises in Johnson/SendSim/Defs.lean.
BudClause covers only the first chain: the analogue of the clauses bud₂ and bud₃ of BudDebts, for
the two other chains, is not stated for our row (see Bud.lean, Limits).
The lemmas are on lists and numbers: no distribution is named.

How it fits. ReadsWithin and BudClause are in Bud.lean, budAt in Johnson/SendSim/At/Sim.lean.
budClause_of_reads serves budClause_of_test (ReadsCountProof.lean), and through budClause_of_light
(ReadsTestTie.lean) budAtLots (AtDescLots.lean).
-/
import Johnson.SendSim.Seat.Bud

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc OnBytes.SendSim.At
open Johnson.Prover.Send (shapeAt)

variable {Xi V W X Pb : Type}

/-- The positions for tree number τ of a part's first round, among those queried of the trees from
number n on, are the positions of tree number n + τ, or there are none. -/
theorem asked_asksFrom (tree : Nat → List Nat) (rs : List Nat) (n τ : Nat) :
    asked (asksFrom tree rs n) τ = tree (n + τ) ∨ asked (asksFrom tree rs n) τ = [] := by
  cases rs with
  | nil => exact .inr rfl
  | cons r rs =>
    by_cases h : τ < r
    · left
      show ((((List.range r).map fun i => tree (n + i))[τ]?).getD []) = _
      rw [List.getElem?_map, List.getElem?_range h]
      rfl
    · right
      show ((((List.range r).map fun i => tree (n + i))[τ]?).getD []) = _
      rw [List.getElem?_eq_none (by rw [List.length_map, List.length_range]; omega)]
      rfl

/-- If ReadsWithin F P n₀ holds, then at every due list of challenges the positions queried of the
first chain's trees from number n₀ on are within the bound budAt P. -/
theorem budAt_of_reads {F : FileDescription Xi} {P : K1.Par} {n₀ : Nat} (h : ReadsWithin F P n₀)
    (ρ : Draws) (hρ : ρ.due F = true) (rs : List Nat) :
    budAt P (asksFrom (treeAsks F ρ 0) rs n₀) := by
  intro k τ hk hτ
  rcases asked_asksFrom (treeAsks F ρ 0) rs n₀ τ with e | e
  · rw [e]
    exact h ρ hρ k τ hk hτ
  · rw [e]
    exact ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩

/-- A side whose row is one part has no member but number 0. -/
theorem number_zero {S Cl : Type} {σ : Side S Cl V W X Pb} {x : ProofFile.Honest.Part V W X × Sim Pb}
    (h : σ.row = [x]) (u : Member V W X Pb) (hu : u ∈ σ.members) : u.number = 0 := by
  unfold Side.members at hu
  rw [h] at hu
  rw [List.mem_singleton.1 hu]

/-- The number of trees (the description declares one Oracle for each root) that are announced in
the rounds of pre, a start of the first chain's list: so many are announced before the sub-protocol
that follows pre. -/
def treesTo (F : FileDescription Xi) (pre : List (Block F.S₁ F.Cl)) : Nat :=
  (((rowsOfChain F.first.blocksInOrder).take (pre.flatMap (·.rounds)).length).map (·.2.length)).sum

/-- If ReadsWithin F J.P (treesTo F pre) holds for every way to split the first chain's list into
pre, a sub-protocol at the place a and a rest, then BudClause F a J holds. An implication only. -/
theorem budClause_of_reads (F : FileDescription Xi) (a : Place) (J : SendJob W X)
    (h : ∀ pre b t, F.first.blocksInOrder = pre ++ b :: t → b.place = a →
      ReadsWithin F J.P (treesTo F pre)) : BudClause (V := V) (Pb := Pb) F a J := by
  intro Bk A B σ hσ u hu pre t n hcut hn ρ hρ
  have hrow : σ.row = (sendRow (V := V) (Pb := Pb) a J).row := row_of_seated hσ
  have h0 : u.number = 0 := number_zero hrow u hu
  have hn' : n = (pre.flatMap (·.rounds)).length := by
    rw [hn, h0]
    rfl
  show budAt J.P _
  rw [hn']
  exact budAt_of_reads (h pre σ.block t hcut (place_of_seated hσ)) ρ hρ _

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.budAt_of_reads
#print axioms OnBytes.SendSim.Seat.budClause_of_reads
