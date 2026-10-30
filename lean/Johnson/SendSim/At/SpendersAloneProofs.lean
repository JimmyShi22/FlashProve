-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/SpendersAloneProofs.lean: the field fresh needs its premises on the book only at
the addresses that spend something. The proofs of the four statements of
Johnson/SendSim/At/SpendersAlone.lean. It claims no property of the protocol: not hiding, not zero
knowledge.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean. The field fresh at
one address (FreshAtP) is defined in Fresh.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file has. Each theorem X proves Spec.X of SpendersAlone.lean.
  freshIdleAtP       For every side, face, book, order, bound on queried positions and address p: if
                     p has no entry that spends a coin of any member of the side, FreshAtP holds at
                     p. No other premise is needed.
  freshAtOfSpenders  For every side: if FreshAtP holds at every address that has a spending entry on
                     some member's coins, the field fresh holds (FreshAt).
  sendFreshAtSpenders   At a seated side of the sender (Seated, Johnson/SendSim/At/Sim.lean): if, at
                     each address that has a spending entry on the sender's coins, the entries that
                     it spends or knows are within the sender's number of coins (WithinAt) and it
                     meets SpenderClear, the field fresh holds for every set of queried positions
                     within the bound budAt (Johnson/SendSim/At/Sim.lean).
  sendFreshAtSpendersWide   The same under the wider condition SpenderClearAny
                     (Johnson/SendSim/At/FreshWide.lean).

How it fits. Spec.sendFreshAtWide (Johnson/SendSim/At/BookWide.lean) takes BookClearAny, which asks,
among other clauses, that every entry on the sender's coins is within the sender's number of coins,
also where nobody spends. At one seated sender, sendFreshAtSpendersWide needs the premises on the
book only at the addresses that spend something of the sender's coins. The four theorems stand
beside the main statement Spec.fieldsAtLots (Johnson/SendSim/Seat/AtDescLots.lean) and do not change
it: that statement still takes BookClearAny. Meant as steps toward index privacy
(Johnson/WholeKey/Statement.lean); nothing in this folder derives index privacy from them. Not one
of the release's goal statements.

How it is proved. Where an address spends nothing, its list of spent runs is empty. So the spent
part on both sides of the field's equation is the same single value, and the two distributions agree
(nothingSpent, Johnson/SendSim/At/NothingSpent.lean). The other three follow by cases
on whether an address spends, from sendFreshAtP (Johnson/SendSim/At/FreshAtMember.lean) and
sendFreshAtPWide (Johnson/SendSim/At/FreshWideProofs.lean).

Limits.
Where nobody spends, the field fresh says little: its equation compares a distribution with itself.
freshIdleAtP is that remark as a theorem, and it is no evidence that a sender's coins are well used.
"Spends nothing" reads the book's entries. An entry of length 0 that is marked as spent counts as
spending, so at such an address the premises are still asked.
The gain is thin: it is the clause "within the number of coins" at entries that are carried to an
address which spends nothing and is before no spender. That the two differ in this clause alone is
by inspection, not proved.
One sender at a time. All limits of Fresh.lean and FreshWide.lean apply.
-/
import Johnson.SendSim.At.SpendersAlone
import Johnson.SendSim.At.NothingSpent
import Johnson.SendSim.At.FreshAtMember
import Johnson.SendSim.At.FreshWideProofs

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc

/-- At an address without a spending entry on any member's coins, the field fresh holds at that
address. -/
theorem freshIdleAtP : Spec.freshIdleAtP :=
  fun _ _ _ _ _ _ φ σ Bk ord _ p h u hu sp ca m ds asks _ _ _ =>
    nothingSpent u.part.takes _ _ (fun c => σ.shows φ u (c, sp, ca) m ds asks)
      (fun c => cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p)) _ (h u hu)

/-- The field fresh follows from FreshAtP at every address that has a spending entry on some
member's coins. -/
theorem freshAtOfSpenders : Spec.freshAtOfSpenders := by
  intro S Cl V W X Pb φ σ Bk ord bud h
  refine (freshAt_iff_each φ σ Bk ord bud).2 fun p => ?_
  by_cases hp : ∃ u ∈ σ.members, Bk.spentBy ⟨σ.block.place, u.number⟩ p ≠ []
  · exact h p hp
  · refine freshIdleAtP S Cl V W X Pb φ σ Bk ord bud p fun u hu => ?_
    by_contra hne
    exact hp ⟨u, hu, hne⟩

/-- At a seated side of the sender the field fresh holds if the premises on the book hold at each
address that has a spending entry on the sender's coins. -/
theorem sendFreshAtSpenders : Spec.sendFreshAtSpenders := by
  intro S Cl V W X Pb φ σ J Bk ord hS hC
  refine freshAtOfSpenders S Cl V W X Pb φ σ Bk ord _ ?_
  rintro p ⟨u, hu, hne⟩
  rw [members_seated hS, List.mem_singleton] at hu
  subst hu
  have hne' : Bk.spentBy ⟨σ.block.place, 0⟩ p ≠ [] := hne
  exact sendFreshAtP S Cl V W X Pb φ σ J Bk ord p hS (hC p hne').1 (hC p hne').2

/-- The same under the wider condition on a spender. -/
theorem sendFreshAtSpendersWide : Spec.sendFreshAtSpendersWide := by
  intro S Cl V W X Pb φ σ J Bk ord hS hC
  refine freshAtOfSpenders S Cl V W X Pb φ σ Bk ord _ ?_
  rintro p ⟨u, hu, hne⟩
  rw [members_seated hS, List.mem_singleton] at hu
  subst hu
  have hne' : Bk.spentBy ⟨σ.block.place, 0⟩ p ≠ [] := hne
  exact sendFreshAtPWide S Cl V W X Pb φ σ J Bk ord p hS (hC p hne').1 (hC p hne').2

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.freshIdleAtP
#print axioms OnBytes.SendSim.At.freshAtOfSpenders
#print axioms OnBytes.SendSim.At.sendFreshAtSpenders
#print axioms OnBytes.SendSim.At.sendFreshAtSpendersWide
