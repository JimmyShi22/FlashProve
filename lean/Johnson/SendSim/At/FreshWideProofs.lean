-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/FreshWideProofs.lean: the equation of rowsFresh holds, under its first five
premises, also where the address p spends all coefficients of a table of any number of rows that is
sent along, if no spent coin and no tail coin of that table is known at p. It claims no property of
the protocol: not hiding, not zero knowledge. The proofs of Spec.rowsFreshAny and of the three
statements of Johnson/SendSim/At/FreshWide.lean.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean. Limits of the
folder: Johnson/SendSim/Defs.lean.

What this file proves. "The five premises" are the first five of rowsFresh: the job fits its place
(sendFits); the challenge consists of exactly the seeds (seedsFit); no seed's factor is 0; the
queried positions are within the bound (budAt); the entries that concern p are within the sender's
number of coins (WithinAt). "The equation" is that of rowsFresh: over the sender's uniform coins,
the tuple (the runs that p spends, shownR, the known runs) has the distribution in which the runs
that p spends are replaced by fresh uniform values, independent of the rest.
  rowsFreshAny      Under the five premises, if p satisfies FoldSpenderAny, the equation holds.
                    FoldSpenderAny is FoldSpender without the clause "the table has one row": p
                    spends, by one entry, all coefficients of one table that is sent along; no spent
                    coin is known; no tail coin of any row of that table is known.
  rowsFreshWide     Under the five premises, if p is clear in the wider sense (SpenderClearAny: p
                    spends nothing, or MaskSpender, or FoldSpenderAny), the equation holds.
  coinsFreshWide    Under WithinAt and SpenderClearAny alone, the same equation without the middle
                    component: it speaks of the spent and the known runs, and of nothing that the
                    sender discloses.
  sendFreshAtPWide  At every Seated side, under WithinAt and SpenderClearAny at the address p, the
                    field fresh holds at p (FreshAtP), with the bound budAt.

Limits.
  - Where the condition on the book is proved, and where each premise is proved for the release's
    files: the table of premises in Johnson/SendSim/Defs.lean.
  - Each statement speaks of one owner and one spender.
  - The spender's own use of the coins is not covered: in the table a coefficient can be at several
    entries, and what the spender then discloses is not analysed here.
  - Nothing is said on what a later part makes of the spent coins.
  - The limits of the folder, in short (in full: Johnson/SendSim/Defs.lean). The theorems are about
    sub-protocols of the kind K1 alone; K2 and K12 send tables too. The honest sender is a
    definition in Lean, connected with no program. Nothing is hashed, and challenges and queried
    positions are fixed in advance. The data are a free variable, connected with the weights by no
    theorem. The premises are public. Each statement is of one execution: one proof of one request.
    None of them is one of the release's goal statements.

How it fits. The statements: Spec.rowsFreshAny and FoldSpenderAny in
Johnson/SendSim/At/FoldAny.lean, the other three and SpenderClearAny in
Johnson/SendSim/At/FreshWide.lean. rowsFreshAny is one application of rowsFreshAny_of_core
(Johnson/SendSim/At/FoldAnyRoad.lean). rowsFreshWide is by cases, from rowsFresh and rowsFreshAny.
In coinsFreshWide two cases are coinsFresh's (Johnson/SendSim/At/CoinsFresh.lean); the third uses
the same lemma on runs of coins (runs_apart, Johnson/SendSim/At/WriteAll.lean).
Johnson/SendSim/At/BookWide.lean states the field fresh under the wider condition at all addresses
(BookClearAny), and the structure Good as one term, whose fields plays and acc hold there vacuously.
Johnson/SendSim/Seat/HandedWideProofs.lean proves both (sendFreshAtWide, goodSeatedWide).
-/
import Johnson.SendSim.At.FreshWide
import Johnson.SendSim.At.FoldAnyRoad
import Johnson.SendSim.At.RowsFresh
import Johnson.SendSim.At.CoinsFresh

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc

/-- Under the first five premises of Spec.rowsFresh, its equation holds where p spends the
coefficients of a table of any number of rows that is sent along (FoldSpenderAny). -/
theorem rowsFreshAny : Spec.rowsFreshAny := rowsFreshAny_of_core sendFresh readUnif

/-- Under the first five premises of Spec.rowsFresh, its equation holds where p is clear in the
wider sense (SpenderClearAny). -/
theorem rowsFreshWide : Spec.rowsFreshWide := rowsFreshWide_of rowsFresh rowsFreshAny

/-- If the entries that concern p are within the sender's number of coins (WithinAt) and p is clear
in the wider sense (SpenderClearAny), then over uniform coins the runs that p spends are uniform and
independent of the known runs. Nothing that the sender discloses is in this equation. -/
theorem coinsFreshWide : Spec.coinsFreshWide := by
  intro P ride Bk ord o p hW hC
  rcases hC with h0 | hM | hF
  · exact coinsFresh P ride Bk ord o p hW (Or.inl h0)
  · exact coinsFresh P ride Bk ord o p hW (Or.inr (Or.inl hM))
  · refine runs_apart (Bk.spentBy o p) (Bk.knownBy ord o p) (fun e he => hW e (.inl he))
      (apart_any hF) hF.unknown ?_
    obtain ⟨_, R, e, _, _, hsp, hc, _⟩ := hF.one
    have h0 : fAll (Bk.spentBy o p) = ∅ := by
      rw [hsp]
      simp [fAll, fOf, hc]
    rw [h0]
    exact Finset.disjoint_empty_left _

/-- At every Seated side, under WithinAt and SpenderClearAny at the address p, the field fresh holds
at p, with the bound budAt. -/
theorem sendFreshAtPWide : Spec.sendFreshAtPWide :=
  sendFreshAtPWide_of_rows rowsFreshWide coinsFreshWide

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.rowsFreshAny
#print axioms OnBytes.SendSim.At.rowsFreshWide
#print axioms OnBytes.SendSim.At.coinsFreshWide
#print axioms OnBytes.SendSim.At.sendFreshAtPWide
