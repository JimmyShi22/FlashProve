-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/JoinFresh.lean: the implication that carries fresh from the level of rows to a
Seated side. Spec.rowsFresh and Spec.coinsFresh imply Spec.sendFreshAtP, and so Spec.sendFreshAt. It
claims no property of the protocol: not hiding, not zero knowledge.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean. Limits of the
folder: Johnson/SendSim/Defs.lean.

What this file has.
  sendFreshAtP_of_rows  Proved here. Spec.rowsFresh and Spec.coinsFresh imply Spec.sendFreshAtP,
                        fresh at a Seated side for one address at a time. By what the sender
                        discloses coin by coin (showsAt).
  sendFreshAt_of_rows   Proved here. The same two imply Spec.sendFreshAt. No file uses it:
                        Johnson/SendSim/At/FreshAtMember.lean takes the two steps one by one.
  Spec.coinsFresh       The equation of fresh without what the sender discloses. For all P, ride,
                        books, orders, owners o and addresses p: if the entries that concern p are
                        within the sender's number of coins (WithinAt) and p is clear (SpenderClear;
                        Johnson/SendSim/At/Fresh.lean, "clear"), then over uniform coins the pair
                        (the runs that p spends, the known runs) has the same distribution as when
                        the first is replaced by fresh uniform values, independent of the rest.
                        Statement only; proved as coinsFresh.

Limits. Implications only: their premises are named propositions that this file does not prove, so
it proves no equation between distributions by itself. Spec.coinsFresh speaks only of coins. The
conditions on the book are public. What is proved of them with a coin spent:
Johnson/SendSim/At/Fresh.lean, Limits.

How it fits. Spec.rowsFresh is stated in Johnson/SendSim/At/CutTie.lean, Spec.sendFreshAtP and
Spec.sendFreshAt in Johnson/SendSim/At/Fresh.lean; showsAt is proved in
Johnson/SendSim/At/Shows.lean, coinsFresh in Johnson/SendSim/At/CoinsFresh.lean. Spec.coinsFresh is
what remains of fresh at a job that does not fit its place, where the sender discloses the error
value. Johnson/SendSim/At/FreshAtMember.lean applies sendFreshAtP_of_rows to the theorems rowsFresh
(Johnson/SendSim/At/RowsFresh.lean) and coinsFresh.
-/
import Johnson.SendSim.At.Joins
import Johnson.SendSim.At.CutTie

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc

variable {S Cl V W X Pb : Type}

/-- States the equation of fresh without what the sender discloses. If the entries that concern p
are within the sender's number of coins (WithinAt) and p is clear (SpenderClear), then over uniform
coins the pair (the runs that p spends, the known runs) has the same distribution as when the first
is replaced by fresh uniform values, independent of the rest. Statement only; proved as coinsFresh
in Johnson/SendSim/At/CoinsFresh.lean. -/
def Spec.coinsFresh : Prop :=
  ∀ (P : K1.Par) (ride : Nat → Option Ride) (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr),
    WithinAt P ride Bk ord o p → SpenderClear P ride Bk ord o p →
    (Prob.unif (Cs (dueR P ride))).map (fun c =>
        (cutAll c (Bk.spentBy o p), cutAll c (Bk.knownBy ord o p))) =
      (Prob.unif (CsAll ((Bk.spentBy o p).map Ahead.named) × Cs (dueR P ride))).map fun a =>
        (some a.1, cutAll a.2 (Bk.knownBy ord o p))

/-- Spec.rowsFresh and Spec.coinsFresh imply Spec.sendFreshAtP. The premises are proved as rowsFresh
in Johnson/SendSim/At/RowsFresh.lean and as coinsFresh in Johnson/SendSim/At/CoinsFresh.lean. -/
theorem sendFreshAtP_of_rows (H : Spec.rowsFresh) (H0 : Spec.coinsFresh) : Spec.sendFreshAtP := by
  intro S Cl V W X Pb φ σ J Bk ord p h hW hB u hu sp ca m ds asks hd hb _
  rw [members_seated h, List.mem_singleton] at hu
  subst hu
  rw [rounds_fst h] at hd
  have e : ∀ c : Cs (dueR J.P J.ride), σ.shows φ (memberAt σ J) (c, sp, ca) m ds asks =
      if sendFits J.P J.ride then
        some (shownR J.P J.first J.ride (J.data m.st.input (frontOf m)) ds asks c)
      else none := fun c => showsAt S Cl V W X Pb φ σ J h m ds asks c hd
  show (Prob.unif (Cs (dueR J.P J.ride))).map (fun c =>
      (cutAll c (Bk.spentBy ⟨σ.block.place, 0⟩ p), σ.shows φ (memberAt σ J) (c, sp, ca) m ds asks,
        cutAll c (Bk.knownBy ord ⟨σ.block.place, 0⟩ p))) =
    (Prob.unif (CsAll ((Bk.spentBy ⟨σ.block.place, 0⟩ p).map Ahead.named) ×
        Cs (dueR J.P J.ride))).map fun a =>
      (some a.1, σ.shows φ (memberAt σ J) (a.2, sp, ca) m ds asks,
        cutAll a.2 (Bk.knownBy ord ⟨σ.block.place, 0⟩ p))
  simp only [e]
  by_cases hf : sendFits J.P J.ride = true
  · simp only [hf, if_true]
    have := congrArg (PMF.map fun t => (t.1, some t.2.1, t.2.2))
      (H J.P J.first J.ride (J.data m.st.input (frontOf m)) ds asks Bk ord ⟨σ.block.place, 0⟩ p hf
        (h.draws ds hd).1 (h.draws ds hd).2 hb hW hB)
    rw [PMF.map_comp, PMF.map_comp] at this
    exact this
  · have hf' : sendFits J.P J.ride = false := by simpa using hf
    simp only [hf', Bool.false_eq_true, if_false]
    have := congrArg (PMF.map fun t => (t.1, (none : Option (List Shown)), t.2))
      (H0 J.P J.ride Bk ord ⟨σ.block.place, 0⟩ p hW hB)
    rw [PMF.map_comp, PMF.map_comp] at this
    exact this

/-- Spec.rowsFresh and Spec.coinsFresh imply Spec.sendFreshAt, the field fresh of Good at a Seated
side if the book is clear at the sender (BookClear). The premises are proved as rowsFresh in
Johnson/SendSim/At/RowsFresh.lean and as coinsFresh in Johnson/SendSim/At/CoinsFresh.lean. -/
theorem sendFreshAt_of_rows (H : Spec.rowsFresh) (H0 : Spec.coinsFresh) : Spec.sendFreshAt :=
  sendFreshAt_of_each (sendFreshAtP_of_rows H H0)

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.sendFreshAtP_of_rows
#print axioms OnBytes.SendSim.At.sendFreshAt_of_rows
