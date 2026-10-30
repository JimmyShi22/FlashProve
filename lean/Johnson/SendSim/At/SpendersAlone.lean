-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/SpendersAlone.lean: four statements that the field fresh of Good needs its
conditions on the book only at the addresses that spend something. It claims no property of the
protocol: not hiding, not zero knowledge.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean. Limits of the
folder: Johnson/SendSim/Defs.lean.

What this file has. Four named propositions. Each is a statement only, proved under the same name
without "Spec." in Johnson/SendSim/At/SpendersAloneProofs.lean.
  Spec.freshIdleAtP   For every side, face, book, order, bound bud and address p: if p spends
                      nothing of any member's coins, the field fresh at p (FreshAtP) holds. There is
                      no other premise on the book, and none on the part, the challenges or the
                      positions.
  Spec.freshAtOfSpenders   For every side: if FreshAtP holds at every address that spends something
                      of some member's coins, the field fresh holds (FreshAt).
  Spec.sendFreshAtSpenders   For the honest sender: if the side is Seated and SpendersClear holds,
                      the side has the field fresh, with the bound budAt. SpendersClear says: at
                      each address that spends something of the sender's coins, the entries that
                      concern it are within the sender's number of coins (WithinAt) and it is clear
                      (SpenderClear).
  Spec.sendFreshAtSpendersWide   The same with SpendersClearAny, which has the wider condition
                      SpenderClearAny in the place of SpenderClear.
Proved here, by definition or on premises only:
  freshIdleAtP_reads  Spec.freshIdleAtP is equivalent to its form with the field's equation written
                      out, by Iff.rfl.
  spendersClear_reads   SpendersClear with SpenderClear written out, by Iff.rfl.
  spendersClear_of_bookClear   BookClear implies SpendersClear. So Spec.sendFreshAtSpenders requires
                      no more of the book than Spec.sendFreshAt does.

Limits.
No equation between distributions is proved in this file.
"Spends nothing" reads the book's entries (ProverCoinCounts.spentBy, Johnson/Desc/ProofFile/Honest/Frame.lean):
owner, spender and the mark "spent". An address to which coins are only carried spends nothing. At
such an address fresh says nothing about what is known there: the first component of its triple has
one value only.
The conditions on the book are public. What is proved of them with a coin spent:
Johnson/SendSim/At/Fresh.lean, Limits.
There is one owner: nothing is said on the runs of two owners together.
All limits of Johnson/SendSim/At/Fresh.lean and Johnson/SendSim/At/FreshWide.lean hold here too.

How it fits. Spec.sendFreshAtP (Johnson/SendSim/At/Fresh.lean) gives fresh address by address, under
conditions on the book at that address. Spec.sendFreshAt gives the field under BookClear, which
requires these conditions of every address and of every entry of the owner. At an address that
spends nothing of the owner's coins, the runs that are replaced by fresh values are the runs of the
empty list, which have one value. So the conditions are required at the addresses that spend
something, and at no other. That SpendersClear can hold where BookClear fails is shown by nothing
here. SpendersClearAny is used at the description (Johnson/SendSim/Seat/AtDescLotsSpenders.lean).

Notes: related lemmas. "Where the list of entries is empty the two distributions are equal", for any
number of coins and any two functions of them, is nothingSpent
(Johnson/SendSim/At/NothingSpent.lean); the framework has fresh_of_nil
(Johnson/Desc/ProofFile/Honest/Law/ToyLaw.lean). The first two statements are stated for every face
and all types: a sending in the shared chain, one of a description's three chains, has the face
.shared and another type of input.
-/
import Johnson.SendSim.At.FreshWide

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc

/-- States that, for every side, face, book, order and bound, the field fresh at an address p
(FreshAtP) holds if p spends nothing of any member's coins. Statement only; proved as freshIdleAtP
in Johnson/SendSim/At/SpendersAloneProofs.lean. -/
def Spec.freshIdleAtP : Prop :=
  ∀ (S Cl V W X Pb : Type) (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (Bk : ProverCoinCounts)
    (ord : List Place) (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (p : Addr),
    (∀ u ∈ σ.members, Bk.spentBy ⟨σ.block.place, u.number⟩ p = []) →
    FreshAtP φ σ Bk ord bud p

/-- States that the field fresh (FreshAt) holds if FreshAtP holds at every address that spends
something of some member's coins. Statement only; proved as freshAtOfSpenders in
Johnson/SendSim/At/SpendersAloneProofs.lean. -/
def Spec.freshAtOfSpenders : Prop :=
  ∀ (S Cl V W X Pb : Type) (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (Bk : ProverCoinCounts)
    (ord : List Place) (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop),
    (∀ p, (∃ u ∈ σ.members, Bk.spentBy ⟨σ.block.place, u.number⟩ p ≠ []) →
      FreshAtP φ σ Bk ord bud p) →
    FreshAt φ σ Bk ord bud

/-- The condition on the book at an owner o, required only at the spenders: at each address that
spends something of o's coins, WithinAt and SpenderClear hold. -/
def SpendersClear (P : K1.Par) (ride : Nat → Option Ride) (Bk : ProverCoinCounts) (ord : List Place)
    (o : Addr) : Prop :=
  ∀ p, Bk.spentBy o p ≠ [] → WithinAt P ride Bk ord o p ∧ SpenderClear P ride Bk ord o p

/-- The condition on the book at an owner o, required only at the spenders, in its wider form: at
each address that spends something of o's coins, WithinAt and SpenderClearAny hold. -/
def SpendersClearAny (P : K1.Par) (ride : Nat → Option Ride) (Bk : ProverCoinCounts) (ord : List Place)
    (o : Addr) : Prop :=
  ∀ p, Bk.spentBy o p ≠ [] → WithinAt P ride Bk ord o p ∧ SpenderClearAny P ride Bk ord o p

/-- States that a Seated side has the field fresh of Good, with the bound budAt, if SpendersClear
holds at the sender. Statement only; proved as sendFreshAtSpenders in
Johnson/SendSim/At/SpendersAloneProofs.lean. -/
def Spec.sendFreshAtSpenders : Prop :=
  ∀ (S Cl V W X Pb : Type) (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : SendJob W X) (Bk : ProverCoinCounts)
    (ord : List Place), Seated σ J → SpendersClear J.P J.ride Bk ord ⟨σ.block.place, 0⟩ →
    FreshAt φ σ Bk ord fun _ _ asks => budAt J.P asks

/-- States that a Seated side has the field fresh of Good, with the bound budAt, if SpendersClearAny
holds at the sender. Statement only; proved as sendFreshAtSpendersWide in
Johnson/SendSim/At/SpendersAloneProofs.lean. -/
def Spec.sendFreshAtSpendersWide : Prop :=
  ∀ (S Cl V W X Pb : Type) (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : SendJob W X) (Bk : ProverCoinCounts)
    (ord : List Place), Seated σ J → SpendersClearAny J.P J.ride Bk ord ⟨σ.block.place, 0⟩ →
    FreshAt φ σ Bk ord fun _ _ asks => budAt J.P asks

/-- Spec.freshIdleAtP is equivalent, by definition, to its form with the equation of the field fresh
at p written out. -/
theorem freshIdleAtP_reads : Spec.freshIdleAtP ↔
    ∀ (S Cl V W X Pb : Type) (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (Bk : ProverCoinCounts)
      (ord : List Place) (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (p : Addr),
      (∀ u ∈ σ.members, Bk.spentBy ⟨σ.block.place, u.number⟩ p = []) →
      ∀ u ∈ σ.members, ∀ sp ca m ds asks,
        drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
        u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid →
        (Prob.unif (Cs u.part.takes)).map (fun c =>
            (cutAll c (Bk.spentBy ⟨σ.block.place, u.number⟩ p), σ.shows φ u (c, sp, ca) m ds asks,
              cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))) =
          (Prob.unif (CsAll ((Bk.spentBy ⟨σ.block.place, u.number⟩ p).map Ahead.named) ×
              Cs u.part.takes)).map fun a =>
            (some a.1, σ.shows φ u (a.2, sp, ca) m ds asks,
              cutAll a.2 (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p)) :=
  Iff.rfl

/-- SpendersClear is equivalent, by definition, to its form with SpenderClear written out. -/
theorem spendersClear_reads (P : K1.Par) (ride : Nat → Option Ride) (Bk : ProverCoinCounts) (ord : List Place)
    (o : Addr) : SpendersClear P ride Bk ord o ↔
      ∀ p, Bk.spentBy o p ≠ [] → WithinAt P ride Bk ord o p ∧
        (Bk.spentBy o p = [] ∨ MaskSpender P ride Bk ord o p ∨ FoldSpender P ride Bk ord o p) :=
  Iff.rfl

/-- BookClear implies SpendersClear. A lemma on premises only: no distribution is named. -/
theorem spendersClear_of_bookClear {P : K1.Par} {ride : Nat → Option Ride} {Bk : ProverCoinCounts}
    {ord : List Place} {o : Addr} (h : BookClear P ride Bk ord o) :
    SpendersClear P ride Bk ord o :=
  fun p _ => ⟨withinAt_of_takes h.1 ord p, h.2 p⟩

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.freshIdleAtP_reads
#print axioms OnBytes.SendSim.At.spendersClear_reads
#print axioms OnBytes.SendSim.At.spendersClear_of_bookClear
