-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/ClearOf.lean: from the numbers of the coins in a book's entries to sets of names
of the instance's coins; and three statements that, under three public premises, the conditions
MaskSpender and FoldSpender on a book imply the general model's conditions on the spent and the
known coins.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean; for MendsOff,
Johnson/SendSim/Defs.lean; sender, wOf, name, number: Johnson/SendSim/At/Bridge.lean. Limits of the
folder: Johnson/SendSim/Defs.lean.

What this file has. Definitions and statements only. The statements speak of sets of names and of
contributions; no distribution is named. Each has three premises in common: the job fits its place
(sendFits), the challenge consists of exactly the seeds (seedsFit), and no seed's factor is 0.
MaskSpender and FoldSpender are two of the three cases of SpenderClear
(Johnson/SendSim/At/Fresh.lean, "clear").
  Spec.mendsOffOf  If also MaskSpender or FoldSpender holds at the owner o and the address p, then
                   the model's premise MendsOff holds at the weights wOf and the sets spentN, knownN
                   and knownT. Statement only; proved as mendsOffOf.
  Spec.clearOfMask   If also MaskSpender holds, there are pads of the instance at which the three
                   sets satisfy the model's condition Sender.Clear. Statement only; proved as
                   clearOfMask.
  Spec.clearOfFold   The same with FoldSpender. Statement only; proved as clearOfFold.
  spentN, knownN, knownT   for a book, an order, an owner o and an address p: the names of the
                   message coins that p spends; of the known message coins; of the known tail coins.

Limits. The conditions on the book are public. What is proved of them with a coin spent:
Johnson/SendSim/At/Fresh.lean, Limits.

How it fits. clearOfMask is proved in Johnson/SendSim/At/ClearOfMask.lean, clearOfFold and
mendsOffOf in Johnson/SendSim/At/ClearOfFold.lean. Sender.Clear is defined in
Johnson/SendSim/Pads.lean; it is another condition than "clear" of Johnson/SendSim/At/Fresh.lean.
Johnson/SendSim/At/JoinRows.lean uses mendsOffOf as the premise MendsOff of sendFresh, for rowsFresh
(Johnson/SendSim/At/RowsFresh.lean). Johnson/SendSim/At/CutTie.lean states, and
Johnson/SendSim/At/CutProof.lean proves, how cutAll at the book's entries is connected with the
instance's coins in these sets.

The other names.
  inNos            a coin, given by its field and number, is in a pair of sets of numbers, one set
                   for each field.
  namesOf, tailsOf   the names in CoinN, and in TailN, of the coins whose numbers are in such a
                   pair. A coin of the extension field is in them with all three coordinates.

Notes. Why the statements say "there are pads at which". Spec.padsOf
(Johnson/SendSim/At/Bridge.lean) states only that pads exist, and Sender.Clear speaks of the pads
themselves. So each statement binds its own pads; the proofs take the pads at the slots padSeat
(Johnson/SendSim/At/PadSeat.lean).
-/
import Johnson.SendSim.At.Fresh
import Johnson.SendSim.At.Onto

set_option autoImplicit false

noncomputable section

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)

/-- A coin, given by its field (e = true: the extension field) and its number n, is in the pair of
sets of numbers NE and NF. -/
def inNos (NE NF : Finset ℕ) (e : Bool) (n : ℕ) : Prop := if e then n ∈ NE else n ∈ NF

variable (P : K1.Par) (ride : Nat → Option Ride)

open Classical in
/-- The names of the message coins whose numbers are in the pair NE, NF. -/
def namesOf (NE NF : Finset ℕ) : Finset (CoinN P ride) :=
  Finset.univ.filter fun n =>
    inNos NE NF ((seatC P ride n).1.inE (shapeAt P n.1)) ((seatC P ride n).1.no P ride n.1)

open Classical in
/-- The names of the tail coins whose numbers are in the pair NE, NF. -/
def tailsOf (NE NF : Finset ℕ) : Finset (TailN P) :=
  Finset.univ.filter fun x =>
    inNos NE NF ((seatT P x.1 x.2.val).1.inE (shapeAt P x.1.1))
      ((seatT P x.1 x.2.val).1.no P ride x.1.1)

variable (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr)

/-- The names of the message coins of the owner o that the address p spends. -/
def spentN : Finset (CoinN P ride) := namesOf P ride (eAll (Bk.spentBy o p)) (fAll (Bk.spentBy o p))

/-- The names of the message coins of the owner o that are known at p. -/
def knownN : Finset (CoinN P ride) :=
  namesOf P ride (eAll (Bk.knownBy ord o p)) (fAll (Bk.knownBy ord o p))

/-- The names of the tail coins of the owner o that are known at p. -/
def knownT : Finset (TailN P) :=
  tailsOf P ride (eAll (Bk.knownBy ord o p)) (fAll (Bk.knownBy ord o p))

/-- If the job fits its place (sendFits), the challenge consists of exactly the seeds (seedsFit), no
seed's factor is 0 and MaskSpender holds at o and p, then there are pads of the instance at which
spentN, knownN and knownT satisfy Sender.Clear. Statement only; proved as clearOfMask in
Johnson/SendSim/At/ClearOfMask.lean. -/
def Spec.clearOfMask : Prop :=
  ∀ (P : K1.Par) (ride : Nat → Option Ride) (ds : List Fmt.Drawn) (Bk : ProverCoinCounts) (ord : List Place)
    (o p : Addr), sendFits P ride = true → seedsFit P ds = true →
    (∀ s ∈ seedsAt P ds, readE s.2 ≠ 0) → MaskSpender P ride Bk ord o p →
    ∃ Pd : (sender P ride).Pads (wOf P ds),
      (sender P ride).Clear (wOf P ds) Pd (spentN P ride Bk o p) (knownN P ride Bk ord o p)
        (knownT P ride Bk ord o p)

/-- The same as Spec.clearOfMask with FoldSpender in place of MaskSpender. Statement only; proved as
clearOfFold in Johnson/SendSim/At/ClearOfFold.lean. -/
def Spec.clearOfFold : Prop :=
  ∀ (P : K1.Par) (ride : Nat → Option Ride) (ds : List Fmt.Drawn) (Bk : ProverCoinCounts) (ord : List Place)
    (o p : Addr), sendFits P ride = true → seedsFit P ds = true →
    (∀ s ∈ seedsAt P ds, readE s.2 ≠ 0) → FoldSpender P ride Bk ord o p →
    ∃ Pd : (sender P ride).Pads (wOf P ds),
      (sender P ride).Clear (wOf P ds) Pd (spentN P ride Bk o p) (knownN P ride Bk ord o p)
        (knownT P ride Bk ord o p)

/-- If the job fits its place (sendFits), the challenge consists of exactly the seeds (seedsFit), no
seed's factor is 0, and MaskSpender or FoldSpender holds at o and p, then Sender.MendsOff holds at
the weights wOf and the sets spentN, knownN and knownT. Statement only; proved as mendsOffOf in
Johnson/SendSim/At/ClearOfFold.lean. -/
def Spec.mendsOffOf : Prop :=
  ∀ (P : K1.Par) (ride : Nat → Option Ride) (ds : List Fmt.Drawn) (Bk : ProverCoinCounts) (ord : List Place)
    (o p : Addr), sendFits P ride = true → seedsFit P ds = true →
    (∀ s ∈ seedsAt P ds, readE s.2 ≠ 0) →
    MaskSpender P ride Bk ord o p ∨ FoldSpender P ride Bk ord o p →
    (sender P ride).MendsOff (wOf P ds) (spentN P ride Bk o p) (knownN P ride Bk ord o p)
      (knownT P ride Bk ord o p)

end OnBytes.SendSim.At
