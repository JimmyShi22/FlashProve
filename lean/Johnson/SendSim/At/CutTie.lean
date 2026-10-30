-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/CutTie.lean: the statement Spec.rowsFresh, the field fresh at the level of rows
under six public premises; and three statements that connect cutAll at a book's entries with the
instance's coins in the sets of names of Johnson/SendSim/At/ClearOf.lean. It claims no property of
the protocol: not hiding, not zero knowledge.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean; for cut and cutT,
Johnson/SendSim/Defs.lean; sender, readC, name: Johnson/SendSim/At/Bridge.lean. Limits of the
folder: Johnson/SendSim/Defs.lean.

What this file has. Statements only; each is proved under the same name without "Spec.".
  Spec.rowsFresh  For all P, first, ride, data, challenges, queried positions, every book and order,
                  an address o (the owner; in use, the sender's) and one address p, under six public
                  premises. (1) The job fits its place (sendFits). (2) The challenge consists of
                  exactly the seeds (seedsFit). (3) No seed's factor is 0. (4) The queried positions
                  are within the bound (budAt). (5) The entries by which p spends and the known
                  entries are within the sender's number of coins (WithinAt). (6) p is clear
                  (SpenderClear; Johnson/SendSim/At/Fresh.lean, "clear"). Then, over the sender's
                  uniform coins, the tuple (the runs that p spends, shownR, the known runs) has the
                  distribution in which the runs that p spends are replaced by fresh uniform values,
                  independent of the rest.
  SpentBack       A property of a function back, from values at the names in spentN to the runs that
                  p spends: for all coins c of the sender, cutAll c at the entries by which p spends
                  is back applied to the instance's coins readC c in spentN.
  Spec.spentTie   If the job fits its place, WithinAt holds, and MaskSpender or FoldSpender holds at
                  o and p, there is a function with SpentBack. It holds for each value of the coins.
  Spec.spentUnif  Under the same premises, every function with SpentBack maps the uniform
                  distribution on the values at spentN to the uniform distribution on the runs. It
                  speaks only of distributions of coins: it names no message, symbol or answer of a
                  sender.
  Spec.knownTie   With no premise: cutAll c at the known entries is one function, the same for all
                  c, of the instance's coins readC c in knownN and knownT.

Limits.
  - Spec.rowsFresh speaks of one owner's runs at one spender. Of the runs of two owners together it
    says nothing.
  - The conditions on the book are public. What is proved of them with a coin spent:
    Johnson/SendSim/At/Fresh.lean, Limits.
  - The other limits of Spec.rowsFresh are in the head of Johnson/SendSim/At/RowsFresh.lean.

How it fits. rowsFresh is proved in Johnson/SendSim/At/RowsFresh.lean, spentTie and knownTie in
Johnson/SendSim/At/CutProof.lean, spentUnif in Johnson/SendSim/At/SpentUnif.lean. For an address
with MaskSpender or FoldSpender, Johnson/SendSim/At/JoinRows.lean applies the model's theorem
sendFresh (Johnson/SendSim/CoreProofs.lean) to the instance; its premises follow from those of
Spec.rowsFresh (withinOf, Johnson/SendSim/At/Within.lean; mendsOffOf,
Johnson/SendSim/At/ClearOfFold.lean). With readUnif and shownTie, the three statements on cutAll
carry its conclusion over to Spec.rowsFresh. The first case of SpenderClear, an address that spends
nothing, is nothingSpent (Johnson/SendSim/At/NothingSpent.lean).
-/
import Johnson.SendSim.At.ClearOf

set_option autoImplicit false

noncomputable section

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc Prob
open Johnson.Prover.Send (shapeAt)

/-- For all coins c of the sender, cutAll c at the entries by which p spends coins of o is some
(back applied to the instance's coins readC c in the set spentN). -/
def SpentBack (P : K1.Par) (ride : Nat → Option Ride) (Bk : ProverCoinCounts) (o p : Addr)
    (back : (↥(spentN P ride Bk o p) → GF) → CsAll ((Bk.spentBy o p).map Ahead.named)) : Prop :=
  ∀ c : Cs (dueR P ride), cutAll c (Bk.spentBy o p) =
    some (back ((sender P ride).cut (spentN P ride Bk o p) (readC P ride c)))

/-- If the job fits its place (sendFits), the entries that concern p are within the sender's number
of coins (WithinAt), and MaskSpender or FoldSpender holds at o and p, then some function back has
SpentBack. Statement only; proved as spentTie in Johnson/SendSim/At/CutProof.lean. -/
def Spec.spentTie : Prop :=
  ∀ (P : K1.Par) (ride : Nat → Option Ride) (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr),
    sendFits P ride = true → WithinAt P ride Bk ord o p →
    MaskSpender P ride Bk ord o p ∨ FoldSpender P ride Bk ord o p →
    ∃ back, SpentBack P ride Bk o p back

open Classical in
/-- Under the premises of Spec.spentTie, every function back with SpentBack maps the uniform
distribution on the values at the names in spentN to the uniform distribution on the runs that p
spends. Statement only; proved as spentUnif in Johnson/SendSim/At/SpentUnif.lean. -/
def Spec.spentUnif : Prop :=
  ∀ (P : K1.Par) (ride : Nat → Option Ride) (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr),
    sendFits P ride = true → WithinAt P ride Bk ord o p →
    MaskSpender P ride Bk ord o p ∨ FoldSpender P ride Bk ord o p →
    ∀ back, SpentBack P ride Bk o p back →
      (unif (↥(spentN P ride Bk o p) → GF)).map back =
        unif (CsAll ((Bk.spentBy o p).map Ahead.named))

/-- With no premise, there is one function back such that, for all coins c of the sender, cutAll c
at the known entries is back applied to the instance's coins readC c in knownN and in knownT.
Statement only; proved as knownTie in Johnson/SendSim/At/CutProof.lean. -/
def Spec.knownTie : Prop :=
  ∀ (P : K1.Par) (ride : Nat → Option Ride) (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr),
    ∃ back : (↥(knownN P ride Bk ord o p) → GF) × (↥(knownT P ride Bk ord o p) → GF) →
        Option (CsAll ((Bk.knownBy ord o p).map Ahead.named)),
      ∀ c : Cs (dueR P ride), cutAll c (Bk.knownBy ord o p) =
        back ((sender P ride).cut (knownN P ride Bk ord o p) (readC P ride c),
          (sender P ride).cutT (knownT P ride Bk ord o p) (readC P ride c))

/-- The field fresh at the level of rows. If the job fits its place (sendFits), the challenge
consists of exactly the seeds (seedsFit), no seed's factor is 0, the queried positions are within
the bound (budAt), WithinAt holds and p is clear (SpenderClear), then over the sender's uniform
coins the tuple (the runs that p spends, shownR, the known runs) has the distribution in which the
runs that p spends are replaced by fresh uniform values, independent of the rest. Statement only;
proved as rowsFresh in Johnson/SendSim/At/RowsFresh.lean. -/
def Spec.rowsFresh : Prop :=
  ∀ (P : K1.Par) (first : Nat) (ride : Nat → Option Ride)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr),
    sendFits P ride = true → seedsFit P ds = true → (∀ s ∈ seedsAt P ds, readE s.2 ≠ 0) →
    budAt P asks → WithinAt P ride Bk ord o p → SpenderClear P ride Bk ord o p →
    (unif (Cs (dueR P ride))).map (fun c =>
        (cutAll c (Bk.spentBy o p), shownR P first ride data ds asks c,
          cutAll c (Bk.knownBy ord o p))) =
      (unif (CsAll ((Bk.spentBy o p).map Ahead.named) × Cs (dueR P ride))).map fun a =>
        (some a.1, shownR P first ride data ds asks a.2, cutAll a.2 (Bk.knownBy ord o p))

end OnBytes.SendSim.At
