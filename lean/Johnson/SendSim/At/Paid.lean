-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Paid.lean: four of the statements that connect the honest sender with the
instance of the general model, under their other premises but without RidesAdd or RidesZero, which
hold for every ride.
Terms: Johnson/SendSim/At/Sim.lean; sender, RidesAdd, RidesZero, the two premises on the seeds:
Johnson/SendSim/At/Bridge.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves. Four corollaries, each in one line. They hold for each value of data and
coins; no distribution is named. "The two premises on the seeds" are seedsFit and that no seed's
factor is 0.
  additive_paid  If the job fits its place (sendFits), the instance's lay is additive.
  mends_paid     If the job fits its place, under the two premises on the seeds: Sender.Mends holds
                 at the weights wOf, that is, for any values of the answers there is a family of
                 message coins, at which lay is additive, that contributes them.
  pads_paid      Under the same premises, each answer has a coin of its own (Sender.Pads). It is
                 here for completeness; no file uses it.
  shown_paid     Under the same premises, what the sender discloses in its two rounds (shownR) is
                 one function, the same for all data and coins, of what the instance discloses.

How it fits. Johnson/SendSim/At/JoinRows.lean uses mends_paid and shown_paid for rowsExact
(Johnson/SendSim/At/RowsExact.lean) and shown_paid for rowsFresh
(Johnson/SendSim/At/RowsFresh.lean). Johnson/SendSim/At/ClearOfFold.lean and
Johnson/SendSim/At/FoldAny.lean use additive_paid for the model's premise MendsOff. The four
statements are in Johnson/SendSim/At/Bridge.lean; ridesAdd and ridesZero are proved in
Johnson/SendSim/At/RideLay.lean.
-/
import Johnson.SendSim.At.RideLay
import Johnson.SendSim.At.MendsOf
import Johnson.SendSim.At.Shown

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc

/-- additiveOf without RidesAdd: if the job fits its place (sendFits), the instance's lay is
additive. -/
theorem additive_paid (P : K1.Par) (ride : Nat → Option Ride) (hf : sendFits P ride = true) :
    (sender P ride).Additive := additiveOf P ride hf (ridesAdd ride)

/-- mendsOf without RidesZero: if the job fits its place (sendFits), the challenge consists of
exactly the seeds (seedsFit) and no seed's factor is 0, Sender.Mends holds at the weights wOf P ds.
-/
theorem mends_paid (P : K1.Par) (ride : Nat → Option Ride) (ds : List Fmt.Drawn)
    (hf : sendFits P ride = true) (hs : seedsFit P ds = true)
    (hβ : ∀ s ∈ seedsAt P ds, readE s.2 ≠ 0) : (sender P ride).Mends (wOf P ds) :=
  mendsOf P ride ds hf (ridesZero ride) hs hβ

/-- padsOf without RidesZero: under the premises of mends_paid the instance has pads (Sender.Pads).
-/
theorem pads_paid (P : K1.Par) (ride : Nat → Option Ride) (ds : List Fmt.Drawn)
    (hf : sendFits P ride = true) (hs : seedsFit P ds = true)
    (hβ : ∀ s ∈ seedsAt P ds, readE s.2 ≠ 0) : Nonempty ((sender P ride).Pads (wOf P ds)) :=
  padsOf P ride ds hf (ridesZero ride) hs hβ

/-- shownTie without RidesZero: under the premises of mends_paid there is one function back such
that, for all data and coins c, shownR is back applied to what the instance discloses at dataOf data
and readC c. -/
theorem shown_paid (P : K1.Par) (first : Nat) (ride : Nat → Option Ride) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) (hf : sendFits P ride = true) (hs : seedsFit P ds = true)
    (hβ : ∀ s ∈ seedsAt P ds, readE s.2 ≠ 0) :
    ∃ back : List GF × (AnsN P → GF) → List Shown,
      ∀ (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (c : Cs (dueR P ride)),
        shownR P first ride data ds asks c =
          back ((sender P ride).shown (wOf P ds) (asksOf P asks) (dataOf P ride data)
            (readC P ride c)) :=
  shownTie P first ride ds asks hf (ridesZero ride) hs hβ

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.additive_paid
#print axioms OnBytes.SendSim.At.mends_paid
#print axioms OnBytes.SendSim.At.pads_paid
#print axioms OnBytes.SendSim.At.shown_paid
