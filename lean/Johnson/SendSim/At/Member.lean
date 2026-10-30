-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Member.lean: the one member of a Seated side, as a term, and three statements
that express what its sender discloses and what its simulator outputs through shownR. It claims no
property of the protocol: not hiding, not zero knowledge.
Terms: Johnson/SendSim/At/Sim.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file has. Below, σ is any side that is Seated at a job J, m any state from which the
sender's rounds are played (Mid), front any value for what earlier parts have disclosed (Before), ds
any challenges that σ's rounds can sample (drawsFit), and asks any queried positions.
  members_seated  Proved here, by unfolding: σ has exactly one member, memberAt σ J.
  Spec.exactOut   If asks is within the bound (budAt), what the sender discloses over its uniform
                  coins has the same distribution as what the simulator outputs over its own uniform
                  coins. ExactAt, and the field exact of Good, have more premises: here nothing
                  connects front with m or with ds.
  Spec.showsAt    For each value c of the coins, the sender discloses shownR at c and at the data
                  that J reads at m if the job fits its place (sendFits), else the error value none.
  Spec.tellsAt    For each c, every input and every front, the simulator outputs shownR at c and at
                  no data (each entry of data absent, read as 0) if the job fits, else none.
The three under Spec are statements only; each is proved under the same name without "Spec.".

Limits. Spec.exactOut has the limits of exact, above all that exact is not quoted without fresh: see
the Limits of Johnson/SendSim/At/ExactAt.lean. Spec.showsAt and Spec.tellsAt hold coin by coin and
name no distribution.

How it fits. showsAt and tellsAt are proved in Johnson/SendSim/At/Shows.lean. By them Spec.exactOut
follows from Spec.rowsExact at J's data against no data (exactOut_of_rows,
Johnson/SendSim/At/Joins.lean), and it implies ExactAt at σ (sendExactAt_of_out,
same file). The theorems exactOut and sendExactAt are in Johnson/SendSim/At/ExactAt.lean. showsAt
also serves the field fresh (Johnson/SendSim/At/JoinFresh.lean, Johnson/SendSim/At/FreshWide.lean).

The other names.
  memberAt  number 0; σ's first two rounds with their oracle messages, which are all the rounds that
            σ has (rounds_fst, Johnson/SendSim/At/Joins.lean); the honest sender sendPart J; its
            simulator sendSim at the address (σ's place, 0).
  frontOf   what J's data are given of m besides the input: the challenges heard, the value that
            parts pass on, the rounds disclosed and the columns handed (Mid.shown), all from before
            the sender's rounds.
-/
import Johnson.SendSim.At.Sim

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc

variable {S Cl V W X Pb : Type}

/-- The member that a side Seated at J has (members_seated): number 0 in the row; the first two
rounds of σ's sub-protocol with their oracle messages; the honest sender sendPart J; and its
simulator sendSim at the address (σ's place, 0). -/
def memberAt (σ : Side S Cl V W X Pb) (J : SendJob W X) : Member V W X Pb :=
  ⟨0, (σ.block.rounds.zip σ.block.oracles).take 2, sendPart J,
    sendSim J.P J.first J.ride ⟨σ.block.place, 0⟩⟩

/-- A side that is Seated at J has exactly one member, memberAt σ J. -/
theorem members_seated {σ : Side S Cl V W X Pb} {J : SendJob W X} (h : Seated σ J) :
    σ.members = [memberAt σ J] := by
  unfold Side.members
  rw [h.row]
  rfl

/-- What a job's data function is given of a state m besides the input: the challenges heard so far,
the value that parts pass on to each other (own), and the rounds disclosed so far with the columns
handed, as a part is given them (Mid.shown). -/
def frontOf (m : Mid W X) : Front X := { heard := m.st.heard, own := m.st.own, seen := m.shown }

/-- States what the honest sender discloses at a Seated side, as a function of its coins c. For
every state m, all challenges ds that the side's rounds can sample and all positions asks, it is
shownR at the data that the job reads at m if the job fits its place (sendFits), and the error value
none otherwise. Statement only; proved as showsAt in Johnson/SendSim/At/Shows.lean. -/
def Spec.showsAt : Prop :=
  ∀ (S Cl V W X Pb : Type) (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : SendJob W X),
    Seated σ J → ∀ (m : Mid W X) (ds : List Fmt.Drawn) (asks : List (List (List Nat)))
      (c : Cs (dueR J.P J.ride)), drawsFit σ.block.rounds ds = true →
    σ.shows φ (memberAt σ J) (c, (), ()) m ds asks =
      if sendFits J.P J.ride then
        some (shownR J.P J.first J.ride (J.data m.st.input (frontOf m)) ds asks c)
      else none

/-- States what the simulator outputs at a Seated side, as a function of its coins c. For every
input w, every front, all challenges ds that the side's rounds can sample and all positions asks, it
is shownR at no data if the job fits its place (sendFits), and the error value none otherwise.
Statement only; proved as tellsAt in Johnson/SendSim/At/Shows.lean. -/
def Spec.tellsAt : Prop :=
  ∀ (S Cl V W X Pb : Type) (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : SendJob W X),
    Seated σ J → ∀ (w : W) (front : Before) (ds : List Fmt.Drawn) (asks : List (List (List Nat)))
      (c : Cs (dueR J.P J.ride)), drawsFit σ.block.rounds ds = true →
    (memberAt σ J).tells φ c w front ds asks =
      if sendFits J.P J.ride then
        some (shownR J.P J.first J.ride (fun _ _ _ => none) ds asks c)
      else none

/-- States the equation of ExactAt at the one member of a Seated side. For every
state m, every front, all challenges ds that the side's rounds can sample and all positions asks
within the bound (budAt), what the sender discloses over its uniform coins has the same distribution
as what the simulator outputs over its own uniform coins. Statement only; proved as exactOut in
Johnson/SendSim/At/ExactAt.lean. -/
def Spec.exactOut : Prop :=
  ∀ (S Cl V W X Pb : Type) (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : SendJob W X),
    Seated σ J → ∀ (m : Mid W X) (front : Before) (ds : List Fmt.Drawn)
      (asks : List (List (List Nat))), drawsFit σ.block.rounds ds = true → budAt J.P asks →
    (Prob.unif (Cs (dueR J.P J.ride))).map
        (fun c => σ.shows φ (memberAt σ J) (c, (), ()) m ds asks) =
      (Prob.unif (Cs (dueR J.P J.ride))).map fun c =>
        (memberAt σ J).tells φ c m.st.input front ds asks

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.members_seated
#print axioms OnBytes.SendSim.At.memberAt
#print axioms OnBytes.SendSim.At.frontOf
#print axioms OnBytes.SendSim.At.Spec.showsAt
#print axioms OnBytes.SendSim.At.Spec.tellsAt
#print axioms OnBytes.SendSim.At.Spec.exactOut
