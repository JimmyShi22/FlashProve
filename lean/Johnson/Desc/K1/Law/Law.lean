-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Law.lean: three further parts of the kind's law, as propositions. Nothing is
proved here.

Main names: WhenLaw (on what the decision's yes hangs); Msg.pads, padPart, has, bits, vertex, weight
and MeansLaw (the sample row's kind, target and every coefficient, in closed form); Msg.form,
pointOf and CatchesLaw (a count of seeds; it names no verifier).

What is not claimed. MeansLaw leaves a coefficient free at an index beyond its table. WhenLaw's "no
factor is 0" is judged on the words as drawn. Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Tries
import Johnson.Desc.Means.Says
import OnBytes.Slice.BlkSend
import Cb.Gen.OodDecPadPowProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice (GE GF readE readL eqW coefAt)

/-! ## WHEN -/

/-- **WHEN.** At a place that passes the tests on the plan, with codes whose lengths are powers of
two, and rounds that fit: the decision's yes hangs on the carried record and on the factors drawn
alone: on nothing that the prover sends. -/
def WhenLaw (dec : Dec) : Prop :=
  ∀ (L : Type) (P : Par) (owed : Option Nat) (d : DState L) (r₁ r₂ : Fmt.RoundView),
    planOkOwn P = true → P.codes.lengthsOk = true → roundsFit (rounds P) [r₁, r₂] = true →
    ((dec L P owed d [r₁, r₂]).isOk = true ↔
      owed = none ∧ d.st.codes = P.codes ∧ d.st.oracles.size = d.book.place.size ∧
        ∀ s ∈ seedsOf P r₁, isZeroE s.2 = false)

/-! ## MEANS -/

/-- The pads' places of all answers: the answer, the index, the power of θ. -/
def Msg.pads (m : Msg) : List (Nat × Nat × Nat) :=
  (List.range m.answers).flatMap fun k => (m.pad k).map fun x => (k, x)

/-- The table that holds the pads. -/
def Msg.padPart (m : Msg) : Part := if m.Kzk != 0 then .mask else .main

def Msg.has (m : Msg) : Part → Bool
  | .main => m.K != 0
  | .mask => m.Kzk != 0

def Msg.bits (m : Msg) : Part → Nat
  | .main => m.mainBits
  | .mask => m.maskBits

/-- The vertex of an entry on the message's cube. -/
def Msg.vertex (m : Msg) (part : Part) (j : Nat) : Nat :=
  (if m.K != 0 && m.Kzk != 0 && part == .mask then 2 ^ (m.v - 1) else 0) + j

/-- The coefficient that the page's words give to an entry in the row of answer i: on a pad's entry
β θ^t in its own answer's row and 0 in the others; elsewhere the weight of the entry's vertex. -/
def Msg.weight (m : Msg) (z : Nat → GE) (β : GE) (i : Nat) (part : Part) (j : Nat) : GE :=
  match m.pads.find? fun x => part == m.padPart && x.2.1 == j with
  | some x => if x.1 = i then β * readE (thetaE x.2.2) else 0
  | none => if m.has part then eqW m.v z (m.vertex part j) else 0

/-- **MEANS**, of the function that makes a row. -/
def MeansLaw (row : Msg → Nat → List E → E → Nat → E → OnBytes.Row) : Prop :=
  ∀ (m : Msg) (o : Nat) (z : List E) (β : E) (i : Nat) (y : E),
    (m.K != 0 || m.Kzk != 0) = true → m.v ≤ z.length →
    (row m o z β i y).kind = .sample ∧ (row m o z β i y).target = y ∧
      (∀ o' part j, o' ≠ o → coefAt (row m o z β i y) o' part j = 0) ∧
      ∀ part j, j < 2 ^ m.bits part →
        coefAt (row m o z β i y) o part j = m.weight (readL z) (readE β) i part j

/-! ## CATCHES -/

/-- The left side of the row of answer i, at a seed, on a message's two tables. -/
def Msg.form (m : Msg) (z : Nat → GE) (β : GE) (i : Nat) (u : Part → Nat → GE) : GE :=
  (∑ j ∈ Finset.range (if m.has .main then 2 ^ m.bits .main else 0),
      m.weight z β i .main j * u .main j) +
    ∑ j ∈ Finset.range (if m.has .mask then 2 ^ m.bits .mask else 0),
      m.weight z β i .mask j * u .mask j

/-- A point of the cube as a function on all numbers. -/
def pointOf {v : Nat} (z : Fin v → GE) (t : Nat) : GE := if h : t < v then z ⟨t, h⟩ else 0

/-- **CATCHES**: a count with no verifier in it: tables that are not all 0, whose pads' entries lie
in the base field where a pad has three, have all their answers 0 at no more than this many of the
seeds with factors other than 0. -/
def CatchesLaw : Prop :=
  ∀ (m : Msg) (u : Part → Nat → GE), m.padFits = true → (m.K != 0 || m.Kzk != 0) = true →
    (∃ part j, m.has part = true ∧ j < 2 ^ m.bits part ∧ u part j ≠ 0) →
    (m.e = 3 → ∀ x ∈ m.pads, u m.padPart x.2.1 ∈ Set.range (algebraMap GF GE)) →
    Prob.cnt (fun ρ : Fin m.answers → (Fin m.v → GE) × GEˣ =>
        ∀ i : Fin m.answers, m.form (pointOf (ρ i).1) ((ρ i).2 : GE) i.val u = 0) ≤
      (max (m.v * Fintype.card GE ^ (m.v - 1) * Fintype.card GEˣ) (Fintype.card GE ^ m.v)) ^
        m.answers

end VerifiableInference.Desc.K1
