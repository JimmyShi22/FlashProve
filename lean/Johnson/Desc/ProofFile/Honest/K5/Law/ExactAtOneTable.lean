-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ExactAtOneTable.lean: definitions of type Prop on a part and its
simulator at the input of the first and the second chain, general in all types. They say what a part
reads, whether it stops, what a simulator reads and tells, what the field exact of Good
(Honest/Side.lean) says at one fixed table, that its premises can meet there, and what the field
fresh says of one owner toward one spender. This file proves nothing.

They stand apart from the statement on the online prover because the search for instances in that
statement's larger scope runs out of its budget at the two uniform laws.
No property is claimed. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open VerifiableInference.Desc (Place)

section General
variable {S Cl V W₀ Rc Xi Tr W X Pb : Type}

/-- **A part's moves read of the input the trace alone**: each says the same at two states with one
trace, the same challenges heard and the same state passed on, whatever else the inputs hold. -/
def ReadsTheTraceAlone (q : Part V (Local W₀ Rc Xi Tr) X) : Prop :=
  ∀ mv ∈ q.moves, ∀ c s (t t' : State (Local W₀ Rc Xi Tr) X), t.input.trace = t'.input.trace →
    t.heard = t'.heard → t.own = t'.own → mv.say c s t = mv.say c s t'

/-- **A part has no stop**: neither of its two stops fires, at any argument. -/
def HasNoStop (q : Part V W X) : Prop :=
  (∀ before own, q.bad before own = none) ∧ ∀ input before own, q.hid input before own = none

/-- **A simulator reads its own coins alone**: it says the same at any two values of its four other
arguments. -/
def ReadsItsCoinsAlone (s : Sim Pb) : Prop :=
  ∀ x x' front front' ds ds' asks asks' c, s.tell x front ds asks c = s.tell x' front' ds' asks' c

/-- **A simulator tells its own coins, and nothing else, in rounds of ns items**: it returns at all
arguments; its rounds hold as many items as ns says, round by round; read in order these are its coins
of the extension field, one by one; and it shows no column. -/
def TellsItsCoins (s : Sim Pb) (ns : List Nat) : Prop :=
  ∀ x front ds asks c, ∃ shown, s.tell x front ds asks c = some shown ∧
    shown.map (·.vals.length) = ns ∧
    shown.flatMap (·.vals) = (coinsE c).map (fun y => Fmt.ItemValue.e y.triple) ∧ ∀ t ∈ shown, t.cols = []

/-- **The field exact at one fixed table, written out**; it follows from the field. The index, the
stored tables' pads and encoding randomness, the instance and the trace are fixed first. The left side
is taken over the blocks that the part spends and over nothing else, where the part has no coin of its
own. The right side is taken over the simulator's own coins; its arguments are x, front, ds, asks and
those coins, and ReadsItsCoinsAlone says that it reads the last alone. The premise on the second stop
is the field's; at a part that HasNoStop it is idle. -/
def ExactAtOneTable (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (On : (u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) →
      CsAll u.part.carries → Mid (Local W₀ Rc Xi Tr) X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) : Prop :=
  ∀ (index : W₀) (table : Rc) (x : Xi) (trace : Tr), ∀ u ∈ σ.members,
    ∀ ca (m : Mid (Local W₀ Rc Xi Tr) X) front ds asks, m.st.input = ⟨index, table, x, trace⟩ →
      On u ca m front → m.seen = front.seen → m.opened = front.opened (readsBefore pre front) →
      drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
      front.holds 0 0 (u.rounds.map (·.1)) ds = true →
      u.part.stopAt (Face.own.sees m.st.input) m.loc ds ≠ some .hid →
      (Prob.unif (Cs u.part.takes × CsAll u.part.spends)).map
          (fun c => σ.shows .own u (c.1, c.2, ca) m ds asks) =
        (Prob.unif (Cs u.sim.takes)).map fun c => u.sim.tell x front ds asks c

/-- **Where the premises of the field exact hold, a part shows something at every coin.** shows and a
simulator's telling are of Option type: a part that errs beside a simulator that tells none meets the
field, so the field alone does not say that anything is shown. -/
def ShowsSome (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (On : (u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) →
      CsAll u.part.carries → Mid (Local W₀ Rc Xi Tr) X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) : Prop :=
  ∀ u ∈ σ.members, ∀ ca (m : Mid (Local W₀ Rc Xi Tr) X) front ds asks,
    On u ca m front → m.seen = front.seen → m.opened = front.opened (readsBefore pre front) →
    drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    front.holds 0 0 (u.rounds.map (·.1)) ds = true →
    u.part.stopAt (Face.own.sees m.st.input) m.loc ds ≠ some .hid →
    ∀ c : Cs u.part.takes × CsAll u.part.spends,
      (σ.shows .own u (c.1, c.2, ca) m ds asks).isSome = true

/-- **The premises of the field exact can meet at one fixed table**: at every index, table, instance
and trace there are a carried block, a state with that input, a front, challenges and positions at
which all the field's premises hold. The state is among those that exist: at a state whose opened
columns no front holds the field asks nothing. -/
def ExactIsLive
    (On : (u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) →
      CsAll u.part.carries → Mid (Local W₀ Rc Xi Tr) X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) : Prop :=
  ∀ (index : W₀) (table : Rc) (x : Xi) (trace : Tr),
    ∃ ca, ∃ m : Mid (Local W₀ Rc Xi Tr) X, ∃ front ds asks, m.st.input = ⟨index, table, x, trace⟩ ∧
      On u ca m front ∧ m.seen = front.seen ∧ m.opened = front.opened (readsBefore pre front) ∧
      drawsFit (u.rounds.map (·.1)) ds = true ∧ bud u.number ds asks ∧
      front.holds 0 0 (u.rounds.map (·.1)) ds = true ∧
      u.part.stopAt (Face.own.sees m.st.input) m.loc ds ≠ some .hid

/-- **The field fresh of one owner toward one spender**: the text of Good's field at one member u and
one address p. -/
def FreshToward {V' W' X' Pb' S' Cl' : Type} (φ : Face V' W' Pb') (σ : Side S' Cl' V' W' X' Pb')
    (Bk : ProverCoinCounts) (ord : List Place)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (u : Member V' W' X' Pb')
    (p : Addr) : Prop :=
  ∀ sp ca m ds asks, drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid →
    (Prob.unif (Cs u.part.takes)).map (fun c =>
        (cutAll c (Bk.spentBy ⟨σ.block.place, u.number⟩ p), σ.shows φ u (c, sp, ca) m ds asks,
          cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))) =
      (Prob.unif (CsAll ((Bk.spentBy ⟨σ.block.place, u.number⟩ p).map Ahead.named) ×
          Cs u.part.takes)).map fun a =>
        (some a.1, σ.shows φ u (a.2, sp, ca) m ds asks,
          cutAll a.2 (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))

end General

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.ReadsTheTraceAlone
#print axioms ProofFile.Honest.K5.HasNoStop
#print axioms ProofFile.Honest.K5.ReadsItsCoinsAlone
#print axioms ProofFile.Honest.K5.TellsItsCoins
#print axioms ProofFile.Honest.K5.ExactAtOneTable
#print axioms ProofFile.Honest.K5.ShowsSome
#print axioms ProofFile.Honest.K5.ExactIsLive
#print axioms ProofFile.Honest.K5.FreshToward
