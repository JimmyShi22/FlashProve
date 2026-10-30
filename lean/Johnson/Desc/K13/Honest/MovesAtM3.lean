--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/MovesAtM3.lean: kind K13, the members' batching: THE HONEST PROVER's ROUNDS,
WITH CODE. DEFINITIONS ALONE: this file defines part of the honest prover; what is proved of it
stands in CodeRow.lean, SubProtocols.lean and Accepts.lean of this folder.

What the prover knows: the matrix and the mask entries (`Wit`, Johnson/Desc/K13/Law/Means.lean); the
pile of rows, which is public data of the verifier's state; the list of the mask entries that were
taken for the hiding polynomial; the elements sampled. Where that list has 2 k + 1 members, as the
verifier's taking gives it, these are the only mask entries that are read (beyond the list's end the
default entry would be read). The scalars are computed over a field K by
Johnson/Desc/K13/Honest/Moves.lean, laid into the program's type E by a function σ, and set beside
the sampled elements. σ is meant to be a section of the reading of E in K; that is a premise where
it is used.
Main names:
  `movesAtM3 ρ σ w pile fresh x eps gs`: **THE PROVER's ROUNDS AT THE PLACE**, of all that it knows.
  `tabsOf ρ w pile a`: for each row of the pile its two tables: the equality vector of its column
    point times its coefficient a^j; its weights times the matrix.
  `maskAt w fresh`: the mask entries that were taken, by their number.
  `codeRounds σ l gs`: pairs of scalars, laid into E, beside the sampled elements.
  `codeHeard ρ σ u T k eps gs`: what is heard of the prover: the sum; then one pair for each
    variable.
  `shownRound s c`, `roundsOf x h`: the 2 + k rounds: nothing sent and x sampled; the sum sent and
    eps sampled; for each variable two coefficients sent and a challenge sampled.

What is not claimed. No theorem stands in this file. The functions take all sampled elements at
once. Of the k challenges gs a round's pair reads the earlier ones alone: `sent_take`, SumLaw.lean;
the sum is a term in which no sampled element stands; no statement says the like of `movesAtM3`.
There are 2 + k rounds only where gs has k members. A round here holds the elements sent and the
element sampled, and no position, digit or digest; that the format's step in front of the decision
passes such rounds, and that a real file's view has this form at these rounds, is not shown. It is
not claimed that the C++ prover sends these scalars. Nothing on running times. Nothing on soundness
or on hiding.

-/
import Johnson.Desc.K13.Honest.Moves
import Johnson.Desc.K13.Law.Means
import Fmt.View

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K13.Law

variable {K : Type} [Field K] (ρ : Reading K) {nR k : ℕ} (σ : K → E)

/-- **The two tables of each row of the pile**, once a is sampled. -/
def tabsOf (w : Wit K nR k) (pile : List TensorRow) (a : K) : List (List K × List K) :=
  List.ofFn fun q : Fin pile.length =>
    (scaleT (a ^ (q : ℕ)) (eqT ((pile.get q).psi.map ρ.val)),
      tabOf k (colOf w (weights ρ nR (pile.get q).g)))

/-- The mask entries that were taken, by their number. -/
abbrev maskAt (w : Wit K nR k) (fresh : List Slot) : ℕ → K := fun j => w.mask (fresh.getD j default)

/-- Pairs of scalars, laid into the program's field, beside the sampled elements. -/
def codeRounds : List (K × K) → List E → List (List E × E)
  | q :: l, g :: gs => ([σ q.1, σ q.2], g) :: codeRounds l gs
  | _, _ => []

/-- What is heard of the prover. u: the 2 k + 1 mask entries by their number. T: the rows' tables.
eps, gs: the sampled elements. -/
def codeHeard (u : ℕ → K) (T : List (List K × List K)) (k : ℕ) (eps : E) (gs : List E) :
    Psc.Heard :=
  ⟨σ (sumU u k), eps, codeRounds σ (sent u (ρ.val eps) k 0 T (gs.map ρ.val)) gs, []⟩

/-- A round in which the elements s are sent and c is sampled. -/
def shownRound (s : List E) (c : E) : Fmt.RoundView :=
  ⟨s.map fun e => .e e.triple, ⟨[c.triple], [], [], none⟩⟩

/-- The rounds of the batching, of the first sampled element and of what is heard. -/
def roundsOf (x : E) (h : Psc.Heard) : List Fmt.RoundView :=
  shownRound [] x :: shownRound [h.mu] h.eps :: h.rounds.map fun p => shownRound p.1 p.2

/-- **The prover's rounds at the place.** w: the matrix and the mask entries. pile: the rows on the
pile. fresh: the mask entries that were taken. x, eps, gs: the sampled elements. -/
def movesAtM3 (w : Wit K nR k) (pile : List TensorRow) (fresh : List Slot) (x eps : E)
    (gs : List E) : List Fmt.RoundView :=
  roundsOf x (codeHeard ρ σ (maskAt w fresh) (tabsOf ρ w pile (ρ.val x)) k eps gs)

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.tabsOf
#print axioms VerifiableInference.Desc.K13.Honest.codeHeard
#print axioms VerifiableInference.Desc.K13.Honest.roundsOf
#print axioms VerifiableInference.Desc.K13.Honest.movesAtM3
