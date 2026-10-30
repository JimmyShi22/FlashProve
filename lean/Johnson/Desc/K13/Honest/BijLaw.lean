--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/BijLaw.lean: the masked sumcheck's honest scalars (plain weights, degree 2,
no value shown at the end): OVER UNIFORM COEFFICIENTS OF THE HIDING POLYNOMIAL, WHAT IS SENT HAS THE
DISTRIBUTION OF 2 n + 1 UNIFORM SCALARS IN THE SAME SHAPE. Over a finite commutative ring.
Statements with their proofs.

It follows from the bijection of Johnson/Desc/K13/Honest/Bij.lean (`viewEquiv`) and the library's
rule that a bijection of uniform coins leaves a distribution as it is (`Prob.map_unif_reindex`,
Prob/LawKit.lean).

OVER WHICH SPACE, AND WHAT IS HELD FIXED. The space: the functions from 2 n + 1 numbers to K,
uniform: the coefficients of the hiding polynomial and nothing else. Fixed, and arbitrary: the
parameter q, or the tables S, which give the summand's round polynomials; the joining element eps;
the challenges seen and gs. At kind K13 q is made of the matrix, of the weights and column points of
the rows on the pile, and of the first sampled element, and of nothing else: not of a row's target,
not of its mask form, not of a sample's answer. No state of a verifier and no statement stands in a
theorem of this file. f: whatever is made of what is sent, for instance the items as bytes.

WHOSE HALF THIS IS. In the protocol the coefficients are mask entries of an oracle message that was
sent earlier. This is the half of the sub-protocol that SPENDS these entries: it takes them as
uniform, and nothing of what is fixed as made of them. That message has an OOD sample, whose answers
have coefficients on these entries and stand in the verifier's statement before the sumcheck begins,
and columns of it are opened later. That the entries are still uniform, given these answers and
columns, is the half of the sub-protocol that SENDS the message: a statement in which the mask rows'
tails and the pads of the answers are sampled along with the entries. Its core in linear algebra is
`Code.fresh_core` (Code/FreshCore.lean); no file ties that core to the index masks' message. It is
not shown here, and nothing here leans on it. THE STATEMENTS OF THIS FILE AND OF Bij.lean ARE NOT TO
BE QUOTED WITHOUT THE SENDER's SENTENCE BESIDE THEM.
Main names:
  `view_law`: the distribution, with the summand as a parameter.
  `viewT_law`: the same where the summand is given by tables.

What is not claimed. The sender's half. What later rows that name these entries show of them: the
row that the batching hands on names all of them. THE CHALLENGES ARE FIXED BEFORE THE ENTRIES ARE
SAMPLED: this is the form for a verifier whose challenges are independent of what is sent; for
challenges that are functions of the scalars sent before, nothing is stated. That the scalars of
these statements are those of the prover's rounds at the place is shown elsewhere:
Johnson/Desc/K13/Honest/Tie.lean. WHICH PROVER: the statements of this file are of the scalars'
formulas with code (Johnson/Desc/K13/Honest/Moves.lean), at coefficients that are handed in: so they
serve the prover that is handed the list of its entries (Tie.lean); the formulas are total and test
nothing; that the C++ prover sends these scalars is not claimed. THE MAP IS ONE TO ONE: with all
that is held fixed, the scalars sent fix every one of these entries, and so every other value that
is computed from them. One list of coefficients serves one run: of two runs at the same coefficients
nothing is said. That a program's mask entries are uniform coins. No property of a protocol is
stated: nothing on soundness, on zero knowledge or on hiding.

-/
import Johnson.Desc.K13.Honest.Bij
import Prob.LawKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest

variable {K : Type} [CommRing K] [Fintype K] {γ : Type}

/-- **What is sent, over uniform coefficients, has the distribution of uniform scalars in its
shape.** eps, q, seen and gs are fixed before the coefficients are sampled. THE SPENDER's HALF: see
the head; not to be quoted without the sender's sentence. -/
theorem view_law (eps : K) (q : List K → K × K × K) (n : ℕ) (hn : 1 ≤ n) (seen gs : List K)
    (f : K × List (K × K) → γ) :
    (Prob.unif (Fin (2 * n + 1) → K)).map (fun v => f (viewL eps q n seen gs v)) =
      (Prob.unif (Fin (2 * n + 1) → K)).map fun c => f (tellL (onNat c) n) :=
  Prob.map_unif_reindex (viewEquiv eps q n hn seen gs) _ _ fun v =>
    congrArg f (viewL_eq_tell eps q n hn seen gs v)

/-- The same where the summand is given by tables. THE SPENDER's HALF: see the head. -/
theorem viewT_law (eps : K) (S : List (List K × List K)) (n : ℕ) (hn : 1 ≤ n) (gs : List K)
    (f : K × List (K × K) → γ) :
    (Prob.unif (Fin (2 * n + 1) → K)).map (fun v => f (viewT eps S n gs v)) =
      (Prob.unif (Fin (2 * n + 1) → K)).map fun c => f (tellL (onNat c) n) :=
  Prob.map_unif_reindex (viewEquiv eps (fun seen => quadAll (foldsAll seen S)) n hn [] gs) _ _
    fun v => congrArg f (viewT_eq_tell eps S n hn gs v)

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.view_law
#print axioms VerifiableInference.Desc.K13.Honest.viewT_law
