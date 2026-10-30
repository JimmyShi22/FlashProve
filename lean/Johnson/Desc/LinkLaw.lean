-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/LinkLaw.lean: what a segment's batching is meant to give.
Two small theorems, which only instantiate theorems of the library. Everything else is STATED, NOT
PROVED: a definition of type Prop. Nothing here is used yet.

A segment (`Link`, Johnson/Desc/Block.lean) has blocks that test nothing at once. Each states
claims: values that must be 0. One block then draws a challenge chi and replaces all claims of the
segment by one equation, in which each claim stands under a power of chi.

1 Which claims reach the batching (stated, not proved).
  `EveryRunOnce`: if the segment passes its check on the plan, the order in which claims are
    batched lists every named run of claims of every block exactly once.
  `ClaimsAreTheRuns`: the list handed to the batching block is the runs' lists of claims, one
    after the other in that order; the state goes from each run to the next.
2 The batching itself (proved, from the library).
  The library has a batching block for any "zero-evader" (Cb/Gen/BatEvader.lean): a rule that turns
  a seed into one coefficient for each claim, such that few seeds annihilate a vector other than 0.
  `powersAt E d e`: claim number j gets the coefficient chi ^ e j, with exponents e j ≤ d.
  `powersAt_ok`: if the exponents differ from each other, it is a zero-evader with at most d bad
    seeds.
  `clean_powersAt`: so the library's batching block, at these coefficients, is sound in the
    library's round-by-round sense (`Blocks.Block.Clean`) from "all n forms have the value 0" to
    "the one form has the value 0": if not all n are 0, the one is not 0 either, but for at most d
    challenges.
3 The batching of a segment (stated, not proved).
  `LinkLaw`, under the hypothesis `FixedBeforeDraw`.

The hypothesis `FixedBeforeDraw`, and why it has a name. The batching block computes the claims at
a state that already holds chi, so by type a claim may depend on chi, and some do: one kind of
block states several equations in one claim, under further powers of chi. The count of bad
challenges holds only if the whole sum is a polynomial in chi whose coefficients were fixed before
chi was drawn. That is what the hypothesis says. In part 2 it is built in: the n forms are the
block's input. It is not shown here for any segment of the protocol.

A LIMIT OF `LinkLaw` AS IT IS STATED: ITS PREMISES ASK MORE THAN A SEGMENT OF THE PROTOCOL GIVES. It
asks that the runs of claims say yes at every chi, and `FixedBeforeDraw` asks its equation at every
chi. But whether a run says yes may itself depend on chi: the smallness test's run of equations
(Johnson/Desc/First/TailClaims/Equations.lean) sums the drawn matrix's columns under powers of chi
and refuses where such a sum is 0. At chi = 0 the sum is the column's first entry, so the run
refuses there as soon as one column that it reads begins with 0; the entries are drawn among -1, 0
and 1. Every segment has that run. So a real segment meets the premise on the runs only by a rare
chance of the draw, and of all other segments `LinkLaw`, though true, says nothing. The form that
speaks of them asks both premises only at the chi at which the runs say yes, and counts only these:
`LinkLawYes`, Johnson/Desc/LinkLawYes.lean [not in this library; so here read: not proved in this library], which is said there to give `LinkLaw` back. A chi at
which a run refuses is a no of the verifier and needs no count.

What is not stated here.
  That the equation which the batching block's text builds is this sum.
  The error of the rounds before and after the batching, and how errors add up over a segment.
  Anything about the masks, and so anything about zero-knowledge.
-/
import Johnson.Desc.Block
import Cb.Gen.BatEvaderProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

/-! ## 1 Which claims reach the batching -/

/-- All named runs of claims of a list of blocks: (the block's number, the run's name). -/
def allRuns {S Cl : Type} (bs : List (Block S Cl)) : List (ℕ × String) :=
  bs.zipIdx.flatMap fun b => b.1.claims.map fun c => (b.2, c.1)

/-- STATED, NOT PROVED. A segment that passes its check on the plan batches every named run of
claims exactly once. -/
def EveryRunOnce : Prop :=
  ∀ (S Cl : Type) (bs : List (Block S Cl)) (order : List (ℕ × String)),
    orderOk bs order = true → order.Perm (allRuns bs) ∧ order.Nodup

/-- The runs named in `order`, one after the other: each run's own list of claims, and the last
state. k: the number of claims made so far, which each run is told. `none` if a run refuses or is
not there. -/
def runsOneByOne {S Cl : Type} (bs : List (Block S Cl)) :
    List (ℕ × String) → ℕ → S → Option (List (List Cl) × S)
  | [], _, s => some ([], s)
  | o :: os, k, s =>
    ((bs[o.1]?).bind fun b => b.claims.lookup o.2).bind fun run =>
      (run k s).toOption.bind fun y =>
        (runsOneByOne bs os (k + y.1.length) y.2).map fun z => (y.1 :: z.1, z.2)

/-- STATED, NOT PROVED. What the batching block is handed is the runs' claims, in the order that
the segment states. -/
def ClaimsAreTheRuns : Prop :=
  ∀ (S Cl : Type) (bs : List (Block S Cl)) (order : List (ℕ × String)) (s : S),
    (claimsIn bs order s).toOption = (runsOneByOne bs order 0 s).map fun x => (x.1.flatten, x.2)

/-! ## 2 The batching itself -/

/-- The coefficients of the batching: claim number j under chi ^ e j. -/
@[reducible] def powersAt (E : Type) [Field E] [Fintype E] {n : ℕ} (d : ℕ)
    (e : Fin n → Fin (d + 1)) : Cb.Evader E (Fin n) :=
  (Cb.Evader.powers E (d + 1)).comap e

/-- PROVED. If the exponents differ from each other, at most d values of chi annihilate a vector of
n values that are not all 0. -/
theorem powersAt_ok (E : Type) [Field E] [Fintype E] {n : ℕ} (d : ℕ) (e : Fin n → Fin (d + 1))
    (he : Function.Injective e) : (powersAt E d e).OK :=
  Cb.ok_comap E (Fin n) (Fin (d + 1)) (Cb.Evader.powers E (d + 1)) e he (Cb.ok_powers E (d + 1))

/-- PROVED. The library's batching block at these coefficients is sound in the library's
round-by-round sense, with at most d bad challenges: from "each of the n forms has the value 0" to
"the one form has the value 0". -/
theorem clean_powersAt (E Y P : Type) [Field E] [Fintype E] (𝔉 : Blocks.Forms E Y P) {n : ℕ} (d : ℕ)
    (e : Fin n → Fin (d + 1)) (he : Function.Injective e) :
    (Cb.batB 𝔉 (powersAt E d e)).Clean (fun x y => ∀ j, 𝔉.val y (x j) = 0)
      (fun f y => 𝔉.val y f = 0) (d, ()) :=
  Cb.clean_batB E (Fin n) Y P 𝔉 (powersAt E d e) (powersAt_ok E d e he)

/-! ## 3 The batching of a segment -/

section
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

/-- A polynomial in chi, as a list of terms (exponent, coefficient), at a value of chi. -/
def termsAt (t : List (ℕ × K)) (chi : K) : K := (t.map fun x => chi ^ x.1 * x.2).sum

/-- The exponents differ from each other and are at most d. -/
def TermsOk (t : List (ℕ × K)) (d : ℕ) : Prop := (t.map (·.1)).Nodup ∧ ∀ x ∈ t, x.1 ≤ d

/-- THE HYPOTHESIS. `total chi` is the sum that the one equation stands for if the challenge is chi.
It is a polynomial in chi whose terms t do not depend on chi: they were fixed before the draw. -/
structure FixedBeforeDraw (total : K → K) (t : List (ℕ × K)) (d : ℕ) : Prop where
  terms : TermsOk K t d
  sum : ∀ chi, total chi = termsAt K t chi

/-- STATED, NOT PROVED. **The law of a segment's batching.**
at' chi: the state at which the batching block computes the claims if the challenge is chi.
cl chi: the claims made there. val chi c: the value of the claim c, with its weight, at the data to
which the prover is bound. t: the equations behind the claims, each with its own power of chi.
If one of these equations fails, at most d challenges make the segment's one equation hold.
A SEGMENT OF THE PROTOCOL MEETS THE PREMISE ON THE RUNS, a yes at every chi, ONLY BY A RARE CHANCE
OF THE DRAW: see the head. The form to use is `LinkLawYes` (Johnson/Desc/LinkLawYes.lean [not in this library]). -/
def LinkLaw : Prop :=
  ∀ (S Cl : Type) (L : Link S Cl) (at' after : K → S) (cl : K → List Cl) (val : K → Cl → K)
    (t : List (ℕ × K)) (d : ℕ),
    orderOk L.hear L.order = true →
    (∀ chi, claimsIn L.hear L.order (at' chi) = .ok (cl chi, after chi)) →
    FixedBeforeDraw K (fun chi => ((cl chi).map (val chi)).sum) t d →
    (∃ x ∈ t, x.2 ≠ 0) →
    (Finset.univ.filter fun chi : K => ((cl chi).map (val chi)).sum = 0).card ≤ d

end

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.powersAt_ok
#print axioms VerifiableInference.Desc.clean_powersAt
