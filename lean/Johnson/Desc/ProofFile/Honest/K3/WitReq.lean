-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/WitReq.lean: the honest side of the kind "lookup" (K3): the letter
req of the filling, as a term at the description's own instance. Definitions with code, among them
two tests, and theorems.

Terms. Honest/K3/GLOSSARY.md: see there sources, seated filling, instance, public part and
covered positions. In this file: the filling of the letters `Sources` (`tiedOwnSources`,
Honest/K3/WitOwner.lean) takes a letter req: of the instance, the covered positions and the
token that is checked at each; the keys of the lookup on the head's calls read them by position.
The instance of a description (`Inst`, Johnson/Desc/ProofFile/Pub.lean) holds the request file's
bytes and the reply file's bytes. The library has both halves as code: `S.coveredAt`
(Johnson/Desc/First/State.lean): of the request's words and a reply, under four tests;
`Head.winOf` (OnBytes/Model/HeadHeard.lean): the checked tokens. The ground of a description is
made with the same `coveredAt` (`lettersBy`, Pub.lean).

What is defined and shown.
  `askedTok`: the reply that is asked about, as a number: that of `Inst.asked`; the tie:
    `asked_eq_askedTok` (Honest/K3/Law/Ties.lean [not in this library]).
  `coveredOfInst`, `reqAt`: the library's covered positions at the public part Z and the instance x;
    the term.
  `reqMadeB`: `coveredAt` returns at Z and x: a test with code on public data.
  `sizesOneB`: the layers' number of tokens is the head's number of positions: a test on Z.
  `coveredAt_sizes`, `winOf_size`: the arrays that `coveredAt` and `winOf` return have one entry a
    position.
  `reqFits_of_covered`, `reqFits_of_tests`: where `coveredAt` returns and the two numbers are one,
    the test `reqFitsB` (Honest/K3/SeatFits.lean) accepts `reqAt Z x`.
No value is filled in unmarked: where `coveredAt` rejects, `reqAt` yields empty arrays, and
`reqFitsB` rejects these wherever the head has a position: the last by the two texts; no theorem of
this file says it; it is evaluated at five requests in Honest/K3/WitReqGuards.lean
[not in this library].

Hypotheses that remain, in the last two.
  `h`, `h1`: `coveredAt` returns at Z and x.
  `hT`, `h2`: the layers' number of tokens is the head's number of positions.

Users. Honest/K3/LotInst.lean and Honest/K3/WitReqGuards.lean [not in this library] import this
file.

Limits. A reply file without a word counts as the token 0, as in the library's `Inst.asked`: no
test here rejects it. The library's own covered positions in a run are made of the reply that was
heard, or of the token 0 until one is heard (`lettersBy`, Pub.lean); these are made of the reply
that is asked about. That the reply file's token is the reply that a prover names is not said here:
the verifier's last test compares the two. That these covered positions are those of another
writer's instance is not said.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.SeatFits
import OnBytes.Model.HeadHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes.Model (Head.Covered Head.winOf)
open OnBytes.Model.Verify (words32)
open VerifiableInference.Desc.First (S)

/-- The reply that is asked about, as a number: the first word of the instance's y; 0 where y holds
no word: a default, which nothing in this file fences. -/
def askedTok (x : Inst) : ℕ := ((words32 x.y).getD 0 0).toNat

/-- The library's covered positions at the public part and the instance. -/
def coveredOfInst (Z : Pub) (x : Inst) : Except String Head.Covered :=
  (Z.s₀.withReq (words32 x.pub.request)).coveredAt Z.p.X.T Z.p.X.P.h.V (askedTok x)

/-- **The term.** The covered positions, and the token that is checked at each. Empty arrays where
the library's tests on the request's words and the reply reject. -/
def reqAt (Z : Pub) (x : Inst) : Head.Covered × Array ℕ :=
  match coveredOfInst Z x with
  | .ok cov => (cov, Head.winOf cov Z.p.X.hS.T (askedTok x))
  | .error _ => (default, #[])

/-- `coveredAt` returns. -/
def reqMadeB (Z : Pub) (x : Inst) : Bool := (coveredOfInst Z x).toOption.isSome

/-- The layers' number of tokens is the head's number of positions. -/
def sizesOneB (Z : Pub) : Bool := Z.p.X.T == Z.p.X.hS.T

/-- The arrays that `coveredAt` returns have one entry a position. -/
theorem coveredAt_sizes {T V y : ℕ} {s : S} {cov : Head.Covered}
    (h : s.coveredAt T V y = .ok cov) :
    cov.hOn.size = T ∧ cov.hWin.size = T ∧ cov.hOnC.size = T := by
  unfold S.coveredAt at h
  dsimp only at h
  split_ifs at h
  obtain rfl := Except.ok.inj h
  simp

/-- `winOf` keeps the number of entries. -/
theorem winOf_size (cov : Head.Covered) (T y : ℕ) : (Head.winOf cov T y).size = cov.hWin.size := by
  unfold Head.winOf
  split <;> simp

/-- **Where `coveredAt` returns and the two numbers are one, `reqFitsB` accepts the term.** -/
theorem reqFits_of_covered (Z : Pub) (x : Inst) (cov : Head.Covered)
    (h : coveredOfInst Z x = .ok cov) (hT : Z.p.X.T = Z.p.X.hS.T) :
    reqFitsB Z.p.X (reqAt Z x) = true := by
  obtain ⟨a, b, c⟩ := coveredAt_sizes h
  unfold reqAt reqFitsB
  rw [h]
  simp only [winOf_size, a, b, c, hT, beq_self_eq_true, Bool.and_self]

/-- The same from the two tests with code. -/
theorem reqFits_of_tests (Z : Pub) (x : Inst) (h1 : reqMadeB Z x = true)
    (h2 : sizesOneB Z = true) : reqFitsB Z.p.X (reqAt Z x) = true := by
  unfold reqMadeB at h1
  unfold sizesOneB at h2
  cases h : coveredOfInst Z x with
  | error e => rw [h] at h1; exact absurd h1 (by simp [Except.toOption])
  | ok cov => exact reqFits_of_covered Z x cov h (beq_iff_eq.1 h2)

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.coveredAt_sizes
#print axioms ProofFile.Honest.K3.winOf_size
#print axioms ProofFile.Honest.K3.reqFits_of_covered
#print axioms ProofFile.Honest.K3.reqFits_of_tests
