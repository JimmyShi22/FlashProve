-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/FrontSet.lean: a name for the form in which the proof file's first query is tied in this
library: a set of requests' early parts that is fixed beforehand and on which the request's spelling
is one to one; and that the first query of a call whose request lies in the set passes the test on
first queries, under further premises on the call (`hrest`, `tableSmall`, three bounds).

THE LETTERS MEET; THIS IS NO TIE. One record, three short definitions, three statements. What is
laid together, all general in the interface with records: Johnson/Top/FrontItems.lean: `okItems`,
`hreq_items`, `okItems_run`; OnBytes/Maker/Page/FitOwn.lean: `fFrontP_own`;
Johnson/Maker/Page/ReqAt.lean: `reqOf`, `early_xinBA`.

THE FORM. sp gives the two strings that the first chain's statement takes of a request's early part:
the value of the item `request`, which holds the tokens by digests of the second hash function K;
and the request file's bytes. For requests in a set R fixed before the hash is drawn and before the
run, on whose early parts the PAIR is one to one: a tie in this form speaks of every accepted call
whose request lies in R; outside R nothing is tied. WHERE THE SECOND STRING IS THE REQUEST FILE's
OWN BYTES THE PAIR IS ONE TO ONE ON ALL EARLY PARTS, BY SPELLING, UNDER PREMISES ON THE OBJECT (two
bounds on its sizes among them): `FrontSet.ownWords` (Johnson/Flat/FrontSetOwnAt.lean): that set has
every instance, and its field `apart` assumes nothing of any hash. At a spelling that held a request
through K's digests alone, `apart` would assume of K what no proof gives for a wide set of requests;
over a set with more early parts than K has values it would be false, by counting. No program tests
whether a request lies in R: an accepted call whose request lies outside R is tied to nothing. And
at a spelling through K's digests ALONE `apart` could not be left out: where the arm holds the
second hash function as a FIXED function, a prover that is bounded in its queries alone could use a
collision of that fixed function, if one lies among the set's early parts, and pick tokens after the
challenges, so that over a set with such a collision no small error could be had for the arm. At
`ownWords` `apart` is a theorem, and a collision of K among the items costs nothing in it. (The
counting and this last sentence are arguments in words; no theorem of this library states them.)
This form is no public statement of soundness, and it is summed into no figure.

  `FrontSet L sp r₀` the data: a test okS on instances (the early parts of R), a test isR on
    records, and three laws: sp is one to one on what passes okS; isR lets r₀ through, and nothing
    else.
  `FrontSet.okX` the test on a typed instance of the interface: `okItems okS isR`.
  `FrontSet.Has S x` the early part of x passes okS: "the request lies in R".
  `FrontSet.hreq` the page's two strings `reqOf sp` are one to one on what passes `okX`: the premise
    `hreq` of `lawsP`, `proofLawsM` (Johnson/Maker/Page/FitM.lean, ProofLawsM.lean) and of
    `silentProof_laws` (OnBytes/Maker/Page/FitSilent.lean).
  `FrontSet.ho` the typed instance that the verifier of a proof file hands its chains passes `okX`,
    at a request that the set has.
  `FrontSet.front` **the test `fFrontP` on the first query says yes at that call**, if rest is tl of
    the root and the answers (hrest), the item "table" is small (hsm), and the two strings and the
    copy's number are below their bounds (hz, hcp): at the outer roots, the instance as the verifier
    lays it, and the front message that a typing lays.
  `FrontSet.single` the set of one early part. One request: too narrow to be of use.

ON EMPTINESS. A value of `FrontSet` is no hypothesis on all requests: its field `apart` speaks of
the named set. Where both strings held the tokens through digests of the second hash function alone,
no value of `FrontSet` would have all real requests, by counting; with the request file's bytes as
the second string one value has them all (`ownWords`), under premises on the object
(Johnson/Flat/FrontSetOwnAt.lean). A value exists at every sp (`single`, or the empty set). What is
said over a value S is said of calls with `S.Has x` alone: at any other call the first query does
not fit, an encoding made from S writes it behind its escape, and nothing is tied. No term here
makes S from a hash function; that S is chosen before the hash function is drawn does not follow
from anything here and has to be asked by whoever speaks under a probability.

On the records. The verifier lays the fixed record r₀ at both places of the instance in its first
query, by `xinBA`'s own text (`early_xinBA`, by unfolding): so the two clauses of `okItems` on the
records are paid at the first query by its form. No statement on the other queries of a run is used:
no other chain query holds an instance where late is none (by the definitions' text; no theorem:
`actOf`, `recomputeChain`, OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean; `lateInstancePart`,
OnBytes/TypedOracleCompiler/Compile/Batch/Oracles.lean).

Not claimed. That two instances that pass okS stand for two request files. `hrest`, `tableSmall` and
the three bounds at any call. That sp's two strings are what a program's statement takes: sp is a
letter, and nothing ties its two halves to each other. Nothing on any hash. Nothing on soundness.

-/
import Johnson.Top.FrontItems
import OnBytes.Maker.Page.FitOwn

set_option autoImplicit false

namespace OnBytes.K.Arm.ProofFront

open _root_.Run Iop
open OnBytes.Maker OnBytes.Maker.Page
open TypedOracleCompiler.Compile.Batch.Cms (typedOracleCarrier xinBA)

variable {I X : Type}

/-- **A test on instances on whose yeses the spelling is one to one** (meant: the early parts of a
set of requests that is fixed beforehand; the type asks neither); with a test that lets the fixed
record alone through. -/
structure FrontSet (L : HolographicProtocol I X) (sp : X → ByteArray × ByteArray) (r₀ : L.Rec) where
  /-- meant: the early parts of the set's requests -/
  okS : X → Bool
  /-- "is the fixed record" -/
  isR : L.Rec → Bool
  /-- no two of the set are spelt alike -/
  apart : ∀ x y, okS x = true → okS y = true → sp x = sp y → x = y
  one : ∀ r, isR r = true → r = r₀
  self : isR r₀ = true

namespace FrontSet
variable {L : HolographicProtocol I X} {sp : X → ByteArray × ByteArray} {r₀ : L.Rec} (S : FrontSet L sp r₀)

/-- The test on a typed instance of the interface. -/
abbrev okX : L.XC → Bool := okItems S.okS S.isR

/-- The request lies in the set: its early part passes. -/
def Has (x : X) : Prop := S.okS (L.early x) = true

/-- The page's two strings are one to one on what passes. -/
theorem hreq : ∀ z z' : L.XC, S.okX z = true → S.okX z' = true →
    reqOf (L := L) sp z = reqOf (L := L) sp z' → z = z' :=
  hreq_items sp S.okS S.isR r₀ S.apart S.one

/-- What the verifier of a proof file hands its chains passes, at a request that the set has. -/
theorem ho (x : X) (h : S.Has x) : S.okX ((some (L.early x), r₀, r₀) : L.XC) = true :=
  okItems_run S.okS S.isR r₀ x h S.self

/-- **The test on the first query says yes at a call whose request the set has**, under hrest, hsm,
the two bounds hz and the bound hcp. c₀, rest: the outer roots; ans, copy: what the front message
holds. -/
theorem front (Bd : Type) (aT : RoundSplits L.offline.shape) (aL : RoundSplits L.link.shape)
    (tl : Dig 256 → List E → List (Dig 256)) (c₀ : Dig 256) (ans : List E) (rest : List (Dig 256))
    (hrest : rest = tl c₀ ans) (hsm : tableSmall (c₀ :: rest) ans = true) (a : X × L.Rec)
    (h : S.Has a.1)
    (hz : (sp (L.early a.1)).1.size + 8 < 2 ^ 64 ∧ (sp (L.early a.1)).2.size + 8 < 2 ^ 64)
    (copy : ℕ) (hcp : copy < 2 ^ 64) :
    fFrontP tl (reqOf (L := L) sp) S.okX (c₀ :: rest)
      ((xinBA r₀ a).map (typedOracleCarrier L Bd aT aL).early) (frontOf ans copy) = true := by
  rw [early_xinBA Bd aT aL r₀ a]
  exact fFrontP_own tl (reqOf (L := L) sp) S.okX c₀ ans rest hrest hsm (some (L.early a.1), r₀, r₀)
    (S.ho a.1 h) hz copy hcp

/-- The set of one early part. One request: too narrow to be of use. -/
def single [DecidableEq X] (isR : L.Rec → Bool) (one : ∀ r, isR r = true → r = r₀)
    (self : isR r₀ = true) (x₀ : X) : FrontSet L sp r₀ where
  okS := fun x => decide (x = x₀)
  isR := isR
  apart := fun _ _ a b _ => (of_decide_eq_true a).trans (of_decide_eq_true b).symm
  one := one
  self := self

end FrontSet

end OnBytes.K.Arm.ProofFront

#print axioms OnBytes.K.Arm.ProofFront.FrontSet.hreq
#print axioms OnBytes.K.Arm.ProofFront.FrontSet.ho
#print axioms OnBytes.K.Arm.ProofFront.FrontSet.front
