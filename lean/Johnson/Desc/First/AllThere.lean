-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/AllThere.lean: at every public test that is asked between two sub-protocols, is
the
public datum there that the test reads? A test with code, beside `allFilled`
(Johnson/Desc/First/AllFilled.lean). No Mathlib.
Why. `allFilled` says that some author's part CLAIMS each public item that is asked. Six sorts of
item
are answered through an option computed from public data ("(nsOf m).any ...", "(placeAt X m dg).any
..."): where that option is none, the test is FALSE AT EVERY STATE OF THE VERIFIER, silently: what
is
asked of the verifier's state there could then never hold.
  `dataThere D q`: the option that the answering part reads at q is some; true at every item whose
  part
    reads none: freeAbove (the number of slots) · callerIn (the caller's slot number, at a
    feed-forward or an attention segment) · lookIn, lookOut (the lookup argument's place AND that
    place's shape: two options, one inside the other) · "K5.okAt", "K5.plain" (the attention
    segment's
    parameters).
  `notThere D M links ps`: for printing: (position, item) wherever it is none.
  `allThere D M links ps`: there is no such pair.
  `allThere_mem`: what its "true" gives, position by position and item by item.
Limits: `dataThere` RESTATES which option each part's test reads: no theorem here holds it against
these
tests. It reads the real data D: it can be evaluated only where D is closed. It has been evaluated
nowhere. That the datum is the RIGHT one is not said. NOT COVERED, BEING NO OPTION OF D's AT THE
ITEM's OWN
SEGMENT: "K5.readsThere" reads the attention parameters at the number of the link that is open in
the
verifier's state; formsIn, formsInT and totalIn answer nowhere where the segment's link is none;
clauses on public data alone inside a test (lengths, codes); defaults of getD. The first version
missed the place's shape (a reader's find). No soundness is claimed.

-/
import Johnson.Desc.First.AllFilled

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First.Look (k3SortAt placeAt)
open VerifiableInference.Desc.First.FillK4 (isLay)

/-- The option that the answering part reads at the item is some. -/
def dataThere (D : PubData) : Pub → Bool
  | .freeAbove m => (D.nsOf m).isSome
  | .callerIn m =>
    if isLay D.links m then (D.nextOf m).isSome
    else if D.d5.isAtt m then (D.d5.first? m).isSome
    else true
  | .lookIn m pc =>
    (k3SortAt D.d3.X m pc).all fun dg => (placeAt D.d3.X m dg).any fun p => p.shape.isSome
  | .lookOut m pc =>
    (k3SortAt D.d3.X m pc).all fun dg => (placeAt D.d3.X m dg).any fun p => p.shape.isSome
  | .more (some m) name =>
    if D.d5.isAtt m && (name == "K5.okAt" || name == "K5.plain") then (D.d5.W.A[m / 2]?).isSome
    else true
  | _ => true

/-- For printing: where the datum is none. -/
def notThere (D : PubData) (M : More) (links : List ModelPart) (ps : List Place) : List (Nat × Pub) :=
  (askedAt M links ps).zipIdx.flatMap fun x =>
    (x.1.filter fun q => !dataThere D q).map fun q => (x.2, q)

/-- **At every asked item the datum that its test reads is there.** -/
def allThere (D : PubData) (M : More) (links : List ModelPart) (ps : List Place) : Bool :=
  (askedAt M links ps).all fun Q => Q.all (dataThere D)

theorem allThere_mem (D : PubData) (M : More) (links : List ModelPart) (ps : List Place)
    (h : allThere D M links ps = true) (Q : List Pub) (hQ : Q ∈ askedAt M links ps) (q : Pub)
    (hq : q ∈ Q) : dataThere D q = true :=
  List.all_eq_true.1 (List.all_eq_true.1 h Q hQ) q hq

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.allThere_mem
