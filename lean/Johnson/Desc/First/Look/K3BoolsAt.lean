-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3BoolsAt.lean: the kind "lookup" (K3): THE PUBLIC Bools THAT THE LOOKUPS'
LAWS ASK, EACH AS A FUNCTION OF A PUBLIC RECORD X, THE CALLER's DATA D, A LINK's NUMBER i, THE SORT
OF LOOKUP AND A CARRIED RECORD s: so that a walk over a chain's records can evaluate them.
Definitions alone: no theorem, no IO, no file is read.

Main names (digits = true: the lookup on the smallness test's digits; false: on the link's calls).
  k3PlaceThere X i digits: the public record has such a place and its parameters make a shape.
  k3OnInAt X i digits s: k3OnIn (Johnson/Desc/First/Look/K3Borders.lean) at that place: TO BE TRUE
    AT THE BORDER IN FRONT OF THE LOOKUP's BLOCK.
  k3OnOutAt X i digits s: k3OnOut at that place: TO BE TRUE BEHIND THE BLOCK AND UP TO THE FRONT OF
    THE LINK's BATCHING.
  k3LookInAt X D i digits s: k3LookIn (K3LookIn.lean): k3OnIn, and the record stands in link i with
    D's table of arrays: IN FRONT OF THE BLOCK.
  digBAt X D i: digB (K3CallerTests.lean) at digAt X i, at rad := 0 and the prime: OF X AND D ALONE:
    no record enters.
  k3DigitsFront X D i s, k3DigitsBehind X i s: what the digits' laws ask together in front and
    behind.
OBJECT. No block's text: Bools on the public record and the carried record.
USER. A walk over a chain's records. Theorems name k3OnOutAt and k3LookInAt
(K3Fill.lean, K3DigitsBehind.lean and others); no theorem calls the other five names.
LETTERS. X, D, i, digits, s.
Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)
Limits. A «true» IS AN EVALUATION AT ONE RECORD OF ONE RUN: it shows that a premise of a law is not
empty there; it proves nothing. None where there is no place: false. D is an argument: whoever
evaluates makes it as Verify.shapesOf and Params.proofSized do. That the record's codes, shape and
layout are D's has no Bool here.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerTests
import Johnson.Desc.First.Look.K3LookIn
import Cb.Gl.GlField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- The public record has such a place, and its parameters make a shape. -/
def k3PlaceThere (X : Verify.Public) (i : Nat) (digits : Bool) : Bool :=
  (placeAt X i digits).any fun p => p.shape.isSome

/-- The promise in front of the lookup's block. -/
def k3OnInAt (X : Verify.Public) (i : Nat) (digits : Bool) (s : First.S) : Bool :=
  (placeAt X i digits).any fun p => Desc.K3.k3OnIn p s

/-- The promise behind it, up to the front of the link's batching. -/
def k3OnOutAt (X : Verify.Public) (i : Nat) (digits : Bool) (s : First.S) : Bool :=
  (placeAt X i digits).any fun p => Desc.K3.k3OnOut p s

/-- The public item «the lookup's condition in front of its block», as the lookups fill it. -/
def k3LookInAt (X : Verify.Public) (D : Sent) (i : Nat) (digits : Bool) (s : First.S) : Bool :=
  (placeAt X i digits).any fun p => k3LookIn p (D.arrayOf.getD i #[]) s

/-- The one Bool of the digits' closed caller, at link i. -/
def digBAt (X : Verify.Public) (D : Sent) (i : Nat) : Bool :=
  (digAt X i).any fun xt => digB (Params.settingOf X.P.frame) xt.1 xt.2 D (fun _ => 0) Cb.Gl.p

/-- In front of the digits' lookup. -/
def k3DigitsFront (X : Verify.Public) (D : Sent) (i : Nat) (s : First.S) : Bool :=
  digBAt X D i && k3LookInAt X D i true s

/-- Behind it. -/
def k3DigitsBehind (X : Verify.Public) (i : Nat) (s : First.S) : Bool := k3OnOutAt X i true s

end VerifiableInference.Desc.First.Look
