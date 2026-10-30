-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Out/TwVN.lean.
The public numbers of the flat function (TwV.vOf) for the lookups that the builder Cb.Tw.keyA makes
(OnBytes/Tie/Pv/Lookup/Value/TwO65.lean).

Every number is read off TwNums.Sizes and every place goes through Cb.Tw.mkM, mkP and kAt, which
are plain functions: no number is typed here. Definitions alone.

Main names:
  `ledJ S pl`: a sumcheck's places, from the function that numbers its mask entries.
  `numsJ K S`: the record TwV.Nums (JOf S) K. A place is an entry of one of the caller's three
    messages, by type: JOf S = Fin nKeys ⊕ Fin nPlanes ⊕ Fin nMasks. The table is the range table:
    row u is u. A key is an entry or a public constant (kAt).
The mask entries are numbered by the clamped functions pTieC, pKeyC, pTabC, pEndC, pBitC: an entry
that a sumcheck does not have goes to its constant's place or to its last shown value's; that no
entry which a sumcheck has is turned is not proved here. ledE.sh, which nothing reads, is the place
of the bits' shown value.
Limits: it holds no theorem. «General in S» is said of the text alone. The tests (their
definitions: OnBytes/Tie/Pv/Lookup/Port/TwRun.lean) run at one S
(TwNums.o65S) and are blind there to: the order of the pair in pads = [(1, 1)] and its exponent;
tgtT's «else 1» and formT's «else []» (no idle plane); rowNum's j < n + 2 against 2^w; keyEntry's
subtraction; ledT and oT at l ≥ 1; tab beyond rows 0, 1. mkM and mkP lay a number out of range on
entry 0. At an order that is no permutation TwV.byVar reads the list's member number o.length,
where the byte-level verifier's byVariable gives 0.

-/
import Cb.Pv.Lookup.Out.TwV
import OnBytes.Tie.Pv.Lookup.Value.TwO65

set_option autoImplicit false

namespace TwV
open TwNums TwNums.Sizes Cb.Tw

/-- a sumcheck's places, from the function that numbers its mask entries -/
def ledJ (S : Sizes) (pl : Ent → ℕ) : Led (JOf S) :=
  ⟨fun r t => mkM S (pl (.coef r t)), mkM S (pl .const), fun a => mkM S (pl (.shown a))⟩

def numsJ (K : Type) [Field K] (S : Sizes) : Nums (JOf S) K where
  v' := S.v'
  d := S.d
  w := S.w
  n := S.n
  tab := fun u => (u : K)
  pads := S.pads
  oK := S.ordK
  oT := S.ordT
  oE := S.ordE
  oB := S.ordB
  kAt := fun b => (kAt K S b).getLeft?
  kC := fun b => Sum.elim (fun _ => 0) id (kAt K S b)
  bAt := fun u j => mkP S (S.planeEntry u j)
  ledTie := fun j => ledJ S (S.pTieC j)
  ledK := fun l => ledJ S (S.pKeyC l)
  ledT := fun l => ledJ S (S.pTabC l)
  ledE := ⟨(ledJ S S.pEndC).pw, (ledJ S S.pEndC).c0, fun _ => mkM S (S.pBit (.shown 0))⟩
  ledB := ledJ S S.pBitC

end TwV
