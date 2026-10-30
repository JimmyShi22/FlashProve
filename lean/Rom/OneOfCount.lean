-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/OneOfCount.lean: let G be a scheme with batches (`Gen.Arg`, ZKCP/Gen.lean) over the one hash
function (`rom lam`), and `oneOf G` (ZKCP/SpecialAny.lean) its form with one request in each call. A
bound on the queries of C, P and V of G is also one for `oneOf G`, as ZKCP/Defs.lean counts queries.
Generic: for every such G.

  `queryBound_ofRom`      An oracle algorithm over the family with one oracle, written in the syntax
                          of ZKCP/Defs.lean, keeps its bound.
  `queryBound_oneOf_C`, `queryBound_oneOf_P`, `queryBound_oneOf_V`
                          A bound for C at i, for P on the batch [(x, w)] and for V is one for the
                          same algorithm of `oneOf G`.

Notation: `G : Gen.Arg (rom lam) I X W IVK ISK Pf` (ZKCP/Gen.lean): ARG = (C, P, V) over the family
S (here `rom lam`); P takes a batch and returns one proof for each slot; `C`, `P`, `V`
(ZKCP/Defs.lean, `Arg`): the index committer; the prover; the verifier;
`oneOf G : Arg lam I X W IVK ISK Pf` (ZKCP/SpecialAny.lean): the scheme of Defs.lean that G gives;
`toRom`, `ofRom` (Rom/Bridge.lean): an oracle algorithm of ZKCP/Defs.lean as one over `rom lam`; an
oracle algorithm over `rom lam` as one of ZKCP/Defs.lean; `rom lam : OSpec` (Rom/OSpec.lean): the
model of ZKCP/Defs.lean: one oracle {0,1}* → {0,1}^lam.

Limits: a query counts as one however long its string. The bounds are on every path; nothing on the
expected number.
-/
import Rom.Bridge
import ZKCP.SpecialAny
import ZKCP.GenKeyTag

set_option autoImplicit false

namespace Rom
open ZKCP ZKCP.SpecialAny

variable {lam : ℕ} {α I X W IVK ISK Pf : Type}

theorem queryBound_ofRom (c : OComp (rom lam) α) (t : ℕ) (h : c.QueryBound t) :
    (ofRom c).QueryBound t :=
  (queryBound_toRom _ _).1 (by rw [toRom_ofRom]; exact h)

variable (G : Gen.Arg (rom lam) I X W IVK ISK Pf) {N : ℕ}

theorem queryBound_oneOf_C (i : I) (h : (G.C i).QueryBound N) : ((oneOf G).C i).QueryBound N :=
  queryBound_ofRom _ N h
theorem queryBound_oneOf_P (isk : ISK) (x : X) (w : W) (h : (G.P isk [(x, w)]).QueryBound N) :
    ((oneOf G).P isk x w).QueryBound N :=
  queryBound_ofRom _ N (Gen.queryBound_mapO _ _ N h)
theorem queryBound_oneOf_V (ivk : IVK) (x : X) (π : Pf) (h : (G.V ivk x π).QueryBound N) :
    ((oneOf G).V ivk x π).QueryBound N :=
  queryBound_ofRom _ N h

end Rom
