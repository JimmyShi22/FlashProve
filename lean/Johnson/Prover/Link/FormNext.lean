-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormNext.lean: THE FORM's HALF: THE FOLD's FRONT AT ANY STAGE: the letter for
what stands in front of a batching whose row a fold takes next, said of a statement, a group's
number and a group: no carried record, no plan.

What is proved of it: Johnson/Prover/Link/FormNextLaws.lean, FormNextSwitch.lean.

Main names.
  StageFront S g G cur nxt i n id   A RECORD OF PREMISES: TestFront
    (Johnson/Prover/Link/FormFirst.lean) without its three clauses on the plan's list of codes and
    on the carried record's note of the mask: the group is there and is G; the statement is in
    order; the rows that the test takes in are dense (DenseRow); G's two codes are i's and are
    the stage cur's; the next stage's two codes are n's and are nxt's; the layout has the stage's
    two numbers of row variables; a member has a main row; no member is kept; the message id is a
    fresh table of 2 ^ h mask rows, unsampled, unspent, no member; three tests on the stages'
    numbers.

Limits. A letter: nothing says here that a record meets it.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12
open OnBytes.Slice.ProxRun (DenseRow)

/-- **What stands in front of a batching whose row a fold takes next.** The field `fresh` says of
the message number id: it is there; `mainRows = 0`; `maskRows = 2 ^ cur.h`; its `maskCode` is i.2;
`sampled = false`; `answers = 0`; `spentAsMask = false`; it is no member of G. -/
structure StageFront (S : Statement) (g : Nat) (G : Group) (cur nxt : Fmt.M1.Stage)
    (i n : Nat × Nat) (id : Nat) : Prop where
  group : S.groups[g]? = some G
  order : InOrder S
  dense : ∀ r ∈ (runRows S G).toList, DenseRow r
  code : G.code = i.1
  maskCode : G.maskCode = i.2
  base : S.codes.base[i.1]? = some ⟨cur.C.a, cur.C.l, cur.C.r⟩
  maskC : S.codes.mask[i.2]? = some ⟨cur.Z.a, cur.Z.l, cur.Z.r⟩
  base1 : S.codes.base[n.1]? = some ⟨nxt.C.a, nxt.C.l, nxt.C.r⟩
  mask1 : S.codes.mask[n.2]? = some ⟨nxt.Z.a, nxt.Z.l, nxt.Z.r⟩
  layK : (layoutOf S G).k = cur.k
  layH : (layoutOf S G).h = cur.h
  main : ∃ j < G.members.size, ∃ x, S.oracles[G.members.getD j noId]? = some x ∧
    0 < x.shape.mainRows
  noKept : ∀ j, G.kept.getD j false = false
  fresh : ∃ o, S.oracles[id]? = some o ∧ o.shape.mainRows = 0 ∧ o.shape.maskRows = 2 ^ cur.h ∧
    o.shape.maskCode = i.2 ∧ o.sampled = false ∧ o.shape.answers = 0 ∧ o.spentAsMask = false ∧
    id ∉ G.members
  stage : K12.stageOk false cur = true
  stage1 : nxt.Z.a ≤ nxt.C.a
  vars : cur.k + ceilLog2 cur.C.l ≤ 63

end Johnson.Prover.Link
