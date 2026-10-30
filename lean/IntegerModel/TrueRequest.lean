-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/TrueRequest.lean: what a true request is, in terms of the
model function.
This file is about the predicate
`Cm.PaperTrue s.kap s.nf i x` (Cm/RelTruePaper.lean; "true request" in
the names of this file's theorems), at a lawful table of scales s, an index i (a matrix of digits
that holds the weights) and a request x: 1,024 tokens, counted from 0; an announced token y, which
counts as token 1,024; two numbers r and e. `isTrueRequest_iff_isReply`: it holds exactly if
  (a) the request has its form: r < e ≤ 1,024, and y = 0 where e < 1,024;
  (b) the reply tokens r + 1 .. e are what the model function outputs, token by token, each after
      the request's tokens before it;
  (c) the model function has a value on the list of the tokens 0 .. 1,023: no range condition of
      the integer program fails at any position, covered or not.
There the model function is `programNextToken` (IntegerModel/Reply.lean), the library's integer
program. `isTrueRequest_iff_model`: the same with `IntegerTransformer.model`, the function on arrays
(IntegerModel/Model.lean, a file without imports), at the arrays made from s, from the weights in i
and from the library's five fixed tables (`Readable.tablesArrays`,
IntegerModel/Readable/Exists.lean). Clause (c) reads the tokens after the reply as well: a true
request is more than a request whose reply is the model's. The statements read i only through the
weights that it holds.
-/
import IntegerModel.ReplyOnWindow
import IntegerModel.Readable.AtCommitted
import Cm.Rel2Proofs
import Cm.RelTrue
import Cm.RelTruePaper

set_option autoImplicit false

open Inst.Model

/- No default table of scales here: `Scl.ref` (Inst/Model/Scl.lean) is off; each `Scl` is named. -/
attribute [-instance] Inst.Model.Scl.ref

namespace IntegerModel

/-- The arguments of the model function at a lawful table of scales and an index: the table's
numbers and the weights that the index holds. `Settings` has room for an acceptance policy, which a
table of scales does not have; it is set to exact match, and `programNextToken` does not read it. -/
def committedOf (s : Cm.Scales) (hs : s.Lawful) (i : Cm.Idx) : Committed :=
  ⟨⟨s.w, s.nf, AcceptancePolicy.exact⟩, i.index, hs.toPP⟩

/-- The sentence `Cm.TrueAt` (Cm/RelBase.lean) is `HoldsOnWindow` at the weights that the index
holds. -/
theorem trueAt_iff_holdsOnWindow (pp : ScalesAndPolicy) (i : Cm.Idx) (x : Request) :
    Cm.TrueAt pp.kap pp.nf i x ↔ HoldsOnWindow pp i.index x :=
  Iff.rfl

/-- `HoldsOnWindow` at given weights is `Cm.TrueAt` at the index made from them. -/
theorem holdsOnWindow_iff_trueAt (pp : ScalesAndPolicy) (w : Weights) (x : Request) :
    HoldsOnWindow pp w x ↔ Cm.TrueAt pp.kap pp.nf (Cm.Idx.ofIndex w) x := by
  rw [trueAt_iff_holdsOnWindow, Cm.index_ofIndex]

/-- At the index made from given weights, the model function's weights are these. -/
theorem committedOf_ofIndex (s : Cm.Scales) (hs : s.Lawful) (w : Weights) :
    (committedOf s hs (Cm.Idx.ofIndex w)).weights = w :=
  Cm.index_ofIndex w

/-- At a lawful table of scales, a request is true exactly if it is well formed, its reply is the
program's, and the program has a value on all 1,024 tokens of its window. -/
theorem isTrueRequest_iff_isReply (s : Cm.Scales) (hs : s.Lawful) (i : Cm.Idx) (x : Request) :
    Cm.PaperTrue s.kap s.nf i x ↔
      (requestWellFormed x = true ∧ IsReply (committedOf s hs i) x ∧
        (programNextToken (committedOf s hs i) (firstToks x 1024)).isSome = true) :=
  (Cm.paper_iff s.kap s.nf i x).symm.trans
    ((trueAt_iff_holdsOnWindow ⟨s.w, s.nf, AcceptancePolicy.exact⟩ i x).trans
      (holdsOnWindow_iff (committedOf s hs i) x))

/-- The same with the function on arrays: `Readable.modelOf m` is `IntegerTransformer.model` at the
arrays made from m and from the five fixed tables (IntegerModel/Readable/AtCommitted.lean), and
`Readable.greedy` applies it token by token (IntegerModel/Readable/Tie.lean). -/
theorem isTrueRequest_iff_model (s : Cm.Scales) (hs : s.Lawful) (i : Cm.Idx) (x : Request) :
    Cm.PaperTrue s.kap s.nf i x ↔
      (requestWellFormed x = true ∧
        (x.r < x.e ∧
          Readable.greedy (Readable.modelOf (committedOf s hs i)) (Readable.nums (promptOf x))
            (x.e - x.r) = some (Readable.vals (replyOf x))) ∧
        (Readable.modelOf (committedOf s hs i)
          (Readable.nums (firstToks x 1024))).isSome = true) := by
  rw [isTrueRequest_iff_isReply s hs, Readable.isReply_iff_model, Readable.modelOf_eq,
      Option.isSome_map]

/-- The right side of `isTrueRequest_iff_isReply` is met. At every lawful table, at the index of the
all-zero weights and for all r < e ≤ 1,024, the request with all tokens 0 is well formed, its reply
is the program's, and the program has a value on its window. At these weights every logit is 0
(Inst/Model/ProgramRGuards.lean: `lg_zero`), so token 0 is the answer whatever the tokens are: the
example does not show that weights or earlier tokens are read. For that, Cm/RelTrue.lean has, at the
reference table of scales, a request that is true at one index and not at another that differs from
it in one layer only (`Cm.true_layer`), and a reply that is true after one prompt and not after
another with the same last token (`Cm.true_earlier`). For the model as a function on arrays:
`modelNextToken_reads_layer`, `modelNextToken_reads_earlier_token`
(VerifiableInference/ModelGuardsAtReference.lean). -/
theorem isTrueRequest_atZeroWeights (s : Cm.Scales) (hs : s.Lawful) (rF eF : Fin (ppref.T + 1))
    (hre : rF.val < eF.val) :
    requestWellFormed (RequestGuards2.xz rF eF) = true ∧
      IsReply (committedOf s hs (Cm.Idx.ofIndex ScalesSanity.iZero)) (RequestGuards2.xz rF eF) ∧
      (programNextToken (committedOf s hs (Cm.Idx.ofIndex ScalesSanity.iZero))
        (firstToks (RequestGuards2.xz rF eF) 1024)).isSome = true :=
  (isTrueRequest_iff_isReply s hs _ _).1 ((Cm.paper_iff _ _ _ _).1 (Cm.true_zero hs.toPP rF eF hre))

end IntegerModel
