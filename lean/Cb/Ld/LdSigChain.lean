-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSigChain.lean: a check that two theorems meet at one joint: the step in which the prover
sends new oracle messages, each with its sample, ends where the lifted reduction on claims about the
messages of all oracles, those of the statement and the new ones, begins, so the rule for chains
applies.

Statement (`Spec.sigChain_send_then`) and proof.

The sending of a family to a statement over S (Cb/Ld/LdSigSum.lean) ends at the joint over
`S.sum N`, with the condition ("collision-free", and the base joint's own condition) moved into the
relaxed relation (`Rels.cf`, Ior/KnowCollGood.lean). A block R on claims about messages, knowledge
sound for each fixed tuple of messages (`GoodAt`, Cb/Ld/LdSigLift.lean), lifted over `S.sum N`,
begins at the same joint (after `goodT_cf`, Ior/KnowCollGood.lean). The rule for chains
(`goodT_seq`, Ior/KnowCollGood.lean) takes the two with nothing in between. The numbers of the
composition are `Nums.seq` of the two (Ior/Chain.lean): errors in a row, probabilities added, the
composed budget; the extractor is the composed extractor (`IOR.extSeq`). The collision is paid once,
in the round of the seed (`ldSendFamErr`, Cb/Ld/LdSendFam.lean: the error of round 1); the block's
errors carry no list size.

Main names:
  `Spec.sigChain_send_then`: under the hypotheses of its statement (those of `Spec.ldSendSig_goodT`,
    Cb/Ld/LdSigSum.lean; `GoodAt R H (S.grow N A bk) B ext P`; `H.Exact (S.grow N A bk).rel P.bud`),
    the composition has `GoodT` from `(S.over A).cf` to `((S.sum N).over B).cf`.
    `IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with
    its honest side, between two joints, at given numbers; among its clauses: completeness between
    the honest relations, outside sets of verifier randomness whose probabilities further clauses
    bound by the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations,
    on the input joint's set of statements, with a given extractor, at the numbers' list of errors;
    and one on honest-verifier zero knowledge. Here `GoodT` is the conclusion of
    `Spec.sigChain_send_then`.

Notation: `S`, `N`: signatures (`Sig`, Cb/Ld/LdSig.lean); `bk`: a function from the new messages and
a further witness to A's further witness; `L`, `t`: a number for each member of N, in `ListLE (L a)`
and `N.budT t`; `P`: the numbers of R (`Nums`, Ior/Chain.lean); `d`: a witness (`S.Wit × Wp`), the
last argument of `IOR.extSeq`. Signature: the oracle messages of a statement: a finite type of
names, with the data of an oracle message for each; not a digital signature. The seven hypotheses of
`Spec.ldSendSig_goodT`, by name: `LdCode.Laws` (Cb/Ld/LdRel.lean); `Sig.Seeds.Fair`,
`Sig.Sender.Laws`, `Sig.Sender.Blind` (Cb/Ld/LdSendFam.lean); `OMsg.ListLE`, `OMsg.Evades`
(Cb/Ld/LdSig.lean); `Enc.Hides` (Cb/Gen/Code.lean) (what each asks: the head of Cb/Ld/LdRng.lean).

Limits: this file says nothing new: a corollary of four theorems, in three steps. For a masked block
(no exact zero knowledge of its own) the same holds of the bundle without zero knowledge
(Ior/Masked.lean), by the same three steps. No statement of this file says it.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSigSumProofs
import Cb.Ld.LdSigLiftProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

namespace Spec

/-- A sending, then a reduction on claims about all messages. -/
def sigChain_send_then : Prop :=
  ∀ (E : Type) [Field E] (S N : Sig E) (Sd : N.Seeds) (Kc St St' Wp Wp' Wp'' : Type)
      (E₀ E₀' : ExtSpec) (A : Rels Kc St E₀ (S.Msg × Wp)) (bk : N.Msg → Wp' → Wp)
      (D : N.Sender (S.Wit × Wp) (S.Wit × Wp')) (L t : N.O → ℕ) (R : IOR St E₀ St' E₀')
      (H : R.Honest ((S.sum N).Msg × Wp') ((S.sum N).Msg × Wp''))
      (B : Rels Kc St' E₀' ((S.sum N).Msg × Wp''))
      (ext : (S.sum N).Msg → St × E₀.Str → Tr R.shape → Wp'' → Wp') (P : Nums Kc R)
      (d : S.Wit × Wp),
    (∀ a, (N.om a).C.Laws) → Sd.Fair → (∀ a, (N.om a).ListLE (L a)) → (∀ a, (N.om a).Evades) →
    D.Laws (S.backN N bk) → D.Blind Sd → D.Nn.Hides (N.budT t) →
    GoodAt R H (S.grow N A bk) B ext P → H.Exact (S.grow N A bk).rel P.bud →
    GoodT ((ldSendSig S N Sd St E₀).seq (R.keep (S.sum N).Smp (S.sum N).ext))
      ((ldSendSigHon Sd St E₀ D).seq ((S.sum N).liftH H)) (S.over A).cf ((S.sum N).over B).cf
      (IOR.extSeq _ _
        (fun _ _ w =>
          (S.left N (T := OMsg.Wit) w.1, bk (N.msgs (S.right N (T := OMsg.Wit) w.1)) w.2))
        (fun a τ w => (w.1, ext ((S.sum N).msgs w.1) (a.1.1, a.2.1) τ w.2)) d)
      ((ldSendSigNums S N Sd St E₀ Kc L t).seq (P.keep (S.sum N).Smp (S.sum N).ext))

end Spec

theorem sigChain_send_then : Spec.sigChain_send_then := by
  intro E _ S N Sd Kc St St' Wp Wp' Wp'' E₀ E₀' A bk D L t R H B ext P d hC hF hL hE hD hB hZ g hx
  have g₁ := ldSendSig_chain E S N Sd Kc St Wp Wp' E₀ A bk D L t hC hF hL hE hD hB hZ
  have g₂ := goodT_cf _ _ _ _ _ _ _ _ _ _ _ _ _
    (sigLift_goodT E (S.sum N) Kc St St' Wp' Wp'' E₀ E₀' R H (S.grow N A bk) B ext P g hx)
  exact goodT_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d _ _ g₁ g₂

end Cb
