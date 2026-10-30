--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/TokenAtEnd.lean.
WHAT IT DOES NOT SHOW. No soundness. THAT THE BLOCKS BEHIND THE NEXT TOKEN's BLOCK LEAVE THE REPLY:
a
premise (hleaves): at a description whose first chain the driver makes it is the guard's law
(Desc/Sound/GuardAtDriver.lean: every block of the flat list stands at a place of the kind K7 or
leaves the reading), together with "no other block stands at such a place", which is not here. That
a fold ends: a premise. That the request's words pass the record's test at any record: a premise.
LETTERS. No "there is".
OBJECT. Desc/Block.lean's chainAt: a chain's fold over its flat list, with nothing left over; and
Desc/First/State.lean's S.reqOk.
USER. The two premises on the LAST record of the law on the description's last test
(Law/FinAsked.lean: fin_of_heard): that what stands in the reply's seat is an entry of the
vocabulary, and that the record passes its own test on the request.
WHAT IT IS. WHAT THE NEXT TOKEN's BLOCK MAKES (every element in the reply's seat is an entry of the
vocabulary) STILL HOLDS AT THE END OF THE CHAIN's FOLD, IF NO LATER BLOCK TURNS THE REPLY; AND THE
RECORD's OWN TEST ON THE REQUEST READS THE REQUEST's WORDS ALONE.
  tokSmall_at_end   the first: one call of the landed law on folds (Desc/Sound/FoldHeardProofs.lean:
                    chainLays), at the reading "TokSmall V" in the place of the reply itself.
  reqOk_of_req      the second.
Searched before it was typed (statements that name chainAt with TokSmall or isToken; conclusions
with reqOk on both sides; over this library, the base's fourth issue, landing 146 and the packs at
hand): nothing of these shapes.

-/
import Mathlib
import Johnson.Desc.Sound.FoldHeardProofs
import Johnson.Desc.Kinds.Law.TokenSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (Block chainAt chainLays)
open VerifiableInference.Desc.First (S)

/-- **What the next token's block makes holds at the end of the chain's fold.** -/
theorem tokSmall_at_end (V : Nat) {Cl : Type} {name : String} {ft : Nat}
    (pre : List (Block S Cl)) (b : Block S Cl) (post : List (Block S Cl)) {s e : S}
    {v : Fmt.View} (hmade : ∀ s rs gs t, b.decide s rs gs = .ok t → TokSmall V t)
    (hleaves : ∀ c ∈ post, c.Leaves (fun s : S => s.out.reply))
    (hfold : chainAt name ft (pre ++ b :: post) s v = .ok e) : TokSmall V e := by
  have h := chainLays S Cl Prop (fun s => TokSmall V s) (fun _ => True) name ft pre b post s e v
    (fun s rs gs t hd => eq_true (hmade s rs gs t hd))
    (fun c hc s rs gs s' hd => propext
      ⟨fun a => tokSmall_rides V a (hleaves c hc s rs gs s' hd).symm,
        fun a => tokSmall_rides V a (hleaves c hc s rs gs s' hd)⟩) hfold
  exact of_eq_true h

/-- **The record's own test on the request reads the request's words alone.** -/
theorem reqOk_of_req {s s' : S} (h : s'.req = s.req) (T V : Nat) :
    s'.reqOk T V = s.reqOk T V := by
  unfold S.reqOk S.tokv S.rowR S.rowE S.reqT
  rw [h]

end VerifiableInference.Desc.Kinds.Head.Law
