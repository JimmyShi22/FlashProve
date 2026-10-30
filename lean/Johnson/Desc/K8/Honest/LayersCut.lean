-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/LayersCut.lean: THE SMALLNESS TEST: THE ORDER OF A LAYERS' SEGMENT's RUNS OF
CLAIMS, CUT AT "K8.equations", AND THE TWO CONDITIONS ON ITS STRETCHES, UNDER NAMES OF THEIR OWN.
Definitions and lemmas; none of the library's goals. No prover stands in them; nothing on
completeness, soundness or hiding.

  `layPre`, `layPost`, `lay_order`   the five entries in front of "K8.equations", the one behind,
      and that the order is these
  `lay_preOk`, `lay_postOk`   `PreOk`, `PostOk` (Johnson/Desc/K8/Honest/GathersPlain.lean) at these
      lists, under the assembly's ties
THE PROOFS ARE THE LINES INSIDE THE PROOF OF `plain_layers` (Johnson/Desc/K8/Honest/CountFrom.lean),
whose statement hides the cut behind an "exists". The like for the other two sorts: `attPre`,
`att_pre`, `post_nil` (FallAtt.lean); `headPre`, `headPost`, `head_pre`, `head_post`
(FallHead.lean).
Limits. The ties are premises.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K8.Honest.GathersPlain
import Johnson.Desc.K8.Honest.PlainRuns
import Johnson.Desc.First.Link.Law.PayLayers
import Johnson.Desc.First.Driver.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc

/-- The entries of a layers' segment's order in front of "K8.equations". -/
def layPre : List (Nat × String) :=
  [(1, "objects"), (1, "guests"), (2, "front"), (6, "objects"), (6, "guests")]

/-- The entry behind it. -/
def layPost : List (Nat × String) := [(2, "back")]

/-- **Each run in front of "K8.equations" at a layers' segment stands under a run that is free of
the batching element.** -/
theorem lay_preOk (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat)
    (ties : LinkJoin.LayersTies L p4 nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits) :
    PreOk L layPre := by
  intro o ho run hat
  simp only [layPre, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, tC run hat, plain_objectsCalls⟩
  · exact ⟨_, ties.tGuests 1 (by simp) run hat, plain_idle⟩
  · obtain ⟨r, l, u⟩ := ties.tFront run hat
    exact ⟨r, u, plain_front p4 r l⟩
  · exact ⟨_, tD run hat, plain_objectsDigits⟩
  · exact ⟨_, ties.tGuests 6 (by simp) run hat, plain_idle⟩

/-- **The like behind it.** -/
theorem lay_postOk (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat)
    (ties : LinkJoin.LayersTies L p4 nU) : PostOk L layPost := by
  intro o ho run hat
  obtain rfl : o = (2, "back") := List.mem_singleton.1 ho
  obtain ⟨r, l, u⟩ := ties.tBack run hat
  exact ⟨r, u, behind_back p4 r l⟩

/-- The order of a layers' segment, cut at "K8.equations". -/
theorem lay_order : First.orderOf .layers = layPre ++ (4, "K8.equations") :: layPost := rfl

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.lay_preOk
#print axioms VerifiableInference.Desc.First.K8.Honest.lay_postOk
#print axioms VerifiableInference.Desc.First.K8.Honest.lay_order
