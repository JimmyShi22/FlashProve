-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/PowBehind.lean: THE SMALLNESS TEST: UNDER "A LEDGER IS OPEN AND ITS BATCHING
ELEMENT IS θ", THE SENTENCE "THE TEST's DATA ARE THERE, AND THEIR VECTORS OF POWERS ARE THE POWERS
OF θ" (`PowAt θ`, Johnson/Desc/K8/Honest/PoweredRests.lean) IS HANDED ON BY EACH RUN THAT STANDS
BEHIND "K8.equations" IN A LINK's ORDER, AT A LINK OF EACH OF THE THREE SORTS: FROM THAT SORT's TIES
ALONE. In the library's three orders (`First.orderOf`) every entry of a lookup stands in front of
"K8.equations", which lays the sentence: SO NOTHING IS ASKED OF A LOOKUP's RUNS HERE. Behind it
stand: one entry at a feed-forward link, none at an attention link, two at the head's. None of the
library's goals.

  `PowOn Lk os`   the sentence is handed on at the entries of the list os
  `split_layers`, `split_attention`, `split_head`   the link's order, written as what stands in
                   front of "K8.equations", that entry, and what stands behind
  **`powOn_layers`**   LayersTake … → PowOn L [(2, "back")]
  **`powOn_head`**   HeadTake … → PowOn L [(3, "logits"), (8, "the merge")]
  `powOn_nil`   PowOn L []: at an attention link nothing stands behind
Each by the tie of that entry and `rests_pow`, as the library's `run_layers` and `run_head`
(Johnson/Desc/First/Link/Law/RunRel.lean) take these entries.
Limits. THE SORT's TIES ARE PREMISES. Nothing on the order behind the batching; nothing on the
adding of the claims; nothing on the draw.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.PoweredRests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (blockAtC)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K4Run
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Desc.First.K8.Honest (PowAt rests_pow)

/-- The sentence is handed on at the entries of a list. -/
def PowOn (Lk : Link S Claim) (os : List (ℕ × String)) : Prop :=
  ∀ θ : E, ∀ o ∈ os, ∀ run, At Lk o run → ∀ n e c e₁, run n e = .ok (c, e₁) →
    HasFork (fun G => G.theta = θ) e → PowAt θ e → PowAt θ e₁

theorem powOn_nil (Lk : Link S Claim) : PowOn Lk [] :=
  fun _ _ ho => absurd ho List.not_mem_nil

theorem split_layers {l : ℕ} {L : Link S Claim} (hL : SegAt l .layers L) :
    L.order = [(1, "objects"), (1, "guests"), (2, "front"), (6, "objects"), (6, "guests")] ++
      (4, "K8.equations") :: [(2, "back")] := by
  rw [hL.order]
  rfl

theorem split_attention {l : ℕ} {L : Link S Claim} (hL : SegAt l .attention L) :
    L.order = [(1, "objects"), (1, "guests"), (2, "first"), (2, "keys"), (2, "join"),
      (2, "second"), (1, "planes"), (6, "objects"), (6, "guests")] ++
      (4, "K8.equations") :: [] := by
  rw [hL.order]
  rfl

theorem split_head {l : ℕ} {L : Link S Claim} (hL : SegAt l .head L) :
    L.order = [(2, "objects"), (2, "guests"), (3, "norm"), (3, "join"), (3, "policy"),
      (2, "planes"), (7, "objects"), (7, "guests")] ++
      (5, "K8.equations") :: [(3, "logits"), (8, "the merge")] := by
  rw [hL.order]
  rfl

variable {β : Type} {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
  {Fu : S → Prop} {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
  {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
  {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}

/-- **Behind "K8.equations" at a feed-forward link.** -/
theorem powOn_layers {p : OnBytes.Desc.First.K4.Par}
    (A : LayersTake L u ψ Ok Fu p nU ent tm4 t3 l3) : PowOn L [(2, "back")] := by
  intro θ o ho run h n e c e₁ hr
  obtain rfl : o = (2, "back") := List.mem_singleton.1 ho
  obtain ⟨r, h0, hu⟩ := A.ties.tBack run h
  exact (rests_pow θ).back p r h0 n e c e₁ (hu n e c e₁ hr)

/-- **Behind "K8.equations" at the head's link.** -/
theorem powOn_head {h : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ} {p : Par}
    {kap : Phi β → Option Seen}
    (A : HeadTake L u ψ Ok Fu h iU3 l' piece p kap nU ent tm4 t3 l3) :
    PowOn L [(3, "logits"), (8, "the merge")] := by
  intro θ o ho run hr
  rcases List.mem_cons.1 ho with rfl | ho
  · obtain ⟨r, h0, hu⟩ := A.ties.tK6 "logits" (by simp) run hr
    exact rel_under hu (hands_run (rests_pow θ)
      (k6_still h iU3 p (phiAll u ψ) Ok kap A.hkap A.okK6 l' piece "logits" r h0).hands)
  · obtain rfl : o = (8, "the merge") := List.mem_singleton.1 ho
    exact rel_under (A.ties.tMerge run hr) (rests_pow θ).merge

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.powOn_nil
#print axioms VerifiableInference.Desc.LinkJoin.split_layers
#print axioms VerifiableInference.Desc.LinkJoin.split_attention
#print axioms VerifiableInference.Desc.LinkJoin.split_head
#print axioms VerifiableInference.Desc.LinkJoin.powOn_layers
#print axioms VerifiableInference.Desc.LinkJoin.powOn_head
