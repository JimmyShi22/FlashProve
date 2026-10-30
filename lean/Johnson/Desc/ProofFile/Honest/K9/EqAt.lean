-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/EqAt.lean: FOR THE ITEM "totalB": `ItemEq` (Honest/K9/EqItem.lean) AT THE CALLERS'
NINE RUNS, SORT BY SORT, FROM THE SEALED LIBRARY's OWN GATHERING OF A SORT's TIES AND LAWS (`LayersTake`, `AttTake`,
`HeadTake`). Statements and proofs; no goal is stated.
  **`eqs_layers`**   at a feed-forward segment: at (2, "front") and (2, "back")
  **`eqs_attention`**   at an attention segment: at (2, "first"), (2, "keys"), (2, "second")
  **`eqs_head`**   at the head's: at (3, "norm"), (3, "policy"), (3, "logits"), (8, "the merge")
EACH: where K9's lens reads the part b at s; s goes on from what is fixed at s under the promise (`Fx9`); the readers'
second hole says nothing at the entry; the table's public test `formsIn` says yes there: `ItemEq` at the sort's own
table of terms (`tmL`, `tmA`, `tmH` at `entUnit`) and the link's own readers. As the library's `items_layers`,
`items_attention`, `items_head` (Johnson/Desc/First/Link/Law/HitemsAt.lean), with the same calls, `eq_…`
(Honest/K9/EqK4.lean, EqStill.lean) standing for `item_…`; the entries "guests" are left out (their terms are the
empty list: Honest/K9/TotalItems.lean). No member; called by Honest/K9/EqCarry.lean and BackAt.lean.
WHAT IS NOT CLAIMED. Any premise at any state or link. That the second hole is silent: at the head's segment the
table's own holes (`K9.holesAt`) may speak where the run answers (where the tables can be made and the run answers
with them laid: by reading, shown nowhere), so these are called there at the empty hole (`K9.withSmall
K9.LinkHoles.none`); the carry from there to the readers with whatever second hole, under "the run itself answers at
s": Honest/K9/EqCarry.lean. The entries of the lookups, the two "join" (the head's: Honest/K9/EqMarks.lean),
"K8.equations". Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.EqK4
import Johnson.Desc.ProofFile.Honest.K9.EqStill
import Johnson.Desc.First.Link.Law.HitemsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc
open K5Law

variable {β : Type}

/-- **At a feed-forward segment.** -/
theorem eqs_layers (H : Desc.K9.LinkHoles) {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {p : OnBytes.Desc.First.K4.Par} {nU : Array ℕ}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {l3 : ℕ × String → Q β → ℕ} (A : LayersTake L u ψ Ok Fu p nU entUnit tm4 t3 l3) (own : List (ℕ × ℕ))
    (rd : ℕ × ℕ → MsgQ) (s : S) (b : Desc.K9.Part) (hb : atS.get? s = some b)
    (hgo : Fx9 (phiAll u ψ) Ok (fixed9 (phiAll u ψ) s) s) :
    ∀ o ∈ [(2, "front"), (2, "back")],
      H.silent o.1 o.2 s = none → Desc.K9.formsIn (Desc.K9.readersOfLink H L) own o.1 o.2 s = true →
      ItemEq (phiAll u ψ) (tmL p entUnit tm4 t3) (Desc.K9.readersOfLink H L) own rd o s b := by
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · intro hsil hin
    obtain ⟨R, hR⟩ := reader_of_formsIn _ own 2 "front" s hin
    obtain ⟨run, hAt⟩ := at_of_reader H L (2, "front") rfl s hsil R hR
    obtain ⟨r, h0, hu⟩ := A.ties.tFront run hAt
    exact eq_front H L _ Ok _ own rd (2, "front") rfl run r hAt p h0 hu (·.own)
      (fun s x hs => phi_k4_pi u ψ s x hs) A.okFront rfl s b hb hgo hsil hin
  · intro hsil hin
    obtain ⟨R, hR⟩ := reader_of_formsIn _ own 2 "back" s hin
    obtain ⟨run, hAt⟩ := at_of_reader H L (2, "back") rfl s hsil R hR
    obtain ⟨r, h0, hu⟩ := A.ties.tBack run hAt
    exact eq_back H L _ Ok _ own rd (2, "back") rfl run r hAt p h0 hu (·.own)
      (fun s x hs => phi_k4_pi u ψ s x hs) A.okBack rfl s b hb hgo hsil hin

/-- **At an attention segment.** -/
theorem eqs_attention (H : Desc.K9.LinkHoles) {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {rdA : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : First.Att.P.ParC}
    {nU : Array ℕ} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : AttTake L u ψ Ok Fu rdA c nU entUnit tm4 t3 l3) (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (s : S)
    (b : Desc.K9.Part) (hb : atS.get? s = some b) (hgo : Fx9 (phiAll u ψ) Ok (fixed9 (phiAll u ψ) s) s) :
    ∀ o ∈ [(2, "first"), (2, "keys"), (2, "second")],
      H.silent o.1 o.2 s = none → Desc.K9.formsIn (Desc.K9.readersOfLink H L) own o.1 o.2 s = true →
      ItemEq (phiAll u ψ) (tmA rdA c entUnit tm4 t3) (Desc.K9.readersOfLink H L) own rd o s b := by
  have key : ∀ (o : ℕ × String) (r : ℕ → S → Except String (List Claim × S))
      (fs : Q β → Option (List Aff)), (o.2 == "K8.equations") = false →
      (∀ run, At L o run → Under run r) → Still (phiAll u ψ) Ok r fs →
      tmA rdA c entUnit tm4 t3 o = plainTm (valsStill Reading.gl fs entUnit) →
      H.silent o.1 o.2 s = none → Desc.K9.formsIn (Desc.K9.readersOfLink H L) own o.1 o.2 s = true →
      ItemEq (phiAll u ψ) (tmA rdA c entUnit tm4 t3) (Desc.K9.readersOfLink H L) own rd o s b :=
    fun o r fs hne ht hS htm hsil hin => by
      obtain ⟨R, hR⟩ := reader_of_formsIn _ own o.1 o.2 s hin
      obtain ⟨run, hAt⟩ := at_of_reader H L o hne s hsil R hR
      exact eq_still_in H L _ Ok _ own rd o hne run r hAt fs (ht run hAt) hS htm s b hb hgo hsil hin
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact key _ _ _ rfl A.ties.tFirst (still_first _ Ok rdA c A.hrd A.okK5) rfl
  · exact key _ _ _ rfl A.ties.tKeys (still_keys _ Ok c) rfl
  · exact key _ _ _ rfl A.ties.tSecond (still_second _ Ok rdA c A.hrd A.okK5) rfl

/-- **At the head's segment.** -/
theorem eqs_head (H : Desc.K9.LinkHoles) {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {h : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ} {p : Kinds.Head.Par}
    {kap : Phi β → Option Kinds.Head.Law.Seen} {nU : Array ℕ} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : HeadTake L u ψ Ok Fu h iU3 l' piece p kap nU entUnit tm4 t3 l3) (own : List (ℕ × ℕ))
    (rd : ℕ × ℕ → MsgQ) (s : S) (b : Desc.K9.Part) (hb : atS.get? s = some b)
    (hgo : Fx9 (phiAll u ψ) Ok (fixed9 (phiAll u ψ) s) s) :
    ∀ o ∈ [(3, "norm"), (3, "policy"), (3, "logits"), (8, "the merge")],
      H.silent o.1 o.2 s = none → Desc.K9.formsIn (Desc.K9.readersOfLink H L) own o.1 o.2 s = true →
      ItemEq (phiAll u ψ) (tmH h iU3 p kap entUnit tm4 t3) (Desc.K9.readersOfLink H L) own rd o s b := by
  have k6 : ∀ name ∈ ["norm", "policy", "logits"], (name == "K8.equations") = false →
      tmH h iU3 p kap entUnit tm4 t3 (3, name) =
        plainTm (valsStill Reading.gl (Kinds.Head.Law.fsK6 h iU3 p kap name) entUnit) →
      H.silent 3 name s = none → Desc.K9.formsIn (Desc.K9.readersOfLink H L) own 3 name s = true →
      ItemEq (phiAll u ψ) (tmH h iU3 p kap entUnit tm4 t3) (Desc.K9.readersOfLink H L) own rd (3, name) s b :=
    fun name hn hne htm hsil hin => by
      obtain ⟨R, hR⟩ := reader_of_formsIn _ own 3 name s hin
      obtain ⟨run, hAt⟩ := at_of_reader H L (3, name) hne s hsil R hR
      obtain ⟨r, h0, hu⟩ := A.ties.tK6 name hn run hAt
      exact eq_still_in H L _ Ok _ own rd (3, name) hne run r hAt _ hu
        (Kinds.Head.Law.k6_still h iU3 p (phiAll u ψ) Ok kap A.hkap A.okK6 l' piece name r h0) htm s b hb hgo
        hsil hin
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · exact k6 "norm" (by simp) rfl rfl
  · exact k6 "policy" (by simp) rfl rfl
  · exact k6 "logits" (by simp) rfl rfl
  · intro hsil hin
    obtain ⟨R, hR⟩ := reader_of_formsIn _ own 8 "the merge" s hin
    obtain ⟨run, hAt⟩ := at_of_reader H L (8, "the merge") rfl s hsil R hR
    exact eq_merge H L _ Ok _ own rd (8, "the merge") rfl run hAt (A.ties.tMerge run hAt) (·.wo)
      (fun s x hs => phi_k11_pi u ψ s x hs) A.okMerge rfl s b hb hgo hsil hin

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.eqs_layers
#print axioms ProofFile.Honest.K9.eqs_attention
#print axioms ProofFile.Honest.K9.eqs_head
