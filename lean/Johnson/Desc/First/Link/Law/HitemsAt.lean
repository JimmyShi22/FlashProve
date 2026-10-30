-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/HitemsAt.lean: `TableOwes.hitems` (LinkTable.lean) AT EACH OF THE THREE
SORTS OF LINK, AS FAR AS THE ITEMS' CLAUSES LIE (HitemsStill.lean, HitemsMerge.lean, HitemsK4.lean):
from what the assembly of the kinds' laws takes there (`LayersTake`, `AttTake`, `HeadTake`), at the
entries `entUnit`, and the readers of the link itself. Theorems.

What is said.
  `lookup_of_find`, `at_of_reader`: where the reader's second hole says nothing and the reader gives
    something at an entry other than the smallness test's, a run stands at the entry. `StmtAt`: the
    facts at a statement that every item's clause takes, under one name: a part is there; the state
    goes on from what is fixed. `items_layers`, `items_attention`, `items_head`: **`ItemAt` at four,
    five and six entries of the sort's order**, each from `StmtAt`, the hole's silence and the
    table's public test's yes at that entry.

What all the clauses lean on. THE READER CALLS A RUN AT THE RECORD OF THE STATEMENT, WITH NO CLAIM
IN FRONT: in front of all the runs; the batching's gatherer calls it behind the earlier entries'
runs. The values agree none the less, because the laws too say a run's values at what is fixed
before the draw. BUT the public test's yes then means that the run says yes at a ledger in which the
earlier runs of the same gathering have laid nothing yet: if «back» or «the merge» tested anything
that an earlier run lays, the reader would give nothing at every honest record, and the condition in
front would have no member. A run of the public test at the real record in front of each batching
decides it.

Limits. 15 of the 28 entries of the three orders. Not here: the lookup's entries («objects»,
«planes»), the two «join», the smallness test's equations. The Takes' letter for the entries is
closed here: `entUnit`. As in HitemsStill.lean: the hole's silence is a premise; whether the public
test says yes at a real record is a run's to show. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.HitemsK4
import Johnson.Desc.First.Link.Law.LinkLawAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)
open K5Law

variable {β W : Type} {F : Frame}

/-- What the search by the name's test finds, the lookup finds. -/
theorem lookup_of_find {γ : Type} (n : String) : ∀ (l : List (String × γ)) (x : String × γ),
    l.find? (fun r => r.1 == n) = some x → l.lookup n = some x.2
  | [], _, h => nomatch h
  | (k, b) :: l, x, h => by
    rw [List.find?_cons] at h
    rw [List.lookup_cons]
    by_cases e : n = k
    · subst e
      simp only [beq_self_eq_true] at h ⊢
      rw [← Option.some.inj h]
    · have e1 : (n == k) = false := beq_false_of_ne e
      have e2 : (k == n) = false := beq_false_of_ne fun h' => e h'.symm
      simp only [e2] at h
      simp only [e1]
      exact lookup_of_find n l x h

/-- Where the second hole says nothing and the reader gives something, a run stands at the entry. -/
theorem at_of_reader (H : K9.LinkHoles) (L : Link S Claim) (o : ℕ × String)
    (hne : (o.2 == "K8.equations") = false) (s : S) (hsil : H.silent o.1 o.2 s = none)
    (R : K9.Read) (hR : (K9.readersOfLink H L).forms o.1 o.2 s = some R) : ∃ run, At L o run := by
  have hR' : (if o.2 == "K8.equations" then H.small s
    else match K9.readerOf (K9.statesOfLink L) o.1 o.2 s with
      | some R => some R
      | Option.none => H.silent o.1 o.2 s) = some R := hR
  rw [hne] at hR'
  cases hr : K9.readerOf (K9.statesOfLink L) o.1 o.2 s with
  | none =>
    rw [hr] at hR'
    have h' : H.silent o.1 o.2 s = some R := hR'
    rw [hsil] at h'
    exact nomatch h'
  | some R' =>
    unfold K9.readerOf at hr
    obtain ⟨x, hx, _⟩ := Option.bind_eq_some_iff.1 hr
    unfold K9.statesOfLink at hx
    cases hb : L.hear[o.1]? with
    | none =>
      rw [hb] at hx
      exact nomatch hx
    | some blk =>
      rw [hb] at hx
      refine ⟨x.2, ?_⟩
      show ((L.hear[o.1]?).bind fun b => b.claims.lookup o.2) = some x.2
      rw [hb]
      exact lookup_of_find o.2 blk.claims x hx

/-- The facts at a statement that every item's clause takes. -/
structure StmtAt (φ : S → Phi β) (Ok : Q β → Prop) (a : S × F.E.Str) (b : K9.Part) : Prop where
  part : atS.get? a.1 = some b
  goes : Fx9 φ Ok (fixed9 φ a.1) a.1

/-- **THE ITEMS' CLAUSES AT AN ATTENTION LINK.** -/
theorem items_attention (H : K9.LinkHoles) {l : ℕ} {L : Link S Claim} (hL : SegAt l .attention L)
    {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop} {Fu : S → Prop}
    {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : First.Att.P.ParC}
    {nU : Array ℕ} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : AttTake L u ψ Ok Fu rd c nU entUnit tm4 t3 l3) (own : List (ℕ × ℕ))
    (rdW : W → ℕ × ℕ → MsgQ) (a : S × F.E.Str) (w : W) (b : K9.Part)
    (St : StmtAt (phiAll u ψ) Ok a b) :
    ∀ o ∈ [(1, "guests"), (2, "first"), (2, "keys"), (2, "second"), (6, "guests")],
      H.silent o.1 o.2 a.1 = none → K9.formsIn (K9.readersOfLink H L) own o.1 o.2 a.1 = true →
      ItemAt L (phiAll u ψ) (tmA rd c entUnit tm4 t3) (lenA rd c l3) (K9.readersOfLink H L) own rdW
        a w o := by
  have key : ∀ (o : ℕ × String) (r : ℕ → S → Except String (List Claim × S))
      (fs : Q β → Option (List Aff)), o ∈ First.orderOf .attention →
      (o.2 == "K8.equations") = false → (∀ run, At L o run → Under run r) →
      Still (phiAll u ψ) Ok r fs →
      tmA rd c entUnit tm4 t3 o = plainTm (valsStill Reading.gl fs entUnit) →
      H.silent o.1 o.2 a.1 = none → K9.formsIn (K9.readersOfLink H L) own o.1 o.2 a.1 = true →
      ItemAt L (phiAll u ψ) (tmA rd c entUnit tm4 t3) (lenA rd c l3) (K9.readersOfLink H L) own rdW
        a w o := fun o r fs ho hne ht hS htm hsil hin => by
    obtain ⟨R, hR⟩ := reader_of_formsIn _ own o.1 o.2 a.1 hin
    obtain ⟨run, hAt⟩ := at_of_reader H L o hne a.1 hsil R hR
    exact item_still_in H L _ Ok _ _ own rdW o (by rw [(order_at hL).1]; exact ho) hne run r hAt fs
      (ht run hAt) hS htm a w b St.part St.goes hsil hin
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl
  · exact key _ _ _ (by decide) rfl (A.ties.tGuests 1 (by simp))
      (idle_still _ Ok fun _ _ => rfl) rfl
  · exact key _ _ _ (by decide) rfl A.ties.tFirst (still_first _ Ok rd c A.hrd A.okK5) rfl
  · exact key _ _ _ (by decide) rfl A.ties.tKeys (still_keys _ Ok c) rfl
  · exact key _ _ _ (by decide) rfl A.ties.tSecond (still_second _ Ok rd c A.hrd A.okK5) rfl
  · exact key _ _ _ (by decide) rfl (A.ties.tGuests 6 (by simp))
      (idle_still _ Ok fun _ _ => rfl) rfl

/-- **THE ITEMS' CLAUSES AT A LAYERS' LINK.** -/
theorem items_layers (H : K9.LinkHoles) {l : ℕ} {L : Link S Claim} (hL : SegAt l .layers L)
    {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop} {Fu : S → Prop}
    {p : OnBytes.Desc.First.K4.Par} {nU : Array ℕ} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : LayersTake L u ψ Ok Fu p nU entUnit tm4 t3 l3) (own : List (ℕ × ℕ))
    (rdW : W → ℕ × ℕ → MsgQ) (a : S × F.E.Str) (w : W) (b : K9.Part)
    (St : StmtAt (phiAll u ψ) Ok a b) :
    ∀ o ∈ [(1, "guests"), (2, "front"), (2, "back"), (6, "guests")],
      H.silent o.1 o.2 a.1 = none → K9.formsIn (K9.readersOfLink H L) own o.1 o.2 a.1 = true →
      ItemAt L (phiAll u ψ) (tmL p entUnit tm4 t3) (lenL p l3) (K9.readersOfLink H L) own rdW
        a w o := by
  have hord : ∀ o, o ∈ First.orderOf .layers → o ∈ L.order := fun o ho => by
    rw [(order_at hL).1]
    exact ho
  have guests : ∀ k ∈ [1, 6], (k, "guests") ∈ First.orderOf .layers →
      H.silent k "guests" a.1 = none →
      K9.formsIn (K9.readersOfLink H L) own k "guests" a.1 = true →
      ItemAt L (phiAll u ψ) (tmL p entUnit tm4 t3) (lenL p l3) (K9.readersOfLink H L) own rdW
        a w (k, "guests") := fun k hk ho hsil hin => by
    obtain ⟨R, hR⟩ := reader_of_formsIn _ own k "guests" a.1 hin
    obtain ⟨run, hAt⟩ := at_of_reader H L (k, "guests") rfl a.1 hsil R hR
    exact item_still_in H L _ Ok _ _ own rdW (k, "guests") (hord _ ho) rfl run _ hAt _
      (A.ties.tGuests k hk run hAt) (idle_still _ Ok fun _ _ => rfl) rfl a w b St.part St.goes hsil
      hin
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · exact guests 1 (by simp) (by decide)
  · intro hsil hin
    obtain ⟨R, hR⟩ := reader_of_formsIn _ own 2 "front" a.1 hin
    obtain ⟨run, hAt⟩ := at_of_reader H L (2, "front") rfl a.1 hsil R hR
    obtain ⟨r, h0, hu⟩ := A.ties.tFront run hAt
    exact item_front H L _ Ok _ _ own rdW (2, "front") (hord _ (by decide)) rfl run r hAt p h0 hu
      (·.own) (fun s x hs => phi_k4_pi u ψ s x hs) A.okFront rfl a w b St.part St.goes hsil hin
  · intro hsil hin
    obtain ⟨R, hR⟩ := reader_of_formsIn _ own 2 "back" a.1 hin
    obtain ⟨run, hAt⟩ := at_of_reader H L (2, "back") rfl a.1 hsil R hR
    obtain ⟨r, h0, hu⟩ := A.ties.tBack run hAt
    exact item_back H L _ Ok _ _ own rdW (2, "back") (hord _ (by decide)) rfl run r hAt p h0 hu
      (·.own) (fun s x hs => phi_k4_pi u ψ s x hs) A.okBack rfl a w b St.part St.goes hsil hin
  · exact guests 6 (by simp) (by decide)

/-- **THE ITEMS' CLAUSES AT THE HEAD's LINK.** -/
theorem items_head (H : K9.LinkHoles) {l : ℕ} {L : Link S Claim} (hL : SegAt l .head L)
    {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop} {Fu : S → Prop}
    {h : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ} {p : Kinds.Head.Par}
    {kap : Phi β → Option Kinds.Head.Law.Seen} {nU : Array ℕ}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : HeadTake L u ψ Ok Fu h iU3 l' piece p kap nU entUnit tm4 t3 l3) (own : List (ℕ × ℕ))
    (rdW : W → ℕ × ℕ → MsgQ) (a : S × F.E.Str) (w : W) (b : K9.Part)
    (St : StmtAt (phiAll u ψ) Ok a b) :
    ∀ o ∈ [(2, "guests"), (3, "norm"), (3, "policy"), (3, "logits"), (7, "guests"),
        (8, "the merge")],
      H.silent o.1 o.2 a.1 = none → K9.formsIn (K9.readersOfLink H L) own o.1 o.2 a.1 = true →
      ItemAt L (phiAll u ψ) (tmH h iU3 p kap entUnit tm4 t3) (lenH h iU3 p kap l3)
        (K9.readersOfLink H L) own rdW a w o := by
  have hord : ∀ o, o ∈ First.orderOf .head → o ∈ L.order := fun o ho => by
    rw [(order_at hL).1]
    exact ho
  have guests : ∀ k ∈ [2, 7], (k, "guests") ∈ First.orderOf .head →
      H.silent k "guests" a.1 = none →
      K9.formsIn (K9.readersOfLink H L) own k "guests" a.1 = true →
      ItemAt L (phiAll u ψ) (tmH h iU3 p kap entUnit tm4 t3) (lenH h iU3 p kap l3)
        (K9.readersOfLink H L) own rdW a w (k, "guests") := fun k hk ho hsil hin => by
    obtain ⟨R, hR⟩ := reader_of_formsIn _ own k "guests" a.1 hin
    obtain ⟨run, hAt⟩ := at_of_reader H L (k, "guests") rfl a.1 hsil R hR
    exact item_still_in H L _ Ok _ _ own rdW (k, "guests") (hord _ ho) rfl run _ hAt _
      (A.ties.tGuests k hk run hAt) (idle_still _ Ok fun _ _ => rfl) rfl a w b St.part St.goes hsil
      hin
  have k6 : ∀ name ∈ ["norm", "policy", "logits"], (3, name) ∈ First.orderOf .head →
      (name == "K8.equations") = false →
      tmH h iU3 p kap entUnit tm4 t3 (3, name) =
        plainTm (valsStill Reading.gl (Kinds.Head.Law.fsK6 h iU3 p kap name) entUnit) →
      H.silent 3 name a.1 = none →
      K9.formsIn (K9.readersOfLink H L) own 3 name a.1 = true →
      ItemAt L (phiAll u ψ) (tmH h iU3 p kap entUnit tm4 t3) (lenH h iU3 p kap l3)
        (K9.readersOfLink H L) own rdW a w (3, name) := fun name hn ho hne htm hsil hin => by
    obtain ⟨R, hR⟩ := reader_of_formsIn _ own 3 name a.1 hin
    obtain ⟨run, hAt⟩ := at_of_reader H L (3, name) hne a.1 hsil R hR
    obtain ⟨r, h0, hu⟩ := A.ties.tK6 name hn run hAt
    exact item_still_in H L _ Ok _ _ own rdW (3, name) (hord _ ho) hne run r hAt _ hu
      (Kinds.Head.Law.k6_still h iU3 p (phiAll u ψ) Ok kap A.hkap A.okK6 l' piece name r h0) htm a w
      b St.part St.goes hsil hin
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
  · exact guests 2 (by simp) (by decide)
  · exact k6 "norm" (by simp) (by decide) rfl rfl
  · exact k6 "policy" (by simp) (by decide) rfl rfl
  · exact k6 "logits" (by simp) (by decide) rfl rfl
  · exact guests 7 (by simp) (by decide)
  · intro hsil hin
    obtain ⟨R, hR⟩ := reader_of_formsIn _ own 8 "the merge" a.1 hin
    obtain ⟨run, hAt⟩ := at_of_reader H L (8, "the merge") rfl a.1 hsil R hR
    exact item_merge H L _ Ok _ _ own rdW (8, "the merge") (hord _ (by decide)) rfl run hAt
      (A.ties.tMerge run hAt) (·.wo) (fun s x hs => phi_k11_pi u ψ s x hs) A.okMerge rfl a w b
      St.part St.goes hsil hin

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.at_of_reader
#print axioms VerifiableInference.Desc.LinkJoin.items_attention
#print axioms VerifiableInference.Desc.LinkJoin.items_layers
#print axioms VerifiableInference.Desc.LinkJoin.items_head
