-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/HitemsJoin.lean: `TableOwes.hitems` (LinkTable.lean) AT THE SEAT's OWN
READERS (`K9.readersAt`, Johnson/Desc/First/Batch/ReadersAt.lean), AT A LAYERS' AND AT AN ATTENTION
LINK: THE JOIN OF THE ITEMS' CLAUSES THAT LIE (HitemsAt.lean; HitemsSmall.lean). Theorems.
  `readersAt_plain`: away from the head's link the seat's readers are the link's own with the first
    hole filled and the second empty: by the text of `holesAt`. So "the second hole says nothing", a
    premise of every clause, holds there outright.
  `stmt_of_part`: the facts at a statement that every clause takes (`StmtAt`), from "a part is
    there" and Ok of what is fixed.
  `hitems_layers`, `hitems_attention`: **the field's own text**, at φ := `phiAll u ψ`, the sort's
    tables of terms at `entUnit`, and Rd := `K9.readersAt lk X mH m`. Behind each an `example`:
    Lean's own check that the end is `TableOwes`' field.
PREMISES. The sort's Take. A run stands at the entry "K8.equations" (hAt), and tm4's coefficients do
not hang on the number of claims in front (h4). hit: the listed items are of the sort's entries.
**hon: AT EVERY STATE OF on0 A PART IS THERE AND Ok HOLDS OF WHAT IS FIXED**: the field is asked
under on0 alone, and every clause wants a part and "goes on". hin: the table's public test says yes
at each listed item. k3i: the clauses at the lookup's entries.
hon asks less than the whole book-keeping in front of the batching
(`k9OnA`): the proof spends of it "a part is there" alone: so hon asks that: the weaker premise.
Limits. IMPLICATIONS. Not at the head's link. hon, hin and k3i are shown of no state here. WHETHER
THE READERS ANSWER AT AN HONEST STATE IN FRONT OF A BATCHING is a run's to show: until then on0 with
hin has no known member. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.HitemsAt
import Johnson.Desc.First.Link.Law.HitemsSmall
import Johnson.Desc.First.Link.Law.LinkTable
import Johnson.Desc.First.Batch.ReadersAt

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

/-- **Away from the head's link the seat's readers are the link's own**, with the first hole filled
and the second empty. -/
theorem readersAt_plain (lk : ℕ → Option (Link S Claim)) (X : OnBytes.Model.Verify.Public)
    (mH m : ℕ) (L : Link S Claim) (hlk : lk m = some L) (hm : (m == mH) = false) :
    K9.readersAt lk X mH m = K9.readersOfLink (K9.withSmall K9.LinkHoles.none) L := by
  rw [K9.readersAt_some lk X mH m L hlk]
  unfold K9.holesAt K9.withSmall K9.LinkHoles.none
  simp [hm]

/-- The facts at a statement that every clause takes. -/
theorem stmt_of_part (φ : S → Phi β) (Ok : Q β → Prop) (a : S × F.E.Str)
    (hA : (atS.get? a.1).isSome = true) (hOk : Ok (fixed9 φ a.1)) : ∃ b, StmtAt φ Ok a b := by
  cases e : atS.get? a.1 with
  | none =>
    rw [e] at hA
    exact nomatch hA
  | some b =>
    refine ⟨b, e, hOk, rfl, pubOf b, b, ?_, e, goesOn_refl b⟩
    show (atS.get? a.1).map pubOf = _
    rw [e]
    rfl

section
variable (lk : ℕ → Option (Link S Claim)) (X : OnBytes.Model.Verify.Public) (mH m : ℕ)
  {L : Link S Claim} (hlk : lk m = some L) (hm : (m == mH) = false) {u : HTailF2} {ψ : S → β}
  {Ok : Q β → Prop} {Fu : S → Prop} {nU : Array ℕ} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
  {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
include hlk hm

/-- **hitems AT A LAYERS' LINK.** -/
theorem hitems_layers (hL : SegAt m .layers L) {p : OnBytes.Desc.First.K4.Par}
    (A : LayersTake L u ψ Ok Fu p nU entUnit tm4 t3 l3)
    (run : ℕ → S → Except String (List Claim × S)) (hAt : At L (4, "K8.equations") run)
    (v4 : Q β → Bound GE8 → List GE8) (h4 : ∀ n q y, (tm4 n q y).map (·.2) = v4 q y)
    (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ) (on0 : S × F.E.Str → Prop)
    (items : List (ℕ × String))
    (hit : ∀ e ∈ items, e ∈ [(1, "objects"), (1, "guests"), (2, "front"), (2, "back"),
      (4, "K8.equations"), (6, "objects"), (6, "guests")])
    (hon : ∀ a, on0 a → (atS.get? a.1).isSome = true ∧ Ok (fixed9 (phiAll u ψ) a.1))
    (hin : ∀ a, on0 a → ∀ e ∈ items, K9.formsIn (K9.readersAt lk X mH m) own e.1 e.2 a.1 = true)
    (k3i : ∀ a w, on0 a → ∀ e ∈ [(1, "objects"), (6, "objects")],
      ItemIn L (phiAll u ψ) (tmL p entUnit tm4 t3) (lenL p l3) (K9.readersAt lk X mH m) own rdW
        a w e) :
    ∀ a w, on0 a → ∀ e ∈ items, ItemIn L (phiAll u ψ) (tmL p entUnit tm4 t3) (lenL p l3)
      (K9.readersAt lk X mH m) own rdW a w e := by
  intro a w ha e he
  obtain ⟨b, St⟩ := stmt_of_part (phiAll u ψ) Ok a (hon a ha).1 (hon a ha).2
  have hi := hin a ha e he
  have k3 := k3i a w ha
  rw [readersAt_plain lk X mH m L hlk hm] at hi k3 ⊢
  have own4 := items_layers (K9.withSmall K9.LinkHoles.none) hL A own rdW a w b St
  have ho : (4, "K8.equations") ∈ L.order := by
    rw [(order_at hL).1]
    decide
  have hmem := hit e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact k3 _ (by simp)
  · exact (own4 _ (by simp) rfl hi).toIn
  · exact (own4 _ (by simp) rfl hi).toIn
  · exact (own4 _ (by simp) rfl hi).toIn
  · exact item_small_layers K9.LinkHoles.none L u ψ p entUnit tm4 t3 l3 own rdW 4 ho run hAt v4 h4
      a w b St.part hi
  · exact k3 _ (by simp)
  · exact (own4 _ (by simp) rfl hi).toIn

/-- **hitems AT AN ATTENTION LINK.** -/
theorem hitems_attention (hL : SegAt m .attention L)
    {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : First.Att.P.ParC}
    (A : AttTake L u ψ Ok Fu rd c nU entUnit tm4 t3 l3)
    (run : ℕ → S → Except String (List Claim × S)) (hAt : At L (4, "K8.equations") run)
    (v4 : Q β → Bound GE8 → List GE8) (h4 : ∀ n q y, (tm4 n q y).map (·.2) = v4 q y)
    (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ) (on0 : S × F.E.Str → Prop)
    (items : List (ℕ × String))
    (hit : ∀ e ∈ items, e ∈ [(1, "objects"), (1, "guests"), (1, "planes"), (2, "join"),
      (2, "first"), (2, "keys"), (2, "second"), (4, "K8.equations"), (6, "objects"),
      (6, "guests")])
    (hon : ∀ a, on0 a → (atS.get? a.1).isSome = true ∧ Ok (fixed9 (phiAll u ψ) a.1))
    (hin : ∀ a, on0 a → ∀ e ∈ items, K9.formsIn (K9.readersAt lk X mH m) own e.1 e.2 a.1 = true)
    (k3i : ∀ a w, on0 a → ∀ e ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")],
      ItemIn L (phiAll u ψ) (tmA rd c entUnit tm4 t3) (lenA rd c l3) (K9.readersAt lk X mH m) own
        rdW a w e) :
    ∀ a w, on0 a → ∀ e ∈ items, ItemIn L (phiAll u ψ) (tmA rd c entUnit tm4 t3) (lenA rd c l3)
      (K9.readersAt lk X mH m) own rdW a w e := by
  intro a w ha e he
  obtain ⟨b, St⟩ := stmt_of_part (phiAll u ψ) Ok a (hon a ha).1 (hon a ha).2
  have hi := hin a ha e he
  have k3 := k3i a w ha
  rw [readersAt_plain lk X mH m L hlk hm] at hi k3 ⊢
  have own5 := items_attention (K9.withSmall K9.LinkHoles.none) hL A own rdW a w b St
  have ho : (4, "K8.equations") ∈ L.order := by
    rw [(order_at hL).1]
    decide
  have hmem := hit e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact k3 _ (by simp)
  · exact (own5 _ (by simp) rfl hi).toIn
  · exact k3 _ (by simp)
  · exact k3 _ (by simp)
  · exact (own5 _ (by simp) rfl hi).toIn
  · exact (own5 _ (by simp) rfl hi).toIn
  · exact (own5 _ (by simp) rfl hi).toIn
  · exact item_small_attention K9.LinkHoles.none L u ψ rd c entUnit tm4 t3 l3 own rdW 4 ho run hAt
      v4 h4 a w b St.part hi
  · exact k3 _ (by simp)
  · exact (own5 _ (by simp) rfl hi).toIn

end

/-- Lean's own check that the layers' end is `TableOwes`' field. -/
example (lk : ℕ → Option (Link S Claim)) (X : OnBytes.Model.Verify.Public) (mH m : ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β) (p : OnBytes.Desc.First.K4.Par)
    (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ) (on0 on1 on2 : S × F.E.Str → Prop)
    (items : List (ℕ × String))
    (T : TableOwes L (phiAll u ψ) (tmL p entUnit tm4 t3) (lenL p l3) on0 on1 on2
      (K9.readersAt lk X mH m) own rdW items) :
    ∀ a w, on0 a → ∀ e ∈ items, ItemIn L (phiAll u ψ) (tmL p entUnit tm4 t3) (lenL p l3)
      (K9.readersAt lk X mH m) own rdW a w e :=
  T.hitems

/-- And attention's. -/
example (lk : ℕ → Option (Link S Claim)) (X : OnBytes.Model.Verify.Public) (mH m : ℕ)
    (L : Link S Claim) (u : HTailF2) (ψ : S → β)
    (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)) (c : First.Att.P.ParC)
    (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ) (on0 on1 on2 : S × F.E.Str → Prop)
    (items : List (ℕ × String))
    (T : TableOwes L (phiAll u ψ) (tmA rd c entUnit tm4 t3) (lenA rd c l3) on0 on1 on2
      (K9.readersAt lk X mH m) own rdW items) :
    ∀ a w, on0 a → ∀ e ∈ items, ItemIn L (phiAll u ψ) (tmA rd c entUnit tm4 t3) (lenA rd c l3)
      (K9.readersAt lk X mH m) own rdW a w e :=
  T.hitems

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.readersAt_plain
#print axioms VerifiableInference.Desc.LinkJoin.stmt_of_part
#print axioms VerifiableInference.Desc.LinkJoin.hitems_layers
#print axioms VerifiableInference.Desc.LinkJoin.hitems_attention
