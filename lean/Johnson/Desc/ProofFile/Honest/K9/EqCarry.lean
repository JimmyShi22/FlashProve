-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/EqCarry.lean: FOR THE ITEM "totalB": THE CARRY AT THE HEAD's SEGMENT: from the
readers with the empty second hole, at which `ItemEq` (Honest/K9/EqItem.lean) is had there, to the readers with
WHATEVER second hole (the table's own, `K9.holesAt`, among them), under "the run itself answers at s". Statements and
proofs over the sealed library's laws; no goal is stated.
  `itemEq_congr`   `ItemEq` reads the readers at the entry and the state alone
  **`zeros_head`**   at the head's segment, at o among (3, "norm"), (3, "policy"), (3, "logits"), (8, "the merge"),
      (3, "join"): from the library's `HeadTake` · K9's part b at s · the promise at what is fixed at s · (hrun) the
      run's own reader answers at o and s · the table's sentence "forms" at o, at the readers of the link with ANY
      second hole H: every coefficient of the entry's terms is 0
WHY. At the table's own holes "the second hole is silent" may fail where the run answers (where the tables can be made
and the run answers with them laid): by reading, shown nowhere (Honest/K9/EqAt.lean's and EqMarks.lean's heads): so
`eqs_head` and `eq_head_join` are called at `K9.withSmall K9.LinkHoles.none`, where silence is by definition, and what
they take and give is carried by the library's `forms_of_run` and `formsIn_congr`
(Johnson/Desc/First/Link/Law/HitemsHead.lean), as the library itself does (Johnson/P1K9R/ItemJoinHead.lean). No
member; `itemEq_congr` is called by `zeros_head`; that by `itemBack_head` (Honest/K9/BackAt.lean).
WHAT IS NOT CLAIMED. (hrun), the promise or "forms" at any state. The lookups' entries at the head, "K8.equations".
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.EqAt
import Johnson.Desc.ProofFile.Honest.K9.EqMarks
import Johnson.Desc.First.Link.Law.HitemsHead

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
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc

variable {α β : Type}

/-- The equation reads the readers at the entry and the state alone. -/
theorem itemEq_congr {φ : S → α}
    {tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)} {Rd Rd' : Desc.K9.Readers}
    {own : List (ℕ × ℕ)} {rd : ℕ × ℕ → MsgQ} {o : ℕ × String} {s : S} {b : Desc.K9.Part}
    (h : Rd'.forms o.1 o.2 s = Rd.forms o.1 o.2 s) (I : ItemEq φ tmOf Rd own rd o s b) :
    ItemEq φ tmOf Rd' own rd o s b := by
  obtain ⟨R, hR, e⟩ := I
  exact ⟨R, h.trans hR, e⟩

/-- **The zeros at the head's five entries, at whatever second hole.** -/
theorem zeros_head (H : Desc.K9.LinkHoles) {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {h : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ} {p : Kinds.Head.Par}
    {kap : Phi β → Option Kinds.Head.Law.Seen} {nU : Array ℕ} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : HeadTake L u ψ Ok Fu h iU3 l' piece p kap nU entUnit tm4 t3 l3) (own : List (ℕ × ℕ))
    (rd : ℕ × ℕ → MsgQ) (s : S) (b : Desc.K9.Part) (hb : atS.get? s = some b)
    (hOk : Ok (fixed9 (phiAll u ψ) s)) :
    ∀ o ∈ [(3, "norm"), (3, "policy"), (3, "logits"), (8, "the merge"), (3, "join")],
      (Desc.K9.readerOf (Desc.K9.statesOfLink L) o.1 o.2 s).isSome = true →
      formsQ (Desc.K9.readersOfLink H L) own o.1 o.2 s rd →
      ∀ n, ∀ c ∈ tmH h iU3 p kap entUnit tm4 t3 o n (fixed9 (phiAll u ψ) s) (dataQ own b rd), c.2 = 0 := by
  intro o ho hrun hQ
  have hne : (o.2 == "K8.equations") = false := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl <;> rfl
  have hgo : Fx9 (phiAll u ψ) Ok (fixed9 (phiAll u ψ) s) s := fx_self _ Ok s b hb hOk
  have e0 := forms_of_run (Desc.K9.withSmall Desc.K9.LinkHoles.none) H L o.1 o.2 s hne hrun
  have hin0 : Desc.K9.formsIn (Desc.K9.readersOfLink (Desc.K9.withSmall Desc.K9.LinkHoles.none) L) own o.1 o.2 s =
      true := (formsIn_congr own o.1 o.2 s e0).trans (formsQ_in _ own o.1 o.2 s rd hQ)
  have hE0 : ItemEq (phiAll u ψ) (tmH h iU3 p kap entUnit tm4 t3)
      (Desc.K9.readersOfLink (Desc.K9.withSmall Desc.K9.LinkHoles.none) L) own rd o s b := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl
    · exact eqs_head _ A own rd s b hb hgo (3, "norm") (by simp) rfl hin0
    · exact eqs_head _ A own rd s b hb hgo (3, "policy") (by simp) rfl hin0
    · exact eqs_head _ A own rd s b hb hgo (3, "logits") (by simp) rfl hin0
    · exact eqs_head _ A own rd s b hb hgo (8, "the merge") (by simp) rfl hin0
    · exact eq_head_join _ A own rd s b hb hgo rfl hin0
  exact zeros_of_eq _ _ _ own rd o s b hb (itemEq_congr e0.symm hE0) hQ

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.itemEq_congr
#print axioms ProofFile.Honest.K9.zeros_head
