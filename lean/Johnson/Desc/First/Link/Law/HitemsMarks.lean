-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/HitemsMarks.lean: `TableOwes.hitems` (LinkTable.lean), ONE ITEM's CLAUSE
AT A RUN THAT DOES NO MORE TO THE RECORD THAN MARK AN OWED CLAIM OF THE HEAD's LEDGER AS ADDED
(`MarksRun`, Johnson/Desc/Kinds/Law/JoinRunAtS.lean): the output head's run «join». At the readers
of the link itself (`K9.readersOfLink`). Theorems, over HitemsStill.lean.

What is said.
  `lateOf_paid`: no slot is late between a ledger and the same ledger with an owed claim marked.
    `item_marks`: **`ItemAt` at an entry of the order whose run stands under such a run**, the table
    of terms there being `plainTm (valsStill …)` at `entUnit`; from, at the statement: a part is
    there; the state goes on from what is fixed; the reader's second hole says nothing; the table's
    public test says yes. `item_head_join`: so at the head's entry (3, «join»), from `HeadTake`.

Limits. One item more: 16 of the 28 entries of the three orders with HitemsAt.lean's fifteen. As in
HitemsStill.lean: the hole's silence is a premise; whether the public test says yes at a real record
is a run's to show. No `TableOwes` is made here. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.HitemsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.K11Run (get_head)
open VerifiableInference.Desc.Kinds.Head.Law (MarksRun join_marks fsJoin)
open VerifiableInference.Desc.EntryUnit (entUnit)

variable {α β W : Type} {F : Frame}

/-- No slot is late between a ledger and the same ledger with an owed claim marked. -/
theorem lateOf_paid (G : Fork) (i : ℕ) : K9.lateOf G (G.paid i) = [] := lateOf_self G

/-- **ONE ITEM's CLAUSE AT A RUN THAT ONLY MARKS AN OWED CLAIM.** -/
theorem item_marks (H : K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (Ok : α × Option Pub9 → Prop)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ)
    (o : ℕ × String) (ho : o ∈ L.order) (hne : (o.2 == "K8.equations") = false)
    (run r : ℕ → S → Except String (List Claim × S)) (hAt : At L o run)
    (fs : α × Option Pub9 → Option (List Aff)) (hu : Under run r) (hM : MarksRun φ Ok r fs)
    (ht : tmOf o = plainTm (valsStill Reading.gl fs entUnit))
    (a : S × F.E.Str) (w : W) (b : K9.Part) (hb : atS.get? a.1 = some b)
    (hf : Fx9 φ Ok (fixed9 φ a.1) a.1) (hsil : H.silent o.1 o.2 a.1 = none)
    (hin : K9.formsIn (K9.readersOfLink H L) own o.1 o.2 a.1 = true) :
    ItemAt L φ tmOf lenOf (K9.readersOfLink H L) own rdW a w o := by
  obtain ⟨R, hR⟩ := reader_of_formsIn _ own o.1 o.2 a.1 hin
  obtain ⟨⟨c, s'⟩, G0, G', hz, h0, hG', _, rfl⟩ := run_of_reader H L o hne run hAt a.1 hsil R hR
  obtain rfl : G0 = b.F := Option.some.inj (h0.symm.trans (K9.get_fork a.1 b hb))
  have hz' := hu 0 a.1 c s' hz
  obtain ⟨ah, i, h1, rfl⟩ := hM.hands 0 a.1 c s' hz'
  obtain ⟨l, hl, rfl⟩ := hM.forms _ 0 a.1 c _ hf hz'
  obtain ⟨a₁, ha₁, f1, _, _, f4⟩ := get_head a.1 b hb ah h1 (ah.F.paid i)
  obtain rfl : G' = ah.F.paid i := by
    have e := K9.get_fork _ a₁ ha₁
    rw [f1] at e
    exact Option.some.inj (hG'.symm.trans e)
  have efs : (l.map fun f => ({ form := f } : Claim)).map (·.form) = l := by
    rw [List.map_map]
    exact List.map_id' l
  have hR' : (K9.readersOfLink H L).forms o.1 o.2 a.1 = some ⟨l, []⟩ := by
    rw [hR]
    show some (⟨(l.map fun f => ({ form := f } : Claim)).map (·.form),
      K9.lateOf b.F (ah.F.paid i)⟩ : K9.Read) = _
    rw [efs, f4, lateOf_paid]
  have hq : (fixed9 φ a.1).2 = some (pubOf b) := by
    show (atS.get? a.1).map pubOf = _
    rw [hb]
    rfl
  refine ⟨b, ⟨l, []⟩, [(⟨(o.2, run), tmOf o, lenOf o⟩, valsStill Reading.gl fs entUnit)], hb, ?_,
    hR', hin, ?_⟩
  · intro x hx
    obtain rfl := List.mem_singleton.1 hx
    refine ⟨List.mem_filterMap.2 ⟨o, ho, ?_⟩, fun n y => ?_⟩
    · rw [show ((L.hear[o.1]?).bind fun b => b.claims.lookup o.2) = some run from hAt]
      rfl
    · show ((tmOf o n (fixed9 φ a.1) y).map (·.2)) = _
      rw [ht]
      exact numbered_snd _ n
  · have he := named_of_formsIn (K9.readersOfLink H L) own o.1 o.2 a.1 b ⟨l, []⟩ hb hR' hin
    show valsStill Reading.gl fs entUnit (fixed9 φ a.1) (dataQ own b (rdW w)) ++ [] = _
    rw [List.append_nil]
    unfold valsStill
    rw [hq, hl]
    exact List.map_congr_left fun f hf' =>
      value_meets_still b (dataQ own b (rdW w)) (fixed9 φ a.1) hq f (he f hf')

/-- **THE ITEM's CLAUSE AT THE HEAD's ENTRY (3, «join»).** -/
theorem item_head_join (H : K9.LinkHoles) {l : ℕ} {L : Link S Claim} (hL : SegAt l .head L)
    {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop} {Fu : S → Prop}
    {h : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ} {p : Kinds.Head.Par}
    {kap : Phi β → Option Kinds.Head.Law.Seen} {nU : Array ℕ}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : HeadTake L u ψ Ok Fu h iU3 l' piece p kap nU entUnit tm4 t3 l3) (own : List (ℕ × ℕ))
    (rdW : W → ℕ × ℕ → MsgQ) (a : S × F.E.Str) (w : W) (b : K9.Part)
    (St : StmtAt (phiAll u ψ) Ok a b) (hsil : H.silent 3 "join" a.1 = none)
    (hin : K9.formsIn (K9.readersOfLink H L) own 3 "join" a.1 = true) :
    ItemAt L (phiAll u ψ) (tmH h iU3 p kap entUnit tm4 t3) (lenH h iU3 p kap l3)
      (K9.readersOfLink H L) own rdW a w (3, "join") := by
  obtain ⟨R, hR⟩ := reader_of_formsIn _ own 3 "join" a.1 hin
  obtain ⟨run, hAt⟩ := at_of_reader H L (3, "join") rfl a.1 hsil R hR
  exact item_marks H L _ Ok _ _ own rdW (3, "join")
    (by rw [(order_at hL).1]; decide) rfl run _ hAt _ (A.ties.tJoin run hAt)
    (join_marks h iU3 p (phiAll u ψ) Ok kap A.hkap A.okK6) rfl a w b St.part St.goes hsil hin

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.lateOf_paid
#print axioms VerifiableInference.Desc.LinkJoin.item_marks
#print axioms VerifiableInference.Desc.LinkJoin.item_head_join
