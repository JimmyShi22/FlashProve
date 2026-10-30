-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/EqMarks.lean: FOR THE ITEM "totalB": AT THE HEAD's ENTRY (3, "join"): THE TERMS'
COEFFICIENTS ARE THE WORTHS OF THE ITEM's FORMS: `ItemEq` (Honest/K9/EqItem.lean). Statements and proofs over the
sealed library's laws; no goal is stated.
  **`eq_marks`**   `ItemEq` at an entry whose run stands under a run r that does no more to the state than mark an
      owed claim of the head's ledger as added (the library's `MarksRun φ Ok r fs`), the table of terms there being
      `plainTm (valsStill … fs entUnit)`
  **`eq_head_join`**   so at the head's entry (3, "join"), from the library's `HeadTake`
THE FIRST PROOF IS THE LIBRARY's OWN PROOF OF `item_marks` (Johnson/Desc/First/Link/Law/HitemsMarks.lean), CUT BY
PROGRAM OFF THAT FILE, as in Honest/K9/EqK4.lean; the second follows its `item_head_join`. No member. `eq_marks` is
called by `eq_head_join`; that by Honest/K9/EqCarry.lean.
WHAT IS NOT CLAIMED. Any premise at any state or link. That the second hole is silent: at the head's segment the
table's own holes (`K9.holesAt`) may speak where the run answers (where the tables can be made and the run answers
with them laid: by reading, shown nowhere), so these are called there at the empty hole (`K9.withSmall
K9.LinkHoles.none`); the carry from there to the readers with whatever second hole, under "the run itself answers at
s": Honest/K9/EqCarry.lean. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.EqItem
import Johnson.Desc.First.Link.Law.HitemsMarks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.K11Run (get_head)
open VerifiableInference.Desc.Kinds.Head.Law (MarksRun join_marks fsJoin)
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc

variable {α β : Type}

/-- **The equation at a run that marks an owed claim.** -/
theorem eq_marks (H : Desc.K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (Ok : α × Option Pub9 → Prop)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (o : ℕ × String)
    (hne : (o.2 == "K8.equations") = false)
    (run r : ℕ → S → Except String (List Claim × S)) (hAt : At L o run)
    (fs : α × Option Pub9 → Option (List Aff)) (hu : Under run r) (hM : MarksRun φ Ok r fs)
    (ht : tmOf o = plainTm (valsStill Reading.gl fs entUnit))
    (s : S) (b : Desc.K9.Part) (hb : atS.get? s = some b)
    (hf : Fx9 φ Ok (fixed9 φ s) s) (hsil : H.silent o.1 o.2 s = none)
    (hin : Desc.K9.formsIn (Desc.K9.readersOfLink H L) own o.1 o.2 s = true) :
    ItemEq φ tmOf (Desc.K9.readersOfLink H L) own rd o s b := by
  obtain ⟨R, hR⟩ := reader_of_formsIn _ own o.1 o.2 s hin
  obtain ⟨⟨c, s'⟩, G0, G', hz, h0, hG', _, rfl⟩ := run_of_reader H L o hne run hAt s hsil R hR
  obtain rfl : G0 = b.F := Option.some.inj (h0.symm.trans (Desc.K9.get_fork s b hb))
  have hz' := hu 0 s c s' hz
  obtain ⟨ah, i, h1, rfl⟩ := hM.hands 0 s c s' hz'
  obtain ⟨l, hl, rfl⟩ := hM.forms _ 0 s c _ hf hz'
  obtain ⟨a₁, ha₁, f1, _, _, f4⟩ := get_head s b hb ah h1 (ah.F.paid i)
  obtain rfl : G' = ah.F.paid i := by
    have e := Desc.K9.get_fork _ a₁ ha₁
    rw [f1] at e
    exact Option.some.inj (hG'.symm.trans e)
  have efs : (l.map fun f => ({ form := f } : Claim)).map (·.form) = l := by
    rw [List.map_map]
    exact List.map_id' l
  have hR' : (Desc.K9.readersOfLink H L).forms o.1 o.2 s = some ⟨l, []⟩ := by
    rw [hR]
    show some (⟨(l.map fun f => ({ form := f } : Claim)).map (·.form),
      Desc.K9.lateOf b.F (ah.F.paid i)⟩ : Desc.K9.Read) = _
    rw [efs, f4, lateOf_paid]
  have hq : (fixed9 φ s).2 = some (pubOf b) := by
    show (atS.get? s).map pubOf = _
    rw [hb]
    rfl
  refine ⟨_, hR', fun n => ?_⟩
  have he := named_of_formsIn (Desc.K9.readersOfLink H L) own o.1 o.2 s b ⟨l, []⟩ hb hR' hin
  rw [ht]
  show (Desc.K9L.numbered n (valsStill Reading.gl fs entUnit (fixed9 φ s) (dataQ own b rd))).map (·.2) = _
  rw [numbered_snd]
  unfold valsStill
  rw [hq, hl]
  exact List.map_congr_left fun f hf' =>
    value_meets_still b (dataQ own b rd) (fixed9 φ s) hq f (he f hf')

/-- **The equation at the head's entry (3, "join").** -/
theorem eq_head_join (H : Desc.K9.LinkHoles) {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {h : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ} {p : Kinds.Head.Par}
    {kap : Phi β → Option Kinds.Head.Law.Seen} {nU : Array ℕ} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : HeadTake L u ψ Ok Fu h iU3 l' piece p kap nU entUnit tm4 t3 l3) (own : List (ℕ × ℕ))
    (rd : ℕ × ℕ → MsgQ) (s : S) (b : Desc.K9.Part) (hb : atS.get? s = some b)
    (hgo : Fx9 (phiAll u ψ) Ok (fixed9 (phiAll u ψ) s) s) (hsil : H.silent 3 "join" s = none)
    (hin : Desc.K9.formsIn (Desc.K9.readersOfLink H L) own 3 "join" s = true) :
    ItemEq (phiAll u ψ) (tmH h iU3 p kap entUnit tm4 t3) (Desc.K9.readersOfLink H L) own rd (3, "join") s b := by
  obtain ⟨R, hR⟩ := reader_of_formsIn _ own 3 "join" s hin
  obtain ⟨run, hAt⟩ := at_of_reader H L (3, "join") rfl s hsil R hR
  exact eq_marks H L _ Ok _ own rd (3, "join") rfl run _ hAt _ (A.ties.tJoin run hAt)
    (join_marks h iU3 p (phiAll u ψ) Ok kap A.hkap A.okK6) rfl s b hb hgo hsil hin

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.eq_marks
#print axioms ProofFile.Honest.K9.eq_head_join
