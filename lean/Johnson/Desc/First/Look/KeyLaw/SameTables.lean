-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/KeyLaw/SameTables.lean: WHAT A ROW SAYS OF WORDS HANGS, OF THE STATEMENT, ON
THE NUMBER OF MESSAGES AND THE TABLES' SIZES ALONE; and: the rows that the kind's own routines make
are plain rows.

Main names:
  SameTables S S': the same number of messages, the same size of every table.
  value_same, says_same, allSay_same: a row's value, a row's claim, a list's claims.
  kind_planesAt, kind_addMasks: the program's two routines leave a row's kind.
  aff_plain, plane_plain, group_plain: rowOfAff's, rowOfPlane's and groupRows's rows are plain.

Limits. Nothing on which steps of a file's verifier keep the tables.

-/
import Johnson.Desc.First.Look.KeyLaw.SaysAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice
open OnBytes.Model (Fork Aff Reading)

/-- Two statements have the same number of messages and the same tables' sizes. -/
def SameTables (S S' : Statement) : Prop :=
  S'.oracles.size = S.oracles.size ∧ ∀ o part, Means.tableSize S' o part = Means.tableSize S o part

theorem SameTables.refl (S : Statement) : SameTables S S := ⟨rfl, fun _ _ => rfl⟩

theorem SameTables.trans {S S' S'' : Statement} (h : SameTables S S') (h' : SameTables S' S'') :
    SameTables S S'' :=
  ⟨h'.1.trans h.1, fun o part => (h'.2 o part).trans (h.2 o part)⟩

theorem SameTables.symm {S S' : Statement} (h : SameTables S S') : SameTables S' S :=
  ⟨h.1.symm, fun o part => (h.2 o part).symm⟩

variable {K : Type} [CommRing K] (ρ : Reading K)

theorem value_same {S S' : Statement} (h : SameTables S S') (r : GRow) (w : Means.Words K) :
    Means.value ρ S' r w = Means.value ρ S r w := by
  unfold Means.value Means.onTable
  rw [h.1]
  simp only [h.2]

/-- **A row's claim.** -/
theorem says_same {S S' : Statement} (h : SameTables S S') (r : GRow) (w : Means.Words K) :
    Means.Says ρ S' r w ↔ Means.Says ρ S r w := by
  unfold Means.Says
  rw [value_same ρ h]

/-- **A list's claims.** -/
theorem allSay_same {S S' : Statement} (h : SameTables S S') (l : List GRow) (w : Means.Words K) :
    Means.AllSay ρ S' l w ↔ Means.AllSay ρ S l w :=
  forall_congr' fun r => imp_congr_right fun _ => says_same ρ h r w

/-! ## The rows are plain -/

theorem kind_fold_add {α : Type} (o : ℕ) (part : Part) (f : α → Tensor) : ∀ (l : List α) (r : GRow),
    (l.foldl (fun r b => r.add o part (f b)) r).kind = r.kind
  | [], _ => rfl
  | b :: l, r => by
    rw [List.foldl_cons, kind_fold_add o part f l]
    rfl

theorem kind_planesAt (x : Params.WfPublic) (codes : Codes) (i : ℕ) (r : GRow) (v : Tensor) :
    (Wf.planesAt x codes i r v).kind = r.kind := by
  unfold Wf.planesAt
  exact kind_fold_add _ _ _ _ _

theorem kind_addMasks : ∀ (m : MaskForm) (r : GRow), (r.addMasks m).kind = r.kind
  | [], _ => rfl
  | p :: m, r => by
    show ((r.addUnit p.1.oracle .mask p.1.index p.2).addMasks m).kind = _
    rw [kind_addMasks m]
    rfl

theorem aff_plain {F : Fork} {home : Array Slot} {a : Aff} {R : GRow}
    (h : rowOfAff F home a = some R) : R.kind = RowKind.plain := by
  unfold rowOfAff at h
  cases hy : maskSide F home a with
  | none => rw [hy] at h; cases h
  | some y =>
    rw [hy] at h
    obtain rfl := Option.some.inj h
    exact kind_addMasks _ _

theorem plane_plain (x : Params.WfPublic) (codes : Codes) (i : ℕ) {F : Fork} {home : Array Slot}
    {turned : Bool} {c : PlaneClaim} {R : GRow}
    (h : rowOfPlane (Wf.planesAt x codes i) F home turned c = some R) :
    R.kind = RowKind.plain := by
  unfold rowOfPlane at h
  cases hy : maskSide F home c.lead with
  | none => rw [hy] at h; cases h
  | some y =>
    rw [hy] at h
    obtain rfl := Option.some.inj h
    cases turned with
    | true =>
      simp only [if_true]
      rw [kind_addMasks, kind_planesAt]
    | false =>
      simp only [Bool.false_eq_true, if_false]
      rw [kind_addMasks, kind_planesAt]

theorem mapM_all {α β : Type} {f : α → Option β} {Q : β → Prop} (hf : ∀ a b, f a = some b → Q b) :
    ∀ (l : List α) (r : List β), l.mapM f = some r → ∀ b ∈ r, Q b
  | [], r, h => by
    cases h
    exact fun b hb => (by cases hb)
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b0 =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some r' =>
        simp only [ha, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        intro b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · exact hf a _ ha
        · exact mapM_all hf l r' hl b hb

/-- **All rows that a lookup leaves in its group are plain.** -/
theorem group_plain (x : Params.WfPublic) (codes : Codes) (i : ℕ) {F : Fork} {home : Array Slot}
    {objects : List Aff} {planes : List PlaneClaim} {rows : List GRow}
    (h : groupRows (Wf.planesAt x codes i) F home objects planes = some rows) :
    ∀ R ∈ rows, R.kind = RowKind.plain := by
  unfold groupRows at h
  match planes, hg : objects.getLast?, h with
  | [leaves, value, counts], some bits, h =>
    simp only at h
    cases h0 : objects.dropLast.mapM (rowOfAff F home) with
    | none => simp [h0] at h
    | some front =>
      cases h1 : rowOfPlane (Wf.planesAt x codes i) F home true leaves with
      | none => simp [h0, h1] at h
      | some r1 =>
        cases h2 : rowOfAff F home bits with
        | none => simp [h0, h1, h2] at h
        | some r2 =>
          cases h3 : rowOfPlane (Wf.planesAt x codes i) F home false value with
          | none => simp [h0, h1, h2, h3] at h
          | some r3 =>
            cases h4 : rowOfPlane (Wf.planesAt x codes i) F home true counts with
            | none => simp [h0, h1, h2, h3, h4] at h
            | some r4 =>
              simp only [h0, h1, h2, h3, h4, Option.bind_eq_bind, Option.bind_some,
                Option.pure_def, Option.some.injEq] at h
              subst h
              intro R hR
              rcases List.mem_append.1 hR with hR | hR
              · exact mapM_all (fun a b hab => aff_plain hab) _ _ h0 R hR
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
                rcases hR with rfl | rfl | rfl | rfl
                · exact plane_plain x codes i h1
                · exact aff_plain h2
                · exact plane_plain x codes i h3
                · exact plane_plain x codes i h4

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.allSay_same
#print axioms VerifiableInference.Desc.K3.KeyLaw.group_plain
