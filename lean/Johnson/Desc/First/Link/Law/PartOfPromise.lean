-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/PartOfPromise.lean: "K9's PART IS THERE" (the lens
atS reads a part: Johnson/Desc/First/Batch/AtS.lean) AT EVERY STATE OF THE TABLE's OWN CONDITION
`onTR` (LinkTiedR.lean beside this file) IN FRONT OF A SUB-PROTOCOL AT WHOSE PLACE THE TABLE ASKS AN
                    OPEN LAYERS' OR ATTENTION SEGMENT: OUT OF THE PROMISE's BOOK-KEEPING `shapeAt`
                    ALONE. AT THE OUTPUT HEAD's SEGMENT: DOWN TO ONE SENTENCE: THE MERGE's SLOT IS
                    LAID. Theorems. A law file; no running text imports it.
  `shape_of_onTR`   onTR N Mg links ps get Rch k a ⊢ shapeAt links ps[k]? (get a.1).2 = true.
  `part_of_lay`, `part_of_att`   where a layers' | an attention segment's part stands open the lens
                    reads a part.
  `part_of_head`    where the head's segment stands open: the lens reads a part just if usedOf
                    answers (the merge's slot).
  `part_of_stand`   standOf s = .link sub, sub not the head's ⊢ (atS.get? s).isSome = true.
  `part_of_onTR`    ps[k]? = some p · standAt links p = .link sub · sub ≠ .head · onTR … k a ⊢
                    (atS.get? (get a.1).2).isSome = true.
  `part_of_onTR_head`   the same at sub = .head, with (usedOf (get a.1).2).isSome = true beside.
  `owed_of_onTR`    ps[k]? = some p · mayWait links p = false · onTR … k a ⊢ owedOf (get a.1).2 =
                    none.

Limits. That usedOf answers at the head's batching's front is not shown here. Nothing on the
ledger's marks. Nothing on soundness or on hiding.
-/
import Johnson.Desc.First.Link.Law.LinkTiedR
import Johnson.Desc.First.Batch.AtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K9 (atS usedOf owedOf)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning shapeAt standOf standAt mayWait Stand)

section
variable {A P W : Type} {Fr : Frame} {N : Numbers} {Mg : Meaning P W} {links : List ModelPart}
  {ps : List Place} {get : A → P × S} {Rch : ℕ → A × Fr.E.Str → Prop} {k : ℕ} {a : A × Fr.E.Str}

/-- The promise's book-keeping, out of the table's own condition. -/
theorem shape_of_onTR (h : onTR N Mg links ps get Rch k a) :
    shapeAt links ps[k]? (get a.1).2 = true := by
  obtain ⟨⟨hq, hm⟩, _⟩ := h
  rcases hq.2 with hf | ⟨hb, _⟩
  · exact absurd hf hm
  · simp only [Bool.and_eq_true] at hb
    exact hb.1.1.1.1.1

end

theorem part_of_stand {s : S} {sub : ModelPart} (h : standOf s = .link sub) (hs : sub ≠ .head) :
    (atS.get? s).isSome = true := by
  unfold standOf at h
  cases hh : s.here with
  | lay a => simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh]
  | att a => simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh]
  | head a =>
    rw [hh] at h
    dsimp only at h
    split at h
    · exact absurd (Stand.link.inj h).symm hs
    · cases h
  | between => rw [hh] at h; cases h
  | fin a => rw [hh] at h; cases h
  | mem a => rw [hh] at h; cases h

theorem part_of_head {s : S} (h : standOf s = .link .head) (hu : (usedOf s).isSome = true) :
    (atS.get? s).isSome = true := by
  unfold standOf at h
  cases hh : s.here with
  | head a =>
    rw [hh] at h
    dsimp only at h
    split at h
    · rename_i hin
      have ho : a.opened = true := by
        cases e : a.opened with
        | true => rfl
        | false => simp [S.inLink, S.fork?, hh, e] at hin
      obtain ⟨u, hu'⟩ := Option.isSome_iff_exists.1 hu
      simp [atS, S.link?, S.fork?, S.tl?, hh, ho, hu']
    · cases h
  | lay a => rw [hh] at h; cases h
  | att a => rw [hh] at h; cases h
  | between => rw [hh] at h; cases h
  | fin a => rw [hh] at h; cases h
  | mem a => rw [hh] at h; cases h

section
variable {A P W : Type} {Fr : Frame} {N : Numbers} {Mg : Meaning P W} {links : List ModelPart}
  {ps : List Place} {get : A → P × S} {Rch : ℕ → A × Fr.E.Str → Prop} {k : ℕ} {a : A × Fr.E.Str}
  {p : Place}

theorem stand_of_onTR (hp : ps[k]? = some p) (h : onTR N Mg links ps get Rch k a) :
    standOf (get a.1).2 = standAt links p := by
  have hs := shape_of_onTR h
  rw [hp] at hs
  unfold shapeAt at hs
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  exact hs.1.1

/-- **A part is there, at a layers' or an attention segment: from the promise alone.** -/
theorem part_of_onTR {sub : ModelPart} (hp : ps[k]? = some p) (hst : standAt links p = .link sub)
    (hs : sub ≠ .head) (h : onTR N Mg links ps get Rch k a) :
    (atS.get? (get a.1).2).isSome = true :=
  part_of_stand ((stand_of_onTR hp h).trans hst) hs

/-- **At the head's segment: with the merge's slot.** -/
theorem part_of_onTR_head (hp : ps[k]? = some p) (hst : standAt links p = .link .head)
    (h : onTR N Mg links ps get Rch k a) (hu : (usedOf (get a.1).2).isSome = true) :
    (atS.get? (get a.1).2).isSome = true :=
  part_of_head ((stand_of_onTR hp h).trans hst) hu

/-- No count of rows waits. -/
theorem owed_of_onTR (hp : ps[k]? = some p) (hw : mayWait links p = false)
    (h : onTR N Mg links ps get Rch k a) : owedOf (get a.1).2 = none := by
  have hs := shape_of_onTR h
  rw [hp] at hs
  unfold shapeAt at hs
  simp only [Bool.and_eq_true, Bool.or_eq_true, hw, Bool.false_eq_true, or_false] at hs
  have hn := hs.1.2
  unfold S.noneWaits at hn
  unfold owedOf
  cases e : (get a.1).2.rowsOwed with
  | none => rfl
  | some r =>
    rw [e] at hn
    have : r = 0 := by simpa using hn
    subst this
    rfl

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.part_of_onTR
#print axioms VerifiableInference.Desc.LinkJoin.part_of_onTR_head
#print axioms VerifiableInference.Desc.LinkJoin.owed_of_onTR
