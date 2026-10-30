-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FormsAgree.lean: THE SENTENCES OF THE CLAIMS ON LINEAR FORMS READ THE WITNESS's
TABLES ONLY WHERE THE SEGMENT's DATA DO: two readers of the witness's tables that give the open
segment the same cells, and the same mask entries below the ledger's number of slots, give these
sentences one truth value. Definitions and theorems.
Why. The composed meaning of the open claims (`mgAll`, Johnson/Desc/Sound/MgAll.lean) states
`formsQ`, `formsQA`, `formsTQ`, `totalQ`, `totalBQ` at the reader `seatTab cs arr ms w`, which is
not clamped: outside a member's ranges it reads what no pin fixes (Johnson/Desc/Sound/MsgSig.lean,
`MsgT`). A law that needs "two pinned witnesses have one table" is stated at a clamped reader
(`LinkJoin.rdC`, Johnson/Desc/First/Link/Law/ClampPin.lean: the member's typed message read back,
0 outside). This file is the step between: it is general in the two readers.
  `AgreeQ own a rd rd'`: `dataQ own a rd'` and `dataQ own a rd` have the same cells, and the same
    mask entry at every j below a.F.ns and below a.F.LS.size.
  `AgreeQA sent own a rd rd'`: that, and the cells that are read ahead (`cellA`) are the same.
  `value_agree`: a form whose slots pass `slotIn` has one value at two data with the same cells
    and the same mask entries below a.F.ns.
  `formsQ_agree`, `formsQA_agree`, `formsTQ_agree`, `totalQ_agree`, `totalBQ_agree`: under the
    agreement at the state's own part, the sentence at rd gives the sentence at rd'.
    `AgreeQ.symm`, `AgreeQA.symm`: so each is an "if and only if".
`formsTQ_agree` asks two things of the stated functions: what they lay reads the data's cells
alone, and they leave the mask row.
Limits: THAT `seatTab` AND A CLAMPED READER AGREE IN THIS SENSE IS NOT SHOWN HERE: for the cells
it wants "an entry inside an array lies inside the member's ranges" (in the library:
Johnson/Goal/Meaning/LaidInside.lean) joined to the plan; for the mask entries "the ledger's
number of slots is at most the mask code's length less the pad": nobody's lemma yet. No soundness
is claimed.

-/
import Johnson.Desc.Sound.FormsQ
import Johnson.Desc.Sound.FormsAhead

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Readers segAt? atS slotIn affIn affInT affInA aheadIn totalIn)
open VerifiableInference.Desc.K9L (Bound worldAt entryAt)
open VerifiableInference.Desc.First (S)

section
variable (own : List (ℕ × ℕ))

/-- The two readers give the segment the same cells, and the same mask entries at the ledger's
slots. -/
structure AgreeQ (a : K9.Part) (rd rd' : ℕ × ℕ → MsgQ) : Prop where
  cell : (dataQ own a rd').cell = (dataQ own a rd).cell
  mask : ∀ j, j < a.F.ns ∨ j < a.F.LS.size → (dataQ own a rd').mask j = (dataQ own a rd).mask j

theorem AgreeQ.symm {a : K9.Part} {rd rd' : ℕ × ℕ → MsgQ} (h : AgreeQ own a rd rd') :
    AgreeQ own a rd' rd := ⟨h.cell.symm, fun j hj => (h.mask j hj).symm⟩

/-- A slot that passes the test stands below the ledger's number of slots. -/
theorem lt_of_slotIn (free : Option ℕ) (late : List (ℕ × E × E)) (a : K9.Part) (j : ℕ)
    (h : slotIn own free late a j = true) : j < a.F.ns := by
  unfold slotIn at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- **A form whose slots pass the test reads the data's cells, and the mask row below the ledger's
number of slots.** -/
theorem value_agree (free : Option ℕ) (late : List (ℕ × E × E)) (a : K9.Part) (Da Db : Bound GQ)
    (f : Aff) (hsl : ∀ x ∈ f.slots.toList, slotIn own free late a x.1 = true)
    (hc : Db.cell = Da.cell) (hm : ∀ j, j < a.F.ns → Db.mask j = Da.mask j) :
    f.value Reading.gl (worldOwn a late Db) = f.value Reading.gl (worldOwn a late Da) :=
  value_ridesW own free late a a Da Db rfl (fun _ _ _ => ⟨rfl, rfl⟩) f hsl
    (fun _ _ _ _ => by rw [hc])
    (fun x hx => hm x.1 (lt_of_slotIn own free late a x.1 (hsl x hx)))

variable (Rd : Readers)

theorem formsQ_agree (piece : ℕ) (run : String) (s : S) (rd rd' : ℕ × ℕ → MsgQ)
    (h : ∀ a, segAt? s = some a → AgreeQ own a rd rd') (hw : formsQ Rd own piece run s rd) :
    formsQ Rd own piece run s rd' := by
  obtain ⟨a, R, ha, hs, hl, hf⟩ := hw
  refine ⟨a, R, ha, hs, hl, fun f hfm => ⟨(hf f hfm).1, ?_⟩⟩
  have hA := h a ha
  have hin := (hf f hfm).1
  unfold affIn at hin
  simp only [Bool.and_eq_true, List.all_eq_true] at hin
  rw [value_agree own (K9.mergeOf s) R.late a _ _ f hin.2 hA.cell
    fun j hj => hA.mask j (Or.inl hj)]
  exact (hf f hfm).2

theorem formsTQ_agree (St : Stated) (piece : ℕ) (run : String) (s : S) (rd rd' : ℕ × ℕ → MsgQ)
    (hC : ∀ D D' : Bound GQ, D'.cell = D.cell → (St.at1 s D').cell = (St.at1 s D).cell)
    (hM : ∀ D : Bound GQ, (St.at1 s D).mask = D.mask)
    (h : ∀ a, segAt? s = some a → AgreeQ own a rd rd') (hw : formsTQ Rd St own piece run s rd) :
    formsTQ Rd St own piece run s rd' := by
  obtain ⟨a, R, ha, hs, hl, hf⟩ := hw
  refine ⟨a, R, ha, hs, hl, fun f hfm => ⟨(hf f hfm).1, ?_⟩⟩
  have hA := h a ha
  have hin := (hf f hfm).1
  unfold affInT at hin
  simp only [Bool.and_eq_true, List.all_eq_true] at hin
  rw [value_agree own (K9.mergeOf s) R.late a _ _ f hin.2 (hC _ _ hA.cell)
    fun j hj => by rw [hM, hM]; exact hA.mask j (Or.inl hj)]
  exact (hf f hfm).2

end

section
variable (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ))

/-- The agreement, and the cells that are read ahead are the same. -/
structure AgreeQA (a : K9.Part) (rd rd' : ℕ × ℕ → MsgQ) : Prop extends AgreeQ own a rd rd' where
  ahead : ∀ b h, aheadIn sent own a b = some h →
    cellA a.d.st.codes h rd' = cellA a.d.st.codes h rd

theorem AgreeQA.symm {a : K9.Part} {rd rd' : ℕ × ℕ → MsgQ} (h : AgreeQA sent own a rd rd') :
    AgreeQA sent own a rd' rd :=
  { toAgreeQ := h.toAgreeQ.symm own, ahead := fun b x hx => (h.ahead b x hx).symm }

theorem dataQA_cell_agree (a : K9.Part) (rd rd' : ℕ × ℕ → MsgQ)
    (h : AgreeQA sent own a rd rd') :
    (dataQA sent own a rd').cell = (dataQA sent own a rd).cell := by
  funext born name i c
  show (match aheadIn sent own a (born, name) with
    | some x => cellA a.d.st.codes x rd' i c
    | none => (dataQ own a rd').cell born name i c) =
    (match aheadIn sent own a (born, name) with
    | some x => cellA a.d.st.codes x rd i c
    | none => (dataQ own a rd).cell born name i c)
  cases e : aheadIn sent own a (born, name) with
  | some x => exact congrFun (congrFun (h.ahead _ x e) i) c
  | none => exact congrFun (congrFun (congrFun (congrFun h.cell born) name) i) c

theorem formsQA_agree (Rd : Readers) (piece : ℕ) (run : String) (s : S)
    (rd rd' : ℕ × ℕ → MsgQ) (h : ∀ a, segAt? s = some a → AgreeQA sent own a rd rd')
    (hw : formsQA sent own Rd piece run s rd) : formsQA sent own Rd piece run s rd' := by
  obtain ⟨a, R, ha, hs, hl, hf⟩ := hw
  refine ⟨a, R, ha, hs, hl, fun f hfm => ⟨(hf f hfm).1, ?_⟩⟩
  have hA := h a ha
  have hin := (hf f hfm).1
  unfold affInA at hin
  simp only [Bool.and_eq_true, List.all_eq_true] at hin
  rw [value_agree own (K9.mergeOf s) R.late a _ _ f hin.2 (dataQA_cell_agree sent own a rd rd' hA)
    fun j hj => hA.mask j (Or.inl hj)]
  exact (hf f hfm).2

end

section
variable (own : List (ℕ × ℕ))

/-- Two summands that agree at the places of the list give one sum. -/
theorem sumFrom_agree {α : Type} (g g' : ℕ → α → GQ) :
    ∀ (l : List α) (s : ℕ), (∀ i x, s ≤ i → i < s + l.length → g' i x = g i x) →
      sumFrom g' s l = sumFrom g s l
  | [], _, _ => rfl
  | x :: l, s, H => by
    simp only [sumFrom]
    rw [H s x (Nat.le_refl s) (by simp),
      sumFrom_agree g g' l (s + 1) fun i y h1 h2 =>
        H i y (Nat.le_of_succ_le h1) (by simp only [List.length_cons]; omega)]

theorem totalQ_agree (s : S) (rd rd' : ℕ × ℕ → MsgQ)
    (h : ∀ a, atS.get? s = some a → AgreeQ own a rd rd') (hw : totalQ own s rd) :
    totalQ own s rd' := by
  obtain ⟨a, ha, hf⟩ := hw
  refine ⟨a, ha, ?_⟩
  have hA := h a ha
  have he : (worldSum a (dataQ own a rd')).entry = (worldSum a (dataQ own a rd)).entry := by
    funext t r i
    show entryAt Reading.gl a.L.arrayOf _ (dataQ own a rd') t r i =
      entryAt Reading.gl a.L.arrayOf _ (dataQ own a rd) t r i
    unfold entryAt
    rw [hA.cell]
  have hsl : ∀ j, j < a.F.LS.size →
      (worldSum a (dataQ own a rd')).slot j = (worldSum a (dataQ own a rd)).slot j := by
    intro j hj
    show Reading.gl.val _ - Reading.gl.val _ * (dataQ own a rd').mask j =
      Reading.gl.val _ - Reading.gl.val _ * (dataQ own a rd).mask j
    rw [hA.mask j (Or.inr hj)]
  have e : a.F.total Reading.gl (worldSum a (dataQ own a rd')) =
      a.F.total Reading.gl (worldSum a (dataQ own a rd)) := by
    unfold Fork.total treesValue slotsValue HTree.value HRow.value
    rw [he]
    congr 2
    exact sumFrom_agree _ _ _ 0 fun i x _ h2 => by
      rw [hsl i (by simpa using h2)]
  rw [e]
  exact hf

theorem totalBQ_agree (after : S → Except String S) (s : S) (rd rd' : ℕ × ℕ → MsgQ)
    (h : ∀ s' a, after s = .ok s' → atS.get? s' = some a → AgreeQ own a rd rd')
    (hw : totalBQ after own s rd) : totalBQ after own s rd' := by
  obtain ⟨s', h1, h2, h3⟩ := hw
  exact ⟨s', h1, h2, totalQ_agree own s' rd rd' (fun a ha => h s' a h1 ha) h3⟩

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.value_agree
#print axioms VerifiableInference.Desc.Sound.formsQ_agree
#print axioms VerifiableInference.Desc.Sound.formsTQ_agree
#print axioms VerifiableInference.Desc.Sound.formsQA_agree
#print axioms VerifiableInference.Desc.Sound.totalQ_agree
#print axioms VerifiableInference.Desc.Sound.totalBQ_agree
