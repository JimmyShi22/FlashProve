-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/HonestTrace/SeatsApartOfLayout.lean

Conditional lemma on public data alone: where every entry inside the sizes has its array in the
request's layout (Meaning.laidThere), the programs' own test on the layout accepts
(OnBytes.reqLayoutOk), the numbers of the witness's messages are apart at the arrays that the labels
name (NumsApartAt) and two labels with one owner are one label (LabelsApart): inside the sizes, two
seats off the layout (Meaning.fLay) that name one message, row and place belong to one label, one
row of symbols and one column (SeatsApart). In the goals' scope, at sizes that follow the plans
(Meaning.Follows), LabelsApart is shown.
This file states no goal.

Why. An honest prover's messages are to hold the packed values of its integers at the layout's
seats. Where two seats name one place and the values differ, no messages can. Whether the seats are
apart is a matter of the public files alone.

Main definitions and theorems:
* "SeatsApart X s f": the sentence on seats. It has the text of SymSeatsApart
  (Johnson/Goal/HonestTrace/ConstrAtThread.lean, a file outside the library, at its bytes
), word for word, by a comparison of bytes. No file of the library states that Lean
  takes the two for one sentence.
* "NumsApartAt X s layout num", "LabelsApart X s": two conditions on public data.
* "seatsApart_of_layout": the lemma of the first paragraph, at every X, s, layout and num.
* "lab_at_owner": under publicOf ... = .ok X and Hd.PublicCore X.P, for k < 25 and an entry a of
  the plan's list: the entry's label is the label of the entry that it names as its owner.
* "labelsApart_of_core": under the same two premises and sizes that follow the plans: LabelsApart.
  "labelsApart_in_scope": the same under the three premises on the files.

How. The weight lies in laidPlace_apart (Johnson/Desc/First/Look/K3CallerLaidApart.lean): under
reqLayoutOk, in one message of one link no entry of the table holds two elements. Around it:
seat_of_laidThere (Johnson/Goal/Meaning/HidSeatsOf.lean) says what a seat is; laidPlace_eq_laidAt
(Johnson/Goal/Meaning/ReadingsOne.lean) joins the two readers of a layout, and the two readers of an
array's name, arrayOf and OnBytes.reqArray, are one by their texts (reqArray_eq_arrayOf, the same
file); nameOf_inj (Johnson/Goal/Meaning/ServedSeats.lean): an array's name names its number. For the
labels: owner_cases (Johnson/Goal/Meaning/HidOwner.lean) and the last clause of the test pairFit at
the 24 readers' entries (planFit_of_core, Johnson/Goal/Meaning/HidPlanFit.lean).

Limits. seatsApart_of_layout shows its four premises of no X, sizes, layout or numbering. Under the
head h : P5J.AtMgA OnBytes.secondHashFunction ... the library has two of the four at the head's own values:
laidThere is the field h.plan.laid, reqLayoutOk is Q38.lawful_at_head
(Johnson/HB/LLHARD/Q38J/LawfulAtHead.lean). NumsApartAt is shown of no numbering here; all four are
had under the head in Johnson/Goal/HonestTrace/SeatsApartAtHead.lean. The seats of symbols in main
rows alone: nothing on mask rows or pads. 25 sub-proofs. owners_apart (ServedSeats.lean) is another
sentence: two entries of ONE list with one owner are one entry; LabelsApart is across two lists and
ends in one label, not in one entry: a reader's entry and its owner's have one label. Two of the
short names stand in other namespaces of the library too: VerifiableInference.Desc.Key.SeatsApart
(Johnson/Desc/Key/KeyLay.lean) and OnBytes.K.Arm.LabelsApart (Johnson/PV/CutAll.lean): other
sentences. A file that opens one of these namespaces beside this one writes the full name.

Not claimed: that an honest prover's messages hold anything; anything on what a verifier accepts;
any property of the protocol.

-/
import Johnson.Goal.Meaning.ServedSeats
import Johnson.Goal.Meaning.HidPlanFit
import Johnson.Goal.Meaning.ScopeCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open OnBytes.Road
open OnBytes.Model.Verify (publicOf)
open OnBytes.Model.Layer (matIx)
open Cb.Pv.Tail (Size)
open Meaning (labAt matsAt ownerK ownerA nameOf fLay laidThere Follows pairFit planFit)
open OnBytes.Params (ReqLayout ReqShape ReqArray)
open VerifiableInference.Desc (arrayOf)

/-- **The seats are apart**: inside the sizes, two seats that name one message, row and place are
the seats of one label, one row of symbols and one column. -/
def SeatsApart (X : Model.Verify.Public) (s : ℕ → Size) (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) : Prop :=
  ∀ m < 25, ∀ a < (s m).NM, ∀ i' < Alg.symRows ((s m).m a), ∀ c < (s m).k a,
  ∀ m' < 25, ∀ a' < (s m').NM, ∀ j' < Alg.symRows ((s m').m a'), ∀ c' < (s m').k a',
    f (labAt X m a) i' c = f (labAt X m' a') j' c' → labAt X m a = labAt X m' a' ∧ i' = j' ∧ c = c'

/-- The numbers of the witness's messages are apart at the arrays that the labels name: two such
arrays whose messages bear one number lie in one link and in one message of it. -/
def NumsApartAt (X : Model.Verify.Public) (s : ℕ → Size) (layout : ReqLayout)
    (num : ℕ → ℕ → ℕ) : Prop :=
  ∀ m < 25, ∀ a < (s m).NM, ∀ m' < 25, ∀ a' < (s m').NM, ∀ A A' : ReqArray,
    arrayOf layout (ownerK (labAt X m a)) (nameOf (ownerA (labAt X m a))) = some A →
    arrayOf layout (ownerK (labAt X m' a')) (nameOf (ownerA (labAt X m' a'))) = some A' →
    num (ownerK (labAt X m a)) A.message = num (ownerK (labAt X m' a')) A'.message →
      ownerK (labAt X m a) = ownerK (labAt X m' a') ∧ A.message = A'.message

/-- Two labels inside the sizes with one owner's sub-proof and one number there are one label. -/
def LabelsApart (X : Model.Verify.Public) (s : ℕ → Size) : Prop :=
  ∀ m < 25, ∀ a < (s m).NM, ∀ m' < 25, ∀ a' < (s m').NM,
    ownerK (labAt X m a) = ownerK (labAt X m' a') → ownerA (labAt X m a) = ownerA (labAt X m' a') →
      labAt X m a = labAt X m' a'

/-- **From the programs' own test on the layout, with laidThere, NumsApartAt and LabelsApart, to the
seats' apartness.** -/
theorem seatsApart_of_layout {X : Model.Verify.Public} {s : ℕ → Size} {codes : OnBytes.Codes}
    {shape : ReqShape} {layout : ReqLayout} {num : ℕ → ℕ → ℕ}
    (hL : laidThere X s layout = true) (ok : OnBytes.reqLayoutOk codes shape layout = true)
    (hN : NumsApartAt X s layout num) (hB : LabelsApart X s) :
    SeatsApart X s (fLay layout num) := by
  intro m hm a ha i' hi c hc m' hm' a' ha' j' hj c' hc' e
  obtain ⟨A, x, hA, -, -, hx, hs⟩ := Meaning.seat_of_laidThere hL num hm ⟨a, ha⟩ hi hc
  obtain ⟨A', x', hA', -, -, hx', hs'⟩ := Meaning.seat_of_laidThere hL num hm' ⟨a', ha'⟩ hj hc'
  have e2 : (num (ownerK (labAt X m a)) A.message, x.1, x.2) =
      (num (ownerK (labAt X m' a')) A'.message, x'.1, x'.2) := hs.symm.trans (e.trans hs')
  have e3 := congrArg Prod.fst e2
  have e4 := congrArg (fun q => q.2.1) e2
  have e5 := congrArg (fun q => q.2.2) e2
  obtain ⟨eK, eM⟩ := hN m hm a ha m' hm' a' ha' A A' hA hA' e3
  have ex : x = x' := Prod.ext e4 e5
  rw [← eK] at hA'
  obtain ⟨en, ei, ec⟩ := VerifiableInference.Desc.First.Look.laidPlace_apart ok hA hA' eM
    ((Meaning.laidPlace_eq_laidAt A i' c).trans hx)
    ((Meaning.laidPlace_eq_laidAt A' j' c').trans (ex ▸ hx'))
  exact ⟨hB m hm a ha m' hm' a' ha' eK (Meaning.nameOf_inj en), ei, ec⟩

section Core
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **An entry's label is the label of the entry that it names as its owner.** -/
theorem lab_at_owner (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {k a : ℕ}
    (hk : k < 25) (ha : a < (matsAt X k).size) :
    labAt X k a = labAt X (ownerK (labAt X k a)) (ownerA (labAt X k a)) := by
  have F := Meaning.planFit_of_core h C
  unfold planFit at F
  rw [Bool.and_eq_true, List.all_eq_true] at F
  have fin : ∀ k' a', pairFit X k a k' a' = true → ownerK (labAt X k a) = k' →
      ownerA (labAt X k a) = a' →
      labAt X k a = labAt X (ownerK (labAt X k a)) (ownerA (labAt X k a)) := by
    intro k' a' hp o1 o2
    unfold pairFit at hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    rw [o1, o2]
    exact hp.2
  rcases Meaning.owner_cases h C hk ha with ⟨o1, o2⟩ | ⟨g, g0, hg, rfl, rfl, o1, o2⟩ |
      ⟨g, hg, rfl, rfl, o1, o2⟩ | ⟨rfl, rfl, o1, o2⟩
  · rw [o1, o2]
  · have Fg := F.1 g (List.mem_range.2 hg)
    rw [Bool.and_eq_true, Bool.or_eq_true] at Fg
    rcases Fg.1 with e | e
    · exact absurd (beq_iff_eq.1 e) (by omega)
    · exact fin _ _ e o1 o2
  · have Fg := F.1 g (List.mem_range.2 hg)
    rw [Bool.and_eq_true] at Fg
    exact fin _ _ Fg.2 o1 o2
  · exact fin _ _ F.2 o1 o2

/-- **Two labels with one owner are one label**, where the sizes follow the plans. -/
theorem labelsApart_of_core (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    {s : ℕ → Size} (F : Follows X s) : LabelsApart X s := by
  intro m hm a ha m' hm' a' ha' eK eA
  rw [F.NM m hm] at ha
  rw [F.NM m' hm'] at ha'
  calc labAt X m a = labAt X (ownerK (labAt X m a)) (ownerA (labAt X m a)) :=
        lab_at_owner h C hm ha
    _ = labAt X (ownerK (labAt X m' a')) (ownerA (labAt X m' a')) := by rw [eK, eA]
    _ = labAt X m' a' := (lab_at_owner h C hm' ha').symm

end Core

/-- The same under the three premises on the files. -/
theorem labelsApart_in_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {s : ℕ → Size} (F : Follows X s) : LabelsApart X s :=
  labelsApart_of_core h (Hd.core_of_scope hZ hR h) F

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.seatsApart_of_layout
#print axioms OnBytes.HonestTrace.lab_at_owner
#print axioms OnBytes.HonestTrace.labelsApart_of_core
#print axioms OnBytes.HonestTrace.labelsApart_in_scope
