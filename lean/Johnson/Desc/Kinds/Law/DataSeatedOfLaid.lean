-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/DataSeatedOfLaid.lean (MatsSeated's columns are a letter Cols):
THE FACTS UNDER WHICH THE FORMS' DATA AND THE HEAD'S
COMPONENTS MEET (Law/DataMeetsCells.lean: DataSeated: eight clauses AN ELEMENT) FROM ONE TEST WITH
CODE ON THE PLAN, ONE CLAUSE OF PlanK6, AND FIVE FACTS A MATRIX ON THE VERIFIER'S STATE.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law).
  MatsSeated arr N Wp own a num lay: for each of segment 24's matrices that has a column in Cols (a
      letter), and the array A that its label names in the layout: the open link's frame names A's
      message: o; A fits the statement's bits of o; the book seats o at x, a tenant of segment 24's
      group, with the number that num gives the message.
  dataSeated_of_laid: DataSeated, from the test laidThere (every element of every matrix is
      laid: Johnson/Goal/Meaning/HidSeatsOf.lean: seat_of_laidThere), "the open link's layout is the
      plan's", PlanK6's clause named, and MatsSeated.

Every letter under "there is" (in MatsSeated): o: pinned by the frame; x: by the book.
What it does not say. MatsSeated AT ANY STATE: five facts on the verifier's state at each of seven
matrices:
nobody's. That the test accepts. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.DataMeetsCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Params
open OnBytes.Model.Verify (borderOf)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (namedOnce)

/-- **Five facts a matrix, on the verifier's state.** -/
def MatsSeated (Cols : Nat → Nat → Prop) (arr : Nat → Nat → Nat) (N : Numbers) (Wp :
    OnBytes.Model.Verify.Public)
    (own : List (Nat × Nat)) (a : K9.Part) (num : Nat → Nat → Nat) (lay : ReqLayout) : Prop :=
  ∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (c : Nat), c < (Meaning.sizesOf Wp 24).k μ →
    Cols μ.val c → ∀ A : ReqArray,
    Desc.arrayOf lay (Meaning.ownerK (Meaning.labAt Wp 24 μ.val))
      (Meaning.nameOf (Meaning.ownerA (Meaning.labAt Wp 24 μ.val))) = some A →
    ∃ (o : Nat) (x : Nat × Nat),
      a.L.check.frame.whereIs (Meaning.ownerK (Meaning.labAt Wp 24 μ.val)) A.message = some o ∧
      laidMatrixOk A (a.d.st.rowBits o .main) (a.d.st.placeBits o .main) = true ∧
      K9.seatAt own a.d.book o = some x ∧ x ∈ N.group 24 ∧
      arr x.1 x.2 = num (Meaning.ownerK (Meaning.labAt Wp 24 μ.val)) A.message

/-- **DataSeated from a test on the plan and five facts a matrix.** -/
theorem dataSeated_of_laid (arr : Nat → Nat → Nat) (N : Numbers)
    (Wp : OnBytes.Model.Verify.Public) (own : List (Nat × Nat)) (a : K9.Part)
    (num : Nat → Nat → Nat) (lay : ReqLayout)
    (T : Meaning.laidThere Wp (Meaning.sizesOf Wp) lay = true)
    (hlay : a.L.check.rows.layout = lay)
    (p1 : ∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
      ColFour Wp.hS Wp.HLy (borderOf Wp.y) μ.val c →
      namedOnce arr N 24 (seatLay Wp lay num 24 μ r c).1 = true)
    (hM : MatsSeated (ColFour Wp.hS Wp.HLy (borderOf Wp.y)) arr N Wp own a num lay) :
    DataSeated arr N Wp own a num := by
  intro μ r c hr hc hcol
  obtain ⟨A, x0, hA, _, _, hl, hs⟩ :=
    Meaning.seat_of_laidThere T num (k := 24) (by decide) μ hr hc
  obtain ⟨o, x, h3, h4, h5, h6, h7⟩ := hM μ c hc hcol A hA
  have h8 := p1 μ r c hr hc hcol
  have e : (seatLay Wp lay num 24 μ r c).1 =
      num (Meaning.ownerK (Meaning.labAt Wp 24 μ.val)) A.message := by
    show (Meaning.seatBy (Meaning.fLay lay num) Wp (Meaning.sizesOf Wp) 24 μ r c).1 = _
    rw [hs]
  rw [e] at h8
  exact ⟨A, x0, o, x, by rw [hlay]; exact hA, hl, h3, h4, h5, h6, h7, h8⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.dataSeated_of_laid
