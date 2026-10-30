-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/K6NamedText.lean: one of the seven conditions that are left in front of the law on
the sub-protocol K6 at the head (`K6LeftSeven`): `namedC`: the message of the
planes' matrix, number NHf + 2 of the head's list, is named once in the head's segment's group. It
follows from the head alone: no test on written values is called, no number is evaluated.

Row or tool. A general law and a law at the head, by calls of named laws. A payer for a premise of
another law.

Why. The test `OffPad.namedAtC arr N Wp lay6 num a` (Johnson/Desc/Kinds/Law/PlanK6Planes.lean) is,
sign for sign, what `P5J.seatsNamedC` (Johnson/P5J/SeatsNamedC.lean) asks at segment 24 and entry a.
The head holds `seatsNamedC` as a field. And NHf + 2 lies below the number of the head's matrices,
which is NHf + 4 wherever the maker of the public data returns (`k6_NM`,
Johnson/Desc/Kinds/Law/HeadPlanesTie.lean).

The test's text. The file that defines `namedAtC` is not imported by name. Its text
stands here spelled out: `namedText`. The file K6NamedAtHead.lean beside this one says the same at
the test's own name.

What is here.
  `namedText arr N Wp lay6 num a`.
  `namedText_of_seatsNamedC`: a yes of `seatsNamedC`, and a below the number of matrices of segment
    24, give it. General.
  `tl_24`, `nm_24`: at segment 24 the reader of the public data gives the head's plan; so the number
    of matrices is that plan's.
  `namedText_at_head`: at the head's own terms, at NHf + 2.

Limits. It says no more than the head's own field says at one entry. Nothing on soundness.


-/
import Johnson.P5J.MgAtAll
import Johnson.P5J.SeatsNamedC
import Johnson.Desc.Kinds.Law.HeadPlanesTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes
open OnBytes.Params (ReqLayout)
open VerifiableInference.Desc (arrayOf Chain)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (namedOnce)

/-- **The test's text.** -/
def namedText (arr : ℕ → ℕ → ℕ) (N : Numbers) (Wp : Model.Verify.Public) (lay6 : ReqLayout)
    (num : ℕ → ℕ → ℕ) (a : ℕ) : Bool :=
  match arrayOf lay6 (Meaning.ownerK (Meaning.labAt Wp 24 a))
      (Meaning.nameOf (Meaning.ownerA (Meaning.labAt Wp 24 a))) with
  | none => false
  | some A => namedOnce arr N 24 (num (Meaning.ownerK (Meaning.labAt Wp 24 a)) A.message)

/-- **It is what the wider test asks at segment 24.** -/
theorem namedText_of_seatsNamedC {X : Model.Verify.Public} {s : ℕ → Cb.Pv.Tail.Size}
    {layout : ReqLayout} {num arr : ℕ → ℕ → ℕ} {N : Numbers}
    (h : seatsNamedC X s layout num arr N = true) {a : ℕ} (ha : a < (s 24).NM) :
    namedText arr N X layout num a = true := by
  unfold seatsNamedC at h
  exact List.all_eq_true.1 (List.all_eq_true.1 h 24 (List.mem_range.2 (by omega))) a
    (List.mem_range.2 ha)

/-- At segment 24 the reader gives the head's plan. -/
theorem tl_24 (X : Model.Verify.Public) : Meaning.tlAt X 24 = X.H.tl := by
  unfold Meaning.tlAt
  rw [if_neg (by omega), if_pos rfl]

theorem nm_24 (X : Model.Verify.Public) : (Meaning.sizesOf X 24).NM = X.H.tl.NM := by
  unfold Meaning.sizesOf
  rw [tl_24]
  rfl

/-- **The condition, at the head's own terms.** -/
theorem namedText_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    namedText h.𝔇.arr h.𝔇.N (At.X Zp) (At.layout Zp) (At.num Zp) ((At.X Zp).hS.NHf + 2) = true := by
  have hn : (At.X Zp).hS.NHf + 2 < (Meaning.sizesOf (At.X Zp) 24).NM := by
    rw [nm_24, VerifiableInference.Desc.Kinds.Head.Law.k6_NM h.pubOne]
    omega
  exact namedText_of_seatsNamedC h.plan.named hn

end P5J

#print axioms P5J.namedText_of_seatsNamedC
#print axioms P5J.tl_24
#print axioms P5J.nm_24
#print axioms P5J.namedText_at_head
