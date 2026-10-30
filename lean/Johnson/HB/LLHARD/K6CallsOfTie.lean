-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/K6CallsOfTie.lean: the one premise that K6CallsText.lean leaves, `callNamesB` at
the built segment 24's list of arrays, follows at the head from "the names' tie" at segment 24, in
the letters of `NamesTie24`: at the number of each matrix's symbol array the built list
names the owner and the name that the matrix's label gives. So the condition `callsC`, at its text,
follows from that tie.

Row or tool. Two laws at the head, by rewriting through named ties. Nothing is evaluated here. So
that a join is one call.

The premise. `NamesTie24 Zp`: for every μ below `(sizesOf Zp.p.X 24).NM`: `((Zp.p.built.links.map
(·.arrayOf)).getD 24 #[])[(tlAt Zp.p.X 24).gtTree.getD μ 0]? = some (ownerK (labAt Zp.p.X 24 μ),
nameOf (ownerA (labAt Zp.p.X 24 μ)))`. It is the conclusion, at k = 24, of the statement
`names_tie_all` that others are typing; `names_tie_head_all` has it at μ below
8 with `Zp.p.X.H.tl` for `tlAt Zp.p.X 24`: `tl_24` (K6NamedText.lean) joins these two spellings.

(Where this and lean/THEOREM.md differ, the page holds.) Neither statement's file is imported here.

What is here.
  `NamesTie24`.
  `callNames_of_tie`: at the head, `NamesTie24 Zp` gives `callNamesB` at the head's own term for the
    list.
  `callsText_of_tie`: so it gives the condition at its text.
  `namesTie24_of_head`: the other spelling, at μ below 8 and `Zp.p.X.H.tl`, gives `NamesTie24 Zp` at
    the head.

Limits. The tie is a premise. Nothing on soundness.


-/
import Johnson.HB.LLHARD.K6CallsText

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes OnBytes.Model Johnson.G
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (Place)
open VerifiableInference.PlanWritten (tailView xShapeOf)
open VerifiableInference.PlanWritten.Joined (xShape_in_scope)
open Meaning (ownerK ownerA nameOf labAt sizesOf tlAt viewTail viewEntry viewTail_at viewEntry_at)

/-- **The names' tie at segment 24.** -/
def NamesTie24 (Zp : ProofFile.Pub) : Prop :=
  ∀ μ, μ < (sizesOf Zp.p.X 24).NM →
    ((Zp.p.built.links.map (·.arrayOf)).getD 24 #[])[(tlAt Zp.p.X 24).gtTree.getD μ 0]? =
      some (ownerK (labAt Zp.p.X 24 μ), nameOf (ownerA (labAt Zp.p.X 24 μ)))

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Place}

/-- At the head the written view's tail at segment 24 is the public data's. -/
theorem view_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    viewTail xShapeFull 24 = tailView (tlAt Zp.p.X 24) ∧
      ∀ a, ownW a = (ownerK (labAt Zp.p.X 24 a), nameOf (ownerA (labAt Zp.p.X 24 a))) := by
  have hF := H2K.Sizes.publicO_at_scope h.scope h.laid.publicO
  have hV : xShapeOf Zp.p.X = xShapeFull :=
    xShape_in_scope h.scope h.laid.pub (pins_of_laid h.scope h.laid).1
  refine ⟨?_, fun a => ?_⟩
  · rw [← hV]
    exact viewTail_at hF.p4 hF.groups (by omega)
  · unfold ownW
    rw [← hV, viewEntry_at hF.p4 hF.groups (by omega) a]

/-- **The tie gives the eight names.** -/
theorem callNames_of_tie (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (T : NamesTie24 Zp) :
    callNamesB (h.𝔇.sent.arrayOf.getD 24 #[]) = true := by
  obtain ⟨hT, hO⟩ := view_at_head h
  have hNM : (sizesOf Zp.p.X 24).NM = 8 := by
    rw [← view_24, hT]
    rfl
  unfold callNamesB
  refine List.all_eq_true.2 fun a ha => ?_
  rw [hT, gt_of, hO a, beq_iff_eq]
  exact T a (hNM ▸ List.mem_range.1 ha)

/-- **So it gives the condition, at its text.** -/
theorem callsText_of_tie (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (T : NamesTie24 Zp) :
    callsText h.𝔇.arr (h.𝔇.N.group 24) (At.layout Zp) (At.num Zp) h.𝔇.sent x.link
      (h.𝔇.l3.seat x.link false)
      (h.𝔇.ms.map fun y => ((y.1.l.get y.2).1, VerifiableInference.Desc.Sound.seatOf y))
      (sizesOf (At.X Zp) 24).NM (At.X Zp).hS.NHf
      (fun a => (ownerK (labAt (At.X Zp) 24 a), nameOf (ownerA (labAt (At.X Zp) 24 a))))
      (fun a => (h.𝔇.sent.arrayOf.getD x.link #[])[(tlAt (At.X Zp) 24).gtTree.getD a 0]? ==
        some (ownerK (labAt (At.X Zp) 24 a), nameOf (ownerA (labAt (At.X Zp) 24 a)))) = true :=
  callsText_at_head h (callNames_of_tie h T)

/-- The other spelling gives the tie. -/
theorem namesTie24_of_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (T : ∀ μ, μ < 8 →
      ((Zp.p.built.links.map (·.arrayOf)).getD 24 #[])[Zp.p.X.H.tl.gtTree.getD μ 0]? =
        some (ownerK (labAt Zp.p.X 24 μ), nameOf (ownerA (labAt Zp.p.X 24 μ)))) :
    NamesTie24 Zp := by
  obtain ⟨hT, -⟩ := view_at_head h
  have hNM : (sizesOf Zp.p.X 24).NM = 8 := by
    rw [← view_24, hT]
    rfl
  intro μ hμ
  rw [tl_24]
  exact T μ (hNM ▸ hμ)

end

end P5J

#print axioms P5J.view_at_head
#print axioms P5J.callNames_of_tie
#print axioms P5J.callsText_of_tie
#print axioms P5J.namesTie24_of_head
