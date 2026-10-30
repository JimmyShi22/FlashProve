-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/OptsTlArm.lean: two of the seven tests `At.OptsOk` of the head's law, `At.tlB Zp`
and `At.armB Zp` (Johnson/P5J/OptsOk.lean): the public data have an approximate range proof's plan
at every segment of layers, and an attention plan at every segment of attention. They accept
wherever the value is laid in scope and the test that holds the made plan to the written one
accepts.

Row or tool. One closed fact with its negative test, general laws, and two laws in scope by
rewriting through named ties. Payers for premises of another law.

The two tests' texts. The file that defines them is not imported by name. They stand here
spelled out, sign for sign: `tlText Zp`, `armText Zp`. That these are `At.tlB Zp` and `At.armB Zp`
is two equations by definition: `tlB_is`, `armB_is` (Johnson/Goal/Skeleton/CondsOfLaid.lean).

(Where this and lean/THEOREM.md differ, the page holds.)

What they read, the written term and the ties. Both read `At.X Zp`, the public data. The view of
their shape (`xShapeOf`) has, for each of the 25 segments, what `First.Look.tlAt` answers there.
Written term: `xShapeFull` (Johnson/G/XShapeLit.lean). Tie: `xShape_in_scope`
(Johnson/Goal/Numbers/MadeInScope.lean). At a segment of attention that reader answers just where
the list of attention plans does, where attention is there and there are twelve groups:
`publicO_at_scope` (Johnson/Desc/K12/Law/Sizes/PublicOAtScope.lean) at `LaidAt.publicO`.

The premise beyond scope, the files read, and the value laid. One: `madePinnedAt … = true`.

What is here.
  `view_some`: each of the 25 entries of `xShapeFull` is there. `view_rejects`: the negative test:
    with the first entry struck, not each is.
  `tl_some`: so, where the view is the written one, `First.Look.tlAt X l` answers at every l below
    25.
  `tlAt_odd`: at an odd l, under the two conditions, it is the attention plan's.
  `segs_written`: the segments of layers are below 25; those of attention are odd and below 24;
    there are twelve of each: neither test is idle.
  `tlB_at_name`, `armB_at_name`.
By evaluations in Lean's kernel (`decide +kernel`): `view_some`, `view_rejects`, `segs_written`.

Limits. Nothing in this file says that `madePinnedAt` accepts at any files. Nothing on soundness.


-/
import Johnson.P5J.LettersAt
import Johnson.P5J.LaidOpens
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Desc.K12.Law.Sizes.PublicOAtScope
import Johnson.G.XShapeLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes OnBytes.Model Johnson.G
open VerifiableInference.Desc.First (ModelPart)
open VerifiableInference.PlanWritten (madePinnedAt xShapeOf tailView)
open VerifiableInference.PlanWritten.Joined (xShape_in_scope)

/-- The text of `At.tlB`. -/
def tlText (Zp : ProofFile.Pub) : Bool :=
  ((List.range At.links.length).filter fun l => At.links[l]? == some ModelPart.layers).all fun l =>
    (VerifiableInference.Desc.First.Look.tlAt (At.X Zp) l).isSome

/-- The text of `At.armB`. -/
def armText (Zp : ProofFile.Pub) : Bool :=
  ((List.range At.links.length).filter fun l => At.links[l]? == some ModelPart.attention).all fun l =>
    ((At.X Zp).A[l / 2]?).isSome

set_option maxRecDepth 1000000 in
/-- **Each of the 25 entries of the written view is there.** -/
theorem view_some :
    ((List.range 25).all fun l => ((xShapeFull.1[l]?).getD none).isSome) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: with the first entry struck. -/
theorem view_rejects :
    ((List.range 25).all fun l => (((xShapeFull.1.set 0 none)[l]?).getD none).isSome) = false := by
  decide +kernel

/-- Where the view is the written one, the reader answers at every segment. -/
theorem tl_some {X : Verify.Public} (hx : xShapeOf X = xShapeFull) {l : ℕ} (hl : l < 25) :
    (VerifiableInference.Desc.First.Look.tlAt X l).isSome = true := by
  have e : (xShapeOf X).1[l]? =
      some ((VerifiableInference.Desc.First.Look.tlAt X l).map tailView) := by
    unfold xShapeOf
    simp only [List.getElem?_map, List.getElem?_range hl, Option.map_some]
  have c := List.all_eq_true.1 view_some l (List.mem_range.2 hl)
  rw [← hx, e, Option.getD_some, Option.isSome_map] at c
  exact c

/-- At an odd segment the reader is the attention plan's. -/
theorem tlAt_odd {X : Verify.Public} (h4 : X.p4 = true) (hN : X.NGr = 12) {l : ℕ}
    (ho : l % 2 = 1) :
    VerifiableInference.Desc.First.Look.tlAt X l = X.A[l / 2]?.map (·.seam.tl) := by
  unfold VerifiableInference.Desc.First.Look.tlAt
  have e1 : (l == 2 * 12) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  have e2 : (l % 2 == 0) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  simp only [h4, hN, if_true, e1, e2, Bool.false_eq_true, if_false]

set_option maxRecDepth 1000000 in
/-- Where the segments of the two sorts stand; twelve of each. -/
theorem segs_written :
    (((List.range At.links.length).filter fun l => At.links[l]? == some ModelPart.layers).all
        fun l => decide (l < 25)) = true ∧
      (((List.range At.links.length).filter fun l => At.links[l]? == some ModelPart.attention).all
        fun l => decide (l % 2 = 1) && decide (l < 24)) = true ∧
      ((List.range At.links.length).filter fun l => At.links[l]? == some ModelPart.layers).length = 12 ∧
      ((List.range At.links.length).filter fun l => At.links[l]? == some ModelPart.attention).length =
        12 := by decide +kernel

section
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}

/-- **`At.tlB`'s text at the closed letters of the head's law.** -/
theorem tlB_at_name (hZ : VerifierAndGoals.InScope Z = true) (_ : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) : tlText Zp = true := by
  unfold tlText
  refine List.all_eq_true.2 fun l hl => ?_
  exact tl_some (xShape_in_scope hZ L.pub hy)
    (of_decide_eq_true (List.all_eq_true.1 segs_written.1 l hl))

/-- **`At.armB`'s text at the closed letters of the head's law.** -/
theorem armB_at_name (hZ : VerifierAndGoals.InScope Z = true) (_ : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    armText Zp = true := by
  have hF := H2K.Sizes.publicO_at_scope hZ L.publicO
  unfold armText
  refine List.all_eq_true.2 fun l hl => ?_
  have c := List.all_eq_true.1 segs_written.2.1 l hl
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at c
  have t := tl_some (xShape_in_scope hZ L.pub hy) (l := l) (by omega)
  rw [tlAt_odd hF.p4 hF.groups c.1, Option.isSome_map] at t
  exact t

end

end P5J

#print axioms P5J.view_some
#print axioms P5J.view_rejects
#print axioms P5J.tl_some
#print axioms P5J.tlAt_odd
#print axioms P5J.segs_written
#print axioms P5J.tlB_at_name
#print axioms P5J.armB_at_name
