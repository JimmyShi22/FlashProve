-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Road/K4/K4NamedConst.lean: THE NINE NAMED TESTS OF K4's ROW (the structure K4NamedW,
Johnson/Road/K4/K4RowAtWide.lean) AT THE COMPOSED MEANING's CLOSED CONSTANT, JOINED: in the very
form in which the structure of K4's law's conditions asks them (its field named: at every opening,
at each of the twelve groups, at the lot's member that K4Here names). One structure,
one statement with its proof: A JOIN: no new argument.

  `K4NamedLeft hA L`: WHAT IS LEFT OF THE NINE: FIVE FAMILIES OF TESTS WITH CODE ON PUBLIC DATA,
    none at an opening, none at a member of a lot:
      fence  (one test)  · room1, maskP (twelve each): each is a theorem under named premises, over
             a closed fact at written values, elsewhere (`fence_const`, K4NamedFence.lean;
             `room1_const`, `maskP_const`, K4NamedWritten.lean);
      front, row (twelve each): asked at the public parameters' own layers and at the group's own
             list of numbers. WHY THESE TWO STAY TESTS: they run the listing of K4's forms and the
             routine wsPending on the LAYERS' layout whole (X.layers.y: not the
             request's layout, which is a written value under WrittenAt); the goals' scope leaves
             eight numbers of the parameter file and the whole scale file free, so that layout is
             no written value; no law says yet that the two returns read the sizes alone.
             (In this tree the head (a member of the head is proved at `storedPublicFiles` and `zGap` alone (at
             secondHashFunction; side library AtFullSide/Top/)) gives both:
             `k4Row_of_head`, Johnson/Road/K4/K4RowOfHead.lean, with `k4Row_two`,
             Johnson/Road/K4/K4RowTestLaws.lean.)
  **`named_of_left`**: hA · K4NamedLeft hA L ⟹ K4NamedW at the constant, at every opening, g < 12,
    x, b under K4Here. PAID INSIDE, WITH NO TEST AND NO WRITTEN VALUE: toldFit, book
    (Johnson/Road/K4/K4NamedFirst.lean) · lookIn (lookIn_public,
    Johnson/Road/K4/Riders/LookInByMake.lean) · readsP (readsP_public,
    Johnson/Road/K4/Rec/ReadsByMake.lean).
  WHAT LEAN HOLDS HERE THAT WAS HELD BY READING: K4Here's equations stand at the opening's Bs.G₀.W;
  the constant's index is the public part's own public parameters: one by the opening's law W; the
  constant's letters sent.shape, sent.layout, sent.arrayOf and pubD.dS.trees are the terms at which
  readsP_public ends.
Limits. K4NamedLeft IS A PREMISE: SHOWN TO HOLD NOWHERE BY LEAN. EVALUATED (in two files of
evaluations, not named here; ONE set: the shipped full-size one; true, each with a negative test
that rejects): all five families, front and row in the very form in which they stand here. A MEMBER
OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/). L is a
letter. The full size alone. K04_law, the law of K4's
sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.K4NamedFirst
import Johnson.Road.K4.Riders.LookInByMake
import Johnson.Road.K4.Rec.ReadsByMake
import Johnson.Road.K4.K4RowAtWide
import Johnson.Road.K4.K4EAll
import Johnson.Goal.Meaning.PlanShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open OnBytes.Desc.First.K4.Total (rowB frontB)
open OnBytes.Road.K4.Riders (lookIn_public)
open OnBytes.Road.K4.Rec (readsP_public)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S flatPlacesOf fenceFit)
open VerifiableInference.Desc.First.RecordPlan (maskSeatP)
open VerifiableInference.Desc.Sound (linksFull)
open Johnson.Desc.First.Walk.Tied (rowsBefore)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **What is left of the nine named tests at the constant.** SHOWN TO HOLD NOWHERE BY LEAN. -/
structure K4NamedLeft (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (L : VerifiableInference.Desc.K12.Door.Laid) : Prop where
  fence : fenceFit hA.𝔇.N linksFull (flatPlacesOf linksFull true) = true
  room1 : ∀ g, g < 12 →
    1 ≤ (eAll Zp cF L).dP.free0 - rowsBefore (eAll Zp cF L).dP.fvs (2 * g)
  maskP : ∀ g, g < 12 →
    (maskSeatP hA.𝔇.sent.shape hA.𝔇.pubD.dS (hA.𝔇.N.sent (2 * g) 0) (eAll Zp cF L).d12.L.places
      (hA.𝔇.N.msgsAt (flatPlacesOf linksFull true)[28 * g + 4]?) (2 * g)).isSome = true
  front : ∀ g, g < 12 → ∀ hp, (P5J.At.X Zp).G[g]? = some hp →
    frontB false (P5J.At.X Zp).layers hp g (P5J.At.X Zp).layers.y.fo = true
  row : ∀ g, g < 12 → ∀ hp, (P5J.At.X Zp).G[g]? = some hp →
    rowB (P5J.At.X Zp).layers g hp.NCL hA.𝔇.d1.lin = true

/-- **UNDER hA AND K4NamedLeft (PREMISES; SHOWN TO HOLD NOWHERE): the nine at the constant, in the
form in which K4's law's conditions ask them.** -/
theorem named_of_left (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {L : VerifiableInference.Desc.K12.Door.Laid} (R : K4NamedLeft hA L) :
    ∀ {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)},
    IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (Desc.K14.Law.seatZ Zp Np) (Desc.K14.Law.secondAt Zp Np) →
    ∀ g, g < 12 → ∀ x b, K4Here cF Zp Bs.G₀ g x b →
      K4NamedW hA.𝔇 (eAll Zp cF L) (28 * g + 4) (2 * g) (parOf x)
      (cF.blocksInOrder.map fun b => b.oracles.flatMap id)
        (Forest.elems (P5J.At.X Zp).y.fo) := by
  intro Bs base O g hg x b h
  obtain ⟨k4, kN, _, hAtt⟩ := Meaning.scope_plans hA.scope hA.reads hA.pubOne
  obtain ⟨a, ha, _⟩ := hAtt g hg
  have e1 : (parOf x).P = { (P5J.At.X Zp).layers with tokv := (P5J.At.X Zp).layers.tokv } := by
    rw [h.P, O.W]
    rfl
  have e1' : (parOf x).P = (P5J.At.X Zp).layers := e1
  have e2 : (parOf x).g = g := h.hg
  have e3 : (P5J.At.X Zp).G[g]? = some (parOf x).hp := by
    have t := h.G
    rw [O.W, e2] at t
    exact t
  exact
    { toldFit := toldFit_const hA O
      book := book_const hA
      fence := R.fence
      room1 := R.room1 g hg
      front := by
        rw [e1', e2]
        exact R.front g hg _ e3
      row := by
        rw [e1', e2]
        exact R.row g hg _ e3
      lookIn := lookIn_public hA.pubOne k4 (by rw [kN]; exact hg) e1 e2 e3
      maskP := R.maskP g hg
      readsP := readsP_public hA.pubOne O.pub k4 e3 ha }

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.named_of_left
set_option pp.deepTerms true in
set_option pp.maxSteps 1000000 in
#check @OnBytes.Road.K4.named_of_left
