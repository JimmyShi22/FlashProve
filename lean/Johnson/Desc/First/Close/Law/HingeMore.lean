-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/HingeMore.lean (kind K10): THREE SMALL PIECES AROUND `ShapesAre` AT THE
PLAN's NUMBERING `noK10`. Theorems; three evaluations in Lean's kernel with two negative lines.
  (1) THE NUMBERING PARTS THE LIST's MEMBERS. `noApartB_full`: at every l < 26 the numbers of all
    places of the written list are different. `noApartB_empty`: THE NEGATIVE LINE: at the empty list
    of seats link 0's are not. `no_inj_full`, `hinj_full`: **`noK10` is injective; so the premise
    hinj of NamesOfShapes.lean's `namesFit_of_shapes`, to the letter.** `noFive_inj`, `hinj_five`:
    the like at the five-list (FiveAtFull.lean).
  (2) THE HEAD's LINK. `t3HeadB`: **the public list of the head's link's group's members
    (`membersPubHead`, MembersPublicHead.lean) is the plan's numbering of the written list's members
    at l = 24.** `t3HeadB_told`: THE NEGATIVE LINE: with the first 340 tellings dropped it is not.
    `t3_head`, `t3_head_at_cut`: the equation at any numbers beneath; and where the first chain's
    cut is the written one.
  (3) "THE CUT IS THE WRITTEN ONE", WHERE THE VALUE IS LAID. `hc_at_laid`: in the goals' scope,
    where the verifier's own value is laid (`P5J.LaidAt`): `cutOf cF.blocksInOrder = cutFirstFull`:
    `cuts_of_laid` (Johnson/Goal/Skeleton/CutIsOfLaid.lean) at the chain's own letter.
    `t3_at_laid`, `t3_head_at_laid`: **so the two equations at `toldOf cF.blocksInOrder`, from the scope and
    "the value is laid" alone.**
Limits. Link 0's like of (2) is not here. THE WRITTEN CUT RESTS ON PRINTS OF LEAN's EVALUATOR;
`cuts_of_laid` draws "the cut is the written one" from an accept of the verifier's entry test: it
moves the premise into the head, it does not show that the head can be met. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.FiveAtFull
import Johnson.Desc.First.Close.Law.MembersPublicHead
import Johnson.Goal.Skeleton.CutIsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close
open OnBytes
open OnBytes.Maker (WholeD)
open Johnson.G (linksFullLit)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.ReqLit (shapeFull)

/-! ## 1 The numbering parts the list's members -/

set_option maxRecDepth 1000000 in
/-- **(W) At every written list the places' numbers are all different.** -/
theorem noApartB_full :
    ((List.range 26).all fun l => decide (((List.finRange (linksFullLit.getD l []).length).map
      (noK10 seatsPlanW (linksFullLit.getD l []) P5T.psFull l)).Nodup)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **(N)** At the empty list of seats link 0's numbers are not all different. -/
theorem noApartB_empty :
    decide (((List.finRange (linksFullLit.getD 0 []).length).map
      (noK10 [] (linksFullLit.getD 0 []) P5T.psFull 0)).Nodup) = false := by decide +kernel

theorem no_inj_full (l : ℕ) (hl : l < 26) :
    Function.Injective (noK10 seatsPlanW (linksFullLit.getD l []) P5T.psFull l) := fun i j e =>
  List.inj_on_of_nodup_map
    (of_decide_eq_true (List.all_eq_true.1 noApartB_full l (List.mem_range.2 hl)))
    (List.mem_finRange i) (List.mem_finRange j) e

/-- **hinj AT `noK10`.** -/
theorem hinj_full (l : ℕ) (hl : l < 26) :
    ∀ i ∈ membersOf (linksFullLit.getD l []), ∀ j ∈ membersOf (linksFullLit.getD l []),
      noK10 seatsPlanW (linksFullLit.getD l []) P5T.psFull l i =
        noK10 seatsPlanW (linksFullLit.getD l []) P5T.psFull l j → i = j :=
  fun _ _ _ _ e => no_inj_full l hl e

theorem noFive_inj : Function.Injective noFive := fun i j e =>
  List.inj_on_of_nodup_map (by rw [noFive_is]; decide) (List.mem_finRange i)
    (List.mem_finRange j) e

theorem hinj_five : ∀ i ∈ membersOf loFive, ∀ j ∈ membersOf loFive, noFive i = noFive j → i = j :=
  fun _ _ _ _ e => noFive_inj e

/-! ## 2 The head's link -/

theorem membersPubHead_free (N₀ N₁ : Numbers) (ps : List Place) (told : List (List Oracle))
    (sh : Params.ReqShape) :
    membersPubHead (N₀.withTold ps told) sh = membersPubHead (N₁.withTold ps told) sh := rfl

set_option maxRecDepth 1000000 in
/-- **(W) The two lists are one at the head's link.** -/
theorem t3HeadB :
    decide (membersPubHead (P5T.N0Full.withTold IM.placesW toldCut) shapeFull =
      (membersOf (linksFullLit.getD 24 [])).map
        (noK10 seatsPlanW (linksFullLit.getD 24 []) P5T.psFull 24)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **(N)** With the first 340 tellings dropped they differ. -/
theorem t3HeadB_told :
    decide (membersPubHead (P5T.N0Full.withTold IM.placesW (toldCut.drop 340)) shapeFull =
      (membersOf (linksFullLit.getD 24 [])).map
        (noK10 seatsPlanW (linksFullLit.getD 24 []) P5T.psFull 24)) = false := by
  decide +kernel

theorem t3_head (N₀ : Numbers) :
    membersPubHead (N₀.withTold IM.placesW toldCut) shapeFull =
      (membersOf (linksFullLit.getD 24 [])).map
        (noK10 seatsPlanW (linksFullLit.getD 24 []) P5T.psFull 24) := by
  rw [membersPubHead_free N₀ P5T.N0Full]
  exact of_decide_eq_true t3HeadB

theorem t3_head_at_cut {St Cl : Type} {bs : List (Block St Cl)}
    (hc : VerifiableInference.PlanWritten.cutOf bs = VerifiableInference.PlanWritten.cutFirstFull)
    (N₀ : Numbers) :
    membersPubHead (N₀.withTold IM.placesW (toldOf bs)) shapeFull =
      (membersOf (linksFullLit.getD 24 [])).map
        (noK10 seatsPlanW (linksFullLit.getD 24 []) P5T.psFull 24) := by
  rw [(told_at_written hc).2]
  exact t3_head N₀

/-! ## 3 Where the value is laid -/

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- **The first chain's cut is the written one, at the chain's own letter.** -/
theorem hc_at_laid (hZ : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) :
    VerifiableInference.PlanWritten.cutOf cF.blocksInOrder =
      VerifiableInference.PlanWritten.cutFirstFull := (P5J.cuts_of_laid hZ L).1

theorem t3_at_laid (hZ : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) (N₀ : Numbers) (l : ℕ) (h1 : 1 ≤ l)
    (h24 : l < 24) :
    membersPub (N₀.withTold IM.placesW (toldOf cF.blocksInOrder)) shapeFull l =
      (membersOf (linksFullLit.getD l [])).map
        (noK10 seatsPlanW (linksFullLit.getD l []) P5T.psFull l) :=
  t3_at_cut (hc_at_laid hZ L) N₀ l h1 h24

theorem t3_head_at_laid (hZ : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) (N₀ : Numbers) :
    membersPubHead (N₀.withTold IM.placesW (toldOf cF.blocksInOrder)) shapeFull =
      (membersOf (linksFullLit.getD 24 [])).map
        (noK10 seatsPlanW (linksFullLit.getD 24 []) P5T.psFull 24) :=
  t3_head_at_cut (hc_at_laid hZ L) N₀

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.noApartB_full
#print axioms VerifiableInference.Desc.First.Close.noApartB_empty
#print axioms VerifiableInference.Desc.First.Close.no_inj_full
#print axioms VerifiableInference.Desc.First.Close.hinj_full
#print axioms VerifiableInference.Desc.First.Close.noFive_inj
#print axioms VerifiableInference.Desc.First.Close.hinj_five
#print axioms VerifiableInference.Desc.First.Close.membersPubHead_free
#print axioms VerifiableInference.Desc.First.Close.t3HeadB
#print axioms VerifiableInference.Desc.First.Close.t3HeadB_told
#print axioms VerifiableInference.Desc.First.Close.t3_head
#print axioms VerifiableInference.Desc.First.Close.t3_head_at_cut
#print axioms VerifiableInference.Desc.First.Close.hc_at_laid
#print axioms VerifiableInference.Desc.First.Close.t3_at_laid
#print axioms VerifiableInference.Desc.First.Close.t3_head_at_laid
