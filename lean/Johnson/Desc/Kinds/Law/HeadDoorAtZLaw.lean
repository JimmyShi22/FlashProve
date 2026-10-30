-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadDoorAtZLaw.lean: what acceptance by the two public tests planK6AtZ Z and
padsAtZ Z (Johnson/Desc/Kinds/HeadDoorAtZ.lean) implies, at the arguments that the composed
soundness statement uses: arr := P5T.arrOf psAll, num := P5T.numOfPlan psAll, N := (P5T.numbersOf
ps1).atBlocks s links bs for any s, links, bs, and ms := P5T.msAt Z lay. Theorems.

What is proved.
  MemsSame Z lay    A NAMED PREMISE, not proved: the shapes and (tree, tenant)s of the typed oracle
          messages ms are, as a set, those of the entries of ps1 with a sample.
  any_mem, all_mem  a list's any and all depend only on which elements it has.
  k6Door_mems, padsDoor_mems   so the two light tests depend on their argument mems only through its
          elements.
  planK6_at_Z       planK6AtZ Z = true, MemsSame Z lay and Meaning.laidThere Z.p.X (sizesOf Z.p.X)
          Z.first.layout = true imply the four clauses named, seats, maskNamed, maskIn of PlanK6
          (Law/K6Cut.lean) at those arguments, with n := num 24 0 and rb := 0.
  named_at_Z        the first two premises imply namedOnce arr N 24 (num 24 0) = true.
  padsFree_at_Z     padsAtZ Z = true, MemsSame Z lay and Meaning.laidThere Z.p.X s' Z.first.layout =
          true imply PadsFree (Johnson/P5J/WordsAtQ.lean) at those arguments.

No existential quantifier in these statements.
Not proved here. MemsSame: the typed oracle messages take their shapes from Johnson.G.sendRowsOf's
rows, the entries of ps1 from Z; a test with code (P5T.membersFault, whose file imports Mathlib)
compares the shapes sending by sending; THAT ITS EMPTY ANSWER IMPLIES MemsSame IS NOT PROVED. At the
full-size stored example both inclusions were evaluated to true, and the two lists are equal in
order. Meaning.laidThere: another entry of the list of public tests implies it. The full size only.
Nothing on soundness.

-/
import Johnson.Desc.Kinds.HeadDoorAtZ
import Johnson.Desc.Kinds.Law.HeadDoorRowsLaw
import Johnson.P5T.MemberLists
import Johnson.Desc.First.NumbersAtBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open OnBytes OnBytes.Road
open OnBytes.Model.Verify (borderOf)
open OnBytes.Params (ReqLayout)
open Cb.Pv.Tail (Size)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (Numbers ModelPart)
open VerifiableInference.Desc.Sound (Mem namedOnce)
open P5J (PadsFree)
open P5T (planSeats planSeatsAll numbersOf arrOf numOfPlan msAt)

/-- **A named premise.** -/
def MemsSame (Z : ProofFile.Pub) (lay : ByteArray) : Prop :=
  ∀ y, y ∈ plainOf (msAt Z lay) ↔ y ∈ memsOf (planSeats Z Z.D.1)

theorem any_mem {α : Type} {l m : List α} (h : ∀ y, y ∈ l ↔ y ∈ m) (p : α → Bool) :
    l.any p = m.any p := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  exact ⟨fun ⟨y, hy, hp⟩ => ⟨y, (h y).1 hy, hp⟩, fun ⟨y, hy, hp⟩ => ⟨y, (h y).2 hy, hp⟩⟩

theorem all_mem {α : Type} {l m : List α} (h : ∀ y, y ∈ l ↔ y ∈ m) (p : α → Bool) :
    l.all p = m.all p := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun k y hy => k y ((h y).2 hy), fun k y hy => k y ((h y).1 hy)⟩

section
variable (cs : OnBytes.Codes) (layout : ReqLayout) (NM NHf ns : ℕ) (labs : ℕ → ℕ)
  (num arr : ℕ → ℕ → ℕ) (group sent0 : List (ℕ × ℕ))
  {m₁ m₂ : List (OnBytes.OracleShape × (ℕ × ℕ))} (h : ∀ y, y ∈ m₁ ↔ y ∈ m₂)
include h

theorem copyV_mems (k : ℕ) (ok : MemV → Bool) :
    copyV (viewPlain cs layout NM NHf ns labs num arr group sent0 m₁) k ok =
      copyV (viewPlain cs layout NM NHf ns labs num arr group sent0 m₂) k ok := by
  unfold copyV viewPlain
  dsimp only
  rw [List.any_map, List.all_map, List.any_map, List.all_map, any_mem h, all_mem h]

theorem matV_mems (o : Option ArrV) :
    matV (viewPlain cs layout NM NHf ns labs num arr group sent0 m₁) o =
      matV (viewPlain cs layout NM NHf ns labs num arr group sent0 m₂) o := by
  cases o with
  | none => rfl
  | some A =>
    show (onceV _ _ && copyV _ _ _) = (onceV _ _ && copyV _ _ _)
    rw [copyV_mems cs layout NM NHf ns labs num arr group sent0 h]
    rfl

/-- The first light test depends on its argument mems only through its elements. -/
theorem k6Door_mems (n rb : ℕ) :
    planK6Door cs layout NM NHf ns labs num arr group sent0 m₁ n rb =
      planK6Door cs layout NM NHf ns labs num arr group sent0 m₂ n rb := by
  unfold planK6Door planK6V
  rw [copyV_mems cs layout NM NHf ns labs num arr group sent0 h]
  simp only [matV_mems cs layout NM NHf ns labs num arr group sent0 h]
  rfl

end

section
variable (cs : OnBytes.Codes) (layout : ReqLayout) (labs : ℕ → ℕ → ℕ) (num arr : ℕ → ℕ → ℕ)
  (group : ℕ → List (ℕ × ℕ)) {m₁ m₂ : List (OnBytes.OracleShape × (ℕ × ℕ))}
  (h : ∀ y, y ∈ m₁ ↔ y ∈ m₂)
include h

theorem padFreeP_mems (k k' a : ℕ) :
    padFreeP cs layout labs num arr group m₁ k k' a =
      padFreeP cs layout labs num arr group m₂ k k' a := by
  unfold padFreeP copyThereP copiesMissP
  simp only [any_mem h, all_mem h]

/-- So does the second. -/
theorem padsDoor_mems (iXI : ℕ) (nas : ℕ → ℕ) (NHf : ℕ) :
    padsDoor cs layout labs num arr group m₁ iXI nas NHf =
      padsDoor cs layout labs num arr group m₂ iXI nas NHf := by
  unfold padsDoor
  simp only [padFreeP_mems cs layout labs num arr group h]

end

variable (Z : ProofFile.Pub) (lay : ByteArray) {St Cl : Type} (s : Params.ReqShape) (links : List ModelPart)
  (bs : List (Block St Cl))

/-- The composed statement's arr, num and N, computed from Z. -/
abbrev arrZ : ℕ → ℕ → ℕ := arrOf (planSeatsAll Z Z.D)
abbrev numZ : ℕ → ℕ → ℕ := numOfPlan (planSeatsAll Z Z.D)
abbrev nZ : Numbers := (numbersOf (planSeats Z Z.D.1)).atBlocks s links bs

/-- The first test at the composed statement's arguments is the test as a function of Z alone. -/
theorem k6Row_at (hm : MemsSame Z lay) :
    planK6Row Z (lettersOf (arrOf (planSeatsAll Z Z.D)) (numOfPlan (planSeatsAll Z Z.D))
      ((numbersOf (planSeats Z Z.D.1)).atBlocks s links bs) (msAt Z lay)) = planK6AtZ Z :=
  k6Door_mems _ _ _ _ _ _ _ _ _ _ hm _ _

theorem padsRow_at (hm : MemsSame Z lay) :
    padsRow Z (lettersOf (arrOf (planSeatsAll Z Z.D)) (numOfPlan (planSeatsAll Z Z.D))
      ((numbersOf (planSeats Z Z.D.1)).atBlocks s links bs) (msAt Z lay)) = padsAtZ Z :=
  padsDoor_mems _ _ _ _ _ _ hm _ _ _

/-- **Acceptance by the first test implies PlanK6's four clauses at those arguments.** -/
theorem planK6_at_Z (h : planK6AtZ Z = true) (hm : MemsSame Z lay)
    (T : Meaning.laidThere Z.p.X (Meaning.sizesOf Z.p.X) Z.first.layout = true) :
    (∀ (μ : Fin (Meaning.sizesOf Z.p.X 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Z.p.X 24).m μ) → c < (Meaning.sizesOf Z.p.X 24).k μ →
      ColFour Z.p.X.hS Z.p.X.HLy (borderOf Z.p.X.y) μ.val c →
      namedOnce (arrZ Z) (nZ Z s links bs) 24
        (seatLay Z.p.X Z.first.layout (numZ Z) 24 μ r c).1 = true) ∧
    (∀ (μ : Fin (Meaning.sizesOf Z.p.X 24).NM) (r c : Nat),
      r < Alg.symRows ((Meaning.sizesOf Z.p.X 24).m μ) → c < (Meaning.sizesOf Z.p.X 24).k μ →
      ColFour Z.p.X.hS Z.p.X.HLy (borderOf Z.p.X.y) μ.val c →
      InCopy Z.first.codes (arrZ Z) (ms0 (msAt Z lay) (nZ Z s links bs)) (msAt Z lay)
        (nZ Z s links bs) 24 (seatLay Z.p.X Z.first.layout (numZ Z) 24 μ r c).1 false
        (seatLay Z.p.X Z.first.layout (numZ Z) 24 μ r c).2.1
        (seatLay Z.p.X Z.first.layout (numZ Z) 24 μ r c).2.2) ∧
    (∀ j, j < Z.p.X.H.ns →
      namedOnce (arrZ Z) (nZ Z s links bs) 24 (plAt (numZ Z 24 0) 0 j).1 = true) ∧
    (∀ j, j < Z.p.X.H.ns →
      InCopy Z.first.codes (arrZ Z) (ms0 (msAt Z lay) (nZ Z s links bs)) (msAt Z lay)
        (nZ Z s links bs) 24 (plAt (numZ Z 24 0) 0 j).1 (plAt (numZ Z 24 0) 0 j).2.1
        (plAt (numZ Z 24 0) 0 j).2.2.1 (plAt (numZ Z 24 0) 0 j).2.2.2) :=
  planK6_of_row Z (arrOf (planSeatsAll Z Z.D)) (numOfPlan (planSeatsAll Z Z.D))
    ((numbersOf (planSeats Z Z.D.1)).atBlocks s links bs) (msAt Z lay)
    ((k6Row_at Z lay s links bs hm).trans h) T

/-- **And that exactly one oracle message of the head's segment has the mask row's message's
number.** -/
theorem named_at_Z (h : planK6AtZ Z = true) (hm : MemsSame Z lay) :
    namedOnce (arrOf (planSeatsAll Z Z.D)) ((numbersOf (planSeats Z Z.D.1)).atBlocks s links bs) 24
      (numOfPlan (planSeatsAll Z Z.D) 24 0) = true :=
  named_of_row Z _ _ _ (msAt Z lay) ((k6Row_at Z lay s links bs hm).trans h)

/-- **Acceptance by the second test implies PadsFree at those arguments.** -/
theorem padsFree_at_Z (s' : ℕ → Size) (h : padsAtZ Z = true) (hm : MemsSame Z lay)
    (T : Meaning.laidThere Z.p.X s' Z.first.layout = true) :
    PadsFree Z.first.codes (arrOf (planSeatsAll Z Z.D)) (msAt Z lay)
      ((numbersOf (planSeats Z Z.D.1)).atBlocks s links bs) s'
      (Meaning.seatBy (Meaning.fLay Z.first.layout (numOfPlan (planSeatsAll Z Z.D))) Z.p.X s')
      Z.p.X :=
  padsFree_of_row Z _ _ _ (msAt Z lay) s' ((padsRow_at Z lay s links bs hm).trans h) T

end VerifiableInference.Desc.Kinds.Head.Law.OffPad

#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.planK6_at_Z
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.named_at_Z
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.padsFree_at_Z
