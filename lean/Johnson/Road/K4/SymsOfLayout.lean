-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SymsOfLayout.lean: `SymsOne` (Johnson/Road/K4/K4PinsSym.lean), "THE TWO READINGS OF
THE COMMITTED SYMBOLS ARE ONE", FROM TESTS AN ARRAY AT A TIME. At the full size a layers' link has
485,035,896 symbols in nine matrices: a test that walks them cannot run. Here `SymsOne` follows, at
the seats that the model's owner makes off the layout (`seatBy (fLay layout num) X s`,
Johnson/Goal/Meaning/HidSeatsOf.lean), from one test a matrix. Two definitions with code and two
theorems. Glue: calls; no draw, no count.

  `tenantB`: the array of a link and a name is there, the caller's list has a member for its
    message, and the tenant of segment k's group with that message's number is seatT of that member:
    `SymsOne`'s last clause, A MESSAGE AT A TIME. NEW.
  `symTieB`: at matrix μ: the lookup's files' own test `symArrB`
    (Johnson/Desc/First/Look/K3CallerAttReads.lean: the array is there, its message stands in the
    caller's list, its blocks tile the matrix and lie in the message's table) · the caller's list of
    arrays names, at the matrix's tree, THE OWNER AND THE NAME THAT THE LABEL NAMES (the first
    conjunct of `entryTieB`, Johnson/Goal/Meaning/ReadingsOne.lean) · `tenantB` there.
  `tenant_of_B`: what a yes of `tenantB` gives.
  `symsOne_of_layout`: `SymsOne A tl arr N k (s k) (seatBy (fLay layout num) X s k)`.

ELDER: `Meaning.seat_of_tie` (ReadingsOne.lean) has the first five clauses from the test
`linkTieB`, with the member's number written as idx of the message's number, idx a letter of each
link; it has ONE letter k for the link, the label and the sizes (`szOf tl`), where this file, as
`SymsOne` itself, has k, A.link, tl and s k apart. `SymsOne` has no idx and asks the tenant besides:
so the walk is made here anew, over the same lemmas, without idx.

CALLED: `laidPlace_some` (Johnson/Desc/First/Look/K3CallerLaid.lean) · `Meaning.laidPlace_eq_laidAt`
(ReadingsOne.lean: two texts of one function) · `symArr_data`, `seatCalls_of`
(Johnson/Road/K4/K4PinsArr.lean, this folder's: what a yes of the test hands out).

PREMISES. hlay: the caller's layout is the layout. hB: `symTieB` at every matrix of sub-proof k's
list: nine questions at a layers' link. NOTHING ELSE: no test on the other lists.

Limits. K04_law IS NOT PROVED BY THIS. NO TEST HAS RUN AT A PLAN HERE. k AND A.link CAN PART IN THE
STATEMENT, as in `SymsOne` itself; nothing is shown of that case (by a reading,
in the goals' scope, the second conjunct of `symTieB` then fails at every array that is the link's
own, so that the theorem is idle there). tl enters by its list of trees alone; that its sizes are
s k is the caller's. The seats are `seatBy (fLay layout num) X s`.
-/
import Johnson.Road.K4.K4PinsArr
import Johnson.Goal.Meaning.ReadingsOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes
open OnBytes.Model (HTailF2)
open OnBytes.Params (ReqLayout ReqArray)
open VerifiableInference.Desc (arrayOf laidAt seatIn)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (sigListCalls laidPlace laidPlace_some symArrB msgIn)
open Meaning (seatBy fLay labAt ownerK ownerA nameOf)
open Cb.Pv.Tail (Size)

section
variable {Cells : Type} (A : PinPlan Cells) (num arr : ℕ → ℕ → ℕ) (N : Numbers) (k : ℕ)

/-- The array of link l and a name is there, the caller's list has a member for its message, and the
tenant of segment k's group with that message's number is seatT of that member. -/
def tenantB (l : ℕ) (name : String) : Bool :=
  match OnBytes.reqArray A.D.layout l name with
  | some a =>
    match msgIn A.D A.link l a.message with
    | some j =>
      if hj : j < (sigListCalls A.D A.rad A.link).length then
        decide (((N.group k).find? fun x => arr x.1 x.2 == num l a.message) =
          some (A.seatT ⟨j, hj⟩))
      else false
    | none => false
  | none => false

/-- What a yes gives. -/
theorem tenant_of_B {l : ℕ} {name : String} (h : tenantB A num arr N k l name = true)
    {a : ReqArray} {j : ℕ} (ha : OnBytes.reqArray A.D.layout l name = some a)
    (hm : msgIn A.D A.link l a.message = some j)
    (hj : j < (sigListCalls A.D A.rad A.link).length) :
    ((N.group k).find? fun x => arr x.1 x.2 == num l a.message) = some (A.seatT ⟨j, hj⟩) := by
  unfold tenantB at h
  split at h
  · rename_i a' ha'
    obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
    split at h
    · rename_i j' hm'
      obtain rfl : j' = j := Option.some.inj (hm'.symm.trans hm)
      rw [dif_pos hj] at h
      exact of_decide_eq_true h
    · cases h
  · cases h

/-- **The test at one matrix.** -/
def symTieB (tl : HTailF2) (X : Model.Verify.Public) (s : ℕ → Size) (μ : ℕ) : Bool :=
  symArrB A.D (sigListCalls A.D A.rad A.link) A.link (tl.gtTree.getD μ 0)
      (Alg.symRows ((s k).m μ)) ((s k).k μ) &&
    decide ((A.D.arrayOf.getD A.link #[])[tl.gtTree.getD μ 0]? =
      some (ownerK (labAt X k μ), nameOf (ownerA (labAt X k μ)))) &&
    tenantB A num arr N k (ownerK (labAt X k μ)) (nameOf (ownerA (labAt X k μ)))

/-- **The two readings of the committed symbols are one, from one test a matrix.** -/
theorem symsOne_of_layout (tl : HTailF2) {X : Model.Verify.Public} {s : ℕ → Size}
    {layout : ReqLayout} (hlay : A.D.layout = layout)
    (hB : ∀ μ < (s k).NM, symTieB A num arr N k tl X s μ = true) :
    SymsOne A tl arr N k (s k) (seatBy (fLay layout num) X s k) := by
  intro μ r c
  have h := hB μ.val μ.isLt
  unfold symTieB at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have h2' := of_decide_eq_true h2
  obtain ⟨bn, a, j, hj, hbn, ha, hm, hb⟩ := symArr_data h1
  obtain rfl : bn = (ownerK (labAt X k μ.val), nameOf (ownerA (labAt X k μ.val))) :=
    Option.some.inj (hbn.symm.trans h2')
  obtain ⟨rp, e1, e2, e3⟩ := laidPlace_some hb r.isLt c.isLt
  have ha' : arrayOf layout (ownerK (labAt X k μ.val)) (nameOf (ownerA (labAt X k μ.val))) =
      some a := by
    rw [← hlay]
    exact ha
  have hx : laidAt a r.val c.val = some rp :=
    (Meaning.laidPlace_eq_laidAt a r.val c.val).symm.trans e1
  have es : seatBy (fLay layout num) X s k μ r.val c.val =
      (num (ownerK (labAt X k μ.val)) a.message, rp.1, rp.2) := by
    unfold seatBy fLay seatIn
    rw [ha']
    simp [hx]
  refine ⟨⟨j, false, rp.1, rp.2⟩, hj, seatCalls_of hbn ha hm e1, rfl, e2, e3, ?_, ?_⟩
  · rw [es]
  · rw [es]
    exact tenant_of_B A num arr N k h3 ha hm hj

end

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.tenant_of_B
#print axioms OnBytes.Road.K4.symsOne_of_layout
