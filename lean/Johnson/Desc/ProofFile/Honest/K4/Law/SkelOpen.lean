-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SkelOpen.lean: CONDITIONAL: on two claims that are alike.

What is here. A CONGRUENCE: THE TABLE OF ONE WEIGHT CLAIM (`fbFree`,
Johnson/Desc/K4/Honest/Units.lean; `openOf`, Johnson/Desc/K4/Honest/Sides.lean) at two claims that
are alike (the library's `ClaimAlike`, OnBytes/Flat/LinksFreeLayer.lean: one unit; factors of the
same sizes) AND AT ANY TWO MATRICES OF WEIGHTS: both tables are missing, or neither is. A
definition, and statements with their proofs.

  `ZipAlike`   two pairs of a factor and a group: factors of the same sizes, one group.
  `size_foldOuterBy`, `foldl_zip_eq`   two folds over lists that go together member by member.
  `rowWeights_size`, `rowNumbers_alike`, `fits_all`   what the tests of `fbFree` read.
  `ite_none_some`   a test in front of a value, at two tests of one value.
  **`fbFree_rel`**, **`openOf_rel`**   the two laws.

Debts and ends. `ZipAlike` IS AN END, SPENT IN THIS FILE: NO DEBT: five lemmas here take it;
`fbFree_rel` has it from `ClaimAlike` (by the library's `All2.zipRight`); no statement of another
file of its writers names it. THE TWO HEAD LAWS ASK `ClaimAlike` ALONE (`openOf_rel` is called from
another file; `fbFree_rel` by it alone); THE TWO MATRICES w AND w₀, WHICH HOLD THE COMMITTED
WEIGHTS' DIGITS, ARE FREE LETTERS: whether a table is there hangs on none of their entries.
`ClaimAlike` is paid where the verifier's list of weight claims is made at two environments of one
skeleton: the library's `weightClaims_rel`, called in `sidesOf_rel` (Law/SkelSides.lean).

Not shown here. NEITHER FUNCTION IS SHOWN TO RETURN ANYWHERE: two calls are compared. Nothing on
what an entry of a table is worth, nor on a table's size.

Kin. No twin is known to its writers. `size_foldOuterBy` is of one make with the library's
`size_foldOuter` (OnBytes/Flat/PendingSizes.lean): the same fold and end, there over row factors and
with each factor's own table, here with one table for each member, a letter; `rowWeights_size`
stands beside that file's `size_wsGamma`. `ite_none_some` stands beside the library's `ite_isSome`
(Johnson/Desc/First/K4/Returns/Pub/Kit.lean): one condition, two pairs. Laws of the short name
fits_all, on other matters, stand in Honest/Law/Rule/Bridge.lean, Honest/K12/FitsAll.lean,
Johnson/Top/H/KeyGp.lean, OnBytes/TypedOracleCompiler/Run/PageXAgree.lean and Run/CodingAgreeX.lean.
No property is claimed.
-/
import Johnson.Desc.First.K4.Returns.Pub.Claims
import Johnson.Desc.K4.Honest.Sides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E F zeroE)
open OnBytes.Model (WsLay WsUnit WsGrp WsFac WsClaim wsOuter)
open OnBytes.Flat (All2 OptRel FacAlike ClaimAlike optRel_bind optRel_bind_same fits_alike
  all_alike onRows_alike size_wsOuter size_table)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.RtPub

/-- Two pairs of a factor and a group: factors of the same sizes, one group. -/
def ZipAlike (y y' : WsFac × WsGrp) : Prop := FacAlike y.1 y'.1 ∧ y.2 = y'.2

/-- The products with one table for each member: the sizes go together. -/
theorem size_foldOuterBy {T T' : WsFac × WsGrp → Array E}
    (hT : ∀ y y', ZipAlike y y' → (T y).size = (T' y').size) {l l' : List (WsFac × WsGrp)}
    (h : All2 ZipAlike l l') : ∀ v v' : Array E, v.size = v'.size →
      (l.foldl (fun v y => wsOuter v (T y)) v).size =
        (l'.foldl (fun v y => wsOuter v (T' y)) v').size := by
  induction h with
  | nil => exact fun _ _ e => e
  | cons h0 _ ih =>
    intro v v' e
    rw [List.foldl_cons, List.foldl_cons]
    refine ih _ _ ?_
    rw [size_wsOuter, size_wsOuter, e, hT _ _ h0]

/-- A fold whose step gives one value at two pairs that are alike. -/
theorem foldl_zip_eq {σ : Type} {f : σ → WsFac × WsGrp → σ}
    (hf : ∀ v y y', ZipAlike y y' → f v y = f v y') {l l' : List (WsFac × WsGrp)}
    (h : All2 ZipAlike l l') : ∀ v : σ, l.foldl f v = l'.foldl f v := by
  induction h with
  | nil => exact fun _ => rfl
  | cons h0 _ ih =>
    intro v
    rw [List.foldl_cons, List.foldl_cons, hf _ _ _ h0]
    exact ih _

/-- The rows' weights are as many. -/
theorem rowWeights_size (u : WsUnit) (st : List (String × Nat)) {l l' : List (WsFac × WsGrp)}
    (h : All2 ZipAlike l l') : (rowWeights u l st).size = (rowWeights u l' st).size := by
  unfold rowWeights
  refine size_foldOuterBy (fun y y' hy => ?_) h.reverse _ _ rfl
  obtain ⟨x, g⟩ := y
  obtain ⟨x', g'⟩ := y'
  obtain ⟨h1, h2⟩ := hy
  have h2' : g = g' := h2
  subst h2'
  have h1' : FacAlike x x' := h1
  show (match strideOf st g with
      | none => (x.onRows g).table g
      | some _ => Array.replicate g.left OnBytes.oneE).size =
    (match strideOf st g with
      | none => (x'.onRows g).table g
      | some _ => Array.replicate g.left OnBytes.oneE).size
  cases strideOf st g with
  | none => exact size_table (onRows_alike h1' g) g
  | some _ => rfl

/-- What each row adds to an entry's number reads no factor. -/
theorem rowNumbers_alike (u : WsUnit) (st : List (String × Nat)) {l l' : List (WsFac × WsGrp)}
    (h : All2 ZipAlike l l') : rowNumbers u l st = rowNumbers u l' st := by
  unfold rowNumbers
  refine foldl_zip_eq (fun v y y' hy => ?_) h.reverse _
  rw [hy.2]

/-- The test on the closed factors' sizes. -/
theorem fits_all (st : List (String × Nat)) {l l' : List (WsFac × WsGrp)}
    (h : All2 ZipAlike l l') :
    (l.all fun y => (strideOf st y.2).isSome || y.1.fits y.2) =
      (l'.all fun y => (strideOf st y.2).isSome || y.1.fits y.2) :=
  all_alike (fun y y' hy => by rw [hy.2, fits_alike hy.1]) h

/-- A test in front of a value, at two tests of one value. -/
theorem ite_none_some {α β : Type} {b b' : Bool} (e : b = b') (x : α) (y : β) :
    (if b = true then none else some x).isSome = (if b' = true then none else some y).isSome := by
  subst e
  cases b <;> rfl

/-- **The unit's weights under a claim's factors**, at two claims that are alike and two matrices:
both are missing, or neither is. -/
theorem fbFree_rel (lay : WsLay) (w w₀ : Nat → Nat → F) {c c₀ : WsClaim} (h : ClaimAlike c c₀)
    (free : List String) : (fbFree lay w c free).isSome = (fbFree lay w₀ c₀ free).isSome := by
  unfold fbFree
  rw [h.1]
  cases lay.U[c₀.ui]? with
  | none => rfl
  | some u =>
    have hz : All2 ZipAlike (c.f.zip u.g) (c₀.f.zip u.g) := h.2.zipRight u.g
    dsimp only
    refine ite_none_some ?_ _ _
    rw [h.2.length, rowWeights_size u _ hz, rowNumbers_alike u _ hz, fits_all _ hz]

/-- **The table of one claim**, at two claims that are alike and two matrices. -/
theorem openOf_rel (lay : WsLay) (w w₀ : Nat → Nat → F) (g0 : Nat) {c c₀ : WsClaim}
    (h : ClaimAlike c c₀) :
    OptRel (fun _ _ => True) (openOf lay w g0 c) (openOf lay w₀ g0 c₀) := by
  unfold openOf
  dsimp only
  rw [h.1]
  refine optRel_bind_same fun _ => ?_
  refine optRel_ite trivial (optRel_bind_same fun _ => ?_)
  exact optRel_bind (optRel_of_isSome (fbFree_rel lay w w₀ h _)) fun _ _ _ => trivial

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.ZipAlike
#print axioms ProofFile.Honest.K4.size_foldOuterBy
#print axioms ProofFile.Honest.K4.foldl_zip_eq
#print axioms ProofFile.Honest.K4.rowWeights_size
#print axioms ProofFile.Honest.K4.rowNumbers_alike
#print axioms ProofFile.Honest.K4.fits_all
#print axioms ProofFile.Honest.K4.ite_none_some
#print axioms ProofFile.Honest.K4.fbFree_rel
#print axioms ProofFile.Honest.K4.openOf_rel
