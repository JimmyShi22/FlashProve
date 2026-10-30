-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SkelWeights.lean: NO HYPOTHESIS BUT RETURNS.

What is here. THE WEIGHTS OF THE SECOND PASS's PRODUCTS (`Sides.trips`, `tripsOf`:
Johnson/Desc/K4/Honest/Sides.lean) DO NOT HANG ON THE READS, THE TOKEN POINT's EQUALITY TABLE, THE
NEVER-SENT VECTOR OR THE SHOWN VALUES: at one shared data, wherever two calls return, the two lists
of products have one list of first components. Three definitions, and statements with their proofs.

  `Both`, its eight rules   two values that may be missing, read where both are there.
  `filter_both`   two lists, member by member, under two tests of one answer.
  `SameW`, `sameW_flat`, `sameW_flatMap`   two lists of products have one list of weights.
  `Fst`, `Fst.pure`, `Fst.bind`, `both_fst`   where a product is there, its weight is a given
      element.
  `tripsOf_weights`   one panel's products.
  **`trips_weights`**   all products of the second pass.

Why. The second token sumcheck's job compares the products' weights token against token
(`jobTermsOn`, Johnson/Desc/K4/Honest/Terms.lean: sameWeights): a test on elements, and the job is
none where it fails. With `trips_weights` that test is true wherever the tokens' rows are made:
shown in Law/SkelTerms.lean (`sameWeights_true`), not here.

Debts and ends. `Both`, `SameW` AND `Fst` ARE ENDS, SPENT IN THIS FILE: NO DEBTS. No statement of
another file of its writers names one of the three. `SameW` is concluded, inside `Both`, by
`tripsOf_weights`, from the library's relation `BlkKeys True` on two panels, and by `sameW_flatMap`,
from `SameW` member by member; `trips_weights` has that relation from the library's `panels_keys`
(Johnson/Desc/First/K4/Returns/Pub/PanelsKeys.lean) at W := True, at two lists of panels that part
in the shown values alone. `Fst` is concluded by `Fst.pure` and `Fst.bind`. `trips_weights`, the one
law here that another file calls, names none of the three and has no hypothesis but the two returns.
THE THREE COMPARE PRODUCTS MADE AT ONE SHARED DATA, SO AT ONE INPUT: between two inputs the laws of
this family compare how many products there are, not their weights (`trips_rel`,
Law/SkelTerms.lean).

Not shown here. `Sides.trips` IS SHOWN TO RETURN NOWHERE: the statement starts from two returns.
THAT THE WEIGHTS ARE THE SAME AT TWO INPUTS: the shared data S is one letter here. What a weight is
made of: by `tripsOf`'s text the panel's call weight times a row's weight; whence these two fields
come is the library's text (OnBytes/Model/LayerPanels.lean). Nothing on the products' two factors,
which hold values made of the input.

Kin. `filter_both` IS A TWIN WITHIN ITS WRITERS' OWN FILES: `all2_filter` (Law/SkelLists.lean) is
the same law, proof and all; neither file imports the other, and each would bring the other's
imports along. `Both.mapM` is the library's `mapM_both` (Johnson/Road/K4/Total/HearRowSkel.lean)
over two lists in S, where that law has one list and writes `Both` out; this file does not import
that one. No other twin is known to its writers. `OptRel` (OnBytes/Flat/LinksFreeLayer.lean) is the
stricter sister of `Both`: both values are missing, or both are there and in the relation; `Both`
says nothing where one is missing. The library has other definitions under the short names SameW
(Johnson/Desc/First/Att/Claims/Same.lean) and Both (OnBytes/Model/TestTailHeld.lean), in other
namespaces, on other things.
No property is claimed.
-/
import Johnson.Desc.First.K4.Returns.Pub.PanelsKeys
import Johnson.Desc.K4.Honest.Sides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Aff)
open OnBytes.Model.Layer (SBlk stubO placePanels)
open OnBytes.Flat (All2 OptRel optRel_bind optRel_bind_same)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.RtPub

/-! ## Two values that may be missing, read where both are there -/

/-- Where both values are there, they are in R. -/
def Both {α β : Type} (R : α → β → Prop) (x : Option α) (y : Option β) : Prop :=
  ∀ a b, x = some a → y = some b → R a b

/-- Two values that are there and in R. -/
theorem Both.pure {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    Both R (Pure.pure a) (Pure.pure b) :=
  fun _ _ e e' => Option.some.inj e ▸ Option.some.inj e' ▸ h

/-- Nothing is asked where the left value is missing. -/
theorem Both.left {α β : Type} {R : α → β → Prop} (y : Option β) : Both R (none : Option α) y :=
  fun _ _ e _ => by cases e

/-- Two binds: from the first values in S, and from S to R. -/
theorem Both.bind {α α' β β' : Type} {S : α → α' → Prop} {R : β → β' → Prop} {x : Option α}
    {x' : Option α'} {f : α → Option β} {f' : α' → Option β'} (hx : Both S x x')
    (hf : ∀ a a', S a a' → Both R (f a) (f' a')) : Both R (x >>= f) (x' >>= f') := by
  intro b b' e e'
  obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨a', ha', hb'⟩ := Option.bind_eq_some_iff.mp e'
  exact hf a a' (hx a a' ha ha') b b' hb hb'

/-- The relation that always holds. -/
theorem Both.any {α α' : Type} (x : Option α) (x' : Option α') : Both (fun _ _ => True) x x' :=
  fun _ _ _ _ => trivial

/-- Two branchings on one condition. -/
theorem Both.ite {α β : Type} {R : α → β → Prop} {c : Prop} [Decidable c] {x z : Option α}
    {x' z' : Option β} (h1 : Both R x x') (h2 : Both R z z') :
    Both R (if c then x else z) (if c then x' else z') := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
    exact h1
  · rw [if_neg h, if_neg h]
    exact h2

/-- Two maps that may yield nothing, over two lists that are in S member by member. -/
theorem Both.mapM {α α' β β' : Type} {S : α → α' → Prop} {R : β → β' → Prop} {f : α → Option β}
    {f' : α' → Option β'} (h : ∀ a a', S a a' → Both R (f a) (f' a')) {l : List α} {l' : List α'}
    (hl : All2 S l l') : Both (All2 R) (l.mapM f) (l'.mapM f') := by
  induction hl with
  | nil =>
    rw [List.mapM_nil, List.mapM_nil]
    exact Both.pure .nil
  | cons h0 _ ih =>
    rw [List.mapM_cons, List.mapM_cons]
    exact Both.bind (h _ _ h0) fun _ _ r => Both.bind ih fun _ _ rs => Both.pure (.cons r rs)

/-- The same over two arrays. -/
theorem Both.amapM {α α' β β' : Type} {S : α → α' → Prop} {R : β → β' → Prop} {f : α → Option β}
    {f' : α' → Option β'} (h : ∀ a a', S a a' → Both R (f a) (f' a')) {l : Array α}
    {l' : Array α'} (hl : All2 S l.toList l'.toList) :
    Both (fun a a' => All2 R a.toList a'.toList) (l.mapM f) (l'.mapM f') := by
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList]
  intro a a' e e'
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp e
  obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp e'
  exact Both.mapM h hl x x' hx hx'

/-- The same over one array. -/
theorem Both.amapM_same {α β β' : Type} {R : β → β' → Prop} {f : α → Option β}
    {f' : α → Option β'} (h : ∀ a, Both R (f a) (f' a)) (l : Array α) :
    Both (fun a a' => All2 R a.toList a'.toList) (l.mapM f) (l.mapM f') :=
  Both.amapM (S := Eq) (fun a _ e => e ▸ h a) (All2.refl (fun _ => rfl) _)

/-- Two lists in R member by member stay so under two tests that give one answer on members in R. -/
theorem filter_both {α β : Type} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hp : ∀ a b, R a b → p a = q b) {l : List α} {l' : List β} (h : All2 R l l') :
    All2 R (l.filter p) (l'.filter q) := by
  induction h with
  | nil => exact .nil
  | @cons a b l l' h0 _ ih =>
    rw [List.filter_cons, List.filter_cons, hp a b h0]
    cases q b
    · exact ih
    · exact .cons h0 ih

/-! ## The weights of a list of products -/

/-- Two lists of products have one list of weights. -/
def SameW (a a' : Array Trip) : Prop := a.toList.map (·.1) = a'.toList.map (·.1)

/-- Lists of lists of products, in `SameW` member by member: laid end to end, one list of weights.
-/
theorem sameW_flat {l l' : List (Array Trip)} (h : All2 SameW l l') :
    (l.flatMap fun r => (id r).toList).map (·.1) =
      (l'.flatMap fun r => (id r).toList).map (·.1) := by
  induction h with
  | nil => rfl
  | cons h0 _ ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, List.map_append, ih]
    exact congrArg (· ++ _) h0

/-- The same over arrays, in `SameW`'s own words. -/
theorem sameW_flatMap {l l' : Array (Array Trip)} (h : All2 SameW l.toList l'.toList) :
    SameW (l.flatMap id) (l'.flatMap id) := by
  unfold SameW
  rw [Array.toList_flatMap, Array.toList_flatMap]
  exact sameW_flat h

/-- Where the product is there, its weight is w. -/
def Fst (w : E) (x : Option Trip) : Prop := ∀ t, x = some t → t.1 = w

/-- A product that is written out has its first component as its weight. -/
theorem Fst.pure (w a c : E) : Fst w (Pure.pure ((w, a, c) : Trip)) :=
  fun _ e => Option.some.inj e ▸ rfl

/-- A bind all of whose arms have the weight w has it. -/
theorem Fst.bind {α : Type} {w : E} {x : Option α} {f : α → Option Trip} (h : ∀ a, Fst w (f a)) :
    Fst w (x >>= f) := by
  intro t e
  obtain ⟨a, _, hb⟩ := Option.bind_eq_some_iff.mp e
  exact h a t hb

/-- Two products of one given weight have one weight. -/
theorem both_fst {w : E} {x x' : Option Trip} (h : Fst w x) (h' : Fst w x') :
    Both (fun t t' : Trip => t.1 = t'.1) x x' :=
  fun t t' e e' => (h t e).trans (h' t' e').symm

/-- **The products of one panel**: where both calls return, one list of weights. -/
theorem tripsOf_weights (S : Sides) (val val' : Aff → Option E) (F F' : Array (Array E))
    (hh hh' : Nat → Nat → E) {b b' : SBlk} (hb : BlkKeys True b b') :
    Both SameW (tripsOf S val F hh b) (tripsOf S val' F' hh' b') := by
  obtain ⟨tri, v0, claim, ec, ni, ny, wy, w, off, A, B, wt, sl, xx, virt⟩ := b
  obtain ⟨tri', v0', claim', ec', ni', ny', wy', w', off', A', B', wt', sl', xx', virt'⟩ := b'
  have e1 : tri = tri' := hb.tri
  have e2 : v0 = v0' := hb.v0
  have e3 : ni = ni' := hb.ni
  have e4 : ny = ny' := hb.ny
  have e5 : virt = virt' := hb.virt
  have e6 : ec = ec' := hb.ec trivial
  have e7 : wt = wt' := hb.wt trivial
  subst e1 e2 e3 e4 e5 e6 e7
  unfold tripsOf
  cases tri with
  | true =>
    simp only [↓reduceIte]
    refine Both.bind (Both.any _ _) fun _ _ _ => Both.bind (Both.any _ _) fun _ _ _ =>
      Both.pure ?_
    unfold SameW
    rw [Array.toList_map, Array.toList_map, List.map_map, List.map_map]
    rfl
  | false =>
    cases v0 <;> cases B <;> cases B' <;>
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine Both.ite (Both.left _) (Both.bind (Both.any _ _) fun f f' _ => Both.bind
        (S := fun r r' => All2 SameW r.toList r'.toList) ?_
        fun _ _ r => Both.pure (sameW_flatMap r))
      refine Both.amapM_same (fun i => ?_) _
      intro r r' e e'
      show r.toList.map (·.1) = r'.toList.map (·.1)
      refine All2.map_eq (fun _ _ q => q) (Both.amapM_same (R := fun t t' : Trip => t.1 = t'.1)
        (fun yv => both_fst (w := OnBytes.mulE ec (wt.getD i zeroE)) ?_ ?_) _ r r' e e')
      all_goals
        first
          | exact Fst.bind fun _ => Fst.bind fun _ => Fst.bind fun _ => Fst.bind fun _ =>
              Fst.pure _ _ _
          | exact Fst.bind fun _ => Fst.bind fun _ => Fst.bind fun _ => Fst.pure _ _ _

/-- **One list of weights**, at one shared data and any two reads, equality tables, never-sent
vectors and lists of shown values. -/
theorem trips_weights (S : Sides) {R R' : Reads} {et et' : Array E} {hh hh' : Nat → Nat → E}
    {sh sh' : Array E} {l l' : Array Trip} (h : S.trips R et hh sh = some l)
    (h' : S.trips R' et' hh' sh' = some l') : l.map (·.1) = l'.map (·.1) := by
  unfold Sides.trips at h h'
  obtain ⟨⟨bl, n⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨bl', n'⟩, hp', h'⟩ := Option.bind_eq_some_iff.mp h'
  obtain ⟨ls, hm, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ls', hm', h'⟩ := Option.bind_eq_some_iff.mp h'
  obtain rfl : ls.flatMap id = l := Option.some.inj h
  obtain rfl : ls'.flatMap id = l' := Option.some.inj h'
  have hbl : All2 (BlkKeys True) bl.toList bl'.toList := by
    unfold Sides.panels at hp hp'
    obtain ⟨pans, hq, hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨pans', hq', hp'⟩ := Option.bind_eq_some_iff.mp hp'
    have r := panels_keys (W := True)
      (p := { v := S.v, e := S.fo.e, shownT := sh, zt := S.zt, stubO := stubO S.v.y })
      (p₀ := { v := S.v, e := S.fo.e, shownT := sh', zt := S.zt, stubO := stubO S.v.y })
      ⟨rfl, rfl, rfl, rfl⟩ (fun _ => ⟨rfl, rfl⟩) S.TS
    rw [hq, hq'] at r
    have r' : PanKeys True pans pans' := r
    have q := (placePanels_keys r'.bl).1
    by_cases c : (pans.nextV != S.opens.size) = true
    · rw [if_pos c] at hp
      cases hp
    · by_cases c' : (pans'.nextV != S.opens.size) = true
      · rw [if_pos c'] at hp'
        cases hp'
      · rw [if_neg c] at hp
        rw [if_neg c'] at hp'
        have a1 : placePanels pans.bl = (bl, n) := Option.some.inj hp
        have a2 : placePanels pans'.bl = (bl', n') := Option.some.inj hp'
        rw [a1, a2] at q
        exact q
  have hf : All2 (BlkKeys True) (bl.filter fun b => b.claim == 1).toList
      (bl'.filter fun b => b.claim == 1).toList := by
    rw [Array.toList_filter, Array.toList_filter]
    exact filter_both (fun a b k => by rw [k.claim]) hbl
  have hs := Both.amapM (R := SameW) (fun b b' k => tripsOf_weights S _ _ _ _ hh hh' k) hf ls ls' hm
    hm'
  have ht := sameW_flatMap hs
  unfold SameW at ht
  rw [← Array.toList_inj, Array.toList_map, Array.toList_map]
  exact ht

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.Both
#print axioms ProofFile.Honest.K4.Both.pure
#print axioms ProofFile.Honest.K4.Both.left
#print axioms ProofFile.Honest.K4.Both.bind
#print axioms ProofFile.Honest.K4.Both.any
#print axioms ProofFile.Honest.K4.Both.ite
#print axioms ProofFile.Honest.K4.Both.mapM
#print axioms ProofFile.Honest.K4.Both.amapM
#print axioms ProofFile.Honest.K4.Both.amapM_same
#print axioms ProofFile.Honest.K4.filter_both
#print axioms ProofFile.Honest.K4.SameW
#print axioms ProofFile.Honest.K4.sameW_flat
#print axioms ProofFile.Honest.K4.sameW_flatMap
#print axioms ProofFile.Honest.K4.Fst
#print axioms ProofFile.Honest.K4.Fst.pure
#print axioms ProofFile.Honest.K4.Fst.bind
#print axioms ProofFile.Honest.K4.both_fst
#print axioms ProofFile.Honest.K4.tripsOf_weights
#print axioms ProofFile.Honest.K4.trips_weights
