-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsFence.lean: WHO CAN PAY `FencedB` (Johnson/Road/K4/K4Pins.lean): two of the
table of joints' own tests on the table and the plan: `fenceFit` (Johnson/Desc/First/FenceFit.lean:
at every border every tenant of an open pin with a sample sits in a tree whose number is below
`Numbers.treesAt` there) and `readsOpen` (Johnson/Desc/First/Borders.lean: every item that a block
closes or reads is open in front of it). Theorems, by unfolding and one induction on the list of
places. No draw, no count.

  `fencedB_of_fenceFit`: `FencedB N m base = true`, from: `fenceFit N links ps = true` · k is a
    border of the list of places · the items pin m 0 and pinI are open at border k · base is
    `N.treesAt ps[k]?`.
  `open_of_readsOpen`: where `readsOpen links ps O = true`: every item that the row of the block at
    place number k closes or reads is a member of the open set at border k.
  `fencedB_at_k4`: `FencedB N m base = true`, from: block number k stands at piece 3 of the layers'
    segment m (`AtK4`, Johnson/Road/K4/K4AtTable.lean) · `readsOpen links ps (start links) = true` ·
    `fenceFit N links ps = true` · base is `N.treesAt (some pl)`.
  `fencedB_of_below`: `FencedB N m base = true`, from: `AtK4` · `readsOpen` · every tenant of a pin
    with a sample that is open at border k sits in a tree below base: THE LINE below OF `K4Keeps`
    (Johnson/Road/K4/K4PromiseBehind.lean) at base := the piece's own: so no equation between a
    piece's base and `treesAt` is wanted there.

OBJECT: none of its own. USER: none yet; meant: whoever calls `PinPlan.k4_own`
(Johnson/Road/K4/K4PinsOwn.lean [not in this library]). LETTERS, filled by nobody: N, links, ps, k,
m, pl, base.

Limits. K04_law IS NOT PROVED BY THIS. THE PREMISES STAY. `fenceFit` and `readsOpen` are tests with
code. WHAT HAS RUN, by prints of the table's authors that we hold: `readsOpen`: yes at the small
example's index and at the full size's index of 358 blocks · `fenceFit`: yes at the small example's
plan (79 borders), no at two controls (`treesAt` one lower; the default numbers); AT THE FULL SIZE:
NO PRINT THAT WE KNOW. That a piece's base is `treesAt` at its place is the pieces' make
(FenceFit.lean's Limits (1)): nobody's yet.
-/
import Johnson.Road.K4.K4Pins
import Johnson.Desc.First.FenceFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (ModelPart Item Numbers rowOf segRow stepOpen openSets readsOpen start
  sampledIn fenceFit fenceFit_at)

/-- **`FencedB` from the table's own test**: from `fenceFit`, k a border, the items pin m 0 and pinI
open at border k, and base = `N.treesAt ps[k]?`. -/
theorem fencedB_of_fenceFit (N : Numbers) (links : List ModelPart) (ps : List Place) (k m base : ℕ)
    (h : fenceFit N links ps = true) (hk : k ≤ ps.length)
    (h0 : Item.pin m 0 ∈ (openSets links ps (start links))[k]?.getD [])
    (hI : Item.pinI ∈ (openSets links ps (start links))[k]?.getD [])
    (hb : base = N.treesAt ps[k]?) : FencedB N m base = true := by
  unfold FencedB
  refine List.all_eq_true.2 fun x hx => decide_eq_true ?_
  rw [hb]
  refine fenceFit_at N links ps h k hk x ?_
  rcases List.mem_append.1 hx with h1 | h1
  · exact List.mem_flatMap.2 ⟨.pin m 0, h0, h1⟩
  · exact List.mem_flatMap.2 ⟨.pinI, hI, h1⟩

/-- Where `readsOpen` says yes, what the row at place number k closes or reads is open at border k.
-/
theorem open_of_readsOpen (links : List ModelPart) :
    ∀ (ps : List Place) (O : List Item), readsOpen links ps O = true →
      ∀ (k : ℕ) (p : Place), ps[k]? = some p →
        ∀ i ∈ (rowOf links p).ins ++ (rowOf links p).ctx, i ∈ (openSets links ps O)[k]?.getD []
  | [], _, _, k, p, hp, _, _ => by simp at hp
  | p0 :: ps, O, h, 0, p, hp, i, hi => by
    have e : p0 = p := by simpa using hp
    subst e
    have h' : (((rowOf links p0).ins ++ (rowOf links p0).ctx).all O.contains &&
        readsOpen links ps (stepOpen O (rowOf links p0))) = true := h
    have h1 : ((rowOf links p0).ins ++ (rowOf links p0).ctx).all O.contains = true :=
      (Eq.mp (Bool.and_eq_true _ _) h').1
    have h2 := List.all_eq_true.1 h1 i hi
    show i ∈ O
    exact List.contains_iff_mem.1 h2
  | p0 :: ps, O, h, k + 1, p, hp, i, hi => by
    have h' : (((rowOf links p0).ins ++ (rowOf links p0).ctx).all O.contains &&
        readsOpen links ps (stepOpen O (rowOf links p0))) = true := h
    have h1 : readsOpen links ps (stepOpen O (rowOf links p0)) = true :=
      (Eq.mp (Bool.and_eq_true _ _) h').2
    have hp' : ps[k]? = some p := by simpa using hp
    exact open_of_readsOpen links ps _ h1 k p hp' i hi

/-- **`FencedB` at K4's place**: from `AtK4`, `readsOpen`, `fenceFit`, and base =
`N.treesAt (some pl)`. -/
theorem fencedB_at_k4 (N : Numbers) {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}
    (base : ℕ) (H : AtK4 links ps k m pl) (hr : readsOpen links ps (start links) = true)
    (hf : fenceFit N links ps = true) (hb : base = N.treesAt (some pl)) :
    FencedB N m base = true := by
  have hrow : rowOf links pl = segRow .layers m 3 := by
    simp only [rowOf, H.link, H.sub, H.piece]
  have hk : k ≤ ps.length := by
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.1 H.here
    exact Nat.le_of_lt hlt
  have ho := open_of_readsOpen links ps (start links) hr k pl H.here
  rw [hrow] at ho
  refine fencedB_of_fenceFit N links ps k m base hf hk (ho _ ?_) (ho _ ?_) (by rw [hb, H.here])
  · exact List.mem_append_right _ (List.mem_cons_self ..)
  · exact List.mem_append_right _ (by
      show Item.pinI ∈ [Item.pin m 0, .pinW, .constr m .small, .pinI]
      simp)

/-- **`FencedB` from the line below of `K4Keeps`**: from `AtK4`, `readsOpen`, and "every tenant of a
pin with a sample that is open at border k sits in a tree below base". -/
theorem fencedB_of_below (N : Numbers) {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}
    (base : ℕ) (H : AtK4 links ps k m pl) (hr : readsOpen links ps (start links) = true)
    (hb : ∀ z ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []), z.1 < base) :
    FencedB N m base = true := by
  have hrow : rowOf links pl = segRow .layers m 3 := by
    simp only [rowOf, H.link, H.sub, H.piece]
  have ho := open_of_readsOpen links ps (start links) hr k pl H.here
  rw [hrow] at ho
  unfold FencedB
  refine List.all_eq_true.2 fun x hx => decide_eq_true (hb x ?_)
  rcases List.mem_append.1 hx with h1 | h1
  · exact List.mem_flatMap.2 ⟨.pin m 0, ho _ (List.mem_append_right _ (List.mem_cons_self ..)), h1⟩
  · exact List.mem_flatMap.2 ⟨.pinI, ho _ (List.mem_append_right _ (by
      show Item.pinI ∈ [Item.pin m 0, .pinW, .constr m .small, .pinI]
      simp)), h1⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.fencedB_of_fenceFit
#print axioms OnBytes.Road.K4.open_of_readsOpen
#print axioms OnBytes.Road.K4.fencedB_at_k4
#print axioms OnBytes.Road.K4.fencedB_of_below
