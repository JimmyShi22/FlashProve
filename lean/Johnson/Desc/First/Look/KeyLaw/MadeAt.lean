-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/KeyLaw/MadeAt.lean: WRITTEN ROUNDS WHOSE ENTRY, KIND AND ITEMS ARE THOSE OF
THE KIND'S DECLARED ROUNDS are made of the lookup's shape (MadeOf, MeetsAt.lean): the entry is the
planner's; the kind is the kind of the entry's name; the items are the cut of the entry's words.

Main names:
  plan_logN: every entry that the planner makes for a lookup has the logarithm of positions 0.
  okName, shape_names: no name of a lookup's shape is the name of a sealing or of a round of seeds.
  cut_shape: the cut of an entry of a shape: the shape's number of elements.
  AsDeclared d e: the written round d has the entry e, the kind of its name, and its cut.
  made_of_declared: one round. made_along: A LOOKUP's WHOLE STRETCH, at the planner's entries.

Limits. AsDeclared is a premise on the written rounds.

-/
import Johnson.Desc.First.Look.KeyLaw.MeetsAt
import Johnson.Desc.First.Look.KeyLaw.Plan
import OnBytes.Params.PlanListsMembers
import Decl.Declared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Params OnBytes.Maker
open OnBytes.Model (RoundName)

/-- Each of the thirteen descriptions of which a lookup's list is made. -/
theorem members_logN (s : Setting) (c : Scope) (x : LookupSize) :
    ∀ y ∈ lookupMembers s x, (y.round s c).entry.logN = 0 := by
  intro y hy
  simp only [lookupMembers, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **Every entry that the planner makes for a lookup has the logarithm of positions 0.** -/
theorem plan_logN (set : Setting) (scope : Scope) (f : Face) (es : List Fmt.Entry)
    (h : entriesG set scope f = some es) : ∀ e ∈ es, e.logN = 0 := by
  unfold entriesG at h
  cases hf : finish set scope (planLookup f.size) with
  | error e => rw [hf] at h; cases h
  | ok P =>
    rw [hf] at h
    obtain rfl : P.rounds.map (·.entry) = es := Option.some.inj h
    obtain ⟨-, hr, -⟩ := finish_rounds (runs_lookup f.size) hf
    intro e he
    rw [hr, List.map_map] at he
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 he
    exact members_logN set scope f.size y (mem_lookupList hy)

/-- The name is not the name of a sealing or of a round of seeds. -/
def okName (n : String) : Bool := Fmt.kindOf n != some .sealed && Fmt.kindOf n != some .seeds

theorem psc_names (sent : List ℕ) (y : Option (ℕ × ℕ)) :
    ∀ x ∈ pscShape sent y, okName x.1 = true := by
  intro x hx
  unfold pscShape at hx
  rcases List.mem_append.1 hx with hx | hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · decide
    · obtain ⟨g, -, rfl⟩ := List.mem_map.1 hx
      exact (by decide : okName RoundName.pscRound.name = true)
  · cases y with
    | none => cases hx
    | some y =>
      rcases List.mem_cons.1 hx with rfl | hx
      · exact (by decide : okName RoundName.pscY.name = true)
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact (by decide : okName RoundName.pscValues.name = true)
        · cases hx

theorem tree_names (more levels : ℕ) : ∀ x ∈ treeShape more levels, okName x.1 = true := by
  intro x hx
  unfold treeShape at hx
  obtain ⟨l, -, hx⟩ := List.mem_flatMap.1 hx
  rcases List.mem_append.1 hx with hx | hx
  · exact psc_names _ _ x hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · decide
    · cases hx

/-- **No name of a lookup's shape is the name of a sealing or of a round of seeds.** -/
theorem shape_names (f : Face) : ∀ x ∈ shapeG f, okName x.1 = true := by
  intro x hx
  unfold shapeG at hx
  simp only [List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with ((((((((rfl | hx) | ⟨_, -, hx⟩) | ⟨_, -, hx⟩) | rfl) | ⟨_, -, hx⟩) | hx) | hx) |
    rfl) | hx
  · decide
  · exact psc_names _ _ x hx
  · exact psc_names _ _ x hx
  · exact psc_names _ _ x hx
  · exact (by decide : okName RoundName.lkpPlanes.name = true)
  · exact tree_names _ _ x hx
  · exact tree_names _ _ x hx
  · exact psc_names _ _ x hx
  · exact (by decide : okName RoundName.zero.name = true)
  · exact psc_names _ _ x hx

/-- The cut of an entry of a shape. -/
theorem cut_shape {e : Fmt.Entry} {x : Shape} (h : bare e = entryOf x) :
    e.cut = List.replicate x.2.1 Fmt.Item.e := by
  have e1 : e.answers = 0 := congrArg Fmt.Entry.answers h
  have e2 : e.roots = 0 := congrArg Fmt.Entry.roots h
  have e3 : e.msg = 24 * x.2.1 := congrArg Fmt.Entry.msg h
  unfold Fmt.Entry.cut
  rw [e1, e2, e3]
  simp

/-- The written round d has the entry e, the kind of its name, and its cut. -/
def AsDeclared (d : RDT) (e : Fmt.Entry) : Prop :=
  d.entry = e ∧ Fmt.kindOf e.name = some d.kind ∧ d.items = e.cut

/-- **One round.** -/
theorem made_of_declared {d : RDT} {e : Fmt.Entry} {x : Shape} (h : AsDeclared d e)
    (he : bare e = entryOf x) (hl : e.logN = 0) (hn : okName x.1 = true) : MadeOf d x := by
  obtain ⟨h1, h2, h3⟩ := h
  have hname : e.name = x.1 := congrArg Fmt.Entry.name he
  rw [hname] at h2
  unfold okName at hn
  rw [h2] at hn
  simp only [bne_iff_ne, ne_eq, Option.some.injEq, Bool.and_eq_true] at hn
  exact ⟨by rw [h1]; exact he, by rw [h1, hl]; exact Nat.zero_le _, hn.1, hn.2,
    by rw [h3]; exact cut_shape he⟩

theorem made_lists : ∀ (ds : List RDT) (es : List Fmt.Entry) (xs : List Shape),
    List.Forall₂ AsDeclared ds es → es.map bare = xs.map entryOf → (∀ e ∈ es, e.logN = 0) →
    (∀ x ∈ xs, okName x.1 = true) → List.Forall₂ MadeOf ds xs
  | [], [], [], _, _, _, _ => .nil
  | d :: ds, e :: es, x :: xs, .cons h1 h2, he, hl, hn => by
    rw [List.map_cons, List.map_cons] at he
    obtain ⟨a, b⟩ := List.cons.inj he
    exact .cons (made_of_declared h1 a (hl e List.mem_cons_self) (hn x List.mem_cons_self))
      (made_lists ds es xs h2 b (fun e' h' => hl e' (List.mem_cons_of_mem _ h'))
        fun x' h' => hn x' (List.mem_cons_of_mem _ h'))
  | [], [], _ :: _, _, he, _, _ => by cases he
  | _ :: _, _ :: _, [], _, he, _, _ => by cases he

/-- **A lookup's whole stretch, at the planner's entries.** -/
theorem made_along (set : Setting) (scope : Scope) (f : Face) (es : List Fmt.Entry)
    (hs : f.shifted = false) (hok : f.ok = true) (h : entriesG set scope f = some es)
    (ds : List RDT) (hd : List.Forall₂ AsDeclared ds es) : List.Forall₂ MadeOf ds (shapeG f) :=
  made_lists ds es _ hd (planShape set scope f es hs hok h) (plan_logN set scope f es h)
    (shape_names f)

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.plan_logN
#print axioms VerifiableInference.Desc.K3.KeyLaw.shape_names
#print axioms VerifiableInference.Desc.K3.KeyLaw.made_along
