-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/KeyLaw/MeetsAt.lean: WRITTEN ROUNDS THAT ARE MADE OF THE PLANNER'S ENTRIES
OF A LOOKUP meet the typed lookup's formats, round by round, and hold no answer to a sample: the two
premises of ViewAt.lean, paid.

Main names:
  MadeOf d x: the written round d is made of an entry of the shape x: its entry is the shape's but
    for the bits of work and the logarithm of positions, which is at most 64; its kind is neither a
    sealing nor one of seeds; its items are the shape's number of elements.
  dsOf_bare: an entry without positions draws the same whatever its logarithm of positions.
  meets_of_made, noAns_of_made: one round.
  shape_nz: in a lookup's shape the elements that are never 0 are none or all of a round's.
  meets_shape: a list of rounds. meets_typed: AT THE TYPED LOOKUP's OWN FORMATS.

Limits. MadeOf is a premise on the written rounds: that a file's written rounds at a lookup's
stretch are so made of the plan's entries is not shown here.

-/
import Johnson.Desc.First.Look.KeyLaw.ViewAt
import Johnson.Desc.First.Look.KeyLaw.Out

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open Iop OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker
open Lk6 (Dat Pl)
open Fo.Peel (MeetsT NoAns)

/-- The written round d is made of an entry of the shape x. -/
structure MadeOf (d : RDT) (x : Shape) : Prop where
  entry : bare d.entry = entryOf x
  logN : d.entry.logN ≤ 64
  notSealed : d.kind ≠ .sealed
  notSeeds : d.kind ≠ .seeds
  items : d.items = List.replicate x.2.1 Fmt.Item.e

/-- An entry without positions draws the same whatever its logarithm of positions. -/
theorem dsOf_bare (e : Fmt.Entry) (k : Fmt.Kind) (h : e.poss = 0) :
    Fmt.dsOf e k = Fmt.dsOf (bare e) k := by
  unfold Fmt.dsOf
  have h' : (bare e).poss = 0 := h
  rw [h, h']
  rfl

/-- In a list of plain elements, then elements that are never 0: from the first of these on. -/
theorem isNZ_tail : ∀ (a b i : ℕ) (l : List Fmt.Draw), a ≤ i → i < a + b →
    IsNZ (List.replicate a Fmt.Draw.elem ++ List.replicate b Fmt.Draw.elemNZ ++ l) i
  | 0, 0, i, _, _, h => absurd h (Nat.not_lt_zero _)
  | 0, b + 1, 0, _, _, _ => trivial
  | 0, b + 1, i + 1, l, _, h => isNZ_tail 0 b i l (Nat.zero_le _) (by omega)
  | a + 1, b, 0, _, h, _ => absurd h (Nat.not_succ_le_zero _)
  | a + 1, b, i + 1, l, h, h' => isNZ_tail a b i l (by omega) (by omega)

/-- **One round.** -/
theorem meets_of_made {d : RDT} {x : Shape} (h : MadeOf d x)
    (hz : x.2.2.2 = 0 ∨ x.2.2.2 = x.2.2.1) : MeetsT d (spOf (fmOf x)) := by
  have e1 : d.entry.poss = 0 := congrArg Fmt.Entry.poss h.entry
  have e2 : d.entry.trits = 0 := congrArg Fmt.Entry.trits h.entry
  have e3 : d.entry.drawE = x.2.2.1 := congrArg Fmt.Entry.drawE h.entry
  have e4 : d.entry.drawNZ = x.2.2.2 := congrArg Fmt.Entry.drawNZ h.entry
  have hle : d.entry.drawNZ ≤ d.entry.drawE := by
    rw [e3, e4]
    rcases hz with hz | hz <;> omega
  refine ⟨⟨?_, plain_dsOf _ _ e2 h.notSealed, (nE_dsOf _ _ hle h.notSeeds).trans e3,
    (nP_dsOf _ _).trans e1, ?_, h.logN⟩, fun hnz i hi => ?_⟩
  · show nS d.items = x.2.1
    rw [h.items]
    exact nS_replicate_e _
  · show AllPos 0 (Fmt.dsOf d.entry d.kind)
    rw [dsOf_bare _ _ e1]
    exact allPos_dsOf (bare d.entry) d.kind
  · have hn : x.2.2.2 ≠ 0 := by simpa [spOf, fmOf] using hnz
    have hall : x.2.2.2 = x.2.2.1 := hz.resolve_left hn
    have hi' : i < x.2.2.1 := hi
    show IsNZ (Fmt.dsOf d.entry d.kind) i
    unfold Fmt.dsOf Fmt.dsElems
    rw [e1, if_neg h.notSeeds, e3, e4, hall, Nat.sub_self]
    exact isNZ_tail 0 x.2.2.1 i _ (Nat.zero_le _) (by omega)

theorem noAns_of_made {d : RDT} {x : Shape} (h : MadeOf d x) : NoAns d.items := by
  intro it hit
  rw [h.items] at hit
  rw [List.eq_of_mem_replicate hit]
  exact fun e => by cases e

/-- In a masked sumcheck's shape. -/
theorem psc_nz (sent : List ℕ) (y : Option (ℕ × ℕ)) :
    ∀ x ∈ pscShape sent y, x.2.2.2 = 0 ∨ x.2.2.2 = x.2.2.1 := by
  intro x hx
  unfold pscShape at hx
  rcases List.mem_append.1 hx with hx | hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact Or.inl rfl
    · obtain ⟨g, -, rfl⟩ := List.mem_map.1 hx
      exact Or.inl rfl
  · cases y with
    | none => cases hx
    | some y =>
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inr rfl
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact Or.inl rfl
        · cases hx

theorem tree_nz (more levels : ℕ) :
    ∀ x ∈ treeShape more levels, x.2.2.2 = 0 ∨ x.2.2.2 = x.2.2.1 := by
  intro x hx
  unfold treeShape at hx
  obtain ⟨l, -, hx⟩ := List.mem_flatMap.1 hx
  rcases List.mem_append.1 hx with hx | hx
  · exact psc_nz _ _ x hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact Or.inl rfl
    · cases hx

/-- **In a lookup's shape the elements that are never 0 are none or all of a round's.** -/
theorem shape_nz (f : Face) : ∀ x ∈ shapeG f, x.2.2.2 = 0 ∨ x.2.2.2 = x.2.2.1 := by
  intro x hx
  unfold shapeG at hx
  simp only [List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with ((((((((rfl | hx) | ⟨_, -, hx⟩) | ⟨_, -, hx⟩) | rfl) | ⟨_, -, hx⟩) | hx) | hx) |
    rfl) | hx
  · exact Or.inl rfl
  · exact psc_nz _ _ x hx
  · exact psc_nz _ _ x hx
  · exact psc_nz _ _ x hx
  · exact Or.inl rfl
  · exact tree_nz _ _ x hx
  · exact tree_nz _ _ x hx
  · exact psc_nz _ _ x hx
  · exact Or.inl rfl
  · exact psc_nz _ _ x hx

/-- **A list of rounds.** -/
theorem meets_shape : ∀ (ds : List RDT) (xs : List Shape), List.Forall₂ MadeOf ds xs →
    (∀ x ∈ xs, x.2.2.2 = 0 ∨ x.2.2.2 = x.2.2.1) →
    List.Forall₂ MeetsT ds ((xs.map fmOf).map spOf) ∧ ∀ d ∈ ds, NoAns d.items
  | [], [], .nil, _ => ⟨.nil, fun d hd => (by cases hd)⟩
  | d :: ds, x :: xs, .cons h1 h2, hz => by
    obtain ⟨r1, r2⟩ := meets_shape ds xs h2 fun y hy => hz y (List.mem_cons_of_mem _ hy)
    refine ⟨.cons (meets_of_made h1 (hz x List.mem_cons_self)) r1, fun d' hd' => ?_⟩
    rcases List.mem_cons.1 hd' with rfl | hd'
    · exact noAns_of_made h1
    · exact r2 d' hd'

/-- **At the typed lookup's own formats.** -/
theorem meets_typed (A : Dat GE) (st : A.St) (P : Pl A) (Ex : ExtSpec) (f : Face)
    (hf : FaceIs A st f) (hadm : A.toPub.Adm Cb.Gl.p) (ds : List RDT)
    (h : List.Forall₂ MadeOf ds (shapeG f)) :
    List.Forall₂ MeetsT ds ((Lk6.lamS_runs A P Ex).rd.fms.map spOf) ∧ ∀ d ∈ ds, NoAns d.items := by
  rw [(Lk6.lamS_runs A P Ex).fms, typedShape A st P f hf hadm]
  exact meets_shape ds _ h (shape_nz f)

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.meets_of_made
#print axioms VerifiableInference.Desc.K3.KeyLaw.shape_nz
#print axioms VerifiableInference.Desc.K3.KeyLaw.meets_typed
