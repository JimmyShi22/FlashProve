-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/RecordSeedsLaws.lean: what the drawing of a record's seeds (Fmt/RecordSeeds.lean) returns has
its lengths and is canonical, at every hash; and the flat list of seeds loses nothing.

Main names:
  `ok_tryWord`, `ok_drawFN`, `okE_drawE`, `okE_drawNZ`: what a draw gives is the spelling of an
    element, on every row of words.
  `SeedsShaped f v a l`: l has a seeds; each point has v coordinates; every coordinate and every
    factor is canonical.
  `drawSeed_shaped`, `recordSeedsW_shaped`: what the drawing returns is so, AT EVERY PLAIN HASH h.
  `flatSeeds_length`, `flatSeeds_ok`: the flat list has a (v + 1) elements, all canonical.
  `flatSeeds_inj`: two lists of seeds whose points all have v coordinates and whose flat lists are
    the same are the same.
Limits:
  No law here says that the drawing returns something: `Chain.queryW` may refuse. Where it does not,
  at a plain hash: `recordSeedsW_some_iff`, Fmt/ChainStmMore.lean.
  That a factor is not 0 is not said here.
  "At every plain hash": h has values in the monad Id. Nothing on a hash that is asked.

-/
import Fmt.RecordSeeds
import Fmt.FieldE
import Fmt.ParsedReadCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fmt

/-- What a try gives is below p. -/
theorem ok_tryWord (f : Fld) (w x : UInt64) (h : f.tryWord w = some x) : f.ok x = true := by
  cases f with
  | one =>
    simp only [Fld.tryWord] at h
    split at h
    · next k => cases h; exact decide_eq_true k
    · cases h
  | two =>
    simp only [Fld.tryWord] at h
    split at h
    · next k => cases h; exact decide_eq_true k
    · cases h

/-- The word 0 is below p. -/
theorem ok_zero (f : Fld) : f.ok 0 = true := by cases f <;> decide

/-- The word 1 is below p. -/
theorem ok_one (f : Fld) : f.ok 1 = true := by cases f <;> decide

/-- An element of the base field, as drawn, is below p. -/
theorem ok_drawFN (f : Fld) : ∀ (n : Nat) (r : Row) (c : Nat), f.ok (drawFN f n r c).1 = true
  | 0, _, _ => ok_zero f
  | n + 1, r, c => by
    show f.ok ((match f.tryWord (Dr.word r c).1 with
      | some x => Dr.pure x
      | none => drawFN f n) r (Dr.word r c).2).1 = true
    cases e : f.tryWord (Dr.word r c).1 with
    | some x => exact ok_tryWord f _ x e
    | none => exact ok_drawFN f n r _

/-- An element of the extension field, as drawn, is canonical. -/
theorem okE_drawE (f : Fld) (r : Row) (c : Nat) : f.okE (drawE f r c).1 = true := by
  show (f.ok _ && f.ok _ && f.ok _) = true
  simp only [Bool.and_eq_true]
  exact ⟨⟨ok_drawFN f 6 r _, ok_drawFN f 6 r _⟩, ok_drawFN f 6 r _⟩

/-- So is one that is drawn not to be 0. -/
theorem okE_drawNZ (f : Fld) (r : Row) (c : Nat) : f.okE (drawNZ f r c).1 = true := by
  show f.okE ((if (drawE f r c).1 = (0, 0, 0) then
      (drawE f).bind fun e' => Dr.pure (if e' = (0, 0, 0) then (1, 0, 0) else e')
    else Dr.pure (drawE f r c).1) r (drawE f r c).2).1 = true
  by_cases k : (drawE f r c).1 = (0, 0, 0)
  · rw [if_pos k]
    show f.okE (if (drawE f r (drawE f r c).2).1 = (0, 0, 0) then (1, 0, 0)
      else (drawE f r (drawE f r c).2).1) = true
    by_cases k' : (drawE f r (drawE f r c).2).1 = (0, 0, 0)
    · rw [if_pos k']
      show (f.ok 1 && f.ok 0 && f.ok 0) = true
      rw [ok_one, ok_zero]
      rfl
    · rw [if_neg k']
      exact okE_drawE f r _
  · rw [if_neg k]
    exact okE_drawE f r c

/-- The form of a list of seeds: a seeds; each point has v coordinates; all elements canonical. -/
def SeedsShaped (f : Fld) (v a : Nat) (l : List (List Ext × Ext)) : Prop :=
  l.length = a ∧ ∀ y ∈ l, y.1.length = v ∧ (∀ e ∈ y.1, f.okE e = true) ∧ f.okE y.2 = true

/-- One seed, as drawn: v coordinates, all canonical, and a canonical factor. -/
theorem drawSeed_shaped (f : Fld) (v : Nat) (r : Row) (c : Nat) :
    (drawSeed f v r c).1.1.length = v ∧ (∀ e ∈ (drawSeed f v r c).1.1, f.okE e = true) ∧
      f.okE (drawSeed f v r c).1.2 = true :=
  ⟨times_len (drawE f) v r c,
    times_all (drawE f) (fun e => f.okE e = true) (fun r c => okE_drawE f r c) v r c,
    okE_drawNZ f r _⟩

/-- A step in the monad Id, run. For letters. -/
theorem idRunBind {α β : Type} (x : Id α) (k : α → Id β) :
    Id.run (x >>= k) = Id.run (k (Id.run x)) := rfl

/-- `recordSeedsW` at a plain hash as a map over the round's value. By the definition's own equation
and `idRunBind`; a letter q stands for the round's value before the two texts are compared: written
so that no checker need compute that value. -/
theorem recordSeedsW_run (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray) (f : Fld)
    (name : ByteArray) (v a : Nat) :
    Id.run (recordSeedsW h f name v a) =
      (Id.run ((⟨recordLabel, Id.run (recordFirstW h name), 0⟩ : Chain).queryW h
        ByteArray.empty .seeds 0 0 (blocksFor (a * (v * 18 + 36))))).map fun x =>
          ((drawSeed f v).times a (rowOf x.2) 0).1 := by
  rw [recordSeedsW, idRunBind, idRunBind]
  generalize Id.run (Chain.queryW _ _ _ _ _ _ _) = q
  cases q with
  | none => rfl
  | some p =>
    cases p
    rfl

/-- WHAT THE DRAWING RETURNS HAS THE FORM, AT EVERY PLAIN HASH. Nothing is asked of h, of the name
or of the two numbers. -/
theorem recordSeedsW_shaped (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray) (f : Fld)
    (name : ByteArray) (v a : Nat) (l : List (List Ext × Ext))
    (e : Id.run (recordSeedsW h f name v a) = some l) : SeedsShaped f v a l := by
  -- by the named equation `recordSeedsW_run`, not by unfolding
  rw [recordSeedsW_run] at e
  obtain ⟨x, -, e'⟩ := Option.map_eq_some_iff.1 e
  · obtain rfl := e'
    exact ⟨times_len _ _ _ _,
      times_all (drawSeed f v)
        (fun y => y.1.length = v ∧ (∀ e ∈ y.1, f.okE e = true) ∧ f.okE y.2 = true)
        (fun r c => drawSeed_shaped f v r c) a _ _⟩

/-- The flat list's length. -/
theorem flatSeeds_length (v : Nat) : ∀ l : List (List Ext × Ext), (∀ y ∈ l, y.1.length = v) →
    (flatSeeds l).length = l.length * (v + 1)
  | [], _ => by simp [flatSeeds]
  | y :: l, h => by
    have a := flatSeeds_length v l fun z hz => h z (List.mem_cons_of_mem _ hz)
    have b := h y (List.mem_cons_self ..)
    show ((y.1 ++ [y.2]) ++ flatSeeds l).length = (l.length + 1) * (v + 1)
    rw [List.length_append, List.length_append, a, b, List.length_singleton, Nat.succ_mul]
    omega

/-- Of seeds with the form: a (v + 1) elements, all canonical. -/
theorem flatSeeds_ok (f : Fld) (v a : Nat) (l : List (List Ext × Ext)) (h : SeedsShaped f v a l) :
    (flatSeeds l).length = a * (v + 1) ∧ ∀ e ∈ flatSeeds l, f.okE e = true := by
  refine ⟨by rw [flatSeeds_length v l fun y hy => (h.2 y hy).1, h.1], fun e he => ?_⟩
  obtain ⟨y, hy, hey⟩ := List.mem_flatMap.1 he
  rcases List.mem_append.1 hey with k | k
  · exact (h.2 y hy).2.1 e k
  · obtain rfl := List.mem_singleton.1 k
    exact (h.2 y hy).2.2

/-- THE FLAT LIST LOSES NOTHING, once the number of a point's coordinates is known. -/
theorem flatSeeds_inj (v : Nat) : ∀ l l' : List (List Ext × Ext), (∀ y ∈ l, y.1.length = v) →
    (∀ y ∈ l', y.1.length = v) → flatSeeds l = flatSeeds l' → l = l'
  | [], [], _, _, _ => rfl
  | [], y :: l', _, _, e => by
    have z := congrArg List.length e
    simp [flatSeeds] at z
  | y :: l, [], _, _, e => by
    have z := congrArg List.length e
    simp [flatSeeds] at z
  | y :: l, y' :: l', h, h', e => by
    have e' : y.1 ++ (y.2 :: flatSeeds l) = y'.1 ++ (y'.2 :: flatSeeds l') := by
      have : (y.1 ++ [y.2]) ++ flatSeeds l = (y'.1 ++ [y'.2]) ++ flatSeeds l' := e
      simpa [List.append_assoc] using this
    have n : y.1.length = y'.1.length := by
      rw [h y (List.mem_cons_self ..), h' y' (List.mem_cons_self ..)]
    obtain ⟨a, b⟩ := List.append_inj e' n
    obtain ⟨b1, b2⟩ := List.cons.inj b
    have t := flatSeeds_inj v l l' (fun z hz => h z (List.mem_cons_of_mem _ hz))
      (fun z hz => h' z (List.mem_cons_of_mem _ hz)) b2
    rw [t, Prod.ext a b1]

end Fmt

#print axioms Fmt.ok_tryWord
#print axioms Fmt.ok_zero
#print axioms Fmt.ok_one
#print axioms Fmt.ok_drawFN
#print axioms Fmt.okE_drawE
#print axioms Fmt.okE_drawNZ
#print axioms Fmt.drawSeed_shaped
#print axioms Fmt.recordSeedsW_shaped
#print axioms Fmt.flatSeeds_length
#print axioms Fmt.flatSeeds_ok
#print axioms Fmt.flatSeeds_inj
