-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/IdSeedSpell.lean: the seeds of a typed record, spelled as a list of pairs and as one flat
list of the program's elements; both spellings are one to one; and what the text of `recordSeeds`
returns, typed and then spelled, comes back.

A record of a stored table holds, for each of s answers, a seed: a point of lg coordinates and a
factor that is not 0. The program's `recordSeeds` (OnBytes/Entry/Table.lean) returns the seeds as a
list of pairs (the point's coordinates, the factor), each element as three machine words below the
prime. The typed form of such a list is `seedOfC` (OnBytes/TypedOracleCompiler/Slice/EntryConv.lean). Here is the
way back, beside the spelling of the answers (OnBytes/K/IdTableSpell.lean).

Main names (namespace `OnBytes.K.IdTable`):
  `spellSeedL lg s ρ`: the typed seeds ρ as a list of pairs: seed by seed; the coordinates in
    their order; each element as `writeE` writes it. It is written after the field `seeds` of the
    program's key of a record (`keyOf`, OnBytes/Slice/KeyOfRec.lean); no theorem here ties the two.
  `spellSeed lg s ρ`: the same as one flat list: for each seed its lg coordinates, then its
    factor.
  `seedOfC_spell`: read back, the list of pairs gives ρ. `spellSeedL_inj`: so that spelling is one
    to one.
  `shaped_spell`: the list has the shape of a record's seeds (`SeedsShaped`,
    OnBytes/K/Arm/SeedOfInj.lean): s seeds, each in order, each point of lg coordinates.
  `spell_seedOfC`, `spellSeed_seedOfC`: on lists of that shape, "typed, then spelled" gives the
    list back: as pairs; and laid flat.
  `recordSeedsW_shaped`: what the generic text of `recordSeeds` (`recordSeedsW`,
    OnBytes/Slice/RecordRead.lean) returns has that shape AT EVERY PLAIN HASH: the hash is a
    variable. `spell_recordSeedsW`, `spellSeed_recordSeedsW`: so the typed form of what it returns,
    spelled, is what it returned: as pairs; and laid flat.
  `spellSeed_recordSeeds`: the same of the program's own `recordSeeds`, by `recordSeedsW_H` there.
    `spellSeed_twin`: the same of its twin with the hash as an argument
    (OnBytes/ChecksWithHashAsArgument/M/Entry/Table.lean), at every plain hash, by `twin_recordSeeds`
    (OnBytes/Tie/EntryTwin.lean).
  `flat_inj`, `flat_length`, `spellSeed_inj`, `spellSeed_length`: the flat list has s (lg + 1)
    elements, and it too is one to one.
What is proved and how. `spellSeedL_inj` follows from `seedOfC_spell`. `spell_seedOfC` follows from
it, `shaped_spell` and `seedOfC_inj` (OnBytes/K/Arm/SeedOfInj.lean). `recordSeedsW_shaped` is the
proof of `recordSeeds_shaped` there, without its first step: one proof stands twice. `flat_inj` asks
that the two lists have one length; that could be had from its other premises.
What is not claimed. That any program hashes either list (the Lean program's `Key.commitmentIdAt`,
OnBytes/Key/Table.lean, lays a flat list of a record's seeds into the commitment ID's string: no
theorem here ties that list to this spelling). Both "one to one" are said at fixed lg and s: ACROSS
SHAPES THE FLAT LIST IS NOT ONE TO ONE (two seeds of one coordinate and one seed of three have four
elements each). In the commitment ID's string lg and s are fixed by the table's name, which stands
before the list. That the drawing returns anything: each law on a drawing has "it returned l" as its
premise, so "at every plain hash" means: at every one at which it returned. That the seed in a key
is what the hash function gives at the table's name. Nothing on how the seeds are distributed, on
any hash function, or on soundness. The laws on a drawing are stated at the format's field `.two`,
the field that `Planned.plan` (OnBytes/Params/Planner.lean) writes into a plan, and at a hash
without effects (the monad `Id`). For proofs only; the program does not import this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.IdTableSpell
import OnBytes.K.Arm.SeedOfInj
import OnBytes.Tie.EntryTwin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.IdTable
open OnBytes.Slice OnBytes.Tie Cb
open TypedOracleCompiler.Slice (seedOf1C seedOfC)
open OnBytes.K.Arm (SeedsShaped seedOfC_inj)

variable (lg s : ℕ)

/-- One typed seed as a pair of the program's elements: the point's coordinates; the factor. -/
def spellSeed1 (y : (Fin lg → GE) × NZ) : List E × E :=
  (List.ofFn fun t : Fin lg => writeE (y.1 t), writeE y.2.val)

/-- The seeds of a typed record, as a list of such pairs. -/
def spellSeedL (ρ : Fin s → (Fin lg → GE) × NZ) : List (List E × E) :=
  List.ofFn fun i : Fin s => spellSeed1 lg (ρ i)

/-- The same as one flat list: for each seed its coordinates, then its factor. -/
def spellSeed (ρ : Fin s → (Fin lg → GE) × NZ) : List E :=
  (spellSeedL lg s ρ).flatMap fun y => y.1 ++ [y.2]

/-- One seed, read back. -/
theorem seedOf1C_spell (y : (Fin lg → GE) × NZ) : seedOf1C lg (spellSeed1 lg y) = y := by
  have h2 : readE (writeE y.2.val) ≠ 0 := by
    rw [readE_writeE]
    exact y.2.property
  refine Prod.ext (funext fun c => ?_) ?_
  · have e : (List.ofFn fun t : Fin lg => writeE (y.1 t)).getD c.val zeroE = writeE (y.1 c) := by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact c.isLt)]
      exact List.getElem_ofFn ..
    show readE ((List.ofFn fun t : Fin lg => writeE (y.1 t)).getD c.val zeroE) = y.1 c
    rw [e]
    exact readE_writeE _
  · show (if h : readE (writeE y.2.val) = 0 then (⟨1, one_ne_zero⟩ : NZ)
      else ⟨readE (writeE y.2.val), h⟩) = y.2
    rw [dif_neg h2]
    exact Subtype.ext (readE_writeE _)

/-- **The list, read back, gives the typed seeds.** -/
theorem seedOfC_spell (ρ : Fin s → (Fin lg → GE) × NZ) :
    seedOfC lg s (spellSeedL lg s ρ) = ρ := funext fun i => by
  have e : (spellSeedL lg s ρ).getD i.val ([], oneE) = spellSeed1 lg (ρ i) := by
    unfold spellSeedL
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt)]
    exact List.getElem_ofFn ..
  show seedOf1C lg ((spellSeedL lg s ρ).getD i.val ([], oneE)) = ρ i
  rw [e]
  exact seedOf1C_spell lg (ρ i)

/-- **The spelling is one to one.** -/
theorem spellSeedL_inj : Function.Injective (spellSeedL lg s) :=
  Function.LeftInverse.injective (g := seedOfC lg s) (seedOfC_spell lg s)

/-- The list has the shape of a record's seeds. -/
theorem shaped_spell (ρ : Fin s → (Fin lg → GE) × NZ) : SeedsShaped lg s (spellSeedL lg s ρ) := by
  refine ⟨List.length_ofFn, fun y hy => ?_⟩
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hy
  have hne : readE (writeE (ρ i).2.val) ≠ 0 := by
    rw [readE_writeE]
    exact (ρ i).2.property
  refine ⟨List.length_ofFn, fun x hx => ?_, written_okE _, ?_, hne⟩
  · have hx' : x ∈ List.ofFn (fun t : Fin lg => writeE ((ρ i).1 t)) := hx
    obtain ⟨t, rfl⟩ := (List.mem_ofFn' _ _).1 hx'
    exact written_okE _
  · show isZeroE (writeE (ρ i).2.val) = false
    cases hz : isZeroE (writeE (ρ i).2.val) with
    | false => rfl
    | true => exact absurd ((isZeroE_iff _ (written_okE _)).1 hz) hne

/-- **On lists of a record's shape, "typed, then spelled" gives the list back.** -/
theorem spell_seedOfC (l : List (List E × E)) (hl : SeedsShaped lg s l) :
    spellSeedL lg s (seedOfC lg s l) = l :=
  seedOfC_inj lg s _ _ (shaped_spell lg s _) hl (seedOfC_spell lg s _)

/-- **What the text of `recordSeeds` returns has a record's shape, at every plain hash.** The hash
is a variable. -/
theorem recordSeedsW_shaped (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → Id ByteArray)
    (name : ByteArray) (bits count : ℕ) (l : List (List E × E))
    (hl : recordSeedsW (m := Id) h .two name bits count = some l) : SeedsShaped bits count l := by
  have ok := seedOK_recordSeedsW h name bits count l hl
  rw [recordSeedsW_pure] at hl
  obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 hl
  rw [timesT_eq] at ok ⊢
  refine ⟨?_, fun y hy => ⟨?_, ok y hy⟩⟩
  · rw [List.length_map]
    exact times_length _ _ count 0
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hy
    rw [List.length_map]
    exact seed_points _ _ bits count 0 t ht

/-- **The typed form of what the text of `recordSeeds` returns, spelled, is what it returned**, at
every plain hash. -/
theorem spell_recordSeedsW (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → Id ByteArray)
    (name : ByteArray) (bits count : ℕ) (l : List (List E × E))
    (hl : recordSeedsW (m := Id) h .two name bits count = some l) :
    spellSeedL bits count (seedOfC bits count l) = l :=
  spell_seedOfC bits count l (recordSeedsW_shaped h name bits count l hl)

/-- Two lists of as many seeds, all with points of k coordinates, that are alike when laid flat are
one list. -/
theorem flat_inj (k : ℕ) : ∀ l l' : List (List E × E), (∀ y ∈ l, y.1.length = k) →
    (∀ y ∈ l', y.1.length = k) → l.length = l'.length →
    (l.flatMap fun y => y.1 ++ [y.2]) = (l'.flatMap fun y => y.1 ++ [y.2]) → l = l'
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, hl, _ => absurd hl (by simp)
  | _ :: _, [], _, _, hl, _ => absurd hl (by simp)
  | x :: l, y :: l', hx, hy, hl, h => by
    rw [List.flatMap_cons, List.flatMap_cons] at h
    have e1 : x.1.length = y.1.length := by
      rw [hx x List.mem_cons_self, hy y List.mem_cons_self]
    obtain ⟨h1, h2⟩ := List.append_inj h (by
      simp only [List.length_append, List.length_cons, List.length_nil, e1])
    obtain ⟨h3, h4⟩ := List.append_inj h1 e1
    have e : x = y := Prod.ext h3 (List.cons.inj h4).1
    rw [e, flat_inj k l l' (fun z hz => hx z (List.mem_cons_of_mem _ hz))
      (fun z hz => hy z (List.mem_cons_of_mem _ hz)) (Nat.succ.inj hl) h2]

/-- Laid flat, a list of seeds with points of k coordinates has k + 1 elements a seed. -/
theorem flat_length (k : ℕ) : ∀ l : List (List E × E), (∀ y ∈ l, y.1.length = k) →
    (l.flatMap fun y => y.1 ++ [y.2]).length = l.length * (k + 1)
  | [], _ => by simp
  | x :: l, hx => by
    have ih := flat_length k l fun z hz => hx z (List.mem_cons_of_mem _ hz)
    rw [List.flatMap_cons, List.length_append, ih, List.length_append, hx x List.mem_cons_self]
    simp only [List.length_cons, List.length_nil]
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- **The flat spelling is one to one.** -/
theorem spellSeed_inj : Function.Injective (spellSeed lg s) := fun ρ ρ' h =>
  spellSeedL_inj lg s (flat_inj lg _ _ (fun y hy => ((shaped_spell lg s ρ).2 y hy).1)
    (fun y hy => ((shaped_spell lg s ρ').2 y hy).1)
    ((shaped_spell lg s ρ).1.trans (shaped_spell lg s ρ').1.symm) h)

/-- The flat list's length hangs on the two numbers alone. -/
theorem spellSeed_length (ρ : Fin s → (Fin lg → GE) × NZ) :
    (spellSeed lg s ρ).length = s * (lg + 1) := by
  unfold spellSeed
  rw [flat_length lg _ fun y hy => ((shaped_spell lg s ρ).2 y hy).1, (shaped_spell lg s ρ).1]

/-- **On lists of a record's shape, "typed, then spelled flat" gives the list laid flat.** -/
theorem spellSeed_seedOfC (l : List (List E × E)) (hl : SeedsShaped lg s l) :
    spellSeed lg s (seedOfC lg s l) = l.flatMap fun y => y.1 ++ [y.2] := by
  unfold spellSeed
  rw [spell_seedOfC lg s l hl]

/-- The typed form of what the text of `recordSeeds` returns, spelled flat, is what it returned,
laid flat: at every plain hash. -/
theorem spellSeed_recordSeedsW (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → Id ByteArray)
    (name : ByteArray) (bits count : ℕ) (l : List (List E × E))
    (hl : recordSeedsW (m := Id) h .two name bits count = some l) :
    spellSeed bits count (seedOfC bits count l) = l.flatMap fun y => y.1 ++ [y.2] :=
  spellSeed_seedOfC bits count l (recordSeedsW_shaped h name bits count l hl)

/-- The same of the program's own `recordSeeds`. -/
theorem spellSeed_recordSeeds (name : ByteArray) (bits count : ℕ) (l : List (List E × E))
    (hl : recordSeeds .two name bits count = some l) :
    spellSeed bits count (seedOfC bits count l) = l.flatMap fun y => y.1 ++ [y.2] :=
  spellSeed_recordSeedsW Fmt.formatHash name bits count l ((recordSeedsW_H .two name bits count).trans hl)

/-- The same of the twin of `recordSeeds` with the hash as an argument, at every plain hash. -/
theorem spellSeed_twin (h : OnBytes.TwoPort.M.HashM Id) (name : ByteArray) (bits count : ℕ)
    (l : List (List E × E))
    (hl : OnBytes.TwoPort.M.recordSeeds (m := Id) h .two name bits count = some l) :
    spellSeed bits count (seedOfC bits count l) = l.flatMap fun y => y.1 ++ [y.2] :=
  spellSeed_recordSeedsW h name bits count l
    ((twin_recordSeeds h .two name bits count).symm.trans hl)

end OnBytes.K.IdTable

#print axioms OnBytes.K.IdTable.seedOf1C_spell
#print axioms OnBytes.K.IdTable.seedOfC_spell
#print axioms OnBytes.K.IdTable.spellSeedL_inj
#print axioms OnBytes.K.IdTable.shaped_spell
#print axioms OnBytes.K.IdTable.spell_seedOfC
#print axioms OnBytes.K.IdTable.recordSeedsW_shaped
#print axioms OnBytes.K.IdTable.spell_recordSeedsW
#print axioms OnBytes.K.IdTable.flat_inj
#print axioms OnBytes.K.IdTable.flat_length
#print axioms OnBytes.K.IdTable.spellSeed_inj
#print axioms OnBytes.K.IdTable.spellSeed_length
#print axioms OnBytes.K.IdTable.spellSeed_seedOfC
#print axioms OnBytes.K.IdTable.spellSeed_recordSeedsW
#print axioms OnBytes.K.IdTable.spellSeed_recordSeeds
#print axioms OnBytes.K.IdTable.spellSeed_twin
