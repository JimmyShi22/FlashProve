-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/OkSeedsOfKey.lean: the key that the program makes of a table passes the test that
every word of every seed is below the prime (`okSeeds`, OnBytes/Maker/OkView.lean).

Statements and proofs. No premise but that `tableKey` (OnBytes/Entry/Table.lean) returns the key:
none on the field, none on the table's answers. The format's draws take a word only if it is below
the prime of the field that they are given (`Fmt.Fld.tryWord`), or put 0 or 1 in its place; the
first field's prime is below the second's, which is the prime of the test.

Main theorems.
  `seeds_below`: the core, at any row of words: every seed of `count` draws of `Fmt.drawSeed f bits`
    has a factor and coordinates whose words are below the prime.
  `recordSeeds_below`: the seeds of a table's record (`recordSeeds`), at either field.
  `okSeeds_of_tableKey`: the key that `tableKey` returns passes `okSeeds`.

`tryWord_below`, `drawFN_below`, `drawE_below`, `drawNZ_below`, `times_every` and `drawSeed_below`
say again what OnBytes/Maker/Page/KeyCleanOf.lean [not in this library] holds (`tryWord_lt`,
`drawFN_lt`, `drawE_ok`,
`drawNZ_ok`, `times_all`, `drawSeed_ok`), at the prime of the test: that file stands above the files
that are to import this one.

What is not claimed. That a factor is not 0 (KeyCleanOf.lean [not in this library] has that).
Anything on the key's answers (`TableKey.record`), or that the seeds are those of the table that
anybody means. Nothing on a key that `tableKey` has not made. Nothing on how the seeds are
distributed. Nothing on soundness.


-/
import OnBytes.Maker.OkWordsOfRead
import OnBytes.TieK.PlaceOpen

set_option autoImplicit false

namespace OnBytes.Maker

/-! ## Three words below the prime -/

/-- The three words are below the prime of the field in which the program computes. -/
def Below3 (t : UInt64 × UInt64 × UInt64) : Prop := Below t.1 ∧ Below t.2.1 ∧ Below t.2.2

/-- They pass the program's test on an element of the extension field. -/
theorem Below3.okE {t : UInt64 × UInt64 × UInt64} (h : Below3 t) :
    OnBytes.okE (E.ofTriple t) = true := by
  show (OnBytes.okF t.1 && OnBytes.okF t.2.1 && OnBytes.okF t.2.2) = true
  rw [h.1.okF, h.2.1.okF, h.2.2.okF]
  rfl

/-! ## The draws -/

/-- A word that a field takes is below the prime. -/
theorem tryWord_below {f : Fmt.Fld} {w x : UInt64} (h : f.tryWord w = some x) : Below x := by
  refine Nat.lt_of_lt_of_le ?_ (p_le_two f)
  cases f with
  | one =>
    simp only [Fmt.Fld.tryWord] at h
    split at h
    · rename_i hlt
      obtain rfl := Option.some.inj h
      exact hlt
    · cases h
  | two =>
    simp only [Fmt.Fld.tryWord] at h
    split at h
    · rename_i hlt
      obtain rfl := Option.some.inj h
      exact hlt
    · cases h

theorem zero_below : Below 0 := by
  show (0 : UInt64).toNat < Fmt.Fld.two.p
  decide

theorem one_below : Below 1 := by
  show (1 : UInt64).toNat < Fmt.Fld.two.p
  decide

/-- An element of the base field as drawn, with at most n tries. -/
theorem drawFN_below (f : Fmt.Fld) : ∀ (n : ℕ) (row : Fmt.Row) (c : ℕ),
    Below (Fmt.drawFN f n row c).1
  | 0, _, _ => zero_below
  | n + 1, row, c => by
    show Below ((match f.tryWord (row c) with
      | some x => Fmt.Dr.pure x
      | none => Fmt.drawFN f n : Fmt.Dr UInt64) row (c + 1)).1
    cases h : f.tryWord (row c) with
    | some x => exact tryWord_below h
    | none => exact drawFN_below f n row (c + 1)

/-- An element of the extension field as drawn. -/
theorem drawE_below (f : Fmt.Fld) (row : Fmt.Row) (c : ℕ) : Below3 (Fmt.drawE f row c).1 :=
  ⟨drawFN_below f _ _ _, drawFN_below f _ _ _, drawFN_below f _ _ _⟩

/-- A factor as drawn. -/
theorem drawNZ_below (f : Fmt.Fld) (row : Fmt.Row) (c : ℕ) : Below3 (Fmt.drawNZ f row c).1 := by
  show Below3 ((if (Fmt.drawE f row c).1 = (0, 0, 0) then
      (Fmt.drawE f).bind fun e' => Fmt.Dr.pure (if e' = (0, 0, 0) then (1, 0, 0) else e')
      else Fmt.Dr.pure (Fmt.drawE f row c).1 : Fmt.Dr Fmt.Ext) row (Fmt.drawE f row c).2).1
  by_cases h : (Fmt.drawE f row c).1 = (0, 0, 0)
  · rw [if_pos h]
    show Below3 (if (Fmt.drawE f row (Fmt.drawE f row c).2).1 = (0, 0, 0) then (1, 0, 0)
        else (Fmt.drawE f row (Fmt.drawE f row c).2).1)
    by_cases h2 : (Fmt.drawE f row (Fmt.drawE f row c).2).1 = (0, 0, 0)
    · rw [if_pos h2]
      exact ⟨one_below, zero_below, zero_below⟩
    · rw [if_neg h2]
      exact drawE_below f _ _
  · rw [if_neg h]
    exact drawE_below f _ _

/-- What holds of every value of a draw holds of all values of the draw made n times. -/
theorem times_every {α : Type} {x : Fmt.Dr α} {P : α → Prop} (hx : ∀ row c, P (x row c).1) :
    ∀ (n : ℕ) (row : Fmt.Row) (c : ℕ), ∀ y ∈ (x.times n row c).1, P y
  | 0, _, _, _, hy => by cases hy
  | n + 1, row, c, y, hy => by
    have hy' : y ∈ (x row c).1 :: (x.times n row (x row c).2).1 := hy
    rcases List.mem_cons.1 hy' with rfl | h
    · exact hx row c
    · exact times_every hx n row _ y h

/-- A seed as drawn: its point's coordinates and its factor. -/
theorem drawSeed_below (f : Fmt.Fld) (v : ℕ) (row : Fmt.Row) (c : ℕ) :
    (∀ y ∈ (Fmt.drawSeed f v row c).1.1, Below3 y) ∧ Below3 (Fmt.drawSeed f v row c).1.2 :=
  ⟨times_every (drawE_below f) v row c, drawNZ_below f row _⟩

/-! ## The seeds -/

/-- **The core, at any row of words**: the seeds of `count` draws pass the program's tests. -/
theorem seeds_below (f : Fmt.Fld) (bits count : ℕ) (row : Fmt.Row) (c : ℕ) :
    ∀ x ∈ ((Fmt.drawSeed f bits).times count row c).1,
      okE (E.ofTriple x.2) = true ∧ ∀ y ∈ x.1, okE (E.ofTriple y) = true := by
  intro x hx
  obtain ⟨h1, h2⟩ := times_every (P := fun s : List Fmt.Ext × Fmt.Ext =>
    (∀ y ∈ s.1, Below3 y) ∧ Below3 s.2) (fun row c => drawSeed_below f bits row c) count row c x hx
  exact ⟨h2.okE, fun y hy => (h1 y hy).okE⟩

/-- The program's `recordSeeds` as a map over the round's value: an equation of two functions.
`recordSeeds` is unfolded while it stands alone, without arguments, and a letter q stands for the
round's value before the two texts are compared: written so that no checker need compute that value.
-/
theorem recordSeeds_asMap :
    recordSeeds = fun f name bits count =>
      ((⟨Fmt.recordLabel, Fmt.recordFirst name, 0⟩ : Fmt.Chain).query ByteArray.empty .seeds 0 0
        (Fmt.blocksFor (count * (bits * 18 + 36)))).map fun x =>
          (timesT (Fmt.drawSeed f bits) count (Fmt.rowOf x.2) 0).1.map fun y =>
            (y.1.map E.ofTriple, E.ofTriple y.2) := by
  delta recordSeeds
  funext f name bits count
  generalize Fmt.Chain.query _ _ _ _ _ _ = q
  cases q with
  | none => rfl
  | some p =>
    cases p
    rfl

/-- **The seeds of a table's record**, at either field. -/
theorem recordSeeds_below {f : Fmt.Fld} {name : ByteArray} {bits count : ℕ}
    {l : List (List E × E)} (h : recordSeeds f name bits count = some l) :
    ∀ x ∈ l, okE x.2 = true ∧ ∀ a ∈ x.1, okE a = true := by
  -- by the named equation `recordSeeds_asMap`, not by unfolding
  have h' : Option.map _ _ = some l :=
    (congrFun (congrFun (congrFun (congrFun recordSeeds_asMap f) name) bits) count).symm.trans h
  obtain ⟨cv, -, e⟩ := Option.map_eq_some_iff.1 h'
  · obtain rfl := e
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    rw [timesT_eq] at hs
    obtain ⟨s2, s1⟩ := seeds_below f bits count _ _ s hs
    refine ⟨s2, fun a ha => ?_⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
    exact s1 y hy

/-! ## The key -/

/-- **The key that `tableKey` returns passes the test on its seeds.** -/
theorem okSeeds_of_tableKey {f : Fmt.Fld} {cfg : ByteArray} {s : Params.IndexShape}
    {table : Params.TableName} {item : ℕ} {κ : TableKey}
    (h : tableKey f cfg s table item = some κ) : okSeeds κ = true := by
  obtain ⟨seeds, hs, rfl, -⟩ := TieK.tableKey_open _ _ _ _ _ _ h
  have hc : ∀ x ∈ seeds, okE x.2 = true ∧ ∀ a ∈ x.1, okE a = true := recordSeeds_below hs
  unfold okSeeds
  rw [List.all_eq_true]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
  show (okE x.2 && x.1.all okE) = true
  rw [(hc x hx).1, Bool.true_and, List.all_eq_true]
  exact (hc x hx).2

end OnBytes.Maker

#print axioms OnBytes.Maker.okSeeds_of_tableKey
#print axioms OnBytes.Maker.seeds_below
