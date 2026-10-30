-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/Room.lean: HOW THE CODE SWITCH's HONEST TEXT READS COINS,
SECOND PART: reads and cuts RETURN where the counts leave room; the base field's likes of the laws
in Honest/K2/Law/Reads.lean; a read by number against the shared sending's total readers `K1.ce` and
`K1.cf` (Honest/K1/Coins.lean). Statements and proofs; no definition.

  `mapM_length`, `mapM_of_all`   what `List.mapM` returns is as long as the list; it returns where
                 the function returns at every member
  `cut_fAt`, `cut_of_le`   coin number i of a cut, in the base field; a cut returns where the counts
                 leave room
  `fs_at`, `es_beyond`, `fs_beyond`   entry i of the n coins read; from n on the array yields its
                 default
  `es_of_le`, `fs_of_le`   a read of many coins returns where the count leaves room
  `eAt_ce`, `fAt_cf`   a coin that a read by number returns is what the total reader yields
  `ce_cast`, `cf_cast`   the total readers do not see under which term the count is written

Limits. Which coin is READ where: no sentence on what a coin is for. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.Reads
import Johnson.Desc.ProofFile.Honest.K1.Coins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Reads

/-- What `List.mapM` returns is as long as the list. -/
theorem mapM_length {α β : Type} (g : α → Except String β) : ∀ (l : List α) (r : List β),
    l.mapM g = .ok r → r.length = l.length
  | [], r, h => by
    rw [List.mapM_nil] at h
    obtain rfl : [] = r := Except.ok.inj h
    rfl
  | x :: l, r, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, _, h⟩ := bind_ok h
    obtain ⟨r', h2, h⟩ := bind_ok h
    obtain rfl : y :: r' = r := Except.ok.inj h
    rw [List.length_cons, List.length_cons, mapM_length g l r' h2]

/-- `List.mapM` returns where the function returns at every member. -/
theorem mapM_of_all {α β : Type} (g : α → Except String β) : ∀ l : List α,
    (∀ a, a ∈ l → ∃ b, g a = .ok b) → ∃ r, l.mapM g = .ok r
  | [], _ => ⟨[], List.mapM_nil⟩
  | x :: l, h => by
    obtain ⟨y, hy⟩ := h x List.mem_cons_self
    obtain ⟨r, hr⟩ := mapM_of_all g l fun a ha => h a (List.mem_cons_of_mem _ ha)
    refine ⟨y :: r, ?_⟩
    rw [List.mapM_cons, hy, hr]
    rfl

/-- Coin number i of a cut from a on is coin number a + i: the base field. -/
theorem cut_fAt {d : Due} {c : Cs d} {a n : Due} {c' : Cs n} (h : c.cut a n = some c') {i : Nat}
    {x : Cb.Gl.F} (hx : c'.fAt i = .ok x) : c.fAt (a.f + i) = .ok x := by
  obtain ⟨hi, rfl⟩ := fAt_ok hx
  unfold Cs.cut at h
  split at h
  · rename_i hc
    obtain rfl := Option.some.inj h
    exact fAt_of_lt c (by have := hc.1; omega)
  · cases h

/-- A cut returns where the counts leave room. -/
theorem cut_of_le {d : Due} (c : Cs d) {a n : Due} (hf : a.f + n.f ≤ d.f) (he : a.e + n.e ≤ d.e) :
    ∃ c', c.cut a n = some c' :=
  ⟨_, dif_pos ⟨hf, he⟩⟩

/-- Entry i of the n coins read from number a on is coin number a + i: the base field. -/
theorem fs_at {s : Stretch} {a n : Nat} {A : Array Cb.Gl.F} (h : s.fs a n = .ok A) {i : Nat}
    (hi : i < n) (z : Cb.Gl.F) : s.coins.fAt (a + i) = .ok (A.getD i z) := by
  obtain ⟨l, hl, rfl⟩ := map_ok h
  obtain ⟨b, hb, hg⟩ := mapM_at _ _ _ hl i i (range_at hi)
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, hb, Option.getD_some]
  exact hg

/-- From n on the array of n coins yields the default. -/
theorem es_beyond {s : Stretch} {a n : Nat} {A : Array Cb.Gl.E} (h : s.es a n = .ok A) {i : Nat}
    (hi : n ≤ i) (z : Cb.Gl.E) : A.getD i z = z := by
  obtain ⟨l, hl, rfl⟩ := map_ok h
  have hn : l.length = n := by rw [mapM_length _ _ _ hl, List.length_range]
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_eq_none (by rw [hn]; exact hi), Option.getD_none]

/-- The like of the base field. -/
theorem fs_beyond {s : Stretch} {a n : Nat} {A : Array Cb.Gl.F} (h : s.fs a n = .ok A) {i : Nat}
    (hi : n ≤ i) (z : Cb.Gl.F) : A.getD i z = z := by
  obtain ⟨l, hl, rfl⟩ := map_ok h
  have hn : l.length = n := by rw [mapM_length _ _ _ hl, List.length_range]
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_eq_none (by rw [hn]; exact hi), Option.getD_none]

/-- A read of many coins returns where the count leaves room. -/
theorem es_of_le (s : Stretch) {a n : Nat} (h : a + n ≤ s.due.e) : ∃ A, s.es a n = .ok A := by
  obtain ⟨l, hl⟩ := mapM_of_all (fun i => s.coins.eAt (a + i)) (List.range n) fun i hi =>
    ⟨_, eAt_of_lt s.coins (by have := List.mem_range.1 hi; omega)⟩
  exact ⟨l.toArray, congrArg (Except.map List.toArray) hl⟩

/-- The like of the base field. -/
theorem fs_of_le (s : Stretch) {a n : Nat} (h : a + n ≤ s.due.f) : ∃ A, s.fs a n = .ok A := by
  obtain ⟨l, hl⟩ := mapM_of_all (fun i => s.coins.fAt (a + i)) (List.range n) fun i hi =>
    ⟨_, fAt_of_lt s.coins (by have := List.mem_range.1 hi; omega)⟩
  exact ⟨l.toArray, congrArg (Except.map List.toArray) hl⟩

/-- A coin that a read by number returns is what the total reader yields at that number. -/
theorem eAt_ce {d : Due} {c : Cs d} {i : Nat} {x : Cb.Gl.E} (h : c.eAt i = .ok x) :
    K1.ce c i = x := by
  obtain ⟨hi, rfl⟩ := eAt_ok h
  exact dif_pos hi

/-- The like of the base field. -/
theorem fAt_cf {d : Due} {c : Cs d} {i : Nat} {x : Cb.Gl.F} (h : c.fAt i = .ok x) :
    K1.cf c i = x := by
  obtain ⟨hi, rfl⟩ := fAt_ok h
  exact dif_pos hi

/-- The total reader does not see under which term the count is written. -/
theorem ce_cast {d d' : Due} (h : d = d') (c : Cs d) (i : Nat) : K1.ce (h ▸ c) i = K1.ce c i := by
  subst h
  rfl

/-- The like of the base field. -/
theorem cf_cast {d d' : Due} (h : d = d') (c : Cs d) (i : Nat) : K1.cf (h ▸ c) i = K1.cf c i := by
  subst h
  rfl

end ProofFile.Honest.K2.Reads

#print axioms ProofFile.Honest.K2.Reads.mapM_length
#print axioms ProofFile.Honest.K2.Reads.mapM_of_all
#print axioms ProofFile.Honest.K2.Reads.cut_fAt
#print axioms ProofFile.Honest.K2.Reads.cut_of_le
#print axioms ProofFile.Honest.K2.Reads.fs_at
#print axioms ProofFile.Honest.K2.Reads.es_beyond
#print axioms ProofFile.Honest.K2.Reads.fs_beyond
#print axioms ProofFile.Honest.K2.Reads.es_of_le
#print axioms ProofFile.Honest.K2.Reads.fs_of_le
#print axioms ProofFile.Honest.K2.Reads.eAt_ce
#print axioms ProofFile.Honest.K2.Reads.fAt_cf
#print axioms ProofFile.Honest.K2.Reads.ce_cast
#print axioms ProofFile.Honest.K2.Reads.cf_cast
