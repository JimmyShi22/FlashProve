-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/Reads.lean: HOW THE CODE SWITCH's HONEST TEXT READS COINS:
small laws on `Stretch.es`, `Stretch.fs` and `Stretch.cut` (Honest/K2/Part.lean) and on `Cs.eAt`,
`Cs.fAt` and `Cs.cut` (Honest/Frame.lean). Statements and proofs; no definition.

  `bind_ok`, `bind_ok'`, `bind_error`, `ite_eq`, `map_ok`   a result that is no refusal, or is one,
                 read back through one step
  `mapM_at`      member number i of what `List.mapM` returns
  `mapM_again`   where one function returns at every member of a list, and a second returns wherever
                 the first does, the second returns on the list
  `range_at`     member number i of `List.range n`
  `eAt_ok`, `eAt_of_lt`, `fAt_ok`, `fAt_of_lt`   a read returns below the count, and there alone
  `cut_eAt`, `cut_again`   coin number i of a cut is coin number a + i; whether a cut returns hangs
                 on the counts alone
  `stretch_cut_ok`, `stretch_cut_of`   the like for a stretch
  `es_at`        entry i of the coins read from number a on is coin number a + i
  `es_again`, `fs_again`   whether a read of many coins returns hangs on the count alone

Limits. Which coin is READ where: no sentence on what a coin is for. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Part

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Reads

/-! ## 1 Results, read back through one step -/

/-- A step that returns: its first half returned, and its second half returned on that. -/
theorem bind_ok' {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- The same, in the monad's own sign. -/
theorem bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b :=
  bind_ok' h

/-- A step that refuses: its first half refused, or returned and the second half refused. -/
theorem bind_error {α β : Type} {x : Except String α} {f : α → Except String β} {e : String}
    (h : (x >>= f) = .error e) : x = .error e ∨ ∃ a, x = .ok a ∧ f a = .error e := by
  cases x with
  | error e' =>
    cases h
    exact Or.inl rfl
  | ok a => exact Or.inr ⟨a, rfl, h⟩

/-- A value that is told by a test: the test holds and it is the first, or not and the second. -/
theorem ite_eq {α : Type} {c : Prop} [Decidable c] {x y z : α} (h : (if c then x else y) = z) :
    (c ∧ x = z) ∨ (¬ c ∧ y = z) := by
  by_cases hc : c
  · rw [if_pos hc] at h
    exact Or.inl ⟨hc, h⟩
  · rw [if_neg hc] at h
    exact Or.inr ⟨hc, h⟩

/-- A result that was mapped and is no refusal. -/
theorem map_ok {α β : Type} {x : Except String α} {f : α → β} {b : β}
    (h : x.map f = .ok b) : ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, Except.ok.inj h⟩

/-- Member number i of what `List.mapM` returns is what the function returns at member number i. -/
theorem mapM_at {α β : Type} (g : α → Except String β) : ∀ (l : List α) (r : List β),
    l.mapM g = .ok r → ∀ (i : Nat) (a : α), l[i]? = some a → ∃ b, r[i]? = some b ∧ g a = .ok b
  | [], _, _, _, _, hi => by cases hi
  | x :: l, r, h, i, a, hi => by
    rw [List.mapM_cons] at h
    obtain ⟨y, h1, h⟩ := bind_ok h
    obtain ⟨r', h2, h⟩ := bind_ok h
    obtain rfl : y :: r' = r := Except.ok.inj h
    cases i with
    | zero =>
      obtain rfl : x = a := Option.some.inj hi
      exact ⟨y, rfl, h1⟩
    | succ j => exact mapM_at g l r' h2 j a hi

/-- Where g returns on a list, and g' returns at every member at which g does, g' returns on the
list. -/
theorem mapM_again {α β γ : Type} (g : α → Except String β) (g' : α → Except String γ) :
    ∀ (l : List α) (r : List β), l.mapM g = .ok r →
      (∀ a b, a ∈ l → g a = .ok b → ∃ c, g' a = .ok c) → ∃ r', l.mapM g' = .ok r'
  | [], _, _, _ => ⟨[], List.mapM_nil⟩
  | x :: l, r, h, hg => by
    rw [List.mapM_cons] at h
    obtain ⟨y, h1, h⟩ := bind_ok h
    obtain ⟨r₁, h2, _⟩ := bind_ok h
    obtain ⟨c, hc⟩ := hg x y List.mem_cons_self h1
    obtain ⟨r', hr⟩ := mapM_again g g' l r₁ h2 fun a b ha => hg a b (List.mem_cons_of_mem _ ha)
    refine ⟨c :: r', ?_⟩
    rw [List.mapM_cons, hc, hr]
    rfl

/-- Member number i of the numbers below n. -/
theorem range_at {n i : Nat} (h : i < n) : (List.range n)[i]? = some i := by
  rw [List.getElem?_eq_getElem (by rw [List.length_range]; exact h), List.getElem_range]

/-! ## 2 One coin -/

/-- A read of the extension field that returns: the number lies below the count, and the value is
the coin. -/
theorem eAt_ok {d : Due} {c : Cs d} {i : Nat} {x : Cb.Gl.E} (h : c.eAt i = .ok x) :
    ∃ h' : i < d.e, c.e ⟨i, h'⟩ = x := by
  unfold Cs.eAt at h
  split at h
  · rename_i h'
    exact ⟨h', Except.ok.inj h⟩
  · cases h

/-- Below the count the read returns the coin. -/
theorem eAt_of_lt {d : Due} (c : Cs d) {i : Nat} (h : i < d.e) : c.eAt i = .ok (c.e ⟨i, h⟩) :=
  dif_pos h

/-- The like of the base field. -/
theorem fAt_ok {d : Due} {c : Cs d} {i : Nat} {x : Cb.Gl.F} (h : c.fAt i = .ok x) :
    ∃ h' : i < d.f, c.f ⟨i, h'⟩ = x := by
  unfold Cs.fAt at h
  split at h
  · rename_i h'
    exact ⟨h', Except.ok.inj h⟩
  · cases h

/-- The like of the base field. -/
theorem fAt_of_lt {d : Due} (c : Cs d) {i : Nat} (h : i < d.f) : c.fAt i = .ok (c.f ⟨i, h⟩) :=
  dif_pos h

/-! ## 3 A cut -/

/-- **Coin number i of a cut from a on is coin number a + i.** -/
theorem cut_eAt {d : Due} {c : Cs d} {a n : Due} {c' : Cs n} (h : c.cut a n = some c') {i : Nat}
    {x : Cb.Gl.E} (hx : c'.eAt i = .ok x) : c.eAt (a.e + i) = .ok x := by
  obtain ⟨hi, rfl⟩ := eAt_ok hx
  unfold Cs.cut at h
  split at h
  · rename_i hc
    obtain rfl := Option.some.inj h
    exact eAt_of_lt c (by have := hc.2; omega)
  · cases h

/-- Whether a cut returns hangs on the counts alone. -/
theorem cut_again {d : Due} {c : Cs d} {a n : Due} {c' : Cs n} (h : c.cut a n = some c')
    (c₂ : Cs d) : ∃ c₂', c₂.cut a n = some c₂' := by
  unfold Cs.cut at h
  split at h
  · rename_i hc
    exact ⟨_, dif_pos hc⟩
  · cases h

/-- A stretch's cut that returns is the coins' cut, with its count. -/
theorem stretch_cut_ok {d : Due} {c : Cs d} {a n : Due} {k : Stretch}
    (h : (Stretch.of c).cut a n = .ok k) : ∃ c' : Cs n, c.cut a n = some c' ∧ k = ⟨n, c'⟩ := by
  cases hc : c.cut a n with
  | none =>
    have h' : (Except.error "coins are asked beyond the count" : Except String Stretch) =
        .ok k := by
      rw [← h]
      show _ = (match c.cut a n with
        | some c => Except.ok (⟨n, c⟩ : Stretch)
        | none => .error "coins are asked beyond the count")
      rw [hc]
    cases h'
  | some c' =>
    refine ⟨c', rfl, ?_⟩
    have h' : (Except.ok ⟨n, c'⟩ : Except String Stretch) = .ok k := by
      rw [← h]
      show _ = (match c.cut a n with
        | some c => Except.ok (⟨n, c⟩ : Stretch)
        | none => .error "coins are asked beyond the count")
      rw [hc]
    exact (Except.ok.inj h').symm

/-- Where the coins' cut returns, the stretch's does. -/
theorem stretch_cut_of {d : Due} {c : Cs d} {a n : Due} {c' : Cs n} (h : c.cut a n = some c') :
    (Stretch.of c).cut a n = .ok ⟨n, c'⟩ := by
  show (match c.cut a n with
    | some c => Except.ok (⟨n, c⟩ : Stretch)
    | none => .error "coins are asked beyond the count") = _
  rw [h]

/-! ## 4 Many coins at once -/

/-- **Entry i of the n coins read from number a on is coin number a + i.** z: any value: below n the
array's default is not met. -/
theorem es_at {s : Stretch} {a n : Nat} {A : Array Cb.Gl.E} (h : s.es a n = .ok A) {i : Nat}
    (hi : i < n) (z : Cb.Gl.E) : s.coins.eAt (a + i) = .ok (A.getD i z) := by
  obtain ⟨l, hl, rfl⟩ := map_ok h
  obtain ⟨b, hb, hg⟩ := mapM_at _ _ _ hl i i (range_at hi)
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, hb, Option.getD_some]
  exact hg

/-- Whether a read of many coins returns hangs on the count alone. -/
theorem es_again {s s' : Stretch} (hd : s'.due = s.due) {a m : Nat} {A : Array Cb.Gl.E}
    (h : s.es a m = .ok A) : ∃ A', s'.es a m = .ok A' := by
  obtain ⟨l, hl, _⟩ := map_ok h
  obtain ⟨l', hl'⟩ := mapM_again _ (fun i => s'.coins.eAt (a + i)) _ _ hl fun i b _ hb => by
    obtain ⟨h', _⟩ := eAt_ok hb
    exact ⟨_, eAt_of_lt s'.coins (by rw [hd]; exact h')⟩
  exact ⟨l'.toArray, congrArg (Except.map List.toArray) hl'⟩

/-- The like of the base field. -/
theorem fs_again {s s' : Stretch} (hd : s'.due = s.due) {a m : Nat} {A : Array Cb.Gl.F}
    (h : s.fs a m = .ok A) : ∃ A', s'.fs a m = .ok A' := by
  obtain ⟨l, hl, _⟩ := map_ok h
  obtain ⟨l', hl'⟩ := mapM_again _ (fun i => s'.coins.fAt (a + i)) _ _ hl fun i b _ hb => by
    obtain ⟨h', _⟩ := fAt_ok hb
    exact ⟨_, fAt_of_lt s'.coins (by rw [hd]; exact h')⟩
  exact ⟨l'.toArray, congrArg (Except.map List.toArray) hl'⟩

end ProofFile.Honest.K2.Reads

#print axioms ProofFile.Honest.K2.Reads.bind_ok'
#print axioms ProofFile.Honest.K2.Reads.bind_ok
#print axioms ProofFile.Honest.K2.Reads.bind_error
#print axioms ProofFile.Honest.K2.Reads.ite_eq
#print axioms ProofFile.Honest.K2.Reads.map_ok
#print axioms ProofFile.Honest.K2.Reads.mapM_at
#print axioms ProofFile.Honest.K2.Reads.mapM_again
#print axioms ProofFile.Honest.K2.Reads.range_at
#print axioms ProofFile.Honest.K2.Reads.eAt_ok
#print axioms ProofFile.Honest.K2.Reads.eAt_of_lt
#print axioms ProofFile.Honest.K2.Reads.fAt_ok
#print axioms ProofFile.Honest.K2.Reads.fAt_of_lt
#print axioms ProofFile.Honest.K2.Reads.cut_eAt
#print axioms ProofFile.Honest.K2.Reads.cut_again
#print axioms ProofFile.Honest.K2.Reads.stretch_cut_ok
#print axioms ProofFile.Honest.K2.Reads.stretch_cut_of
#print axioms ProofFile.Honest.K2.Reads.es_at
#print axioms ProofFile.Honest.K2.Reads.es_again
#print axioms ProofFile.Honest.K2.Reads.fs_again
