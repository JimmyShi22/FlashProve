-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/WholeEntries.lean: the rounds' data of a whole file keep the entries of the rounds from
which they are made.

The data of a file with three joined chains (`WholeD.of`, OnBytes/Maker/WholeOf.lean) are made from
three lists of rounds (`Three.Whole.of`, OnBytes/Three/Data.lean). Here: round by round they hold
the same entry of the plan; the first chain comes without its last round (in a file's first chain
that is the seal; here it is `dropLast`). So a condition on entries that holds of the rounds of the
three chains holds of the data. Of the trees less is stated for the whole file: a bound on their
number a round. A description of a chain that passes the format's test
(`Fmt.Spec.ok`, Fmt/Rules8.lean) has at most 64 bits of work and positions of fewer than 64 bits in
every round.

Main names:
  `sentBefore_length`, `rdsFromL_entry`, `rdsFromL_trees`: on one chain.
  `of_entry₁`, `of_entry₂`, `of_entry₃`: the entries of the data's three lists are those of the
    three lists of rounds, the first without its last.
  `of_all₁`, `of_all₂`, `of_all₃`: a condition on entries carries over.
  `of_trees`: if no message of the three lists has more than n roots among its items, no round's
    data have more than n trees. (The equation, as many trees as roots, is stated of one chain's
    elder data alone: `rdsFromL_trees`.)
  `fits_roots`, `fits_trees`: three lists that pass the test `Three.Whole.fits` at n have at most n
    roots a message, and their data at most n trees a round.
  `roundsOk_work`, `ok_work`: in a description that passes the format's test every round has at most
    64 bits of work and positions of fewer than 64 bits.

Limits: that the three lists of rounds are those of a description that passes the test is a
hypothesis of whoever uses `ok_work` with the others. The proof of `fits_roots` takes the test
`Three.Whole.fits` apart as six clauses, of which it uses the first. This file imports
OnBytes/Maker/WholeOf.lean and, through it, OnBytes/Three/Data.lean: it can stand only where these
stand. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.Maker.WholeOf

set_option autoImplicit false

namespace OnBytes.Flat
open OnBytes.Params (Rounds)
open OnBytes.Three OnBytes.Maker

theorem foldl_push_size (R : Rounds) : ∀ (n : Nat) (acc : Array Nat),
    (R.foldl (fun (a : Nat × Array Nat) r =>
      (a.1 + r.1.items.countP (· == .root), a.2.push a.1)) (n, acc)).2.size =
      acc.size + R.length := by
  induction R with
  | nil => intro n acc; rfl
  | cons r R ih =>
    intro n acc
    rw [List.foldl_cons, ih, Array.size_push, List.length_cons]
    show acc.size + 1 + R.length = acc.size + (R.length + 1)
    omega

theorem sentBefore_length (R : Rounds) : (sentBefore R).length = R.length := by
  unfold sentBefore
  rw [Array.length_toList, foldl_push_size]
  simp

/-- A map that reads the first argument alone, along a second list of the same length. -/
theorem wholeEntries_zipWith_left {α β γ δ : Type} (f : α → β → γ) (g : γ → δ) (h : α → δ)
    (e : ∀ a b, g (f a b) = h a) :
    ∀ (l : List α) (m : List β), m.length = l.length → (List.zipWith f l m).map g = l.map h
  | [], _, _ => by simp
  | _ :: _, [], hm => by simp at hm
  | a :: l, b :: m, hm => by
    rw [List.zipWith_cons_cons, List.map_cons, List.map_cons, e,
      wholeEntries_zipWith_left f g h e l m (by simpa using hm)]

theorem rdsFromL_entry (all : List (Nat × Fmt.Shape × Nat × Nat)) (t₁ t₂ here base first : Nat)
    (R : Rounds) : (rdsFromL all t₁ t₂ here base first R).map (·.entry) = R.map (·.1.entry) :=
  wholeEntries_zipWith_left (rdOf all t₁ t₂ here base first) (fun d : RDL => d.entry)
    (fun r : Fmt.Round × List Fmt.Stored => r.1.entry) (fun _ _ => rfl) R _ (sentBefore_length R)

theorem rdsFromL_trees (all : List (Nat × Fmt.Shape × Nat × Nat)) (t₁ t₂ here base first : Nat)
    (R : Rounds) : (rdsFromL all t₁ t₂ here base first R).map (·.trees.length) =
      R.map fun r => r.1.items.countP (· == .root) :=
  wholeEntries_zipWith_left (rdOf all t₁ t₂ here base first) (fun d : RDL => d.trees.length)
    (fun r : Fmt.Round × List Fmt.Stored => r.1.items.countP (· == Fmt.Item.root))
    (fun _ _ => by simp [rdOf]) R _ (sentBefore_length R)

variable (a : ℕ) (R₁ R₂ R₃ : Rounds)

theorem of_entry₁ : (WholeD.of a (Whole.of R₁ R₂ R₃)).ds₁.map (·.entry) =
    (R₁.map (·.1.entry)).dropLast := by
  show (((Whole.of R₁ R₂ R₃).ds₁.dropLast).map rdtOf).map (·.entry) = _
  rw [List.map_map, ← List.map_dropLast]
  have e : ((fun d : RDT => d.entry) ∘ rdtOf) = fun d : RDL => d.entry := rfl
  rw [e, List.map_dropLast, List.map_dropLast]
  exact congrArg List.dropLast (rdsFromL_entry _ _ _ _ _ _ R₁)

theorem of_entry₂ : (WholeD.of a (Whole.of R₁ R₂ R₃)).ds₂.map (·.entry) = R₂.map (·.1.entry) := by
  show (((Whole.of R₁ R₂ R₃).ds₂).map rdtOf).map (·.entry) = _
  rw [List.map_map]
  exact rdsFromL_entry _ _ _ _ _ _ R₂

theorem of_entry₃ : (WholeD.of a (Whole.of R₁ R₂ R₃)).ds₃.map (·.entry) = R₃.map (·.1.entry) := by
  show (((Whole.of R₁ R₂ R₃).ds₃).map rdtOf).map (·.entry) = _
  rw [List.map_map]
  exact rdsFromL_entry _ _ _ _ _ _ R₃

/-- From an equation of the lists of entries: a condition on entries carries over. -/
theorem all_of_map {α β γ : Type} (f : α → γ) (g : β → γ) (p : γ → Prop) {l : List α} {m : List β}
    (e : l.map f = m.map g) (h : ∀ y ∈ m, p (g y)) : ∀ x ∈ l, p (f x) := by
  intro x hx
  have h1 : f x ∈ m.map g := e ▸ List.mem_map_of_mem hx
  obtain ⟨y, hy, ey⟩ := List.mem_map.1 h1
  exact ey ▸ h y hy

theorem of_all₁ (p : Fmt.Entry → Prop) (h : ∀ r ∈ R₁, p r.1.entry) :
    ∀ d ∈ (WholeD.of a (Whole.of R₁ R₂ R₃)).ds₁, p d.entry := by
  intro d hd
  have h1 : d.entry ∈ (R₁.map (·.1.entry)).dropLast :=
    of_entry₁ a R₁ R₂ R₃ ▸ List.mem_map_of_mem (f := (·.entry)) hd
  obtain ⟨r, hr, er⟩ := List.mem_map.1 (List.mem_of_mem_dropLast h1)
  exact er ▸ h r hr

theorem of_all₂ (p : Fmt.Entry → Prop) (h : ∀ r ∈ R₂, p r.1.entry) :
    ∀ d ∈ (WholeD.of a (Whole.of R₁ R₂ R₃)).ds₂, p d.entry :=
  all_of_map (fun d : RDT => d.entry) (fun r : Fmt.Round × List Fmt.Stored => r.1.entry) p
    (of_entry₂ a R₁ R₂ R₃) h

theorem of_all₃ (p : Fmt.Entry → Prop) (h : ∀ r ∈ R₃, p r.1.entry) :
    ∀ d ∈ (WholeD.of a (Whole.of R₁ R₂ R₃)).ds₃, p d.entry :=
  all_of_map (fun d : RDT => d.entry) (fun r : Fmt.Round × List Fmt.Stored => r.1.entry) p
    (of_entry₃ a R₁ R₂ R₃) h

/-- If no message of the three lists has more than n roots, no round's data have more than n
trees. -/
theorem of_trees (n : ℕ) (h : ∀ r ∈ R₁ ++ (R₂ ++ R₃), r.1.items.countP (· == .root) ≤ n) :
    ∀ d ∈ (WholeD.of a (Whole.of R₁ R₂ R₃)).ds₁ ++ ((WholeD.of a (Whole.of R₁ R₂ R₃)).ds₂ ++
      (WholeD.of a (Whole.of R₁ R₂ R₃)).ds₃), d.trees.length ≤ n := by
  have key : ∀ (all : List (Nat × Fmt.Shape × Nat × Nat)) (t₁ t₂ here base first : Nat)
      (R : Rounds), (∀ r ∈ R, r.1.items.countP (· == .root) ≤ n) →
      ∀ d ∈ rdsFromL all t₁ t₂ here base first R, d.trees.length ≤ n :=
    fun all t₁ t₂ here base first R hR =>
      all_of_map (fun d : RDL => d.trees.length)
        (fun r : Fmt.Round × List Fmt.Stored => r.1.items.countP (· == Fmt.Item.root)) (· ≤ n)
        (rdsFromL_trees all t₁ t₂ here base first R) hR
  intro d hd
  rcases List.mem_append.1 hd with h1 | h23
  · obtain ⟨x, hx, ex⟩ := List.mem_map.1 h1
    rw [← ex]
    exact key _ _ _ _ _ _ R₁ (fun r hr => h r (List.mem_append_left _ hr)) x
      (List.mem_of_mem_dropLast hx)
  · rcases List.mem_append.1 h23 with h2 | h3
    · obtain ⟨x, hx, ex⟩ := List.mem_map.1 h2
      rw [← ex]
      exact key _ _ _ _ _ _ R₂
        (fun r hr => h r (List.mem_append_right _ (List.mem_append_left _ hr))) x hx
    · obtain ⟨x, hx, ex⟩ := List.mem_map.1 h3
      rw [← ex]
      exact key _ _ _ _ _ _ R₃
        (fun r hr => h r (List.mem_append_right _ (List.mem_append_right _ hr))) x hx

/-- Three lists of rounds that pass the test on the limits of the map at n have no message with more
than n roots. -/
theorem fits_roots {n : ℕ} (h : Whole.fits R₁ R₂ R₃ n = true) :
    ∀ r ∈ R₁ ++ (R₂ ++ R₃), r.1.items.countP (· == .root) ≤ n := by
  simp only [Whole.fits, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at h1
  intro r hr
  rcases List.mem_append.1 hr with h' | h'
  · exact (h1.1 r h').1
  · rcases List.mem_append.1 h' with h'' | h''
    · exact (h1.2.1 r h'').1
    · exact (h1.2.2 r h'').1

/-- So their data have at most n trees a round. -/
theorem fits_trees {n : ℕ} (h : Whole.fits R₁ R₂ R₃ n = true) :
    ∀ d ∈ (WholeD.of a (Whole.of R₁ R₂ R₃)).ds₁ ++ ((WholeD.of a (Whole.of R₁ R₂ R₃)).ds₂ ++
      (WholeD.of a (Whole.of R₁ R₂ R₃)).ds₃), d.trees.length ≤ n :=
  of_trees a R₁ R₂ R₃ n (fits_roots R₁ R₂ R₃ h)

/-- Every round of a list that passes the format's test on rounds has at most 64 bits of work and
positions of fewer than 64 bits. -/
theorem roundsOk_work (P : Fmt.Plan) (noRand : Bool) (firstTree : Nat) :
    ∀ (rs : List Fmt.Round) (after : Bool) (sent : Nat),
      Fmt.roundsOk P noRand firstTree after sent rs = true →
      ∀ r ∈ rs, r.entry.work ≤ 64 ∧ r.entry.logN < 64
  | [], _, _, _, _, hr => by cases hr
  | r :: rs, after, sent, h, x, hx => by
    unfold Fmt.roundsOk at h
    rw [Bool.and_eq_true] at h
    rcases List.mem_cons.1 hx with rfl | hx'
    · have h1 := h.1
      unfold Fmt.Round.ok at h1
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      exact ⟨by tauto, by tauto⟩
    · exact roundsOk_work P noRand firstTree rs _ _ h.2 x hx'

/-- The same of a description that passes the format's test. -/
theorem ok_work {S : Fmt.Spec} (h : S.ok = true) :
    ∀ r ∈ S.rounds, r.entry.work ≤ 64 ∧ r.entry.logN < 64 := by
  unfold Fmt.Spec.ok at h
  simp only [Bool.and_eq_true] at h
  exact roundsOk_work _ _ _ S.rounds _ _ h.1.1.2

end OnBytes.Flat
