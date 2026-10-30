-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/RunBefore.lean: what a run of `runC` has shown before a part. The
lemmas compute `Run.beforeAt` (Honest/Side.lean). At an address whose rounds form one contiguous
stretch of one chain, it is what the rounds produced before the stretch show (and, for the second
chain, also all rounds of the two earlier chains), in the form of `shownBy`
(Honest/Law/Rule/Shown.lean). These are `before_first`, `before_shared` and `before_second`.

  1  `takeWhile_stretch`, `any_of_mask`   on lists
  2  `shownIn_fst`, `shownBy_take`, `front_eq`   one chain
  3  `len_pos`, `any_laid`, `before_first`, `before_shared`, `before_second`   the file

That a whole chain's `shownIn` is `shownBy` is a hypothesis here, chain by chain. `shown_is`
(Honest/Law/Rule/Reads.lean) proves it where `RunOk` holds. All four lemmas of section 3 take that
`ready` has returned R, and that in each chain every `Step` declares as many oracle messages as its
entry counts roots. `before_shared` and `before_second` also take the description's test on the
places (`FileDescription.placesOk`): by it no earlier chain has a round at the address. `before_first` has
that hypothesis among its binders too, by the section's `include`, and does not use it.

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.RunAtFile
import Johnson.Desc.ProofFile.Honest.Law.Rule.Shown

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {Xi W Y W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 On lists -/

theorem takeWhile_stretch {α : Type} (f : α → Bool) (l : List α) (n : Nat)
    (h1 : ∀ x ∈ l.take n, f x = false) (h2 : ∀ x, (l.drop n).head? = some x → f x = true) :
    l.takeWhile (fun x => !f x) = l.take n := by
  have e : l = l.take n ++ l.drop n := (List.take_append_drop n l).symm
  have g : (l.drop n).takeWhile (fun x => !f x) = [] := by
    cases hd : l.drop n with
    | nil => rfl
    | cons x t =>
      have hx := h2 x (by rw [hd]; rfl)
      rw [List.takeWhile_cons_of_neg (by rw [hx]; exact Bool.false_ne_true)]
  calc l.takeWhile (fun x => !f x)
      = (l.take n ++ l.drop n).takeWhile (fun x => !f x) := by rw [← e]
    _ = l.take n := by
      rw [List.takeWhile_append_of_pos (fun x hx => by rw [h1 x hx]; rfl), g, List.append_nil]

theorem any_of_mask {α β : Type} {l : List α} {l' : List β} {f : α → Bool} {g : β → Bool}
    (h : l.map f = l'.map g) : l.any f = l'.any g := by
  have e1 : (l.map f).any id = l.any f := by rw [List.any_map]; rfl
  have e2 : (l'.map g).any id = l'.any g := by rw [List.any_map]; rfl
  rw [← e1, ← e2, h]

/-! ## 2 One chain -/

theorem shownIn_fst (ch : Nat) (l : List Played) (qs : List Read) :
    (shownIn ch l qs).map (·.1) = l := by
  unfold shownIn
  rw [List.map_map]
  exact numbered_fst l 0

theorem shownBy_take (ch : Nat) (tree : Nat → List Nat) : ∀ (l : List Played) (k n : Nat),
    shownBy ch tree (l.take n) k = (shownBy ch tree l k).take n
  | [], _, n => by simp [shownBy]
  | _ :: _, _, 0 => rfl
  | p :: l, k, n + 1 =>
    congrArg ((ch, p.shownBy tree k, p.drawn) :: ·) (shownBy_take ch tree l (k + p.tables.length) n)

section
variable {pl : List Played} {ss : List (Step W Y)} {ds : List Fmt.Drawn} {a : Addr} {n len : Nat}

/-- **What has been shown before the part, in one chain.** -/
theorem front_eq (hl : LaidAs pl ss ds) (hs : InStretch ss a n len) (hlen : 0 < len) (ch : Nat)
    (qs : List Read) (tree : Nat → List Nat)
    (hsh : ((shownIn ch pl qs).map fun y => (ch, y.2, y.1.drawn)) = shownBy ch tree pl 0) :
    ((((shownIn ch pl qs).map fun x => (x.1, ch, x.2, x.1.drawn)).takeWhile
      fun x => !x.1.isAt a).map (·.2)) = shownBy ch tree (pl.take n) 0 := by
  have M := laidAs_mask hl a
  have hO : ((shownIn ch pl qs).map fun x => (x.1, ch, x.2, x.1.drawn)).map
      (fun x : Played × Nat × Shown × Fmt.Drawn => x.1) = pl := by
    rw [List.map_map]
    exact shownIn_fst ch pl qs
  have mO : ((shownIn ch pl qs).map fun x => (x.1, ch, x.2, x.1.drawn)).map
      (fun x : Played × Nat × Shown × Fmt.Drawn => x.1.isAt a) = ss.map fun s => s.addr == a := by
    have e : ((shownIn ch pl qs).map fun x => (x.1, ch, x.2, x.1.drawn)).map
        (fun x : Played × Nat × Shown × Fmt.Drawn => x.1.isAt a) =
        (((shownIn ch pl qs).map fun x => (x.1, ch, x.2, x.1.drawn)).map
          (fun x : Played × Nat × Shown × Fmt.Drawn => x.1)).map (·.isAt a) := by
      simp only [List.map_map] <;> rfl
    rw [e, hO, M]
  rw [takeWhile_stretch (fun x : Played × Nat × Shown × Fmt.Drawn => x.1.isAt a) _ n
    (fun x hx => by
      refine all_of_map (l := ((shownIn ch pl qs).map fun x =>
        (x.1, ch, x.2, x.1.drawn)).take n) (l' := ss.take n)
        (g := fun x : Played × Nat × Shown × Fmt.Drawn => x.1.isAt a)
        (g' := fun s : Step W Y => s.addr == a) ?_ hs.front x hx
      rw [List.map_take, List.map_take, mO])
    (fun x hx => by
      refine all_of_map (l := (((shownIn ch pl qs).map fun x =>
        (x.1, ch, x.2, x.1.drawn)).drop n).take len) (l' := (ss.drop n).take len)
        (g := fun x : Played × Nat × Shown × Fmt.Drawn => x.1.isAt a)
        (g' := fun s : Step W Y => s.addr == a) ?_ hs.own x ?_
      · rw [List.map_take, List.map_take, List.map_drop, List.map_drop, mO]
      · cases hd : ((shownIn ch pl qs).map fun x => (x.1, ch, x.2, x.1.drawn)).drop n with
        | nil =>
          rw [hd] at hx
          cases hx
        | cons y t =>
          rw [hd] at hx
          cases hx
          obtain ⟨k, rfl⟩ : ∃ k, len = k + 1 := ⟨len - 1, by omega⟩
          exact List.mem_cons_self)]
  rw [← List.map_take, shownBy_take, ← hsh, List.map_take, List.map_take, List.map_map]
  rfl

end

/-! ## 3 The file -/

theorem len_pos {W' Y' : Type} {ss : List (Step W' Y')} {a : Addr}
    (ha : ss.any (·.addr == a) = true) : 0 < (ss.filter fun s => s.addr == a).length := by
  obtain ⟨s, hs, e⟩ := List.any_eq_true.1 ha
  exact List.length_pos_of_mem (List.mem_filter.2 ⟨hs, e⟩)

section
variable {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {c : Coins B} {ρ : Draws} {r : RunC F} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
  (h : runC F B H w₀ rc x c ρ = .ok r) (hR : ready F B H w₀ rc x c = .ok R)
  (o₁ : ∀ s ∈ R.first, s.oracles.length = s.decl.entry.roots)
  (o₂ : ∀ s ∈ R.shared, s.oracles.length = s.decl.entry.roots)
  (o₃ : ∀ s ∈ R.second, s.oracles.length = s.decl.entry.roots) (hp : F.placesOk = true)
include h hR o₁ o₂ o₃ hp

omit hp in
/-- A chain's rounds as produced have one at the address exactly if the chain's `Step`s, as `ready`
prepares them, have one. -/
theorem any_laid (a : Addr) :
    r.run.played.1.any (·.isAt a) = R.first.any (·.addr == a) ∧
    r.run.played.2.1.any (·.isAt a) = R.shared.any (·.addr == a) ∧
    r.run.played.2.2.any (·.isAt a) = R.second.any (·.addr == a) := by
  obtain ⟨l1, l2, l3⟩ := runC_laidAs h hR o₁ o₂ o₃
  exact ⟨any_of_mask (laidAs_mask l1 a), any_of_mask (laidAs_mask l2 a),
    any_of_mask (laidAs_mask l3 a)⟩

/-- **`Run.beforeAt` at an address of the first chain**: what the chain's rounds before the address
show. -/
theorem before_first {a : Addr} (ha : R.first.any (·.addr == a) = true)
    (hseg : (R.first.drop (R.first.takeWhile fun s => s.addr != a).length).take
      (R.first.filter fun s => s.addr == a).length = R.first.filter fun s => s.addr == a)
    (tree : Nat → List Nat)
    (hsh : ((shownIn 0 r.run.played.1 (r.run.reads.1 ++ r.run.reads.2.1 ++ r.run.reads.2.2)).map
      fun y => (0, y.2, y.1.drawn)) = shownBy 0 tree r.run.played.1 0)
    (st : List (Nat × Nat × List UInt64)) :
    r.run.beforeAt st a = ⟨shownBy 0 tree
      (r.run.played.1.take (R.first.takeWhile fun s => s.addr != a).length) 0, st⟩ := by
  obtain ⟨l1, -, -⟩ := runC_laidAs h hR o₁ o₂ o₃
  obtain ⟨n1, -, -⟩ := any_laid h hR o₁ o₂ o₃ a
  unfold Run.beforeAt
  simp only [n1, ha, if_true]
  rw [front_eq l1 (stretch_of R.first a hseg) (len_pos ha) 0 _ tree hsh]

/-- **`Run.beforeAt` at an address of the shared chain**: what the chain's rounds before the address
show. -/
theorem before_shared {a : Addr} (ha : R.shared.any (·.addr == a) = true)
    (hseg : (R.shared.drop (R.shared.takeWhile fun s => s.addr != a).length).take
      (R.shared.filter fun s => s.addr == a).length = R.shared.filter fun s => s.addr == a)
    (tree : Nat → List Nat)
    (hsh : ((shownIn 1 r.run.played.2.1
      (r.run.reads.1 ++ r.run.reads.2.1 ++ r.run.reads.2.2)).map
      fun y => (1, y.2, y.1.drawn)) = shownBy 1 tree r.run.played.2.1 0)
    (st : List (Nat × Nat × List UInt64)) :
    r.run.beforeAt st a = ⟨shownBy 1 tree
      (r.run.played.2.1.take (R.shared.takeWhile fun s => s.addr != a).length) 0, st⟩ := by
  obtain ⟨-, l2, -⟩ := runC_laidAs h hR o₁ o₂ o₃
  obtain ⟨n1, n2, -⟩ := any_laid h hR o₁ o₂ o₃ a
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  obtain ⟨p1, p2, p3⟩ := places_chain hp
  have hnot : R.first.any (·.addr == a) = false := by
    rw [List.any_eq_false]
    intro s hs
    rw [off_chain (by decide) (steps_chain s2 p2) (steps_chain s1 p1) ha s hs]
    exact Bool.false_ne_true
  unfold Run.beforeAt
  simp only [n1, n2, hnot, ha, if_true, Bool.false_eq_true, if_false]
  rw [front_eq l2 (stretch_of R.shared a hseg) (len_pos ha) 1 _ tree hsh]

/-- **`Run.beforeAt` at an address of the second chain**: what all rounds of the two earlier chains
show, and then what the second chain's rounds before the address show. -/
theorem before_second {a : Addr} (ha : R.second.any (·.addr == a) = true)
    (hseg : (R.second.drop (R.second.takeWhile fun s => s.addr != a).length).take
      (R.second.filter fun s => s.addr == a).length = R.second.filter fun s => s.addr == a)
    (t₀ t₁ t₂ : Nat → List Nat)
    (h₀ : ((shownIn 0 r.run.played.1 (r.run.reads.1 ++ r.run.reads.2.1 ++ r.run.reads.2.2)).map
      fun y => (0, y.2, y.1.drawn)) = shownBy 0 t₀ r.run.played.1 0)
    (h₁ : ((shownIn 1 r.run.played.2.1
      (r.run.reads.1 ++ r.run.reads.2.1 ++ r.run.reads.2.2)).map
      fun y => (1, y.2, y.1.drawn)) = shownBy 1 t₁ r.run.played.2.1 0)
    (h₂ : ((shownIn 2 r.run.played.2.2
      (r.run.reads.1 ++ r.run.reads.2.1 ++ r.run.reads.2.2)).map
      fun y => (2, y.2, y.1.drawn)) = shownBy 2 t₂ r.run.played.2.2 0)
    (st : List (Nat × Nat × List UInt64)) :
    r.run.beforeAt st a = ⟨shownBy 0 t₀ r.run.played.1 0 ++ shownBy 1 t₁ r.run.played.2.1 0 ++
      shownBy 2 t₂ (r.run.played.2.2.take (R.second.takeWhile fun s => s.addr != a).length) 0,
      st⟩ := by
  obtain ⟨-, -, l3⟩ := runC_laidAs h hR o₁ o₂ o₃
  obtain ⟨n1, n2, -⟩ := any_laid h hR o₁ o₂ o₃ a
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  obtain ⟨p1, p2, p3⟩ := places_chain hp
  have hnot₁ : R.first.any (·.addr == a) = false := by
    rw [List.any_eq_false]
    intro s hs
    rw [off_chain (by decide) (steps_chain s3 p3) (steps_chain s1 p1) ha s hs]
    exact Bool.false_ne_true
  have hnot₂ : R.shared.any (·.addr == a) = false := by
    rw [List.any_eq_false]
    intro s hs
    rw [off_chain (by decide) (steps_chain s3 p3) (steps_chain s2 p2) ha s hs]
    exact Bool.false_ne_true
  unfold Run.beforeAt
  simp only [n1, n2, hnot₁, hnot₂, Bool.false_eq_true, if_false]
  rw [front_eq l3 (stretch_of R.second a hseg) (len_pos ha) 2 _ t₂ h₂, ← h₀, ← h₁,
    List.map_map, List.map_map]
  rfl

end

end ProofFile.Honest

#print axioms ProofFile.Honest.takeWhile_stretch
#print axioms ProofFile.Honest.any_of_mask
#print axioms ProofFile.Honest.shownIn_fst
#print axioms ProofFile.Honest.shownBy_take
#print axioms ProofFile.Honest.front_eq
#print axioms ProofFile.Honest.any_laid
#print axioms ProofFile.Honest.len_pos
#print axioms ProofFile.Honest.before_first
#print axioms ProofFile.Honest.before_shared
#print axioms ProofFile.Honest.before_second
