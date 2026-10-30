-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/RunAt.lean: a part's share of a run of `runC` (Honest/Walk.lean),
computed from the plan and the challenges. Book-keeping lemmas on `Run.drawnAt`, `Run.askedAt`
(Honest/Side.lean) and `RunC.called`. Take an address whose rounds are one consecutive stretch of
one chain's rounds, as `ready` has prepared them. Then the part's challenges are that stretch of the
chain's challenges; the positions read of its tables are those that the declared rounds read of
these trees, with no table supplied; and if the stretch's first round is a real round, the part was
called. In this file the lemmas are on one chain's share of the three functions (`partIn`). Two
hypotheses here: `LaidAs`, and in `asked_chain` that `tree` gives the run's positions.
Honest/Law/RunAtFile.lean proves both of a run of `runC` and states the three results.

  1  `filter_stretch`, `all_of_map`, `of_mem_takeWhile`, `addr_beq`   on lists; on addresses
  2  `numbered_fst`, `numbered_take`, `numbered_drop`, `asks_numbered`, `mem_numbered`   on
     `numbered`
  3  `InStretch`, `stretch_of`   an address's rounds are one consecutive stretch
  4  `LaidAs`, `laidAs_mask`, `laidAs_tables`, `laidAs_drawn`, `partIn_stretch`, `partIn_none`   one
     chain
  5  `drawn_chain`, `asked_chain`, `told_chain`   one chain's share of the three functions

Limits.
  * That no other chain has a round at the address is a hypothesis of whoever uses section 5.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.WalkReads
import Johnson.Desc.ProofFile.Honest.Law.Rule.Session

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {W Y : Type}

/-! ## 1 On lists; on addresses -/

theorem filter_stretch {α : Type} (f : α → Bool) (l : List α) (n len : Nat)
    (h1 : ∀ x ∈ l.take n, f x = false) (h2 : ∀ x ∈ (l.drop n).take len, f x = true)
    (h3 : ∀ x ∈ (l.drop n).drop len, f x = false) : l.filter f = (l.drop n).take len := by
  have e : l = l.take n ++ ((l.drop n).take len ++ (l.drop n).drop len) := by
    rw [List.take_append_drop, List.take_append_drop]
  have g1 : (l.take n).filter f = [] :=
    List.filter_eq_nil_iff.2 fun x hx => by rw [h1 x hx]; exact Bool.false_ne_true
  have g2 : ((l.drop n).take len).filter f = (l.drop n).take len := List.filter_eq_self.2 h2
  have g3 : ((l.drop n).drop len).filter f = [] :=
    List.filter_eq_nil_iff.2 fun x hx => by rw [h3 x hx]; exact Bool.false_ne_true
  calc l.filter f
      = (l.take n ++ ((l.drop n).take len ++ (l.drop n).drop len)).filter f := by rw [← e]
    _ = (l.drop n).take len := by
      rw [List.filter_append, List.filter_append, g1, g2, g3, List.nil_append, List.append_nil]

theorem all_of_map {α β γ : Type} {l : List α} {l' : List β} {g : α → γ} {g' : β → γ} {c : γ}
    (h : l.map g = l'.map g') (h' : ∀ y ∈ l', g' y = c) : ∀ x ∈ l, g x = c := by
  intro x hx
  have h1 : g x ∈ l.map g := List.mem_map.2 ⟨x, hx, rfl⟩
  rw [h] at h1
  obtain ⟨y, hy, e⟩ := List.mem_map.1 h1
  rw [← e]
  exact h' y hy

theorem of_mem_takeWhile {α : Type} (p : α → Bool) : ∀ (l : List α) (x : α),
    x ∈ l.takeWhile p → p x = true
  | [], _, h => by simp at h
  | a :: l, x, h => by
    by_cases hp : p a = true
    · rw [List.takeWhile_cons_of_pos hp] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact hp
      · exact of_mem_takeWhile p l x h
    · rw [List.takeWhile_cons_of_neg hp] at h
      cases h

theorem addr_beq (x a : Addr) : (x == a) = (x.place == a.place && x.part == a.part) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨p, i⟩ := x
    obtain ⟨q, j⟩ := a
    have h1' : p = q := h1
    have h2' : i = j := h2
    subst h1' h2'
    rfl

/-! ## 2 On `numbered` -/

theorem numbered_fst : ∀ (l : List Played) (k : Nat), (numbered l k).map (·.1) = l
  | [], _ => rfl
  | p :: l, k => congrArg (p :: ·) (numbered_fst l (k + p.tables.length))

theorem numbered_take : ∀ (l : List Played) (k n : Nat),
    (numbered l k).take n = numbered (l.take n) k
  | [], _, n => by simp [numbered]
  | _ :: _, _, 0 => rfl
  | p :: l, k, n + 1 => congrArg ((p, k) :: ·) (numbered_take l (k + p.tables.length) n)

theorem numbered_drop : ∀ (l : List Played) (k n : Nat),
    (numbered l k).drop n = numbered (l.drop n) (k + ((l.take n).map (·.tables.length)).sum)
  | [], _, n => by simp [numbered]
  | _ :: _, _, 0 => rfl
  | p :: l, k, n + 1 => by
    show (numbered l (k + p.tables.length)).drop n =
      numbered (l.drop n) (k + (p.tables.length + ((l.take n).map (·.tables.length)).sum))
    rw [numbered_drop l _ n, Nat.add_assoc]

theorem mem_numbered {l : List Played} {k : Nat} {x : Played × Nat} (h : x ∈ numbered l k) :
    x.1 ∈ l := by
  have h1 : x.1 ∈ (numbered l k).map (·.1) := List.mem_map.2 ⟨x, h, rfl⟩
  rw [numbered_fst] at h1
  exact h1

/-- By round and by root, from the numbers that `numbered` assigns. -/
theorem asks_numbered (tree : Nat → List Nat) : ∀ (l : List Played) (k : Nat),
    ((numbered l k).map fun x => (List.range x.1.tables.length).map fun i => tree (x.2 + i)) =
      asksFrom tree (l.map (·.tables.length)) k
  | [], _ => rfl
  | p :: l, k => congrArg (((List.range p.tables.length).map fun i => tree (k + i)) :: ·)
      (asks_numbered tree l (k + p.tables.length))

/-! ## 3 One stretch -/

/-- The rounds at the address `a` are one consecutive stretch of `ss`: `n` rounds come before it,
`len` are in it. -/
structure InStretch (ss : List (Step W Y)) (a : Addr) (n len : Nat) : Prop where
  front : ∀ s ∈ ss.take n, (s.addr == a) = false
  own : ∀ s ∈ (ss.drop n).take len, (s.addr == a) = true
  behind : ∀ s ∈ (ss.drop n).drop len, (s.addr == a) = false

/-- In the form in which a caller has it: `n` and `len` are counted from the list; the stretch is
the filter. -/
theorem stretch_of (ss : List (Step W Y)) (a : Addr)
    (hseg : (ss.drop (ss.takeWhile fun s => s.addr != a).length).take
      (ss.filter fun s => s.addr == a).length = ss.filter fun s => s.addr == a) :
    InStretch ss a (ss.takeWhile fun s => s.addr != a).length
      (ss.filter fun s => s.addr == a).length := by
  have hpre : ss.take (ss.takeWhile fun s => s.addr != a).length =
      ss.takeWhile fun s => s.addr != a :=
    (List.prefix_iff_eq_take.1 (List.takeWhile_prefix _)).symm
  have c1 : ∀ s ∈ ss.take (ss.takeWhile fun s => s.addr != a).length, (s.addr == a) = false := by
    intro s hs
    rw [hpre] at hs
    have h := of_mem_takeWhile _ _ _ hs
    simpa [bne] using h
  have c2 : ∀ s ∈ (ss.drop (ss.takeWhile fun s => s.addr != a).length).take
      (ss.filter fun s => s.addr == a).length, (s.addr == a) = true := by
    intro s hs
    rw [hseg] at hs
    exact (List.mem_filter.1 hs).2
  refine ⟨c1, c2, ?_⟩
  have e : ss = ss.take (ss.takeWhile fun s => s.addr != a).length ++
      ((ss.drop (ss.takeWhile fun s => s.addr != a).length).take
          (ss.filter fun s => s.addr == a).length ++
        (ss.drop (ss.takeWhile fun s => s.addr != a).length).drop
          (ss.filter fun s => s.addr == a).length) := by
    rw [List.take_append_drop, List.take_append_drop]
  have g1 : (ss.take (ss.takeWhile fun s => s.addr != a).length).filter
      (fun s => s.addr == a) = [] :=
    List.filter_eq_nil_iff.2 fun x hx => by rw [c1 x hx]; exact Bool.false_ne_true
  have g2 := List.filter_eq_self.2 c2
  have h := congrArg (List.filter fun s : Step W Y => s.addr == a) e
  rw [List.filter_append, List.filter_append, g1, g2, List.nil_append, hseg] at h
  have h3 := List.self_eq_append_right.1 h
  intro s hs
  have h4 := List.filter_eq_nil_iff.1 h3 s hs
  exact Bool.eq_false_iff.2 h4

/-! ## 4 One chain -/

/-- The rounds that a chain has produced, reduced to place, part, number of tables and challenge,
are the `Step`s zipped with the challenges (the second half of `reads_bare`,
Honest/Law/WalkReads.lean). -/
def LaidAs (pl : List Played) (ss : List (Step W Y)) (ds : List Fmt.Drawn) : Prop :=
  ds.length = ss.length ∧
    pl.map (fun p => (p.place, p.part, p.tables.length, p.drawn)) =
      (ss.zip ds).map fun u => (u.1.addr.place, u.1.addr.part, u.1.oracles.length, u.2)

section
variable {pl : List Played} {ss : List (Step W Y)} {ds : List Fmt.Drawn}

theorem laidAs_mask (h : LaidAs pl ss ds) (a : Addr) :
    pl.map (·.isAt a) = ss.map fun s => s.addr == a := by
  have h1 := congrArg (List.map fun x : Place × Nat × Nat × Fmt.Drawn =>
    x.1 == a.place && x.2.1 == a.part) h.2
  rw [List.map_map, List.map_map] at h1
  have h2 : (ss.zip ds).map ((fun x : Place × Nat × Nat × Fmt.Drawn =>
      x.1 == a.place && x.2.1 == a.part) ∘ fun u : Step W Y × Fmt.Drawn =>
        (u.1.addr.place, u.1.addr.part, u.1.oracles.length, u.2)) =
      ((ss.zip ds).map Prod.fst).map fun s => s.addr == a := by
    rw [List.map_map]
    exact List.map_congr_left fun u _ => (addr_beq u.1.addr a).symm
  rw [h2, List.map_fst_zip (Nat.le_of_eq h.1.symm)] at h1
  exact h1

theorem laidAs_tables (h : LaidAs pl ss ds) :
    pl.map (·.tables.length) = ss.map (·.oracles.length) := by
  have h1 := congrArg (List.map fun x : Place × Nat × Nat × Fmt.Drawn => x.2.2.1) h.2
  rw [List.map_map, List.map_map] at h1
  have h2 : (ss.zip ds).map ((fun x : Place × Nat × Nat × Fmt.Drawn => x.2.2.1) ∘
      fun u : Step W Y × Fmt.Drawn =>
        (u.1.addr.place, u.1.addr.part, u.1.oracles.length, u.2)) =
      ((ss.zip ds).map Prod.fst).map (·.oracles.length) := by
    rw [List.map_map]
    rfl
  rw [h2, List.map_fst_zip (Nat.le_of_eq h.1.symm)] at h1
  exact h1

theorem laidAs_drawn (h : LaidAs pl ss ds) : pl.map (·.drawn) = ds := by
  have h1 := congrArg (List.map fun x : Place × Nat × Nat × Fmt.Drawn => x.2.2.2) h.2
  rw [List.map_map, List.map_map] at h1
  exact h1.trans (List.map_snd_zip (Nat.le_of_eq h.1))

/-- **The part's rounds in one chain**: the stretch, numbered from the tables produced before it. -/
theorem partIn_stretch (h : LaidAs pl ss ds) {a : Addr} {n len : Nat} (hs : InStretch ss a n len)
    (ch : Nat) (qs : List Read) :
    partIn ch pl qs a =
      (numbered ((pl.drop n).take len) ((pl.take n).map (·.tables.length)).sum).map fun x =>
        (x.1, (List.range x.1.tables.length).map fun i =>
          qs.filter fun q => q.src == some (ch, x.2 + i)) := by
  have M := laidAs_mask h a
  have m1 : (pl.take n).map (·.isAt a) = (ss.take n).map fun s => s.addr == a := by
    rw [List.map_take, List.map_take, M]
  have m2 : ((pl.drop n).take len).map (·.isAt a) =
      ((ss.drop n).take len).map fun s => s.addr == a := by
    rw [List.map_take, List.map_take, List.map_drop, List.map_drop, M]
  have m3 : ((pl.drop n).drop len).map (·.isAt a) =
      ((ss.drop n).drop len).map fun s => s.addr == a := by
    rw [List.map_drop, List.map_drop, List.map_drop, List.map_drop, M]
  have e : (numbered pl 0).filter (fun x => x.1.isAt a) =
      numbered ((pl.drop n).take len) ((pl.take n).map (·.tables.length)).sum := by
    rw [filter_stretch (fun x : Played × Nat => x.1.isAt a) (numbered pl 0) n len
      (fun x hx => by
        rw [numbered_take] at hx
        exact all_of_map m1 hs.front x.1 (mem_numbered hx))
      (fun x hx => by
        rw [numbered_drop, numbered_take] at hx
        exact all_of_map m2 hs.own x.1 (mem_numbered hx))
      (fun x hx => by
        rw [numbered_drop, numbered_drop] at hx
        exact all_of_map m3 hs.behind x.1 (mem_numbered hx)),
      numbered_drop, numbered_take, Nat.zero_add]
  unfold partIn
  rw [e]

/-- A chain without a round at the address has no share. -/
theorem partIn_none (h : LaidAs pl ss ds) {a : Addr} (hn : ∀ s ∈ ss, (s.addr == a) = false)
    (ch : Nat) (qs : List Read) : partIn ch pl qs a = [] := by
  have M := laidAs_mask h a
  unfold partIn
  rw [List.filter_eq_nil_iff.2 fun x hx => by
    rw [all_of_map M hn x.1 (mem_numbered hx)]
    exact Bool.false_ne_true]
  rfl

/-! ## 5 One chain's share of the three functions -/

theorem drawn_chain (h : LaidAs pl ss ds) {a : Addr} {n len : Nat} (hs : InStretch ss a n len)
    (ch : Nat) (qs : List Read) :
    (partIn ch pl qs a).map (·.1.drawn) = (ds.drop n).take len := by
  rw [partIn_stretch h hs, List.map_map]
  have e : (numbered ((pl.drop n).take len) ((pl.take n).map (·.tables.length)).sum).map
      ((fun x : Played × List (List Read) => x.1.drawn) ∘ fun x : Played × Nat =>
        (x.1, (List.range x.1.tables.length).map fun i =>
          qs.filter fun q => q.src == some (ch, x.2 + i))) =
      ((numbered ((pl.drop n).take len) ((pl.take n).map (·.tables.length)).sum).map
        (·.1)).map (·.drawn) := by
    rw [List.map_map]
    rfl
  rw [e, numbered_fst, List.map_take, List.map_drop, laidAs_drawn h]

/-- `tree`: the positions read of the chain's tree number j, however they are given; `hq`: that
these are the run's. -/
theorem asked_chain (h : LaidAs pl ss ds) {a : Addr} {n len : Nat} (hs : InStretch ss a n len)
    (ch : Nat) (qs : List Read) (tree : Nat → List Nat)
    (hq : ∀ j, ((qs.filter fun q => q.src == some (ch, j)).map (·.pos)) = tree j) :
    ((partIn ch pl qs a).map fun x => x.2.map fun l => l.map (·.pos)) =
      asksFrom tree (((ss.drop n).take len).map (·.oracles.length))
        ((ss.take n).map (·.oracles.length)).sum := by
  rw [partIn_stretch h hs, List.map_map]
  have e : (numbered ((pl.drop n).take len) ((pl.take n).map (·.tables.length)).sum).map
      ((fun x : Played × List (List Read) => x.2.map fun l => l.map (·.pos)) ∘
        fun x : Played × Nat => (x.1, (List.range x.1.tables.length).map fun i =>
          qs.filter fun q => q.src == some (ch, x.2 + i))) =
      (numbered ((pl.drop n).take len) ((pl.take n).map (·.tables.length)).sum).map fun x =>
        (List.range x.1.tables.length).map fun i => tree (x.2 + i) := by
    refine List.map_congr_left fun x _ => ?_
    show ((List.range x.1.tables.length).map fun i =>
      qs.filter fun q => q.src == some (ch, x.2 + i)).map (fun l => l.map (·.pos)) = _
    rw [List.map_map]
    exact List.map_congr_left fun i _ => hq (x.2 + i)
  rw [e, asks_numbered, List.map_take, List.map_drop, List.map_take, laidAs_tables h,
    ← List.map_drop, ← List.map_take, ← List.map_take]

/-- If the stretch's first round is a real round, there is a real round at the address. -/
theorem told_chain (h : LaidAs pl ss ds) {a : Addr} {n len : Nat} (hs : InStretch ss a n len)
    (hl : 0 < len) (ht : ((pl.drop n).head?.map (·.told)) = some true) :
    (pl.any fun p => p.told && p.place == a.place && p.part == a.part) = true := by
  cases hd : pl.drop n with
  | nil =>
    rw [hd] at ht
    cases ht
  | cons p t =>
    rw [hd] at ht
    have ht' : p.told = true := Option.some.inj ht
    have hp : p ∈ pl := List.mem_of_mem_drop (by rw [hd]; exact List.mem_cons_self)
    have M := laidAs_mask h a
    have m2 : ((pl.drop n).take len).map (·.isAt a) =
        ((ss.drop n).take len).map fun s => s.addr == a := by
      rw [List.map_take, List.map_take, List.map_drop, List.map_drop, M]
    have hin : p ∈ (pl.drop n).take len := by
      rw [hd]
      obtain ⟨k, rfl⟩ : ∃ k, len = k + 1 := ⟨len - 1, by omega⟩
      exact List.mem_cons_self
    have hat : p.isAt a = true := all_of_map m2 hs.own p hin
    refine List.any_eq_true.2 ⟨p, hp, ?_⟩
    have hat' : (p.place == a.place && p.part == a.part) = true := hat
    rw [Bool.and_assoc, ht', hat']
    rfl

end

end ProofFile.Honest

#print axioms ProofFile.Honest.filter_stretch
#print axioms ProofFile.Honest.all_of_map
#print axioms ProofFile.Honest.of_mem_takeWhile
#print axioms ProofFile.Honest.addr_beq
#print axioms ProofFile.Honest.numbered_fst
#print axioms ProofFile.Honest.numbered_take
#print axioms ProofFile.Honest.numbered_drop
#print axioms ProofFile.Honest.mem_numbered
#print axioms ProofFile.Honest.asks_numbered
#print axioms ProofFile.Honest.stretch_of
#print axioms ProofFile.Honest.laidAs_mask
#print axioms ProofFile.Honest.laidAs_tables
#print axioms ProofFile.Honest.laidAs_drawn
#print axioms ProofFile.Honest.partIn_stretch
#print axioms ProofFile.Honest.partIn_none
#print axioms ProofFile.Honest.drawn_chain
#print axioms ProofFile.Honest.asked_chain
#print axioms ProofFile.Honest.told_chain
