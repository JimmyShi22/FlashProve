-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndOnce.lean: if objectsF returns (`HTailF2.objectsF`, OnBytes/Model/Tail.lean),
no place of a vector of the tables is named by two reads, or by one read at two columns.

Theorems with their proofs. objectsF keeps a mark for each place of the part of a vector that holds
tables. Before a read is added its places are marked, and a place that is marked already is refused
(`HTailF2.markLoop`). OnBytes/Tie/Pv/Tail/EndCover.lean has that every place is named at least once.
Here: at most once.

Main names:
  `markLoop_once`, `markRead_once`: one read: marks stay set; each of its places was unset before
    and is set after; its places at two columns differ.
  `PlacesApart tl x y`: two reads on one part of the marks name no place in common.
  `runFold_once`: the reads one after the other: the same three, and any two reads of the list, by
    their places in the list, are apart.
  `objectsF_apart`: if objectsF returns, the list of its reads is pairwise apart, and each read's
    places at two columns differ.
  `objectsF_once`: two reads of the list and two columns with one place, on one part: the same read
    (table and segment) and the same column.

  `objectsF_table_once`: a table with a column and a segment stands once in the list of tables.
  `objectsF_onceAt`: two tables of the list, by their numbers, each with a column and a segment, at
    one place of one part: the same number, column and segment. `posOf_eq`: the place, written out.

Limits: one direction: from a run that returns. The two parts of the marks (the first and the third
vector) are not compared with each other.


-/
import OnBytes.Tie.Pv.Tail.EndCover

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port

/-- A mark that reads as unset where a place outside would read as set lies inside, and is unset. -/
theorem unset_inside (marks : Array Bool) (i : Nat) (h : marks.getD i true = false) :
    i < marks.size ∧ marks.getD i false = false := by
  by_cases hlt : i < marks.size
  · refine ⟨hlt, ?_⟩
    simpa [Array.getD, hlt] using h
  · simp [Array.getD, hlt] at h

/-- The mark that was just set. -/
theorem set_here (marks : Array Bool) (i : Nat) (h : i < marks.size) :
    (marks.set! i true).getD i false = true := by
  simp [Array.getD, h]

/-- The other marks. -/
theorem set_else (marks : Array Bool) (i j : Nat) (h : j ≠ i) :
    (marks.set! i true).getD j false = marks.getD j false := by
  by_cases hlt : j < marks.size
  · simp [Array.getD, hlt, Ne.symm h]
  · simp [Array.getD, hlt]

/-- One read's loop: marks stay set; each place was unset before and is set after; the places at two
columns differ. -/
theorem markLoop_once (tl : HTailF2) (Fn : HFun) (sg t0 : Nat) :
    ∀ (count c : Nat) (marks marks' : Array Bool),
      tl.markLoop Fn sg t0 count c marks = some marks' →
      (∀ i, marks.getD i false = true → marks'.getD i false = true) ∧
      (∀ d, c ≤ d → d < c + count → t0 ≤ posOf tl Fn sg d ∧
        marks.getD (posOf tl Fn sg d - t0) false = false ∧
        marks'.getD (posOf tl Fn sg d - t0) false = true) ∧
      ∀ d d', c ≤ d → d < d' → d' < c + count → posOf tl Fn sg d ≠ posOf tl Fn sg d'
  | 0, c, marks, marks', h => by
    simp only [HTailF2.markLoop, Option.some.injEq] at h
    subst h
    exact ⟨fun _ hi => hi, fun d h1 h2 => by omega, fun d d' h1 h2 h3 => by omega⟩
  | count + 1, c, marks, marks', h => by
    simp only [HTailF2.markLoop] at h
    cases hp : tl.tabAt Fn c sg with
    | none => simp [hp] at h
    | some pos =>
      simp only [hp] at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
        obtain ⟨hle, hun⟩ := hc
        obtain ⟨hin, hun0⟩ := unset_inside marks _ hun
        obtain ⟨m1, m2, m3⟩ := markLoop_once tl Fn sg t0 count (c + 1) _ _ h
        have hpc : posOf tl Fn sg c = pos := by
          unfold posOf
          rw [hp]
          rfl
        have step : ∀ i, marks.getD i false = true →
            (marks.set! (pos - t0) true).getD i false = true := by
          intro i hi
          by_cases hie : i = pos - t0
          · rw [hie]
            exact set_here marks _ hin
          · rw [set_else marks _ i hie]
            exact hi
        refine ⟨fun i hi => m1 i (step i hi), fun d h1 h2 => ?_, fun d d' h1 h2 h3 => ?_⟩
        · by_cases hd : d = c
          · rw [hd, hpc]
            exact ⟨hle, hun0, m1 _ (set_here marks _ hin)⟩
          · obtain ⟨a1, a2, a3⟩ := m2 d (by omega) (by omega)
            refine ⟨a1, ?_, a3⟩
            cases hb : marks.getD (posOf tl Fn sg d - t0) false with
            | false => rfl
            | true =>
              rw [step _ hb] at a2
              exact absurd a2 (by simp)
        · by_cases hd : d = c
          · obtain ⟨a1, a2, -⟩ := m2 d' (by omega) (by omega)
            rw [hd, hpc]
            intro e
            rw [← e, set_here marks _ hin] at a2
            exact absurd a2 (by simp)
          · exact m3 d d' (by omega) h2 (by omega)
      · simp at h

/-- One read: marks stay set; each place was unset before and is set after; the places at two
columns differ. -/
theorem markRead_once (tl : HTailF2) (Fn : HFun) (sg : Nat) (rd rd' : Array (Array Bool))
    (h : tl.markRead Fn sg rd = some rd') :
    (∀ q i, markAt rd q i → markAt rd' q i) ∧
    (∀ d, d < (tl.mats.getD Fn.mat {}).k →
      tl.tabFirst.getD (Fn.tree / 2) 0 ≤ posOf tl Fn sg d ∧
      ¬ markAt rd (Fn.tree / 2) (posOf tl Fn sg d - tl.tabFirst.getD (Fn.tree / 2) 0) ∧
      markAt rd' (Fn.tree / 2) (posOf tl Fn sg d - tl.tabFirst.getD (Fn.tree / 2) 0)) ∧
    ∀ d d', d < d' → d' < (tl.mats.getD Fn.mat {}).k → posOf tl Fn sg d ≠ posOf tl Fn sg d' := by
  unfold HTailF2.markRead at h
  simp only [] at h
  cases hl : tl.markLoop Fn sg (tl.tabFirst.getD (Fn.tree / 2) 0) (tl.mats.getD Fn.mat {}).k 0
      (rd.getD (Fn.tree / 2) #[]) with
  | none =>
    rw [hl] at h
    exact absurd h (by simp)
  | some marks =>
    simp only [hl, Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨m1, m2, m3⟩ := markLoop_once tl Fn sg _ _ _ _ _ hl
    have other : ∀ q, q ≠ Fn.tree / 2 →
        ((rd.set! (Fn.tree / 2) #[]).set! (Fn.tree / 2) marks).getD q #[] = rd.getD q #[] := by
      intro q hq
      by_cases hlt : q < rd.size
      · simp [Array.getD, hlt, Ne.symm hq]
      · simp [Array.getD, hlt]
    by_cases hlt : Fn.tree / 2 < rd.size
    · have e : ((rd.set! (Fn.tree / 2) #[]).set! (Fn.tree / 2) marks).getD (Fn.tree / 2) #[] =
          marks := by
        simp [Array.getD, hlt]
      refine ⟨fun q i hm => ?_, fun d hd => ?_, fun d d' h1 h2 => m3 d d' (by omega) h1 (by omega)⟩
      · unfold markAt at hm ⊢
        by_cases hq : q = Fn.tree / 2
        · rw [hq, e]
          rw [hq] at hm
          exact m1 i hm
        · rw [other q hq]
          exact hm
      · obtain ⟨a1, a2, a3⟩ := m2 d (by omega) (by omega)
        refine ⟨a1, ?_, ?_⟩
        · unfold markAt
          rw [a2]
          simp
        · unfold markAt
          rw [e]
          exact a3
    · have e0 : rd.getD (Fn.tree / 2) #[] = #[] := by simp [Array.getD, hlt]
      have hs := (markLoop_spec tl Fn sg _ _ _ _ _ hl).1
      rw [e0] at hs
      have none' : ∀ i, marks.getD i false = false := by
        intro i
        have : ¬ i < marks.size := by
          rw [hs]
          simp
        simp [Array.getD, this]
      have e : ((rd.set! (Fn.tree / 2) #[]).set! (Fn.tree / 2) marks).getD (Fn.tree / 2) #[] =
          rd.getD (Fn.tree / 2) #[] := by
        simp [Array.getD, hlt]
      refine ⟨fun q i hm => ?_, fun d hd => ?_, fun d d' h1 h2 => m3 d d' (by omega) h1 (by omega)⟩
      · unfold markAt at hm ⊢
        by_cases hq : q = Fn.tree / 2
        · rw [hq, e]
          rw [hq] at hm
          exact hm
        · rw [other q hq]
          exact hm
      · obtain ⟨-, -, a3⟩ := m2 d (by omega) (by omega)
        rw [none'] at a3
        exact absurd a3 (by simp)

/-- Two reads on one part of the marks name no place in common. -/
def PlacesApart (tl : HTailF2) (x y : HFun × Nat) : Prop :=
  x.1.tree / 2 = y.1.tree / 2 → ∀ d, d < (tl.mats.getD x.1.mat {}).k →
    ∀ d', d' < (tl.mats.getD y.1.mat {}).k → posOf tl x.1 x.2 d ≠ posOf tl y.1 y.2 d'

/-- The relation does not mind the order. -/
theorem PlacesApart.symm {tl : HTailF2} {x y : HFun × Nat} (h : PlacesApart tl x y) :
    PlacesApart tl y x :=
  fun e d hd d' hd' he => h e.symm d' hd' d hd he.symm

/-- The reads one after the other. -/
theorem runFold_once (tl : HTailF2) :
    ∀ (l : List (HFun × Nat)) (b : MProd Nat (Array (Array Bool))) (F : Fork) (c : Ctx)
      (b' : MProd Nat (Array (Array Bool))) (F' : Fork) (c' : Ctx),
      RunFoldS (stepM tl) l b F c b' F' c' →
      (∀ q i, markAt b.snd q i → markAt b'.snd q i) ∧
      (∀ x ∈ l, ∀ d, d < (tl.mats.getD x.1.mat {}).k →
        tl.tabFirst.getD (x.1.tree / 2) 0 ≤ posOf tl x.1 x.2 d ∧
        ¬ markAt b.snd (x.1.tree / 2) (posOf tl x.1 x.2 d - tl.tabFirst.getD (x.1.tree / 2) 0) ∧
        markAt b'.snd (x.1.tree / 2) (posOf tl x.1 x.2 d - tl.tabFirst.getD (x.1.tree / 2) 0)) ∧
      (∀ x ∈ l, ∀ d d', d < d' → d' < (tl.mats.getD x.1.mat {}).k →
        posOf tl x.1 x.2 d ≠ posOf tl x.1 x.2 d') ∧
      l.Pairwise (PlacesApart tl)
  | [], b, _, _, b', _, _, h => by
    obtain ⟨rfl, -, -⟩ := h
    exact ⟨fun _ _ hm => hm, fun _ hx => absurd hx (List.not_mem_nil),
      fun _ hx => absurd hx (List.not_mem_nil), List.Pairwise.nil⟩
  | a :: l, b, F, c, b', F', c', h => by
    obtain ⟨b1, F1, c1, ⟨-, hr⟩, ht⟩ := h
    obtain ⟨r1, r2, r3⟩ := markRead_once tl a.1 a.2 _ _ hr
    obtain ⟨i1, i2, i3, i4⟩ := runFold_once tl l b1 F1 c1 b' F' c' ht
    refine ⟨fun q i hm => i1 q i (r1 q i hm), fun x hx d hd => ?_, fun x hx => ?_,
      List.pairwise_cons.2 ⟨fun y hy e d hd d' hd' he => ?_, i4⟩⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · obtain ⟨a1, a2, a3⟩ := r2 d hd
        exact ⟨a1, a2, i1 _ _ a3⟩
      · obtain ⟨a1, a2, a3⟩ := i2 x hx d hd
        exact ⟨a1, fun hm => a2 (r1 _ _ hm), a3⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact r3
      · exact i3 x hx
    · obtain ⟨-, -, a3⟩ := r2 d hd
      obtain ⟨-, b2, -⟩ := i2 y hy d' hd'
      rw [e, he] at a3
      exact b2 a3

/-- If objectsF returns, the list of its reads is pairwise apart, and each read's places at two
columns differ. -/
theorem objectsF_apart (tl tl' : HTailF2) (funs : Array HFun) (F G : Fork) (c c' : Ctx)
    (h : tl.objectsF funs F c = .ok ((tl', G), c')) :
    (readsList tl' funs).Pairwise (PlacesApart tl') ∧
      ∀ x ∈ readsList tl' funs, ∀ d d', d < d' → d' < (tl'.mats.getD x.1.mat {}).k →
        posOf tl' x.1 x.2 d ≠ posOf tl' x.1 x.2 d' := by
  obtain ⟨tl1, b', Fx, Fy, cx, cy, t1, t2, t3, t4, rfl, hr, -⟩ :=
    objectsF_marks tl tl' funs F G c c' h
  obtain ⟨-, -, i3, i4⟩ := runFold_once tl1 _ _ _ _ _ _ _ hr
  exact ⟨i4, i3⟩

/-- If objectsF returns: two reads of the list and two columns with one place, on one part of the
marks: the same read and the same column. -/
theorem objectsF_once (tl tl' : HTailF2) (funs : Array HFun) (F G : Fork) (c c' : Ctx)
    (h : tl.objectsF funs F c = .ok ((tl', G), c')) (x y : HFun × Nat)
    (hx : x ∈ readsList tl' funs) (hy : y ∈ readsList tl' funs)
    (e : x.1.tree / 2 = y.1.tree / 2) (d d' : Nat) (hd : d < (tl'.mats.getD x.1.mat {}).k)
    (hd' : d' < (tl'.mats.getD y.1.mat {}).k)
    (he : posOf tl' x.1 x.2 d = posOf tl' y.1 y.2 d') : x = y ∧ d = d' := by
  obtain ⟨hp, hc⟩ := objectsF_apart tl tl' funs F G c c' h
  have hxy : x = y := by
    by_contra hne
    exact hp.forall (fun _ _ hs => hs.symm) hx hy hne e d hd d' hd' he
  subst hxy
  refine ⟨rfl, ?_⟩
  rcases Nat.lt_trichotomy d d' with h1 | h1 | h1
  · exact absurd he (hc x hx d d' h1 hd')
  · exact h1
  · exact absurd he.symm (hc x hx d' d h1 hd)

/-! ## The tables' numbers -/

/-- Two members of a list at two places, in their order, are a sublist. -/
theorem pair_sublist {α : Type} (a b : α) : ∀ (l : List α) (i j : Nat), i < j → l[i]? = some a →
    l[j]? = some b → [a, b].Sublist l
  | [], _, _, _, h, _ => by simp at h
  | x :: l, 0, j + 1, _, h, h' => by
    obtain rfl : x = a := by simpa using h
    have hb : b ∈ l := List.mem_of_getElem? (by simpa using h')
    exact (List.singleton_sublist.2 hb).cons₂ x
  | x :: l, i + 1, j + 1, hij, h, h' =>
    (pair_sublist a b l i j (by omega) (by simpa using h) (by simpa using h')).cons x

/-- A sublist's images in a row are a sublist of the list's. -/
theorem sublist_flatMap {α β : Type} (f : α → List β) {l₁ l₂ : List α} (h : l₁.Sublist l₂) :
    (l₁.flatMap f).Sublist (l₂.flatMap f) := by
  induction h with
  | slnil => exact List.Sublist.refl _
  | cons a _ ih =>
    rw [List.flatMap_cons]
    exact List.sublist_append_of_sublist_right ih
  | cons₂ a _ ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    exact (List.Sublist.refl _).append ih

/-- A member's image is a sublist. -/
theorem mem_flatMap_sublist {α β : Type} (f : α → List β) {a : α} {l : List α} (h : a ∈ l) :
    (f a).Sublist (l.flatMap f) := by
  have := sublist_flatMap f (List.singleton_sublist.2 h)
  simpa using this

/-- A segment of a table is a read of the table's matrix and vector. -/
theorem mem_segsOf (tl : HTailF2) (Fn : HFun) (sg : Nat)
    (hs : sg < (tl.mats.getD Fn.mat {}).m / Fn.len) : (Fn, sg) ∈ segsOf tl Fn.mat Fn.tree Fn := by
  unfold segsOf
  rw [if_pos (by simp)]
  exact List.mem_map.2 ⟨sg, List.mem_range.2 hs, rfl⟩

/-- The reads of one matrix and vector are a sublist of all reads. -/
theorem part_sublist (tl : HTailF2) (funs : Array HFun) (mu un : Nat) (hm : mu < tl.NM)
    (hu : un = 0 ∨ un = 2) :
    (funs.toList.flatMap (segsOf tl mu un)).Sublist (readsList tl funs) := by
  unfold readsList
  refine List.Sublist.trans ?_ (mem_flatMap_sublist _ (List.mem_range.2 hm))
  exact mem_flatMap_sublist (fun un => funs.toList.flatMap (segsOf tl mu un))
    (by rcases hu with rfl | rfl <;> simp)

/-- A segment of a table of the list is a read of the list. -/
theorem mem_readsList (tl : HTailF2) (funs : Array HFun) (n : Nat) (Fn : HFun) (sg : Nat)
    (hn : funs[n]? = some Fn) (hm : Fn.mat < tl.NM) (hu : Fn.tree = 0 ∨ Fn.tree = 2)
    (hs : sg < (tl.mats.getD Fn.mat {}).m / Fn.len) : (Fn, sg) ∈ readsList tl funs := by
  refine (part_sublist tl funs Fn.mat Fn.tree hm hu).subset ?_
  have hmem : Fn ∈ funs.toList :=
    List.mem_of_getElem? (l := funs.toList) (i := n) (by simpa using hn)
  exact List.mem_flatMap.2 ⟨Fn, hmem, mem_segsOf tl Fn sg hs⟩

/-- If objectsF returns, a table with a column and a segment stands once in the list of tables. -/
theorem objectsF_table_once (tl tl' : HTailF2) (funs : Array HFun) (F G : Fork) (c c' : Ctx)
    (h : tl.objectsF funs F c = .ok ((tl', G), c')) (n n' : Nat) (Fn : HFun)
    (hn : funs[n]? = some Fn) (hn' : funs[n']? = some Fn) (hm : Fn.mat < tl'.NM)
    (hu : Fn.tree = 0 ∨ Fn.tree = 2) (sg d : Nat)
    (hs : sg < (tl'.mats.getD Fn.mat {}).m / Fn.len) (hd : d < (tl'.mats.getD Fn.mat {}).k) :
    n = n' := by
  obtain ⟨hp, -⟩ := objectsF_apart tl tl' funs F G c c' h
  have key : ∀ i j : Nat, i < j → funs[i]? = some Fn → funs[j]? = some Fn → False := by
    intro i j hij hi hj
    have s1 : [Fn, Fn].Sublist funs.toList :=
      pair_sublist Fn Fn funs.toList i j hij (by simpa using hi) (by simpa using hj)
    have s2 := sublist_flatMap (segsOf tl' Fn.mat Fn.tree) s1
    have s3 : [(Fn, sg), (Fn, sg)].Sublist ([Fn, Fn].flatMap (segsOf tl' Fn.mat Fn.tree)) := by
      have one := List.singleton_sublist.2 (mem_segsOf tl' Fn sg hs)
      have two := one.append one
      simpa using two
    have s4 := (s3.trans s2).trans (part_sublist tl' funs Fn.mat Fn.tree hm hu)
    exact List.pairwise_pair.1 (hp.sublist s4) rfl d hd d hd rfl
  rcases Nat.lt_trichotomy n n' with h1 | h1 | h1
  · exact (key n n' h1 hn hn').elim
  · exact h1
  · exact (key n' n h1 hn' hn).elim

/-- If objectsF returns: two tables of the list, by their numbers, each with a column and a segment,
at one place of one part of the marks: the same number, column and segment. -/
theorem objectsF_onceAt (tl tl' : HTailF2) (funs : Array HFun) (F G : Fork) (c c' : Ctx)
    (h : tl.objectsF funs F c = .ok ((tl', G), c')) (n n' : Nat) (Fn Fn' : HFun)
    (hn : funs[n]? = some Fn) (hn' : funs[n']? = some Fn') (hm : Fn.mat < tl'.NM)
    (hm' : Fn'.mat < tl'.NM) (hu : Fn.tree = 0 ∨ Fn.tree = 2) (hu' : Fn'.tree = 0 ∨ Fn'.tree = 2)
    (e : Fn.tree / 2 = Fn'.tree / 2) (sg sg' d d' : Nat)
    (hs : sg < (tl'.mats.getD Fn.mat {}).m / Fn.len)
    (hs' : sg' < (tl'.mats.getD Fn'.mat {}).m / Fn'.len)
    (hd : d < (tl'.mats.getD Fn.mat {}).k) (hd' : d' < (tl'.mats.getD Fn'.mat {}).k)
    (he : posOf tl' Fn sg d = posOf tl' Fn' sg' d') : n = n' ∧ d = d' ∧ sg = sg' := by
  obtain ⟨exy, ed⟩ := objectsF_once tl tl' funs F G c c' h (Fn, sg) (Fn', sg')
    (mem_readsList tl' funs n Fn sg hn hm hu hs) (mem_readsList tl' funs n' Fn' sg' hn' hm' hu' hs')
    e d d' hd hd' he
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj exy
  exact ⟨objectsF_table_once tl tl' funs F G c c' h n n' Fn hn hn' hm hu sg d hs hd, ed, rfl⟩

/-- The place, written out. -/
theorem posOf_eq (tl : HTailF2) (Fn : HFun) (sg d : Nat) (hm : Fn.mat < tl.NM)
    (hs : sg < (tl.mats.getD Fn.mat {}).m / Fn.len) (hd : d < (tl.mats.getD Fn.mat {}).k) :
    posOf tl Fn sg d = Fn.start + d * ((tl.mats.getD Fn.mat {}).m / Fn.len) + sg := by
  have hl : Fn.len ≠ 0 := by
    intro e0
    rw [e0, Nat.div_zero] at hs
    omega
  unfold posOf HTailF2.tabAt
  rw [if_pos (by
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
    exact ⟨hm, hl⟩)]
  dsimp only
  rw [if_pos (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hd, hs⟩)]
  rfl

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.objectsF_onceAt
#print axioms OnBytes.Tie.Pv.Tail.posOf_eq
#print axioms OnBytes.Tie.Pv.Tail.objectsF_apart
#print axioms OnBytes.Tie.Pv.Tail.objectsF_once
