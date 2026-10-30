-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/TailClaims/MarksOfTiles.lean: THE TILING GIVES THE MARKS: where the tables of
the smallness test tile the parts of the first and the third vector that hold tables, the marking
of all reads' places returns, and every mark is set behind it. A general law, the way FORWARD: from
the plan's numbers to a return. Nothing is evaluated but a toy.

Why. The list "K8.equations" (Johnson/Desc/First/TailClaims/Equations.lean) keeps one mark for each
entry of these parts. Before a read is added its places are marked one by one, a place that is
marked already or lies outside is refused (HTailF2.markLoop, HTailF2.markRead,
OnBytes/Model/Tail.lean), and at the end all marks must be set. The library's laws on these marks
all start from a return (OnBytes/Tie/Pv/Tail/EndReads.lean, EndCover.lean, EndOnce.lean;
Johnson/Desc/First/TailClaims/EquationsCover.lean). Whoever is to show that the list returns at a
plan needs the other way. By evaluation it is out of reach at a large plan: the marks are an array
as long as the part, written one entry at a time, and Lean's kernel holds an array as a list. The
same list also tests that the tables tile the parts (HTailF2.tablesTile): that test walks the
TABLES, which are few. This file shows that it is enough.

  1  `tabAt_there`, `markLoop_fwd`, `markRead_fwd`, `fold_fwd`: the marking returns where the
     places are there, inside, not yet marked and apart from each other; what is then marked comes
     by the library's own laws from a return.
  2  `walk_tiles`, `stretch`, `Apart`, `tiles_say`: what a return of tablesTile says of the tables
     on one vector: their stretches do not meet, lie inside the part, are not empty, and cover it.
  3  `place_lt`, `place_inj`, `place_of`: column d and segment sg of a table with n segments lie
     at entry d * n + sg of its stretch: inside, at one place each, and every entry is such a
     place.
     `mem_segs`, `segs_nodup`, `reads_nodup`: under both tilings no read stands twice in the list.
  4  `none_marked`, `start_sizes`, **`marks_of_tiles`**: tablesTile returns at both vectors, there
     are at most two parts, each table's matrix is one of the NM ⊢ the fold of markRead over
     readsList from no mark returns some rd, and every mark of rd is set.
  5  A toy: a matrix of two rows and two columns with one table of two segments: both premises by
     evaluation, so the law is not empty (the first vector's part is empty in the toy: its tiling
     is met idly); and with the table moved by one entry the tiling refuses.

Limits. The law says nothing on whether the tables tile at any plan: that stays a test with code,
on the tables. One way: the converse is the library's. Nothing on what a read adds. Nothing on
soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Tail.EndOnce
import OnBytes.Tie.Pv.Tail.EndLoopsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law.Marks
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail OnBytes.Tie.Pv.Tail.Port

/-! ## 1 The marking returns where the places are there, free and apart -/

/-- Where the table's matrix, the segment and the column are there, tabAt names the place. -/
theorem tabAt_there {tl : HTailF2} {Fn : HFun} {sg d : Nat} (hm : Fn.mat < tl.NM)
    (hs : sg < (tl.mats.getD Fn.mat {}).m / Fn.len) (hd : d < (tl.mats.getD Fn.mat {}).k) :
    tl.tabAt Fn d sg = some (posOf tl Fn sg d) := by
  have hl : Fn.len ≠ 0 := by
    intro e0
    rw [e0, Nat.div_zero] at hs
    omega
  have e : tl.tabAt Fn d sg =
      some (Fn.start + d * ((tl.mats.getD Fn.mat {}).m / Fn.len) + sg) := by
    unfold HTailF2.tabAt
    simp [hm, hl]
    exact ⟨by simpa using hd, by simpa using hs⟩
  unfold posOf
  rw [e]
  rfl

/-- One read's loop. -/
theorem markLoop_fwd (tl : HTailF2) (Fn : HFun) (sg t0 : Nat) :
    ∀ (count c : Nat) (marks : Array Bool),
      (∀ d, c ≤ d → d < c + count → tl.tabAt Fn d sg = some (posOf tl Fn sg d) ∧
        t0 ≤ posOf tl Fn sg d ∧ posOf tl Fn sg d - t0 < marks.size ∧
        marks.getD (posOf tl Fn sg d - t0) false = false) →
      (∀ d d', c ≤ d → d < d' → d' < c + count → posOf tl Fn sg d ≠ posOf tl Fn sg d') →
      ∃ marks', tl.markLoop Fn sg t0 count c marks = some marks'
  | 0, c, marks, _, _ => ⟨marks, by simp only [HTailF2.markLoop]⟩
  | count + 1, c, marks, H, A => by
    obtain ⟨h0, h1, h2, h3⟩ := H c (Nat.le_refl c) (by omega)
    have hg : marks.getD (posOf tl Fn sg c - t0) true = false := by
      simp only [Array.getD, h2, dif_pos] at h3 ⊢
      exact h3
    simp only [HTailF2.markLoop, h0]
    rw [if_pos (by simp [h1, hg])]
    refine markLoop_fwd tl Fn sg t0 count (c + 1) _ (fun d hc hd => ?_)
      (fun d d' hc hdd hd => A d d' (by omega) hdd (by omega))
    obtain ⟨g0, g1, g2, g3⟩ := H d (by omega) (by omega)
    refine ⟨g0, g1, by simpa using g2, ?_⟩
    rw [set_else marks _ _ (fun e => A c d (Nat.le_refl c) (by omega) (by omega) (by omega))]
    exact g3

/-- One read. -/
theorem markRead_fwd (tl : HTailF2) (Fn : HFun) (sg : Nat) (rd : Array (Array Bool))
    (hm : Fn.mat < tl.NM) (hs : sg < (tl.mats.getD Fn.mat {}).m / Fn.len)
    (H : ∀ d, d < (tl.mats.getD Fn.mat {}).k →
      tl.tabFirst.getD (Fn.tree / 2) 0 ≤ posOf tl Fn sg d ∧
      posOf tl Fn sg d - tl.tabFirst.getD (Fn.tree / 2) 0 < marksOf rd (Fn.tree / 2) ∧
      ¬ markAt rd (Fn.tree / 2) (posOf tl Fn sg d - tl.tabFirst.getD (Fn.tree / 2) 0))
    (A : ∀ d d', d < d' → d' < (tl.mats.getD Fn.mat {}).k →
      posOf tl Fn sg d ≠ posOf tl Fn sg d') :
    ∃ rd', tl.markRead Fn sg rd = some rd' := by
  obtain ⟨m', hm'⟩ := markLoop_fwd tl Fn sg (tl.tabFirst.getD (Fn.tree / 2) 0)
    (tl.mats.getD Fn.mat {}).k 0 (rd.getD (Fn.tree / 2) #[])
    (fun d _ hd => by
      have hd' : d < (tl.mats.getD Fn.mat {}).k := by omega
      obtain ⟨a, b, c⟩ := H d hd'
      refine ⟨tabAt_there hm hs hd', a, b, ?_⟩
      unfold markAt at c
      simpa using c)
    (fun d d' _ hdd hd => A d d' hdd (by omega))
  unfold HTailF2.markRead
  simp only [hm', Option.map_some]
  exact ⟨_, rfl⟩

/-- **The reads one after the other.** len: the numbers of marks, part by part. -/
theorem fold_fwd (tl : HTailF2) (len : Nat → Nat) :
    ∀ (l : List (HFun × Nat)) (rd : Array (Array Bool)),
      (∀ p, marksOf rd p = len p) →
      (∀ x ∈ l, x.1.mat < tl.NM ∧ x.2 < (tl.mats.getD x.1.mat {}).m / x.1.len ∧
        (∀ d, d < (tl.mats.getD x.1.mat {}).k →
          tl.tabFirst.getD (x.1.tree / 2) 0 ≤ posOf tl x.1 x.2 d ∧
          posOf tl x.1 x.2 d - tl.tabFirst.getD (x.1.tree / 2) 0 < len (x.1.tree / 2) ∧
          ¬ markAt rd (x.1.tree / 2) (posOf tl x.1 x.2 d - tl.tabFirst.getD (x.1.tree / 2) 0)) ∧
        ∀ d d', d < d' → d' < (tl.mats.getD x.1.mat {}).k →
          posOf tl x.1 x.2 d ≠ posOf tl x.1 x.2 d') →
      l.Pairwise (PlacesApart tl) →
      ∃ rd', l.foldlM (fun rd x => tl.markRead x.1 x.2 rd) rd = some rd' ∧
        (∀ p, marksOf rd' p = len p) ∧ (∀ q i, markAt rd q i → markAt rd' q i) ∧
        ∀ x ∈ l, ∀ d, d < (tl.mats.getD x.1.mat {}).k →
          markAt rd' (x.1.tree / 2) (posOf tl x.1 x.2 d - tl.tabFirst.getD (x.1.tree / 2) 0)
  | [], rd, hz, _, _ => ⟨rd, rfl, hz, fun _ _ h => h, fun _ hx => by cases hx⟩
  | x :: l, rd, hz, H, P => by
    obtain ⟨hm, hs, hp, ha⟩ := H x (List.mem_cons_self ..)
    obtain ⟨r1, h1⟩ := markRead_fwd tl x.1 x.2 rd hm hs
      (fun d hd => by
        obtain ⟨a, b, c⟩ := hp d hd
        exact ⟨a, by rw [hz]; exact b, c⟩) ha
    obtain ⟨S, -⟩ := markRead_spec tl x.1 x.2 rd r1 h1
    obtain ⟨O1, O2, -⟩ := markRead_once tl x.1 x.2 rd r1 h1
    obtain ⟨Px, Pl⟩ := List.pairwise_cons.1 P
    obtain ⟨rd', hf, hz', hk, hn⟩ := fold_fwd tl len l r1 (fun p => by rw [S, hz])
      (fun y hy => by
        obtain ⟨ym, ys, yp, ya⟩ := H y (List.mem_cons_of_mem _ hy)
        refine ⟨ym, ys, fun d hd => ?_, ya⟩
        obtain ⟨a, b, c⟩ := yp d hd
        refine ⟨a, b, fun hmk => ?_⟩
        rcases markRead_marks tl x.1 x.2 rd r1 h1 _ _ hmk with h | ⟨e, d', hd', he⟩
        · exact c h
        · exact Px y hy e.symm d' hd' d hd (by rw [he]; omega)) Pl
    refine ⟨rd', ?_, hz', fun q i h => hk q i (O1 q i h), fun y hy d hd => ?_⟩
    · rw [List.foldlM_cons, h1]
      exact hf
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact hk _ _ (O2 d hd).2.2
      · exact hn y hy d hd

/-! ## 2 What a tiling says -/

/-- The walk of tablesTile over the sorted stretches (first entry, length, segments), as a function
of its step. Where it returns, the stretches follow each other from p0 to p1: each lies behind the
ones in front; each lies inside and is not empty; every entry between p0 and p1 lies in one. -/
theorem walk_tiles (f : Option (Nat × Nat) → Nat × Nat × Nat → Option (Nat × Nat))
    (hn : ∀ x, f none x = none)
    (hf : ∀ p g x, f (some (p, g)) x =
      if x.2.1 != 0 && x.1 == p then some (p + x.2.1, g + x.2.2) else none) :
    ∀ (L : List (Nat × Nat × Nat)) (p0 g0 p1 g1 : Nat),
      L.foldl f (some (p0, g0)) = some (p1, g1) →
      p0 ≤ p1 ∧ L.Pairwise (fun a b => a.1 + a.2.1 ≤ b.1) ∧
        (∀ a ∈ L, p0 ≤ a.1 ∧ a.1 + a.2.1 ≤ p1 ∧ a.2.1 ≠ 0) ∧
        ∀ i, p0 ≤ i → i < p1 → ∃ a ∈ L, a.1 ≤ i ∧ i < a.1 + a.2.1
  | [], p0, g0, p1, g1, h => by
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨Nat.le_refl _, List.Pairwise.nil, (fun _ ha => by cases ha), (fun i a b => by omega)⟩
  | a :: L, p0, g0, p1, g1, h => by
    rw [List.foldl_cons, hf] at h
    by_cases hc : (a.2.1 != 0 && a.1 == p0) = true
    · rw [if_pos hc] at h
      obtain ⟨c1, c2⟩ : a.2.1 ≠ 0 ∧ a.1 = p0 := by simpa using hc
      obtain ⟨i0, i1, i2, i3⟩ := walk_tiles f hn hf L _ _ _ _ h
      refine ⟨by omega, List.pairwise_cons.2 ⟨fun b hb => by have := (i2 b hb).1; omega, i1⟩,
        fun b hb => ?_, fun i h0 h1 => ?_⟩
      · rcases List.mem_cons.1 hb with rfl | hb
        · exact ⟨by omega, by omega, c1⟩
        · obtain ⟨x, y, z⟩ := i2 b hb
          exact ⟨by omega, y, z⟩
      · by_cases hi : i < p0 + a.2.1
        · exact ⟨a, List.mem_cons_self .., by omega, by omega⟩
        · obtain ⟨b, hb, x, y⟩ := i3 i (by omega) h1
          exact ⟨b, List.mem_cons_of_mem _ hb, x, y⟩
    · rw [if_neg hc] at h
      have : ∀ (L : List (Nat × Nat × Nat)), L.foldl f none = none := by
        intro L
        induction L with
        | nil => rfl
        | cons b L ih => rw [List.foldl_cons, hn, ih]
      rw [this] at h
      cases h

/-- A table's stretch: its first entry, its number of entries, its number of segments. -/
def stretch (tl : HTailF2) (Fn : HFun) : Nat × Nat × Nat :=
  (Fn.start, (tl.mats.getD Fn.mat {}).k * ((tl.mats.getD Fn.mat {}).m / Fn.len),
    (tl.mats.getD Fn.mat {}).m / Fn.len)

/-- Two stretches do not meet. -/
def Apart (a b : Nat × Nat × Nat) : Prop := a.1 + a.2.1 ≤ b.1 ∨ b.1 + b.2.1 ≤ a.1

/-- **What tablesTile's return says of the tables on one vector.** -/
theorem tiles_say {tl : HTailF2} {funs : Array HFun} {un s : Nat}
    (h : tl.tablesTile funs un = some s) :
    ((funs.toList.filter fun Fn => Fn.tree == un).Pairwise fun a b =>
        Apart (stretch tl a) (stretch tl b)) ∧
      (∀ Fn ∈ funs.toList, Fn.tree = un → tl.tabFirst.getD (un / 2) 0 ≤ Fn.start ∧
        Fn.start + (stretch tl Fn).2.1 ≤ tl.tabFirst.getD (un / 2) 0 + tl.tabLen.getD (un / 2) 0 ∧
        (stretch tl Fn).2.1 ≠ 0) ∧
      ∀ i, i < tl.tabLen.getD (un / 2) 0 → ∃ Fn ∈ funs.toList, Fn.tree = un ∧
        Fn.start ≤ tl.tabFirst.getD (un / 2) 0 + i ∧
        tl.tabFirst.getD (un / 2) 0 + i < Fn.start + (stretch tl Fn).2.1 := by
  unfold HTailF2.tablesTile at h
  simp only [] at h
  obtain ⟨⟨p1, g1⟩, hw, he⟩ := Option.bind_eq_some_iff.1 h
  have hp : p1 = tl.tabFirst.getD (un / 2) 0 + tl.tabLen.getD (un / 2) 0 := by
    by_cases hc : (p1 == tl.tabFirst.getD (un / 2) 0 + tl.tabLen.getD (un / 2) 0 &&
        ((tl.ix.U.getD un none).isNone || decide (p1 ≤ tl.nUF.getD un 0))) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact hc.1
    · simp only [hc] at he
      cases he
  obtain ⟨-, w1, w2, w3⟩ := walk_tiles _ (fun _ => rfl) (fun _ _ _ => rfl) _ _ _ _ _ hw
  have perm := List.mergeSort_perm ((funs.toList.filter fun Fn => Fn.tree == un).map (stretch tl))
    (fun a b => decide (a.1 ≤ b.1))
  refine ⟨?_, fun Fn hF ht => ?_, fun i hi => ?_⟩
  · have := (perm.pairwise_iff (R := Apart) (fun hab => Or.symm hab)).1
      (w1.imp fun hab => Or.inl hab)
    exact List.pairwise_map.1 this
  · have hmem : stretch tl Fn ∈ (funs.toList.filter fun Fn => Fn.tree == un).map (stretch tl) :=
      List.mem_map.2 ⟨Fn, List.mem_filter.2 ⟨hF, by simp [ht]⟩, rfl⟩
    obtain ⟨a, b, c⟩ := w2 _ (perm.mem_iff.2 hmem)
    exact ⟨a, by rw [← hp]; exact b, c⟩
  · obtain ⟨a, ha, x, y⟩ := w3 (tl.tabFirst.getD (un / 2) 0 + i) (by omega) (by omega)
    obtain ⟨Fn, hF, rfl⟩ := List.mem_map.1 (perm.mem_iff.1 ha)
    obtain ⟨hF1, hF2⟩ := List.mem_filter.1 hF
    exact ⟨Fn, hF1, by simpa using hF2, x, y⟩

/-! ## 3 The places of one table -/

theorem place_lt {d k sg n : Nat} (hd : d < k) (hs : sg < n) : d * n + sg < k * n := by
  have h : (d + 1) * n ≤ k * n := Nat.mul_le_mul_right _ hd
  rw [Nat.add_mul, Nat.one_mul] at h
  omega

theorem place_inj {d d' sg sg' n : Nat} (hs : sg < n) (hs' : sg' < n)
    (h : d * n + sg = d' * n + sg') : d = d' ∧ sg = sg' := by
  have e : sg = sg' := by
    have := congrArg (· % n) h
    simp only [Nat.add_comm (_ * n), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs,
      Nat.mod_eq_of_lt hs'] at this
    exact this
  subst e
  have h' : d * n = d' * n := by omega
  exact ⟨Nat.eq_of_mul_eq_mul_right (by omega : 0 < n) h', rfl⟩

/-- Every entry of a table's stretch is the place of one column and one segment. -/
theorem place_of {i k n : Nat} (h : i < k * n) : ∃ d sg, d < k ∧ sg < n ∧ d * n + sg = i := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at h
    · exact hn
  refine ⟨i / n, i % n, (Nat.div_lt_iff_lt_mul hn).2 h, Nat.mod_lt _ hn, ?_⟩
  rw [Nat.mul_comm]
  exact Nat.div_add_mod i n

/-- What lies in segsOf. -/
theorem mem_segs {tl : HTailF2} {mu un : Nat} {Fn : HFun} {x : HFun × Nat}
    (h : x ∈ segsOf tl mu un Fn) : x.1 = Fn ∧ Fn.mat = mu ∧ Fn.tree = un := by
  unfold segsOf at h
  split at h
  · rename_i hc
    obtain ⟨sg, -, rfl⟩ := List.mem_map.1 h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨rfl, hc.1, hc.2⟩
  · cases h

theorem segs_nodup (tl : HTailF2) (mu un : Nat) (Fn : HFun) : (segsOf tl mu un Fn).Nodup := by
  unfold segsOf
  split
  · exact List.Nodup.map (fun a b h => (Prod.mk.inj h).2) List.nodup_range
  · exact List.nodup_nil

/-- **Under both tilings no read stands twice in the list.** -/
theorem reads_nodup {tl : HTailF2} {funs : Array HFun} {s1 s3 : Nat}
    (h0 : tl.tablesTile funs 0 = some s1) (h2 : tl.tablesTile funs 2 = some s3) :
    (readsList tl funs).Nodup := by
  have inner : ∀ mu un, (un = 0 ∨ un = 2) → (funs.toList.flatMap (segsOf tl mu un)).Nodup := by
    intro mu un hu
    obtain ⟨s, hs⟩ : ∃ s, tl.tablesTile funs un = some s := by
      rcases hu with rfl | rfl
      · exact ⟨_, h0⟩
      · exact ⟨_, h2⟩
    obtain ⟨t1, t2, -⟩ := tiles_say hs
    refine List.nodup_flatMap.2 ⟨fun Fn _ => segs_nodup tl mu un Fn, ?_⟩
    have hp := List.pairwise_filter.1 t1
    have hq : funs.toList.Pairwise fun a b => a ∈ funs.toList ∧
        ((a.tree == un) = true → (b.tree == un) = true → Apart (stretch tl a) (stretch tl b)) :=
      (List.pairwise_iff_forall_sublist.2 fun {a b} hab =>
        ⟨hab.subset (List.mem_cons_self ..), (List.pairwise_iff_forall_sublist.1 hp) hab⟩)
    refine hq.imp ?_
    rintro a b ⟨ha, hab⟩ x hxa hxb
    obtain ⟨e1, -, e3⟩ := mem_segs hxa
    obtain ⟨f1, -, f3⟩ := mem_segs hxb
    have hE : a = b := e1.symm.trans f1
    subst hE
    have := hab (by simp [e3]) (by simp [e3])
    have hne := (t2 a ha e3).2.2
    unfold Apart at this
    omega
  unfold readsList
  refine List.nodup_flatMap.2 ⟨fun mu _ => ?_, ?_⟩
  · refine List.nodup_flatMap.2 ⟨fun un hu => inner mu un (by simpa using hu), ?_⟩
    refine List.pairwise_cons.2 ⟨fun b hb => ?_, List.pairwise_singleton _ _⟩
    obtain rfl : b = 2 := by simpa using hb
    intro x hx0 hx2
    obtain ⟨F, -, hF⟩ := List.mem_flatMap.1 hx0
    obtain ⟨G, -, hG⟩ := List.mem_flatMap.1 hx2
    obtain ⟨a1, -, a3⟩ := mem_segs hF
    obtain ⟨b1, -, b3⟩ := mem_segs hG
    rw [← a1] at a3
    rw [← b1] at b3
    omega
  · refine List.nodup_range.imp ?_
    intro a b hab x hxa hxb
    obtain ⟨u, -, hu⟩ := List.mem_flatMap.1 hxa
    obtain ⟨v, -, hv⟩ := List.mem_flatMap.1 hxb
    obtain ⟨F, -, hF⟩ := List.mem_flatMap.1 hu
    obtain ⟨G, -, hG⟩ := List.mem_flatMap.1 hv
    obtain ⟨a1, a2, -⟩ := mem_segs hF
    obtain ⟨b1, b2, -⟩ := mem_segs hG
    rw [← a1] at a2
    rw [← b1] at b2
    exact hab (a2.symm.trans b2)

/-! ## 4 The tiling gives the marks -/

/-- No mark is set at the start. -/
theorem none_marked (tl : HTailF2) (p i : Nat) :
    ¬ markAt (tl.tabLen.map fun n => Array.replicate n false) p i := by
  unfold markAt
  by_cases hp : p < tl.tabLen.size
  · by_cases hi : i < tl.tabLen[p]
    · simp [Array.getD, hp, hi]
    · simp [Array.getD, hp, hi]
  · simp [Array.getD, hp]

theorem start_sizes (tl : HTailF2) (p : Nat) :
    marksOf (tl.tabLen.map fun n => Array.replicate n false) p = tl.tabLen.getD p 0 := by
  unfold marksOf
  by_cases hp : p < tl.tabLen.size
  · simp [Array.getD, hp]
  · simp [Array.getD, hp]

/-- **THE TILING GIVES THE MARKS.** Where the tables on the first and on the third vector tile their
parts, each table's matrix is there and there are at most two parts: marking the places of all
reads, one read after the other, from no mark, returns, and every mark is set behind it. -/
theorem marks_of_tiles {tl : HTailF2} {funs : Array HFun} {s1 s3 : Nat}
    (h0 : tl.tablesTile funs 0 = some s1) (h2 : tl.tablesTile funs 2 = some s3)
    (hz : tl.tabLen.size ≤ 2) (hin : ∀ Fn ∈ funs.toList, Fn.mat < tl.NM) :
    ∃ rd, (readsList tl funs).foldlM (fun rd x => tl.markRead x.1 x.2 rd)
        (tl.tabLen.map fun n => Array.replicate n false) = some rd ∧
      (rd.all fun a => a.all id) = true := by
  have tile : ∀ un, (un = 0 ∨ un = 2) → ∃ s, tl.tablesTile funs un = some s := by
    rintro un (rfl | rfl)
    · exact ⟨_, h0⟩
    · exact ⟨_, h2⟩
  -- a read's places, written out, lie in its table's stretch
  have inside : ∀ Fn sg, (Fn, sg) ∈ readsList tl funs → ∀ d, d < (tl.mats.getD Fn.mat {}).k →
      posOf tl Fn sg d = Fn.start + d * ((tl.mats.getD Fn.mat {}).m / Fn.len) + sg ∧
      Fn.start ≤ posOf tl Fn sg d ∧ posOf tl Fn sg d < Fn.start + (stretch tl Fn).2.1 := by
    intro Fn sg hx d hd
    obtain ⟨-, hm, -, hs⟩ := (Port.mem_readsList tl funs Fn sg).1 hx
    have e := posOf_eq tl Fn sg d hm hs hd
    have := place_lt hd hs
    refine ⟨e, by omega, ?_⟩
    show _ < Fn.start + (tl.mats.getD Fn.mat {}).k * ((tl.mats.getD Fn.mat {}).m / Fn.len)
    omega
  obtain ⟨rd, hf, hsz, -, hset⟩ := fold_fwd tl (fun p => tl.tabLen.getD p 0) (readsList tl funs)
    (tl.tabLen.map fun n => Array.replicate n false) (start_sizes tl)
    (by
      rintro ⟨Fn, sg⟩ hx
      obtain ⟨hF, hm, hu, hs⟩ := (Port.mem_readsList tl funs Fn sg).1 hx
      obtain ⟨s, ht⟩ := tile Fn.tree hu
      obtain ⟨-, t2, -⟩ := tiles_say ht
      obtain ⟨a, b, -⟩ := t2 Fn hF rfl
      refine ⟨hm, hs, fun d hd => ?_, fun d d' hdd hd' he => ?_⟩
      · dsimp only at hd ⊢
        obtain ⟨-, i1, i2⟩ := inside Fn sg hx d hd
        exact ⟨by omega, by omega, none_marked tl _ _⟩
      · dsimp only at hd' he
        rw [(inside Fn sg hx d (by omega)).1, (inside Fn sg hx d' hd').1] at he
        have := (place_inj hs hs (by omega : d * _ + sg = d' * _ + sg)).1
        omega)
    ((reads_nodup h0 h2).pairwise_of_forall_ne (by
      rintro ⟨Fn, sg⟩ hx ⟨Gn, sg'⟩ hy hne e d hd d' hd' he
      dsimp only at e hd hd' he
      obtain ⟨hF, -, hu, hs⟩ := (Port.mem_readsList tl funs Fn sg).1 hx
      obtain ⟨hG, -, hv, hs'⟩ := (Port.mem_readsList tl funs Gn sg').1 hy
      obtain ⟨x0, x1, x2⟩ := inside Fn sg hx d hd
      obtain ⟨y0, y1, y2⟩ := inside Gn sg' hy d' hd'
      have et : Fn.tree = Gn.tree := by
        have e' : Fn.tree / 2 = Gn.tree / 2 := e
        rcases hu with a | a <;> rcases hv with b | b <;> rw [a, b] at e' <;> omega
      by_cases hFG : Fn = Gn
      · subst hFG
        rw [x0, y0] at he
        exact hne (by rw [(place_inj hs hs' (by omega : d * _ + sg = d' * _ + sg')).2])
      · obtain ⟨s, ht⟩ := tile Fn.tree hu
        obtain ⟨t1, -, -⟩ := tiles_say ht
        have := t1.forall (fun a b hab => Or.symm hab)
          (List.mem_filter.2 ⟨hF, by simp⟩) (List.mem_filter.2 ⟨hG, by simp [et]⟩) hFG
        unfold Apart at this
        have s1 : (stretch tl Fn).1 = Fn.start := rfl
        have s2 : (stretch tl Gn).1 = Gn.start := rfl
        omega))
  refine ⟨rd, hf, ?_⟩
  rw [Array.all_eq_true]
  intro q hq
  rw [Array.all_eq_true]
  intro i hi
  have hsq : rd[q].size = tl.tabLen.getD q 0 := by
    have := hsz q
    unfold marksOf at this
    simpa [Array.getD, hq] using this
  have hq2 : q < 2 := by
    by_contra hc
    have : tl.tabLen.getD q 0 = 0 := by simp [Array.getD, show ¬ q < tl.tabLen.size by omega]
    omega
  have hun : (2 * q = 0 ∨ 2 * q = 2) := by omega
  obtain ⟨s, ht⟩ := tile (2 * q) hun
  obtain ⟨-, -, t3⟩ := tiles_say ht
  have hh : 2 * q / 2 = q := by omega
  rw [hh] at t3
  obtain ⟨Fn, hF, hT, a, b⟩ := t3 i (by omega)
  obtain ⟨d, sg, hd, hs, hp⟩ := place_of (i := tl.tabFirst.getD q 0 + i - Fn.start)
    (k := (tl.mats.getD Fn.mat {}).k) (n := (tl.mats.getD Fn.mat {}).m / Fn.len) (by
      have : (stretch tl Fn).2.1 =
        (tl.mats.getD Fn.mat {}).k * ((tl.mats.getD Fn.mat {}).m / Fn.len) := rfl
      omega)
  have hx : (Fn, sg) ∈ readsList tl funs :=
    (Port.mem_readsList tl funs Fn sg).2 ⟨hF, hin Fn hF, by omega, hs⟩
  have hm := hset (Fn, sg) hx d hd
  have hpos := (inside Fn sg hx d hd).1
  have hpart : Fn.tree / 2 = q := by omega
  simp only [hpart] at hm
  have hidx : posOf tl Fn sg d - tl.tabFirst.getD q 0 = i := by omega
  rw [hidx] at hm
  unfold markAt at hm
  simpa [Array.getD, hq, hi] using hm

/-! ## 5 A toy -/

/-- One matrix of two rows and two columns; the third vector's part has four entries. -/
def toyTl : HTailF2 := { NM := 1, mats := #[{ m := 2, k := 2 }], tabLen := #[0, 4] }

/-- One table on it, of two segments of one row each, from entry a on. -/
def toyFuns (a : Nat) : Array HFun := #[{ mat := 0, len := 1, tree := 2, start := a }]

theorem toy_tiles : toyTl.tablesTile (toyFuns 0) 0 = some 0 ∧
    toyTl.tablesTile (toyFuns 0) 2 = some 2 := by decide +kernel

/-- The law at the toy: its premises can be met together. -/
theorem toy_marks : ∃ rd, (readsList toyTl (toyFuns 0)).foldlM
    (fun rd x => toyTl.markRead x.1 x.2 rd) (toyTl.tabLen.map fun n => Array.replicate n false) =
      some rd ∧ (rd.all fun a => a.all id) = true :=
  marks_of_tiles toy_tiles.1 toy_tiles.2 (by decide) (by decide)

/-- A negative test: with the table moved by one entry the tiling refuses. -/
theorem toy_no : toyTl.tablesTile (toyFuns 1) 2 = none := by decide +kernel

end VerifiableInference.Desc.First.TailClaims.Law.Marks

#print axioms VerifiableInference.Desc.First.TailClaims.Law.Marks.toy_tiles
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Marks.toy_marks
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Marks.toy_no
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Marks.none_marked
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Marks.start_sizes
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Marks.mem_segs
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Marks.segs_nodup
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Marks.marks_of_tiles
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Marks.place_lt
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Marks.place_inj
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Marks.place_of
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Marks.reads_nodup
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Marks.walk_tiles
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Marks.tiles_say
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Marks.fold_fwd
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Marks.tabAt_there
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Marks.markLoop_fwd
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Marks.markRead_fwd
