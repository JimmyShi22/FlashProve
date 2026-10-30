-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CountsHeadPub.lean

If Head.layout returns, its public numbers of padding keys of the lookup of the output head's calls
count the padding places of the calls' key vectors, tree by tree.

The lookup of the calls of the output head's sub-proof cuts the calls' key vectors into trees of
2^dT places. Some places are padding places. The Lean verifier under OnBytes/Model/ counts them tree
by tree when it lays the sub-proof out (Head.pubOf, OnBytes/Model/HeadLayout.lean): the field pub of
the layout's Forest.Shape. The library's terms for the key vectors (Ends.H.kvH,
OnBytes/Tie/Pv/Lookup/Ends/H.lean) find the entry that stands in a column by Ends.H.colH. This file
says by colH which places are padding places ("padH") and shows that pub counts these.

Main definition and theorems:
* "padH h L q i": place i of call q lies in column i / T. It is a padding place if colH finds no
  entry in that column, or finds entry x of one of the five segments with one entry for each
  vocabulary entry (Head.perEntry) with h.V ≤ Head.firstEntry L sn + x.
* "pubFits_H": if Head.layout h tau returns L, then PubFits L.fs (padH h L)
  (Johnson/HonestTrace/Counts.lean): for every tree y below NT, pub[y] is the number of the x
  below 2^dT for which place x + 2^dT (y % 2^iota) of the tree's call is a padding place.
* "HeadPub.entry_seg": if Head.layout h tau returns L, and colH finds entry x of a segment sn in a
  column, then the first member of Head.segments h L with the name sn has more than x entries.
* "HeadPub.entry_lt": if Head.layout h tau returns L, and colH finds entry x of a segment sn with
  Head.perEntry sn in a column, then Head.firstEntry L sn + x is below L.JV.

The steps stand in the namespace HeadPub: "forIn_adds" (a "for" loop that adds to an array of
numbers), "pubOf_get" (what Head.pubOf returns, tree by tree), "col_sum" (a sum over columns as a
sum over the entries of segments that share no column), "laid_place" and "laid_of_layout" (what is
used of the placing rule, from Johnson/Road/HeadCallsLaid.lean and Johnson/Road/FormsKeysPub.lean),
"pubCall_in" and "pubCall_out" (what one call adds to a tree of its own, and to another tree).

Limits. All statements are on public numbers of a layout: no cell, key, challenge or message
occurs. That Head.layout returns a layout for some shape is not shown in this file. A sub-proof has
a second lookup, of the smallness test's digits; this file is not on it. padH is this file's own
definition. What the key vectors hold at its places is not said here; see
Johnson/HonestTrace/CountsHead.lean.

Not claimed: that the C++ programs count so; that a verifier accepts anything; anything on
soundness or zero knowledge.

-/
import Johnson.HonestTrace.CountsJoint
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPubH
import OnBytes.Tie.Pv.Lookup.Peel.FoPayCaller
import Johnson.Road.HeadCallsLaid
import Johnson.Road.FormsKeysPub

set_option autoImplicit false

namespace OnBytes.HonestTrace

open Finset
open OnBytes.Model

/-- Whether place i of call q of the lookup of the output head's calls is a padding place. The place
lies in column i / T. It is a padding place if Ends.H.colH finds no entry in that column, and also
if colH finds entry x of a segment sn with Head.perEntry sn (one entry for each vocabulary entry)
and h.V ≤ Head.firstEntry L sn + x. For a number q that is no call's, colH finds nothing, so every
place is a padding place. -/
def padH (h : Head.Shape) (L : Head.HL) (q i : ℕ) : Bool :=
  match Ends.H.colH L q (i / h.T) with
  | some (sn, x) => Head.perEntry sn && decide (h.V ≤ Head.firstEntry L sn + x)
  | none => true

namespace HeadPub

/-! ## Loops that add to an array of numbers -/

/-- A "for" loop over a list, in Except String, on an array of numbers. Suppose that every step f x
pub that returns, on an array of size n, goes on to the next member (it yields), that Pr x then
holds, and that the step keeps the size and adds A x y at every index y below n. Then a loop that
returns, from an array of size n, has Pr at every member of the list, keeps the size, and adds at
every index y below n the sum of A x y over the list. -/
theorem forIn_adds {α : Type} (f : α → Array ℕ → Except String (ForInStep (Array ℕ)))
    (A : α → ℕ → ℕ) (n : ℕ) (Pr : α → Prop)
    (hf : ∀ x pub s, pub.size = n → f x pub = .ok s →
      ∃ pub', s = .yield pub' ∧ Pr x ∧ pub'.size = n ∧
        ∀ y, y < n → pub'.getD y 0 = pub.getD y 0 + A x y) :
    ∀ (l : List α) (pub pub' : Array ℕ), pub.size = n → forIn l pub f = .ok pub' →
      (∀ x ∈ l, Pr x) ∧ pub'.size = n ∧
        ∀ y, y < n → pub'.getD y 0 = pub.getD y 0 + (l.map fun x => A x y).sum
  | [], pub, pub', hs, h => by
    rw [List.forIn_nil] at h
    have e : pub = pub' := Except.ok.inj (show Except.ok pub = Except.ok pub' from h)
    subst e
    exact ⟨fun x hx => absurd hx List.not_mem_nil, hs, fun y _ => by simp⟩
  | x :: l, pub, pub', hs, h => by
    rw [List.forIn_cons] at h
    obtain ⟨s, h1, h2⟩ := Road.ok_of_bind h
    obtain ⟨p1, rfl, hp, s1, e1⟩ := hf x pub s hs h1
    obtain ⟨hq, s2, e2⟩ := forIn_adds f A n Pr hf l p1 pub' s1 h2
    refine ⟨fun z hz => ?_, s2, fun y hy => ?_⟩
    · rcases List.mem_cons.mp hz with e | e
      · exact e ▸ hp
      · exact hq z e
    · rw [e2 y hy, e1 y hy, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- Adding T at the index ix of an array of size n: the size stays n, and an index y below n then
holds T more if ix = y, and what it held if not. -/
theorem modify_adds (pub : Array ℕ) (ix T n : ℕ) (hs : pub.size = n) :
    (pub.modify ix (· + T)).size = n ∧ ∀ y, y < n →
      (pub.modify ix (· + T)).getD y 0 = pub.getD y 0 + if ix = y then T else 0 := by
  refine ⟨by rw [Array.size_modify]; exact hs, fun y hy => ?_⟩
  by_cases e : ix = y
  · have hi : ix < pub.size := by rw [e, hs]; exact hy
    rw [Road.getD_modify_add pub ix y T hi, if_pos e, if_pos e]
  · have hy' : y < pub.size := by rw [hs]; exact hy
    rw [if_neg e, Nat.add_zero]
    simp [Array.getD, hy', Array.getElem_modify, e]

/-- A step that adds T at the index ix and goes on, in the form that forIn_adds asks. -/
theorem step_mod (ix T n : ℕ) (pub : Array ℕ) (s : ForInStep (Array ℕ)) (hs : pub.size = n)
    (hx : (Except.ok (ForInStep.yield (pub.modify ix (· + T))) : Except String _) = .ok s) :
    ∃ pub', s = .yield pub' ∧ True ∧ pub'.size = n ∧
      ∀ y, y < n → pub'.getD y 0 = pub.getD y 0 + if ix = y then T else 0 :=
  ⟨_, (Except.ok.inj hx).symm, trivial, (modify_adds pub ix T n hs).1,
    (modify_adds pub ix T n hs).2⟩

/-- A step that adds T at the index ix if c is true, changes nothing if not, and goes on, in the
form that forIn_adds asks. -/
theorem step_if (c : Bool) (ix T n : ℕ) (pub : Array ℕ) (s : ForInStep (Array ℕ))
    (hs : pub.size = n)
    (hx : (if c = true then
        (Except.ok (ForInStep.yield (pub.modify ix (· + T))) : Except String _)
      else Except.ok (ForInStep.yield pub)) = .ok s) :
    ∃ pub', s = .yield pub' ∧ True ∧ pub'.size = n ∧
      ∀ y, y < n → pub'.getD y 0 = pub.getD y 0 + if c = true ∧ ix = y then T else 0 := by
  by_cases hc : c = true
  · rw [if_pos hc] at hx
    obtain ⟨p, e, -, s1, e1⟩ := step_mod ix T n pub s hs hx
    refine ⟨p, e, trivial, s1, fun y hy => ?_⟩
    rw [e1 y hy]
    by_cases k : ix = y
    · rw [if_pos k, if_pos ⟨hc, k⟩]
    · rw [if_neg k, if_neg fun q => k q.2]
  · rw [if_neg hc] at hx
    exact ⟨pub, (Except.ok.inj hx).symm, trivial, hs, fun y _ => by
      rw [if_neg fun q => hc q.1, Nat.add_zero]⟩

/-! ## What Head.pubOf returns -/

/-- What the loops of Head.pubOf add to the count of tree y for one call cd. cs: a tree holds 2^cs
columns; base: the call's first tree. T for each column j below cd.J whose mark is 0 and whose tree
base + j / 2^cs is y; and, in each segment g with Head.perEntry g.name, T for each entry from h.V -
Head.firstEntry L g.name on, below g.n, whose column's tree is y. -/
def pubCall (h : Head.Shape) (L : Head.HL) (cs base : ℕ) (cd : CallD) (y : ℕ) : ℕ :=
  ((List.range cd.J).map fun j =>
    if (cd.used.getD j 0 == 0) = true ∧ base + j / 2 ^ cs = y then h.T else 0).sum +
  (cd.segs.map fun g => if Head.perEntry g.name = true then
      ((List.range (g.n - (h.V - Head.firstEntry L g.name))).map fun x =>
        if base + g.pos.getD (h.V - Head.firstEntry L g.name + x) 0 / 2 ^ cs = y then h.T
        else 0).sum
    else 0).sum

/-- If Head.pubOf h L fs calls returns pub: every call cd with its number q has cd.J / 2^(dT - lt) =
2^iota[q]; pub has fs.NT members; and for y below fs.NT, pub[y] is the sum of pubCall over the
calls, each at its first tree fs.first[q]. -/
theorem pubOf_get {h : Head.Shape} {L : Head.HL} {fs : Forest.Shape} {calls : List CallD}
    {pub : Array ℕ} (e : Head.pubOf h L fs calls = .ok pub) :
    (∀ x ∈ calls.zipIdx, x.1.J / 2 ^ (fs.dT - h.lt) = 2 ^ fs.iota.getD x.2 0) ∧
    pub.size = fs.NT ∧ ∀ y, y < fs.NT → pub.getD y 0 =
      (calls.zipIdx.map fun x =>
        pubCall h L (fs.dT - h.lt) (fs.first.getD x.2 0) x.1 y).sum := by
  unfold Head.pubOf at e
  dsimp only at e
  obtain ⟨r, h1, h2⟩ := Road.ok_of_bind e
  have er : r = pub := Except.ok.inj (show Except.ok r = Except.ok pub from h2)
  subst er
  have key : (∀ x ∈ calls.zipIdx, x.1.J / 2 ^ (fs.dT - h.lt) = 2 ^ fs.iota.getD x.2 0) ∧
      r.size = fs.NT ∧ ∀ y, y < fs.NT → r.getD y 0 = (Array.replicate fs.NT 0).getD y 0 +
        (calls.zipIdx.map fun x =>
          pubCall h L (fs.dT - h.lt) (fs.first.getD x.2 0) x.1 y).sum := by
    refine forIn_adds _ (fun x y => pubCall h L (fs.dT - h.lt) (fs.first.getD x.2 0) x.1 y)
      fs.NT (fun x => x.1.J / 2 ^ (fs.dT - h.lt) = 2 ^ fs.iota.getD x.2 0) ?_ _ _ _
      (Array.size_replicate ..) h1
    rintro ⟨cd, q⟩ p s hs hx
    dsimp only at hx
    obtain ⟨hn, hx⟩ := Road.Hd.ok_of_needed hx
    obtain ⟨r1, g1, hx⟩ := Road.ok_of_bind hx
    obtain ⟨r2, g2, hx⟩ := Road.ok_of_bind hx
    obtain ⟨-, s1, e1⟩ := forIn_adds _ (fun j y =>
      if (cd.used.getD j 0 == 0) = true ∧ fs.first.getD q 0 + j / 2 ^ (fs.dT - h.lt) = y
      then h.T else 0) fs.NT (fun _ => True)
      (fun j p s hs hx => step_if _ _ _ _ p s hs hx) _ _ _ hs g1
    obtain ⟨-, s2, e2⟩ := forIn_adds _ (fun (g : Seg) y =>
      if Head.perEntry g.name = true then
        ((List.range (g.n - (h.V - Head.firstEntry L g.name))).map fun x =>
          if fs.first.getD q 0 +
            g.pos.getD (h.V - Head.firstEntry L g.name + x) 0 / 2 ^ (fs.dT - h.lt) = y
          then h.T else 0).sum
      else 0) fs.NT (fun _ => True)
      (fun g p s hs hx => by
        by_cases hp : Head.perEntry g.name = true
        · rw [if_pos hp] at hx
          obtain ⟨r3, g3, hx⟩ := Road.ok_of_bind hx
          obtain ⟨-, s3, e3⟩ := forIn_adds _ (fun x y =>
            if fs.first.getD q 0 +
              g.pos.getD (h.V - Head.firstEntry L g.name + x) 0 / 2 ^ (fs.dT - h.lt) = y
            then h.T else 0) fs.NT (fun _ => True)
            (fun x p s hs hx => step_mod _ _ _ p s hs hx) _ _ _ hs g3
          refine ⟨r3, (Except.ok.inj hx).symm, trivial, s3, fun y hy => ?_⟩
          rw [e3 y hy]
          dsimp only
          rw [if_pos hp]
        · rw [if_neg hp] at hx
          exact ⟨p, (Except.ok.inj hx).symm, trivial, hs, fun y _ => by
            dsimp only
            rw [if_neg hp, Nat.add_zero]⟩) _ _ _ s1 g2
    refine ⟨r2, (Except.ok.inj hx).symm, by simpa using hn, s2, fun y hy => ?_⟩
    rw [e2 y hy, e1 y hy, Nat.add_assoc]
    rfl
  refine ⟨key.1, key.2.1, fun y hy => ?_⟩
  rw [key.2.2 y hy]
  simp [Array.getD, hy]

/-! ## Which entry of which segment stands in a column -/

/-- Which entry of which segment of the list l stands in column j: the text of Ends.H.colH, at a
list of segments. -/
def colL (l : List Seg) (j : ℕ) : Option (String × ℕ) :=
  l.findSome? fun g => (g.pos.findIdx? (· == j)).map fun x => (g.name, x)

/-- Ends.H.colH L q j is colL at the segments of call number q of the layout. -/
theorem colH_eq (L : Head.HL) (q j : ℕ) :
    Ends.H.colH L q j = colL (L.calls.getD q default).segs j := rfl

/-- j is among a segment's columns if and only if it is the column of an entry x below pos.size. -/
theorem mem_pos (g : Seg) (j : ℕ) :
    j ∈ g.pos.toList ↔ ∃ x, x < g.pos.size ∧ g.pos.getD x 0 = j := by
  rw [Array.mem_toList_iff, Array.mem_iff_getElem]
  constructor
  · rintro ⟨x, hx, e⟩
    exact ⟨x, hx, by simp [Array.getD, hx, e]⟩
  · rintro ⟨x, hx, e⟩
    exact ⟨x, hx, by simpa [Array.getD, hx] using e⟩

/-- findIdx? finds no entry of the segment for column j if and only if j is not among the segment's
columns. -/
theorem idx_none (g : Seg) (j : ℕ) :
    g.pos.findIdx? (· == j) = none ↔ j ∉ g.pos.toList := by
  rw [Array.findIdx?_eq_none_iff, Array.mem_toList_iff]
  constructor
  · intro h hj
    simpa using h j hj
  · intro h a ha
    by_contra hne
    have e : a = j := by simpa using hne
    exact h (e ▸ ha)

/-- colL finds nothing in column j if and only if no segment of the list lists j. -/
theorem colL_none (l : List Seg) (j : ℕ) : colL l j = none ↔ ∀ g ∈ l, j ∉ g.pos.toList := by
  unfold colL
  rw [List.findSome?_eq_none_iff]
  refine forall₂_congr fun g _ => ?_
  rw [Option.map_eq_none_iff, idx_none]

/-- In a segment that lists no column twice: findIdx? finds entry x for column j if and only if x is
below pos.size and x's column is j. -/
theorem idx_some (g : Seg)
    (hinj : ∀ x x', x < x' → x' < g.pos.size → g.pos.getD x 0 ≠ g.pos.getD x' 0) (j x : ℕ) :
    g.pos.findIdx? (· == j) = some x ↔ x < g.pos.size ∧ g.pos.getD x 0 = j := by
  rw [Array.findIdx?_eq_some_iff_getElem]
  constructor
  · rintro ⟨hx, e, -⟩
    exact ⟨hx, by simpa [Array.getD, hx] using e⟩
  · rintro ⟨hx, e⟩
    refine ⟨hx, by simpa [Array.getD, hx] using e, fun x' hx' k => ?_⟩
    have hx'' : x' < g.pos.size := Nat.lt_trans hx' hx
    have e' : g.pos.getD x' 0 = j := by simpa [Array.getD, hx''] using k
    exact hinj x' x hx' hx (e'.trans e.symm)

/-- Let val none j = 0 for all j, and let the segment g list columns below J alone and none twice.
Then the sum over the columns j below J of val, at the entry of g that findIdx? finds for j, is the
sum over the entries x of g of val at (g.name, x) and x's column. -/
theorem seg_sum (J : ℕ) (val : Option (String × ℕ) → ℕ → ℕ) (h0 : ∀ j, val none j = 0) (g : Seg)
    (hlt : ∀ x, x < g.pos.size → g.pos.getD x 0 < J)
    (hinj : ∀ x x', x < x' → x' < g.pos.size → g.pos.getD x 0 ≠ g.pos.getD x' 0) :
    ∑ j ∈ range J, val ((g.pos.findIdx? (· == j)).map fun x => (g.name, x)) j =
      ∑ x ∈ range g.pos.size, val (some (g.name, x)) (g.pos.getD x 0) := by
  have e1 : ∀ x ∈ range g.pos.size, val (some (g.name, x)) (g.pos.getD x 0) =
      ∑ j ∈ range J, if g.pos.getD x 0 = j then val (some (g.name, x)) j else 0 := by
    intro x hx
    rw [sum_ite_eq, if_pos (mem_range.2 (hlt x (mem_range.1 hx)))]
  rw [sum_congr rfl e1, sum_comm]
  refine sum_congr rfl fun j _ => ?_
  cases hf : g.pos.findIdx? (· == j) with
  | none =>
    rw [Option.map_none, h0]
    symm
    refine sum_eq_zero fun x hx => if_neg fun e => ?_
    exact (idx_none g j).1 hf ((mem_pos g j).2 ⟨x, mem_range.1 hx, e⟩)
  | some x0 =>
    obtain ⟨hx0, e0⟩ := (idx_some g hinj j x0).1 hf
    rw [Option.map_some, sum_eq_single x0, if_pos e0]
    · intro x hx hne
      refine if_neg fun e => hne ?_
      have k := (idx_some g hinj j x).2 ⟨mem_range.1 hx, e⟩
      rw [hf] at k
      exact (Option.some.inj k).symm
    · intro k
      exact absurd (mem_range.2 hx0) k

/-- Let val none j = 0 for all j. Let every segment of the list l have one column for each of its n
entries, all below J and no two equal, and let no two segments of l share a column. Then the sum
over the columns j below J of val (colL l j) j is the sum over the segments g of l and their entries
x of val at (g.name, x) and x's column. -/
theorem col_sum (J : ℕ) (val : Option (String × ℕ) → ℕ → ℕ) (h0 : ∀ j, val none j = 0) :
    ∀ l : List Seg, (∀ g ∈ l, g.pos.size = g.n) →
      (∀ g ∈ l, ∀ x, x < g.n → g.pos.getD x 0 < J) →
      (∀ g ∈ l, ∀ x x', x < x' → x' < g.n → g.pos.getD x 0 ≠ g.pos.getD x' 0) →
      l.Pairwise Road.Hd.NoShare →
      ∑ j ∈ range J, val (colL l j) j =
        (l.map fun g => ∑ x ∈ range g.n, val (some (g.name, x)) (g.pos.getD x 0)).sum
  | [], _, _, _, _ => by simp [colL, h0]
  | g :: l, hsz, hlt, hinj, hap => by
    obtain ⟨hpg, hpl⟩ := List.pairwise_cons.mp hap
    have hg : g ∈ g :: l := List.mem_cons_self
    have sg := hsz g hg
    have ig : ∀ x x', x < x' → x' < g.pos.size → g.pos.getD x 0 ≠ g.pos.getD x' 0 := by
      rw [sg]
      exact hinj g hg
    have ih := col_sum J val h0 l (fun g' h' => hsz g' (List.mem_cons_of_mem _ h'))
      (fun g' h' => hlt g' (List.mem_cons_of_mem _ h'))
      (fun g' h' => hinj g' (List.mem_cons_of_mem _ h')) hpl
    have e : ∀ j ∈ range J, val (colL (g :: l) j) j =
        val ((g.pos.findIdx? (· == j)).map fun x => (g.name, x)) j + val (colL l j) j := by
      intro j _
      unfold colL
      rw [List.findSome?_cons]
      cases hf : g.pos.findIdx? (· == j) with
      | none =>
        rw [Option.map_none, h0, Nat.zero_add]
      | some x0 =>
        obtain ⟨hx0, e0⟩ := (idx_some g ig j x0).1 hf
        have hn : colL l j = none := by
          rw [colL_none]
          intro g' h' hj
          obtain ⟨x', hx', e'⟩ := (mem_pos g' j).1 hj
          rw [hsz g' (List.mem_cons_of_mem _ h')] at hx'
          rw [sg] at hx0
          exact hpg g' h' x0 hx0 x' hx' (e0.trans e'.symm)
        unfold colL at hn
        rw [Option.map_some, hn, h0, Nat.add_zero]
    rw [sum_congr rfl e, sum_add_distrib, ih, List.map_cons, List.sum_cons,
      seg_sum J val h0 g (by rw [sg]; exact hlt g hg) ig, sg]

/-! ## A call that the placing rule has made -/

/-- After the marking of the columns of a list of segments (markUsed, OnBytes/Model/Calls.lean), an
index j of the array holds 0 if and only if it held 0 and no segment lists j. -/
theorem used_zero (j : ℕ) : ∀ (segs : List Seg) (u : Array ℕ), j < u.size →
    ((segs.foldl markUsed u).getD j 0 = 0 ↔ u.getD j 0 = 0 ∧ ∀ g ∈ segs, j ∉ g.pos.toList)
  | [], u, _ => by simp
  | g :: segs, u, hj => by
    obtain ⟨a1, a2, a3⟩ := Road.markUsed_get u g j
    rw [List.foldl_cons, used_zero j segs (markUsed u g) (by rw [a1]; exact hj)]
    by_cases hg : j ∈ g.pos.toList
    · rw [a2 hg hj]
      have hm : Road.markOf g ≠ 0 := by
        unfold Road.markOf
        split_ifs <;> simp
      exact ⟨fun k => absurd k.1 hm, fun k => absurd hg (k.2 g List.mem_cons_self)⟩
    · rw [a3 hg]
      refine and_congr_right fun _ => ?_
      exact ⟨fun k g' h' => by
          rcases List.mem_cons.mp h' with e | e
          · exact e ▸ hg
          · exact k g' e, fun k g' h' => k g' (List.mem_cons_of_mem _ h')⟩

/-- What is used of a call with its segments placed in columns: J = 2^lJ; every segment has one
column for each of its n entries; these are below J and no two are equal; no two segments share a
column; a column below J has the mark 0 if and only if no segment lists it. -/
structure Laid (cd : CallD) : Prop where
  J : cd.J = 2 ^ cd.lJ
  size : ∀ g ∈ cd.segs, g.pos.size = g.n
  lt : ∀ g ∈ cd.segs, ∀ x, x < g.n → g.pos.getD x 0 < cd.J
  inj : ∀ g ∈ cd.segs, ∀ x x', x < x' → x' < g.n → g.pos.getD x 0 ≠ g.pos.getD x' 0
  apart : cd.segs.Pairwise Road.Hd.NoShare
  used : ∀ j, j < cd.J → (cd.used.getD j 0 = 0 ↔ ∀ g ∈ cd.segs, j ∉ g.pos.toList)

/-- A call that the placing rule (place, OnBytes/Model/Calls.lean) makes of segments of lengths
below 2^41 is Laid. -/
theorem laid_place (name kind : String) (asks : List SegAsk) (fl : ℕ)
    (hlen : ∀ a ∈ asks, a.2.1 < 2 ^ (topBit + 1)) : Laid (place name kind asks fl) := by
  have hJ : (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).2 ≤ (place name kind asks fl).J := by
    show (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).2 ≤
      2 ^ max (ceilLog2 (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).2) fl
    exact Nat.le_trans (Road.le_two_pow_ceilLog2 _)
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_max_left _ _))
  have hT := Road.Hd.ranged_piecesBelow (asks.map (·.2.1)) (topBit + 1) 0
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rw [Road.Hd.place_segs_eq] at hg
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hg
    exact (Road.Hd.segAt_rising asks hlen z hz).1
  · intro g hg x hx
    rw [Road.Hd.place_segs_eq] at hg
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hg
    obtain ⟨s1, r1⟩ := Road.Hd.segAt_rising asks hlen z hz
    exact Nat.lt_of_lt_of_le (r1.lt x (by rw [s1]; exact hx)) hJ
  · intro g hg x x' hxx hx'
    rw [Road.Hd.place_segs_eq] at hg
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hg
    obtain ⟨s1, r1⟩ := Road.Hd.segAt_rising asks hlen z hz
    exact Nat.ne_of_lt (r1.mono x x' hxx (by rw [s1]; exact hx'))
  · rw [Road.Hd.place_segs_eq, List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ (Road.Hd.zipIdx_rising asks 0)
    intro z z' hz hz' hlt x hx x' hx' he
    obtain ⟨s1, r1⟩ := Road.Hd.segAt_rising asks hlen z hz
    obtain ⟨s2, r2⟩ := Road.Hd.segAt_rising asks hlen z' hz'
    have q1 := r1.inQ x (by rw [s1]; exact hx)
    have q2 := r2.inQ x' (by rw [s2]; exact hx')
    rw [← he] at q2
    exact Road.Hd.inPiece_apart hT (Nat.ne_of_lt hlt) q1 q2
  · intro j hj
    have hu : (place name kind asks fl).used = (place name kind asks fl).segs.foldl markUsed
        (Array.replicate (place name kind asks fl).J 0) := rfl
    rw [hu, used_zero j _ _ (by rw [Array.size_replicate]; exact hj),
      Road.Hd.getD_replicate_zero]
    exact ⟨fun k => k.2, fun k => ⟨rfl, k⟩⟩

/-! ## What one call adds, by columns -/

/-- Whether column j of a call with the segments l holds padding keys: padH's rule, by columns. -/
def padCol (h : Head.Shape) (L : Head.HL) (l : List Seg) (j : ℕ) : Bool :=
  match colL l j with
  | some (sn, x) => Head.perEntry sn && decide (h.V ≤ Head.firstEntry L sn + x)
  | none => true

/-- h.T if the entry (sn, x) has Head.perEntry sn and h.V ≤ Head.firstEntry L sn + x, and j / M = b;
else 0; and 0 at none. -/
def fillVal (h : Head.Shape) (L : Head.HL) (M b : ℕ) : Option (String × ℕ) → ℕ → ℕ
  | some (sn, x), j =>
    if (Head.perEntry sn && decide (h.V ≤ Head.firstEntry L sn + x)) = true ∧ j / M = b then h.T
    else 0
  | none, _ => 0

/-- The sum of G (r + x) over x below n - r is the sum over x below n of G x where r ≤ x, and of 0
elsewhere. -/
theorem sum_shift (G : ℕ → ℕ) (r n : ℕ) :
    ((List.range (n - r)).map fun x => G (r + x)).sum =
      ∑ x ∈ range n, if r ≤ x then G x else 0 := by
  rw [list_sum_range]
  by_cases hr : r ≤ n
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
    rw [Nat.add_sub_cancel_left, sum_range_add,
      sum_eq_zero fun x hx => if_neg (by have := mem_range.1 hx; omega), Nat.zero_add]
    exact sum_congr rfl fun x _ => (if_pos (Nat.le_add_right _ _)).symm
  · rw [show n - r = 0 by omega, range_zero, sum_empty]
    exact (sum_eq_zero fun x hx => if_neg (by have := mem_range.1 hx; omega)).symm

/-- For a Laid call of A · 2^cs columns, and every b: what the call adds to tree base + b is h.T for
each column j below A · 2^cs with padCol and j / 2^cs = b. -/
theorem pubCall_in (h : Head.Shape) (L : Head.HL) {cd : CallD} (hL : Laid cd) {A cs : ℕ}
    (hJ : cd.J = A * 2 ^ cs) (base b : ℕ) :
    pubCall h L cs base cd (base + b) = ((List.range (A * 2 ^ cs)).map fun j =>
      if padCol h L cd.segs j = true ∧ j / 2 ^ cs = b then h.T else 0).sum := by
  unfold pubCall
  have e2 : ∀ g ∈ cd.segs, (if Head.perEntry g.name = true then
        ((List.range (g.n - (h.V - Head.firstEntry L g.name))).map fun x =>
          if base + g.pos.getD (h.V - Head.firstEntry L g.name + x) 0 / 2 ^ cs = base + b
          then h.T else 0).sum
      else 0) =
      ∑ x ∈ range g.n, fillVal h L (2 ^ cs) b (some (g.name, x)) (g.pos.getD x 0) := by
    intro g _
    by_cases hp : Head.perEntry g.name = true
    · rw [if_pos hp, sum_shift (fun x => if base + g.pos.getD x 0 / 2 ^ cs = base + b
        then h.T else 0)]
      refine sum_congr rfl fun x _ => ?_
      show _ = if (Head.perEntry g.name && decide (h.V ≤ Head.firstEntry L g.name + x)) = true ∧
        g.pos.getD x 0 / 2 ^ cs = b then h.T else 0
      rw [hp, Bool.true_and]
      by_cases h1 : h.V ≤ Head.firstEntry L g.name + x
      · rw [if_pos (by omega)]
        by_cases h2 : g.pos.getD x 0 / 2 ^ cs = b
        · rw [if_pos (by omega), if_pos ⟨decide_eq_true h1, h2⟩]
        · rw [if_neg (by omega), if_neg fun k => h2 k.2]
      · rw [if_neg (by omega), if_neg fun k => h1 (of_decide_eq_true k.1)]
    · rw [if_neg hp]
      symm
      refine sum_eq_zero fun x _ => ?_
      show (if (Head.perEntry g.name && decide (h.V ≤ Head.firstEntry L g.name + x)) = true ∧
        g.pos.getD x 0 / 2 ^ cs = b then h.T else 0) = 0
      rw [if_neg]
      intro k
      rw [Bool.and_eq_true] at k
      exact hp k.1.1
  rw [List.map_congr_left e2,
    ← col_sum cd.J (fillVal h L (2 ^ cs) b) (fun _ => rfl) cd.segs hL.size hL.lt hL.inj hL.apart,
    list_sum_range, list_sum_range, ← hJ, ← sum_add_distrib]
  refine sum_congr rfl fun j hj => ?_
  have hu := hL.used j (mem_range.1 hj)
  rw [← colL_none] at hu
  unfold padCol
  cases hc : colL cd.segs j with
  | none =>
    have h0 : (cd.used.getD j 0 == 0) = true := by simpa using hu.2 hc
    show (if _ then _ else _) + 0 = if true = true ∧ _ then _ else _
    rw [Nat.add_zero]
    by_cases h2 : j / 2 ^ cs = b
    · rw [if_pos ⟨h0, by omega⟩, if_pos ⟨rfl, h2⟩]
    · rw [if_neg fun k => h2 (by omega), if_neg fun k => h2 k.2]
  | some a =>
    obtain ⟨sn, x⟩ := a
    have h0 : ¬ (cd.used.getD j 0 == 0) = true := by
      intro k
      have k' := hu.1 (by simpa using k)
      rw [hc] at k'
      cases k'
    rw [if_neg fun k => h0 k.1, Nat.zero_add]
    rfl

/-- A Laid call of A · 2^cs columns adds nothing to a tree y that is none of base + b, b below A. -/
theorem pubCall_out (h : Head.Shape) (L : Head.HL) {cd : CallD} (hL : Laid cd) {A cs : ℕ}
    (hJ : cd.J = A * 2 ^ cs) {base y : ℕ} (hy : ∀ b, b < A → base + b ≠ y) :
    pubCall h L cs base cd y = 0 := by
  have hd : ∀ j, j < cd.J → base + j / 2 ^ cs ≠ y := fun j hj =>
    hy _ (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hJ]; exact hj))
  unfold pubCall
  rw [Nat.add_eq_zero_iff]
  constructor
  · refine List.sum_eq_zero fun v hv => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
    exact if_neg fun k => hd j (List.mem_range.1 hj) k.2
  · refine List.sum_eq_zero fun v hv => ?_
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hv
    split_ifs
    · refine List.sum_eq_zero fun w hw => ?_
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
      have hx' := List.mem_range.1 hx
      exact if_neg (hd _ (hL.lt g hg _ (by omega)))
    · rfl

/-! ## The layouts that Head.layout returns -/

/-- If Head.layout h tau returns L: Head.pubOf at L, L.fs and L's calls returns L.fs.pub; la ≤ dT;
and L.fs has as many calls as L. -/
theorem layout_open {h : Head.Shape} {tau : Array F} {L : Head.HL}
    (hy : Head.layout h tau = .ok L) :
    Head.pubOf h L L.fs L.calls.toList = .ok L.fs.pub ∧ h.la ≤ L.fs.dT ∧
      L.fs.calls.size = L.calls.size := by
  unfold Head.layout at hy
  obtain ⟨-, hy⟩ := Road.Hd.ok_of_needed hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨L0, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨cs, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, hy⟩ := Road.Hd.ok_of_needed hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨fs, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨hla, hy⟩ := Road.Hd.ok_of_needed hy
  obtain ⟨kb, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨pub, hpub, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, hy⟩ := Road.Hd.ok_of_needed hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  cases hy
  exact ⟨hpub, by simpa using hla, by simp [Head.lookups]⟩

/-- If Head.layout h tau returns L, every call of L is Laid. -/
theorem laid_of_layout {h : Head.Shape} {tau : Array F} {L : Head.HL}
    (hy : Head.layout h tau = .ok L) : ∀ cd ∈ L.calls.toList, Laid cd := by
  have A := Road.Hd.admittedH_of_layout hy
  obtain ⟨cs, hc, _, hL⟩ := A.calls
  obtain ⟨c1, _⟩ := Road.Hd.callsOf_spec hc
  intro cd hcd
  rw [hL] at hcd
  obtain ⟨name, kind, asks, fl, e1, e2⟩ := c1 cd hcd
  rw [e1]
  refine laid_place name kind asks fl fun a ha => ?_
  obtain ⟨x, f1, f2⟩ := e2 a ha
  rw [f2]
  exact Road.Hd.segments_lt A x (List.mem_of_find?_eq_some f1)

/-- If 2^a / 2^c = 2^i then 2^a = 2^i · 2^c. -/
theorem pow_div_eq {a c i : ℕ} (e : 2 ^ a / 2 ^ c = 2 ^ i) : 2 ^ a = 2 ^ i * 2 ^ c := by
  by_cases hc : c ≤ a
  · rw [Nat.pow_div hc (by norm_num)] at e
    have k : a - c = i := Nat.pow_right_injective (le_refl 2) e
    rw [← pow_add, ← k, Nat.sub_add_cancel hc]
  · rw [Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))] at e
    exact absurd e.symm (by positivity)

/-- Reading an array's list with a default is reading the array with it. -/
theorem getD_toList {α : Type} [Inhabited α] (a : Array α) (q : ℕ) :
    a.toList.getD q default = a.getD q default := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

/-! ## How many entries a listed segment has -/

/-- If colL finds (sn, x) in a column, a segment of the list has the name sn and more than x
columns. -/
theorem colL_some {l : List Seg} {j : ℕ} {sn : String} {x : ℕ} (hc : colL l j = some (sn, x)) :
    ∃ g ∈ l, g.name = sn ∧ x < g.pos.size := by
  unfold colL at hc
  obtain ⟨g, hg, h0⟩ := List.exists_of_findSome?_eq_some hc
  cases hf : g.pos.findIdx? (· == j) with
  | none =>
    rw [hf] at h0
    cases h0
  | some x0 =>
    rw [hf] at h0
    obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj h0)
    obtain ⟨hi, -⟩ := Array.findIdx?_eq_some_iff_getElem.1 hf
    exact ⟨g, hg, e1, e2 ▸ hi⟩

/-- For n ≥ 1: 2^(ceilLog2 n - 1) ≤ n. -/
theorem half_le {n : ℕ} (hn : 1 ≤ n) : 2 ^ (ceilLog2 n - 1) ≤ n := by
  unfold ceilLog2
  split_ifs with h1
  · simpa using hn
  · rw [Nat.add_sub_cancel]
    have k := Nat.log2_self_le (n := n - 1) (by omega)
    omega

/-- If Head.layout h tau returns L, and Ends.H.colH L q j is entry x of a segment sn, then the first
member of the head's list of segments (Head.segments h L) with the name sn has more than x entries.
-/
theorem entry_seg {h : Head.Shape} {tau : Array F} {L : Head.HL}
    (hy : Head.layout h tau = .ok L) {q j : ℕ} {sn : String} {x : ℕ}
    (hc : Ends.H.colH L q j = some (sn, x)) :
    ∃ y, (Head.segments h L).find? (fun y => y.1 == sn) = some y ∧ x < y.2.2 := by
  have A := Road.Hd.admittedH_of_layout hy
  obtain ⟨cs, hcs, _, hL⟩ := A.calls
  obtain ⟨c1, _⟩ := Road.Hd.callsOf_spec hcs
  rw [colH_eq, ← getD_toList, hL] at hc
  obtain ⟨g, hg, hn, hx⟩ := colL_some hc
  have hg' : g ∈ (cs.getD q default).segs := hg
  by_cases hq : q < cs.length
  · have e : cs.getD q default = cs[q] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
    rw [e] at hg'
    obtain ⟨name, kind, asks, fl, e1, e2⟩ := c1 cs[q] (List.getElem_mem hq)
    rw [e1, Road.Hd.place_segs_eq] at hg'
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hg'
    have hlen : ∀ a ∈ asks, a.2.1 < 2 ^ (topBit + 1) := by
      intro a ha
      obtain ⟨x', f1, f2⟩ := e2 a ha
      rw [f2]
      exact Road.Hd.segments_lt A x' (List.mem_of_find?_eq_some f1)
    obtain ⟨s1, _⟩ := Road.Hd.segAt_rising asks hlen z hz
    obtain ⟨x', f1, f2⟩ := e2 z.1 (Road.mem_zipIdx_getD (fun _ => 0) asks 0 z.1 z.2 hz).1
    have hn' : z.1.1 = sn := hn
    rw [hn'] at f1
    refine ⟨x', f1, ?_⟩
    rw [← f2]
    rw [s1] at hx
    exact hx
  · have e : cs.getD q default = default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
    rw [e] at hg'
    cases hg'

/-- **Every listed entry of the five segments with one entry for each vocabulary entry stands for an
entry below JV.** If Head.layout h tau returns L, and Ends.H.colH L q j is entry x of a segment sn
with Head.perEntry sn, then Head.firstEntry L sn + x < L.JV. -/
theorem entry_lt {h : Head.Shape} {tau : Array F} {L : Head.HL}
    (hy : Head.layout h tau = .ok L) {q j : ℕ} {sn : String} {x : ℕ}
    (hc : Ends.H.colH L q j = some (sn, x)) (hp : Head.perEntry sn = true) :
    Head.firstEntry L sn + x < L.JV := by
  have A := Road.Hd.admittedH_of_layout hy
  have hV : 1 ≤ L.JV := by
    have e := A.adm
    simp only [Head.admitted, Bool.and_eq_true, decide_eq_true_eq] at e
    have hS : 0 < h.S2 := Nat.pow_pos (by norm_num)
    have k : h.V ≤ roundUp h.V h.S2 := (Road.Hd.roundUp_bounds h.V hS).1
    rw [← A.JV] at k
    omega
  have ha : L.JVa ≤ L.JV := by
    rw [A.JVa]
    exact half_le hV
  obtain ⟨x', f1, hx'⟩ := entry_seg hy hc
  simp only [Head.perEntry, Bool.or_eq_true, beq_iff_eq] at hp
  rcases hp with (((rfl | rfl) | rfl) | rfl) | rfl <;>
    simp [Head.segments] at f1 <;> subst f1 <;> simp [Head.firstEntry] <;> simp at hx' <;> omega

end HeadPub

open HeadPub in
/-- **If Head.layout returns, its numbers of padding keys count the padding places.** If Head.layout
h tau returns L, then PubFits L.fs (padH h L): for every tree y below L.fs.NT, L.fs.pub[y] is the
number of the x below 2^dT for which padH holds at the tree's call and at place x + 2^dT (y %
2^iota). -/
theorem pubFits_H {h : Head.Shape} {tau : Array F} {L : Head.HL}
    (hy : Head.layout h tau = .ok L) : PubFits L.fs (padH h L) := by
  have hok : FoNums.ok L.fs = true := Fo.Pay.shapeOf_ok (Fo.Pub2.shapeOf_headLayout hy).1
  obtain ⟨⟨_, _, _, _, _, _, a7⟩, hb, hcc, _⟩ := Cb.Fo.ok_parts hok
  obtain ⟨hp, hla, hsz⟩ := layout_open hy
  have hlaid := laid_of_layout hy
  have hlt : h.lt ≤ L.fs.dT := by
    have e := (Road.Hd.admittedH_of_layout hy).adm
    simp only [Head.admitted, Bool.and_eq_true, decide_eq_true_eq] at e
    omega
  obtain ⟨hdiv, -, hget⟩ := pubOf_get hp
  have hlen : L.calls.toList.length = L.fs.NC := by rw [Array.length_toList, ← hsz, a7]
  have hJ : ∀ q, q < L.fs.NC → Laid (L.calls.toList.getD q default) ∧
      (L.calls.toList.getD q default).J = 2 ^ FoNums.io L.fs q * 2 ^ (L.fs.dT - h.lt) := by
    intro q hq
    have hq' : q < L.calls.toList.length := by rw [hlen]; exact hq
    have e : L.calls.toList.getD q default = L.calls.toList[q] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq', Option.getD_some]
    have hz : (L.calls.toList[q], q) ∈ L.calls.toList.zipIdx :=
      List.mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem hq')
    rw [e]
    have l := hlaid _ (List.getElem_mem hq')
    refine ⟨l, ?_⟩
    have d := hdiv _ hz
    rw [l.J] at d ⊢
    exact pow_div_eq d
  intro y hy'
  obtain ⟨hq, lo, hi⟩ := hb y hy'
  obtain ⟨q, hqd⟩ : ∃ q, q = FoNums.co L.fs y := ⟨_, rfl⟩
  rw [← hqd] at hq lo hi ⊢
  obtain ⟨_, _, _, hqq⟩ := hcc q hq
  obtain ⟨_, _, q3⟩ := hqq (y - FoNums.fst L.fs q) (by omega)
  rw [Nat.add_sub_cancel' lo] at q3
  have hbA : y % 2 ^ FoNums.io L.fs q < 2 ^ FoNums.io L.fs q := Nat.mod_lt _ (by positivity)
  have hyb : FoNums.fst L.fs q + y % 2 ^ FoNums.io L.fs q = y := by
    rw [q3]
    omega
  have hT : 2 ^ (L.fs.dT - h.lt) * h.T = 2 ^ L.fs.dT := by
    show 2 ^ (L.fs.dT - h.lt) * 2 ^ h.lt = _
    rw [← pow_add, Nat.sub_add_cancel hlt]
  rw [hget y hy', Road.zipIdx_sum default _ _ 0, hlen, sum_eq_single q]
  · obtain ⟨l, j⟩ := hJ q hq
    have k := pubCall_in h L l j (FoNums.fst L.fs q) (y % 2 ^ FoNums.io L.fs q)
    rw [hyb, Road.sum_block (padCol h L (L.calls.toList.getD q default).segs) h.T
      (2 ^ (L.fs.dT - h.lt)) hbA, ← Road.card_block, hT] at k
    simp only [Nat.zero_add]
    refine k.trans (congrArg card (filter_congr fun x _ => ?_))
    rw [getD_toList, Nat.mul_comm, Nat.add_comm]
    rfl
  · intro q' hq' hne
    simp only [Nat.zero_add]
    obtain ⟨l', j'⟩ := hJ q' (mem_range.1 hq')
    refine pubCall_out h L l' j' fun b' hb' e => hne ?_
    have k := ((hcc q' (mem_range.1 hq')).2.2.2 b' hb').2.1
    rw [show FoNums.fst L.fs q' + b' = y from e] at k
    rw [← k, hqd]
  · intro k
    exact absurd (mem_range.2 hq) k

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.HeadPub.forIn_adds
#print axioms OnBytes.HonestTrace.HeadPub.modify_adds
#print axioms OnBytes.HonestTrace.HeadPub.step_mod
#print axioms OnBytes.HonestTrace.HeadPub.step_if
#print axioms OnBytes.HonestTrace.HeadPub.pubOf_get
#print axioms OnBytes.HonestTrace.HeadPub.colH_eq
#print axioms OnBytes.HonestTrace.HeadPub.mem_pos
#print axioms OnBytes.HonestTrace.HeadPub.idx_none
#print axioms OnBytes.HonestTrace.HeadPub.colL_none
#print axioms OnBytes.HonestTrace.HeadPub.idx_some
#print axioms OnBytes.HonestTrace.HeadPub.seg_sum
#print axioms OnBytes.HonestTrace.HeadPub.col_sum
#print axioms OnBytes.HonestTrace.HeadPub.used_zero
#print axioms OnBytes.HonestTrace.HeadPub.laid_place
#print axioms OnBytes.HonestTrace.HeadPub.sum_shift
#print axioms OnBytes.HonestTrace.HeadPub.pubCall_in
#print axioms OnBytes.HonestTrace.HeadPub.pubCall_out
#print axioms OnBytes.HonestTrace.HeadPub.layout_open
#print axioms OnBytes.HonestTrace.HeadPub.laid_of_layout
#print axioms OnBytes.HonestTrace.HeadPub.pow_div_eq
#print axioms OnBytes.HonestTrace.HeadPub.getD_toList
#print axioms OnBytes.HonestTrace.HeadPub.colL_some
#print axioms OnBytes.HonestTrace.HeadPub.half_le
#print axioms OnBytes.HonestTrace.HeadPub.entry_seg
#print axioms OnBytes.HonestTrace.HeadPub.entry_lt
#print axioms OnBytes.HonestTrace.pubFits_H
