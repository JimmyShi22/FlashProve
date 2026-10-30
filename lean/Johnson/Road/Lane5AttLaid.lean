-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttLaid.lean

HOW THE FOUR LOOKUP CALLS OF AN ATTENTION SUB-PROOF ARE LAID, AS A THEOREM: "LaidA"
(Johnson/Road/Lane5KvVec.lean) for every shape that the verifier's own function shapeHid returns at
a configuration with the usual call list and one shift in the group (for shape: four_of_shape with
laidA_of_four). With it: the kinds
of the four calls, and that the pieces of each call fit into its keys.

The verifier lays a call's keys in three steps (OnBytes/Model/AttentionShape.lean: placePieces): it
lists the pieces by segment kind, layer and query head; it sorts them by falling size, pieces of one
size keeping their order; it gives each the number of its first key (layOff). At the usual call
list the list is sorted already, so the sort returns it (List.mergeSort_of_pairwise).

* "offsL", "sizeL", "layOff_eq": layOff as a recursion on the list. "offsL_ge", "offsL_apart",
  "offsL_map": a piece lies between the start and the end; the pieces are pairwise apart; a family
  of pieces of one size.
* "fam_range": the pairs (layer, query head) in the verifier's order are the numbers b, as
  (b / HA, b % HA).
* "place_two", "place_one": what placePieces returns for two segment kinds, the larger first, and
  for one.
* "shsOf_one": with one shift in the group the list of the group's shifts has one member.
* "UsualCalls cf": the call list is (KR: rm rd), (KFD: fm fd), (R16: wl ix), (WH: wh), under any
  names; all layers of the group have the first layer's shift. Public: on the configuration alone.
  "usualB", "usual_of_test": a test that a program can run, with its theorem: if the test says
  true, UsualCalls holds. The other direction is not proved.
* "tests_of_shape", "tests_of_hid": two of shape's own tests, read off its run: lB + 2 ≤ lt; there
  is at least one query head for each head of keys and values.
* "FourCalls cf S": what the theorems below read of a shape's calls.
* "four_of_shape", "four_of_hid": shape and shapeHid give it.
* **"laidA_of_four"**, **"laidA_of_hid"**: LaidA.
* "kinds_of_four": call q has the kind with the library's number q. "room_of_four": the library's
  "used q" is at most 2^n of call q.

UsualCalls is no test of the verifier: the verifier takes other call lists, and groups with two
shifts (there it makes a call of kinds KR and KFD for each shift); at these this file says
nothing. UsualCalls is also narrower than LaidA needs: with (KR: rd rm) the sort by falling size
gives, by a reading of placePieces, the same pieces at the same places, and UsualCalls is false.
Not claimed: that a parameter file gives the usual call list.
-/
import Johnson.Road.Lane5AttCallsH
import Johnson.Road.Lane5KvCheck
import Johnson.Road.Lane5KvNums
import OnBytes.Slice.ProgCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model
open Attention (ACall Cfg Shape Listed Table Seg Piece Line shape shapeHid layCall expandLine
  placePieces layOff segBits nMOf nDOf)

/-! ## 1. The numbers of the first keys -/

/-- The pieces of a list, each with the number of its first key, from off on. -/
def offsL : List Piece → ℕ → List Piece
  | [], _ => []
  | p :: l, off => { p with off := off } :: offsL l (off + 2 ^ p.b)

/-- The sum of the pieces' sizes. -/
def sizeL (l : List Piece) : ℕ := (l.map fun p => 2 ^ p.b).sum

theorem layFold (l : List Piece) : ∀ (acc : Array Piece) (off : ℕ),
    l.foldl (fun (st : Array Piece × ℕ) p => (st.1.push { p with off := st.2 }, st.2 + 2 ^ p.b))
        (acc, off) = ((acc.toList ++ offsL l off).toArray, off + sizeL l) := by
  induction l with
  | nil =>
    intro acc off
    simp [offsL, sizeL]
  | cons p l ih =>
    intro acc off
    rw [List.foldl_cons]
    exact (ih (acc.push { p with off := off }) (off + 2 ^ p.b)).trans
      (by simp [offsL, sizeL, Nat.add_assoc])

/-- **layOff as a recursion on the list.** -/
theorem layOff_eq (l : List Piece) (off : ℕ) :
    layOff l off = ((offsL l off).toArray, off + sizeL l) := by
  unfold Attention.layOff
  rw [layFold]
  simp

theorem offsL_append (l1 l2 : List Piece) (off : ℕ) :
    offsL (l1 ++ l2) off = offsL l1 off ++ offsL l2 (off + sizeL l1) := by
  induction l1 generalizing off with
  | nil => simp [offsL, sizeL]
  | cons p l ih => simp [offsL, sizeL, ih, Nat.add_assoc]

theorem sizeL_append (l1 l2 : List Piece) : sizeL (l1 ++ l2) = sizeL l1 + sizeL l2 := by
  simp [sizeL]

/-- A piece lies between the start and the end. -/
theorem offsL_ge {l : List Piece} {off : ℕ} {q : Piece} (h : q ∈ offsL l off) :
    off ≤ q.off ∧ q.off + 2 ^ q.b ≤ off + sizeL l := by
  induction l generalizing off with
  | nil => simp [offsL] at h
  | cons p l ih =>
    simp only [offsL, List.mem_cons] at h
    rcases h with rfl | h
    · simp [sizeL]
    · have h2 := ih h
      have hp : 0 < 2 ^ p.b := Nat.two_pow_pos _
      simp only [sizeL, List.map_cons, List.sum_cons] at h2 ⊢
      omega

/-- The pieces are pairwise apart. -/
theorem offsL_apart (l : List Piece) (off : ℕ) :
    (offsL l off).Pairwise fun p r => p.off + 2 ^ p.b ≤ r.off ∨ r.off + 2 ^ r.b ≤ p.off := by
  induction l generalizing off with
  | nil => simp [offsL]
  | cons p l ih =>
    simp only [offsL]
    exact List.pairwise_cons.2 ⟨fun r hr => Or.inl (offsL_ge hr).1, ih _⟩

/-- A family of n pieces of one size. -/
theorem offsL_map (g : ℕ → Piece) (c : ℕ) (hg : ∀ j, (g j).b = c) (off n : ℕ) :
    offsL ((List.range n).map g) off =
        (List.range n).map (fun j => { g j with off := off + j * 2 ^ c }) ∧
      sizeL ((List.range n).map g) = n * 2 ^ c := by
  induction n with
  | zero => simp [offsL, sizeL]
  | succ n ih =>
    obtain ⟨i1, i2⟩ := ih
    constructor
    · rw [List.range_succ, List.map_append, offsL_append, i1, i2, List.map_append]
      simp [offsL]
    · rw [List.range_succ, List.map_append, sizeL_append, i2]
      simp only [sizeL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hg]
      ring

/-! ## 2. The pairs of a layer and a query head -/

/-- The piece of segment kind s for pair number b, of 2^c keys; the number of its first key is not
set. -/
def pcOf (s : Seg) (HA c b : ℕ) : Piece := { seg := s, lam := b / HA, a := b % HA, b := c }

theorem fam_range (HA : ℕ) (hHA : 0 < HA) (g : ℕ → ℕ → Piece) (n : ℕ) :
    ((List.range n).flatMap fun lam => (List.range HA).map fun a => g lam a) =
      (List.range (n * HA)).map fun b => g (b / HA) (b % HA) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ih, Nat.add_mul, Nat.one_mul, List.range_add,
      List.map_append, List.map_map]
    congr 1
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    apply List.map_congr_left
    intro a ha
    have ha' := List.mem_range.1 ha
    have e1 : (n * HA + a) / HA = n := by
      rw [Nat.mul_comm, Nat.mul_add_div hHA, Nat.div_eq_of_lt ha', Nat.add_zero]
    have e2 : (n * HA + a) % HA = a := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt ha']
    simp only [Function.comp, e1, e2]

theorem pw_of_mem {α : Type} {R : α → α → Prop} {l : List α} (h : ∀ x ∈ l, ∀ y ∈ l, R x y) :
    l.Pairwise R := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
    exact List.pairwise_cons.2
      ⟨fun y hy => h a (List.mem_cons_self ..) y (List.mem_cons_of_mem _ hy),
        ih fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)⟩

theorem fam_b {s : Seg} {HA c n : ℕ} {x : Piece} (h : x ∈ (List.range n).map (pcOf s HA c)) :
    x.b = c := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 h
  rfl

/-! ## 3. What placePieces returns -/

variable {cf : Cfg} {HA : ℕ} {kind : Table} {sh : ℕ}

/-- The pieces of one segment kind as placePieces lists them, where every layer of the group is
taken. -/
theorem listed_fam (hHA : 0 < HA)
    (hsh : kind.bySh = true → ∀ lam < 2 ^ cf.ll, cf.sh.getD lam 0 = sh) (s : Seg) :
    ((List.range (2 ^ cf.ll)).flatMap fun lam =>
      if kind.bySh && cf.sh.getD lam 0 != sh then []
      else (List.range HA).map fun a =>
        ({ seg := s, lam := lam, a := a, b := segBits cf s } : Piece)) =
      (List.range (2 ^ cf.ll * HA)).map (pcOf s HA (segBits cf s)) := by
  have e := fam_range HA hHA
    (fun lam a => ({ seg := s, lam := lam, a := a, b := segBits cf s } : Piece)) (2 ^ cf.ll)
  refine Eq.trans ?_ e
  rw [List.flatMap_def, List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro lam hlam
  have hl := List.mem_range.1 hlam
  have hc : (kind.bySh && cf.sh.getD lam 0 != sh) = false := by
    cases hb : kind.bySh with
    | false => rfl
    | true => simp [hsh hb lam hl]
  simp only [hc, Bool.false_eq_true, if_false]

/-- **Two segment kinds, the larger pieces first.** -/
theorem place_two (hHA : 0 < HA)
    (hsh : kind.bySh = true → ∀ lam < 2 ^ cf.ll, cf.sh.getD lam 0 = sh) (s1 s2 : Seg)
    (hle : segBits cf s2 ≤ segBits cf s1) :
    placePieces cf HA kind sh [s1, s2] =
      (((List.range (2 ^ cf.ll * HA)).map (fun b =>
          { pcOf s1 HA (segBits cf s1) b with off := 0 + b * 2 ^ segBits cf s1 }) ++
        (List.range (2 ^ cf.ll * HA)).map (fun b =>
          { pcOf s2 HA (segBits cf s2) b with
            off := 0 + 2 ^ cf.ll * HA * 2 ^ segBits cf s1 + b * 2 ^ segBits cf s2 })).toArray,
        0 + (2 ^ cf.ll * HA * 2 ^ segBits cf s1 + 2 ^ cf.ll * HA * 2 ^ segBits cf s2)) := by
  unfold Attention.placePieces
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, listed_fam hHA hsh]
  have hs : ((List.range (2 ^ cf.ll * HA)).map (pcOf s1 HA (segBits cf s1)) ++
      (List.range (2 ^ cf.ll * HA)).map (pcOf s2 HA (segBits cf s2))).Pairwise
      fun x y => decide (y.b ≤ x.b) = true := by
    rw [List.pairwise_append]
    refine ⟨pw_of_mem fun x hx y hy => ?_, pw_of_mem fun x hx y hy => ?_, fun x hx y hy => ?_⟩
    · rw [fam_b hx, fam_b hy]
      simp
    · rw [fam_b hx, fam_b hy]
      simp
    · rw [fam_b hx, fam_b hy]
      exact decide_eq_true hle
  rw [List.mergeSort_of_pairwise hs, layOff_eq, offsL_append, sizeL_append,
    (offsL_map (pcOf s1 HA (segBits cf s1)) _ (fun _ => rfl) 0 _).1,
    (offsL_map (pcOf s1 HA (segBits cf s1)) _ (fun _ => rfl) 0 _).2,
    (offsL_map (pcOf s2 HA (segBits cf s2)) _ (fun _ => rfl) _ _).1,
    (offsL_map (pcOf s2 HA (segBits cf s2)) _ (fun _ => rfl) 0 _).2]
  rfl

/-- **One segment kind.** -/
theorem place_one (hHA : 0 < HA)
    (hsh : kind.bySh = true → ∀ lam < 2 ^ cf.ll, cf.sh.getD lam 0 = sh) (s1 : Seg) :
    placePieces cf HA kind sh [s1] =
      (((List.range (2 ^ cf.ll * HA)).map (fun b =>
          { pcOf s1 HA (segBits cf s1) b with off := 0 + b * 2 ^ segBits cf s1 })).toArray,
        0 + 2 ^ cf.ll * HA * 2 ^ segBits cf s1) := by
  unfold Attention.placePieces
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, listed_fam hHA hsh]
  have hs : ((List.range (2 ^ cf.ll * HA)).map (pcOf s1 HA (segBits cf s1))).Pairwise
      fun x y => decide (y.b ≤ x.b) = true := by
    refine pw_of_mem fun x hx y hy => ?_
    rw [fam_b hx, fam_b hy]
    simp
  rw [List.mergeSort_of_pairwise hs, layOff_eq,
    (offsL_map (pcOf s1 HA (segBits cf s1)) _ (fun _ => rfl) 0 _).1,
    (offsL_map (pcOf s1 HA (segBits cf s1)) _ (fun _ => rfl) 0 _).2]
  rfl

/-! ## 4. One shift; the usual call list -/

theorem eraseDups_replicate (s n : ℕ) : (List.replicate (n + 1) s).eraseDups = [s] := by
  simp [List.replicate_succ, List.eraseDups_cons]

/-- With one shift in the group the list of the group's shifts has one member. -/
theorem shsOf_one (hsz : cf.sh.size = 2 ^ cf.ll)
    (h1 : ∀ l < 2 ^ cf.ll, cf.sh.getD l 0 = cf.sh.getD 0 0) : shsOf cf = [cf.sh.getD 0 0] := by
  have hl : cf.sh.toList = List.replicate (2 ^ cf.ll) (cf.sh.getD 0 0) := by
    rw [List.eq_replicate_iff]
    refine ⟨by simpa using hsz, fun b hb => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hb
    have hi' : i < cf.sh.size := by simpa using hi
    rw [← h1 i (hsz ▸ hi')]
    simp [Array.getD, hi']
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ cf.ll = m + 1 :=
    ⟨2 ^ cf.ll - 1, by have := Nat.two_pow_pos cf.ll; omega⟩
  unfold shsOf
  rw [hl, List.mergeSort_of_pairwise (by rw [List.pairwise_replicate]; right; simp), hm,
    eraseDups_replicate]

/-- **The usual call list, and one shift in the group.** Public: on the configuration alone. -/
structure UsualCalls (cf : Cfg) : Prop where
  lines : ∃ n0 n1 n2 n3 : String, cf.lines =
    [⟨n0, .kr, [.rm, .rd]⟩, ⟨n1, .kfd, [.fm, .fd]⟩, ⟨n2, .r16, [.wl, .ix]⟩, ⟨n3, .wh, [.wh]⟩]
  one : ∀ l < 2 ^ cf.ll, cf.sh.getD l 0 = cf.sh.getD 0 0

/-- UsualCalls as a test. -/
def usualB (cf : Cfg) : Bool :=
  decide ((cf.lines.map fun l => (l.kind, l.segs)) =
    [(.kr, [.rm, .rd]), (.kfd, [.fm, .fd]), (.r16, [.wl, .ix]), (.wh, [.wh])]) &&
  (List.range (2 ^ cf.ll)).all fun l => decide (cf.sh.getD l 0 = cf.sh.getD 0 0)

theorem line_eq {l : Line} {k : Table} {sg : List Seg} (h : (l.kind, l.segs) = (k, sg)) :
    l = ⟨l.name, k, sg⟩ := by
  obtain ⟨n, k', sg'⟩ := l
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  have h1' : k' = k := h1
  have h2' : sg' = sg := h2
  rw [h1', h2']

/-- **The test gives UsualCalls.** -/
theorem usual_of_test (h : usualB cf = true) : UsualCalls cf := by
  unfold usualB at h
  rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hm, hs⟩ := h
  refine ⟨?_, fun l hl => of_decide_eq_true (hs l (List.mem_range.2 hl))⟩
  obtain ⟨l0, t0, e0, f0, m0⟩ := List.map_eq_cons_iff.1 hm
  obtain ⟨l1, t1, e1, f1, m1⟩ := List.map_eq_cons_iff.1 m0
  obtain ⟨l2, t2, e2, f2, m2⟩ := List.map_eq_cons_iff.1 m1
  obtain ⟨l3, t3, e3, f3, m3⟩ := List.map_eq_cons_iff.1 m2
  have e4 := List.map_eq_nil_iff.1 m3
  refine ⟨l0.name, l1.name, l2.name, l3.name, ?_⟩
  rw [e0, e1, e2, e3, e4, ← line_eq f0, ← line_eq f1, ← line_eq f2, ← line_eq f3]

/-- Two of shape's own tests, read off its run. -/
theorem tests_of_shape {S : Shape} (h : shape cf = Except.ok S) :
    cf.lB + 2 ≤ cf.lt ∧ 0 < cf.H / 2 ^ cf.lgk := by
  unfold Attention.shape at h
  obtain ⟨e1, h⟩ := refuse_ok h
  obtain ⟨e2, -⟩ := refuse_ok h
  constructor
  · simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at e1
    omega
  · rw [Bool.or_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq] at e2
    exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero e2.1) (Nat.dvd_of_mod_eq_zero e2.2))
      (Nat.two_pow_pos _)

theorem tests_of_hid {lid : ℕ} {S : Shape} {fs : Model.Forest.Shape}
    (h : shapeHid lid cf = Except.ok (S, fs)) : cf.lB + 2 ≤ cf.lt ∧ 0 < cf.H / 2 ^ cf.lgk := by
  obtain ⟨A, -, -, hA, -, -⟩ := hid_calls h
  exact tests_of_shape hA

theorem mapM_cons_ok {α β : Type} {f : α → Except String β} {x : α} {l : List α} {r : List β}
    (h : (x :: l).mapM f = Except.ok r) :
    ∃ y ys, f x = Except.ok y ∧ l.mapM f = Except.ok ys ∧ r = y :: ys := by
  rw [List.mapM_cons] at h
  obtain ⟨y, hy, h⟩ := bind_ok h
  obtain ⟨ys, hys, h⟩ := bind_ok h
  exact ⟨y, ys, hy, hys, (Except.ok.inj h).symm⟩

/-- What layCall returns, beside the table. -/
theorem layCall_parts {Sm : ℕ} {Tt : Array ℕ} {name : String} {segs : List Seg} {k : ACall}
    (h : layCall cf HA Sm Tt (name, kind, sh, segs) = Except.ok k) :
    k.kind = kind ∧ k.sh = sh ∧ k.pcs = (placePieces cf HA kind sh segs).1 ∧
      k.call.n = max (ceilLog2 (placePieces cf HA kind sh segs).2) cf.nmin := by
  unfold Attention.layCall at h
  obtain ⟨-, h⟩ := refuse_ok h
  have e := Except.ok.inj h
  subst e
  refine ⟨rfl, rfl, rfl, ?_⟩
  cases kind <;> rfl

/-- The pieces of a family, each with the number of its first key. -/
def famAt (s : Seg) (HA c base n : ℕ) : List Piece :=
  (List.range n).map fun b => { pcOf s HA c b with off := base + b * 2 ^ c }

/-- **What the theorems below read of a shape's four calls.** The number of pairs is
2 ^ cf.ll * (cf.H / 2 ^ cf.lgk). -/
structure FourCalls (cf : Cfg) (S : Shape) : Prop where
  size : S.calls.size = 4
  kind : (callAt S 0).kind = .kr ∧ (callAt S 1).kind = .kfd ∧ (callAt S 2).kind = .r16 ∧
    (callAt S 3).kind = .wh
  sh : (callAt S 1).sh = cf.sh.getD 0 0
  p0 : (callAt S 0).pcs.toList =
    famAt .rm (cf.H / 2 ^ cf.lgk) (nMOf cf) 0 (2 ^ cf.ll * (cf.H / 2 ^ cf.lgk)) ++
      famAt .rd (cf.H / 2 ^ cf.lgk) (nDOf cf)
        (2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ nMOf cf) (2 ^ cf.ll * (cf.H / 2 ^ cf.lgk))
  p1 : (callAt S 1).pcs.toList =
    famAt .fm (cf.H / 2 ^ cf.lgk) (nMOf cf) 0 (2 ^ cf.ll * (cf.H / 2 ^ cf.lgk)) ++
      famAt .fd (cf.H / 2 ^ cf.lgk) (nDOf cf)
        (2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ nMOf cf) (2 ^ cf.ll * (cf.H / 2 ^ cf.lgk))
  p2 : (callAt S 2).pcs.toList =
    famAt .wl (cf.H / 2 ^ cf.lgk) (segBits cf .wl) 0 (2 ^ cf.ll * (cf.H / 2 ^ cf.lgk)) ++
      famAt .ix (cf.H / 2 ^ cf.lgk) (segBits cf .ix)
        (2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ segBits cf .wl) (2 ^ cf.ll * (cf.H / 2 ^ cf.lgk))
  p3 : (callAt S 3).pcs.toList =
    famAt .wh (cf.H / 2 ^ cf.lgk) (segBits cf .wh) 0 (2 ^ cf.ll * (cf.H / 2 ^ cf.lgk))
  ap : ∀ q < 4, (callAt S q).pcs.toList.Pairwise fun p r =>
    p.off + 2 ^ p.b ≤ r.off ∨ r.off + 2 ^ r.b ≤ p.off
  n0 : 2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ nMOf cf +
    2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ nDOf cf ≤ 2 ^ (callAt S 0).call.n
  n1 : 2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ nMOf cf +
    2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ nDOf cf ≤ 2 ^ (callAt S 1).call.n
  n2 : 2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ segBits cf .wl +
    2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ segBits cf .ix ≤ 2 ^ (callAt S 2).call.n
  n3 : 2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ segBits cf .wh ≤ 2 ^ (callAt S 3).call.n

/-! ## 5. The four calls of a shape -/

theorem callAt_of_list {S : Shape} {l : List ACall} (h : S.calls.toList = l) (q : ℕ) :
    callAt S q = l.getD q default := by
  unfold callAt
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, h, List.getD_eq_getElem?_getD]

/-- The pieces that placePieces returns are pairwise apart, whatever the call. -/
theorem place_apart (cf : Cfg) (HA : ℕ) (kind : Table) (sh : ℕ) (segs : List Seg) :
    (placePieces cf HA kind sh segs).1.toList.Pairwise fun p r =>
      p.off + 2 ^ p.b ≤ r.off ∨ r.off + 2 ^ r.b ≤ p.off := by
  unfold Attention.placePieces
  rw [layOff_eq]
  exact offsL_apart _ _

theorem le_pow_max (t m : ℕ) : t ≤ 2 ^ max (ceilLog2 t) m :=
  le_trans (Slice.le_two_pow_ceilLog2 t) (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))

/-- **The four calls, from what shape has run.** f: what a later step does to call number i; it
leaves kind, shift, pieces and the number n. -/
theorem four_of_list {S A : Shape} (hA : shape cf = Except.ok A) (U : UsualCalls cf)
    (f : ℕ → ACall → ACall)
    (hf : ∀ i k, (f i k).kind = k.kind ∧ (f i k).sh = k.sh ∧ (f i k).pcs = k.pcs ∧
      (f i k).call.n = k.call.n)
    (hS : S.calls.toList = A.calls.toList.mapIdx f) : FourCalls cf S := by
  obtain ⟨hlt, hHA⟩ := tests_of_shape hA
  obtain ⟨calls, hM, hc, -, hsz⟩ := calls_of_shape hA
  obtain ⟨n0, n1, n2, n3, hL⟩ := U.lines
  rw [shsOf_one hsz U.one, hL] at hM
  have hx : ([⟨n0, .kr, [.rm, .rd]⟩, ⟨n1, .kfd, [.fm, .fd]⟩, ⟨n2, .r16, [.wl, .ix]⟩,
      ⟨n3, .wh, [.wh]⟩] : List Line).flatMap (expandLine [cf.sh.getD 0 0]) =
      [(n0 ++ "", .kr, cf.sh.getD 0 0, [.rm, .rd]), (n1 ++ "", .kfd, cf.sh.getD 0 0, [.fm, .fd]),
        (n2, .r16, 0, [.wl, .ix]), (n3, .wh, 0, [.wh])] := rfl
  rw [hx] at hM
  obtain ⟨k0, r0, h0, hM0, rfl⟩ := mapM_cons_ok hM
  obtain ⟨k1, r1, h1, hM1, rfl⟩ := mapM_cons_ok hM0
  obtain ⟨k2, r2, h2, hM2, rfl⟩ := mapM_cons_ok hM1
  obtain ⟨k3, r3, h3, hM3, rfl⟩ := mapM_cons_ok hM2
  have hr : r3 = [] := by
    rw [List.mapM_nil] at hM3
    exact (Except.ok.inj hM3).symm
  subst hr
  have hT : S.calls.toList = [f 0 k0, f 1 k1, f 2 k2, f 3 k3] := by
    rw [hS, hc]
    simp [List.mapIdx_cons]
  have c0 : callAt S 0 = f 0 k0 := by rw [callAt_of_list hT]; rfl
  have c1 : callAt S 1 = f 1 k1 := by rw [callAt_of_list hT]; rfl
  have c2 : callAt S 2 = f 2 k2 := by rw [callAt_of_list hT]; rfl
  have c3 : callAt S 3 = f 3 k3 := by rw [callAt_of_list hT]; rfl
  obtain ⟨a1, a2, a3, a4⟩ := layCall_parts h0
  obtain ⟨b1, b2, b3, b4⟩ := layCall_parts h1
  obtain ⟨d1, d2, d3, d4⟩ := layCall_parts h2
  obtain ⟨e1, e2, e3, e4⟩ := layCall_parts h3
  have hMD : nDOf cf ≤ nMOf cf := by
    unfold Attention.nDOf Attention.nMOf
    omega
  have hWX : segBits cf .ix ≤ segBits cf .wl := by
    show cf.lgk + cf.lt ≤ 1 + cf.lgk + cf.lt + cf.ldh
    omega
  have noSh : ∀ {k : Table}, k.bySh = false →
      k.bySh = true → ∀ lam < 2 ^ cf.ll, cf.sh.getD lam 0 = 0 := by
    intro k hk hk'
    rw [hk] at hk'
    cases hk'
  have P0 := place_two (kind := .kr) hHA (fun _ => U.one) .rm .rd hMD
  have P1 := place_two (kind := .kfd) hHA (fun _ => U.one) .fm .fd hMD
  have P2 := place_two (kind := .r16) hHA (noSh rfl) .wl .ix hWX
  have P3 := place_one (kind := .wh) hHA (noSh rfl) .wh
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Array.length_toList, hT]
    rfl
  · rw [c0, (hf 0 k0).1, a1]
  · rw [c1, (hf 1 k1).1, b1]
  · rw [c2, (hf 2 k2).1, d1]
  · rw [c3, (hf 3 k3).1, e1]
  · rw [c1, (hf 1 k1).2.1, b2]
  · rw [c0, (hf 0 k0).2.2.1, a3, P0]
    simp [famAt, segBits]
  · rw [c1, (hf 1 k1).2.2.1, b3, P1]
    simp [famAt, segBits]
  · rw [c2, (hf 2 k2).2.2.1, d3, P2]
    simp [famAt]
  · rw [c3, (hf 3 k3).2.2.1, e3, P3]
    simp [famAt]
  · intro q hq
    have hq' : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
    rcases hq' with rfl | rfl | rfl | rfl
    · rw [c0, (hf 0 k0).2.2.1, a3]
      exact place_apart _ _ _ _ _
    · rw [c1, (hf 1 k1).2.2.1, b3]
      exact place_apart _ _ _ _ _
    · rw [c2, (hf 2 k2).2.2.1, d3]
      exact place_apart _ _ _ _ _
    · rw [c3, (hf 3 k3).2.2.1, e3]
      exact place_apart _ _ _ _ _
  · rw [c0, (hf 0 k0).2.2.2, a4, P0]
    simpa [segBits] using le_pow_max (0 + (2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ segBits cf .rm +
      2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ segBits cf .rd)) cf.nmin
  · rw [c1, (hf 1 k1).2.2.2, b4, P1]
    simpa [segBits] using le_pow_max (0 + (2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ segBits cf .fm +
      2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ segBits cf .fd)) cf.nmin
  · rw [c2, (hf 2 k2).2.2.2, d4, P2]
    simpa using le_pow_max (0 + (2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ segBits cf .wl +
      2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ segBits cf .ix)) cf.nmin
  · rw [c3, (hf 3 k3).2.2.2, e4, P3]
    simpa using le_pow_max (0 + 2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ segBits cf .wh) cf.nmin

theorem mapIdx_keep {α : Type} : ∀ l : List α, l.mapIdx (fun _ k => k) = l
  | [] => rfl
  | a :: l => by
    rw [List.mapIdx_cons]
    exact congrArg (a :: ·) (mapIdx_keep l)

/-- What shape returns. -/
theorem four_of_shape {S : Shape} (h : shape cf = Except.ok S) (U : UsualCalls cf) :
    FourCalls cf S :=
  four_of_list h U (fun _ k => k) (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩) (mapIdx_keep _).symm

/-- What shapeHid returns. -/
theorem four_of_hid {lid : ℕ} {S : Shape} {fs : Model.Forest.Shape}
    (h : shapeHid lid cf = Except.ok (S, fs)) (U : UsualCalls cf) : FourCalls cf S := by
  obtain ⟨A, io, kbA, hA, eS, -⟩ := hid_calls h
  refine four_of_list hA U
    (fun q c => { c with call := { c.call with iota := io q } })
    (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩) ?_
  rw [eS]
  exact Array.toList_mapIdx ..

/-! ## 6. LaidA, the kinds, the room -/

theorem mem_famAt {s : Seg} {HA c base n b : ℕ} (hb : b < n) :
    ({ seg := s, lam := b / HA, a := b % HA, b := c, off := base + b * 2 ^ c } : Piece) ∈
      famAt s HA c base n :=
  List.mem_map.2 ⟨b, List.mem_range.2 hb, rfl⟩

/-- The library's numbers of an attention segment, at the sizes made from the shape, are the
verifier's. -/
theorem dim_nums {S : Shape} (P : Shaped cf S) (hlt : cf.lB + 2 ≤ cf.lt) :
    (dimOf S).nb = 2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) ∧ (dimOf S).lM = nMOf cf ∧
      (dimOf S).lD = nDOf cf ∧ (dimOf S).lW = segBits cf .wl ∧ (dimOf S).lX = segBits cf .ix ∧
      (dimOf S).l4 = segBits cf .wh := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show S.Lam * S.HA = _
    rw [P.Lam, P.HA]
  · show S.cf.lgk + (S.lnT - 1) + (S.lnT - 1 + 1) + S.cf.lB + S.cf.lB = cf.lgk + 2 * cf.lt - 1
    rw [P.cfg, P.lnT]
    omega
  · show S.cf.lgk + (S.lnT - 1 + 1) + S.cf.lB + S.cf.lB = cf.lgk + cf.lt + cf.lB
    rw [P.cfg, P.lnT]
    omega
  · show 1 + S.cf.lgk + (S.lnT - 1 + 1 + S.cf.lB) + S.cf.ldh = 1 + cf.lgk + cf.lt + cf.ldh
    rw [P.cfg, P.lnT]
    omega
  · show S.cf.lgk + (S.lnT - 1 + 1 + S.cf.lB) = cf.lgk + cf.lt
    rw [P.cfg, P.lnT]
    omega
  · show S.cf.lgk + (S.lnT - 1 + 1 + S.cf.lB) + S.cf.ldh = cf.lgk + cf.lt + cf.ldh
    rw [P.cfg, P.lnT]
    omega

/-- **How the four calls are laid, as a theorem.** -/
theorem laidA_of_four {S : Shape} (P : Shaped cf S) (hlt : cf.lB + 2 ≤ cf.lt)
    (Fo : FourCalls cf S) : LaidA S fun q : Fin 4 => callAt S q.val := by
  obtain ⟨hnb, hM, hD, hW, hX, h4⟩ := dim_nums P hlt
  refine ⟨?_, fun q => Fo.ap q.val q.isLt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    have hq : q.val < S.calls.size := by rw [Fo.size]; exact q.isLt
    unfold callAt
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hq]
    rfl
  · show (callAt S 1).sh = S.cf.sh.getD 0 0
    rw [P.cfg]
    exact Fo.sh
  · intro b hb
    show pcAt S .rm (dimOf S).lM 0 b ∈ (callAt S 0).pcs.toList
    rw [Fo.p0, hM]
    unfold pcAt
    rw [P.HA]
    exact List.mem_append_left _ (mem_famAt (hnb ▸ hb))
  · intro b hb
    show pcAt S .rd (dimOf S).lD ((dimOf S).nb * 2 ^ (dimOf S).lM) b ∈ (callAt S 0).pcs.toList
    rw [Fo.p0, hM, hD, hnb]
    unfold pcAt
    rw [P.HA]
    exact List.mem_append_right _ (mem_famAt (hnb ▸ hb))
  · intro b hb
    show pcAt S .fm (dimOf S).lM 0 b ∈ (callAt S 1).pcs.toList
    rw [Fo.p1, hM]
    unfold pcAt
    rw [P.HA]
    exact List.mem_append_left _ (mem_famAt (hnb ▸ hb))
  · intro b hb
    show pcAt S .fd (dimOf S).lD ((dimOf S).nb * 2 ^ (dimOf S).lM) b ∈ (callAt S 1).pcs.toList
    rw [Fo.p1, hM, hD, hnb]
    unfold pcAt
    rw [P.HA]
    exact List.mem_append_right _ (mem_famAt (hnb ▸ hb))
  · intro b hb
    show pcAt S .wl (dimOf S).lW 0 b ∈ (callAt S 2).pcs.toList
    rw [Fo.p2, hW]
    unfold pcAt
    rw [P.HA]
    exact List.mem_append_left _ (mem_famAt (hnb ▸ hb))
  · intro b hb
    show pcAt S .ix (dimOf S).lX ((dimOf S).nb * 2 ^ (dimOf S).lW) b ∈ (callAt S 2).pcs.toList
    rw [Fo.p2, hW, hX, hnb]
    unfold pcAt
    rw [P.HA]
    exact List.mem_append_right _ (mem_famAt (hnb ▸ hb))
  · intro b hb
    show pcAt S .wh (dimOf S).l4 0 b ∈ (callAt S 3).pcs.toList
    rw [Fo.p3, h4]
    unfold pcAt
    rw [P.HA]
    exact mem_famAt (hnb ▸ hb)

/-- Call q has the kind with the library's number q. -/
theorem kinds_of_four {S : Shape} (Fo : FourCalls cf S) :
    ∀ q : Fin 4, noK (callAt S q.val).kind = q
  | ⟨0, _⟩ => by
    show noK (callAt S 0).kind = 0
    rw [Fo.kind.1]
    rfl
  | ⟨1, _⟩ => by
    show noK (callAt S 1).kind = 1
    rw [Fo.kind.2.1]
    rfl
  | ⟨2, _⟩ => by
    show noK (callAt S 2).kind = 2
    rw [Fo.kind.2.2.1]
    rfl
  | ⟨3, _⟩ => by
    show noK (callAt S 3).kind = 3
    rw [Fo.kind.2.2.2]
    rfl

/-- The pieces of call q fit into its 2^n keys. -/
theorem room_of_four {S : Shape} (P : Shaped cf S) (hlt : cf.lB + 2 ≤ cf.lt)
    (Fo : FourCalls cf S) : ∀ q : Fin 4, (dimOf S).used q ≤ 2 ^ (callAt S q.val).call.n := by
  obtain ⟨hnb, hM, hD, hW, hX, h4⟩ := dim_nums P hlt
  intro q
  match q with
  | ⟨0, _⟩ =>
    show (dimOf S).nb * 2 ^ (dimOf S).lM + (dimOf S).nb * 2 ^ (dimOf S).lD ≤
      2 ^ (callAt S 0).call.n
    rw [hnb, hM, hD]
    exact Fo.n0
  | ⟨1, _⟩ =>
    show (dimOf S).nb * 2 ^ (dimOf S).lM + (dimOf S).nb * 2 ^ (dimOf S).lD ≤
      2 ^ (callAt S 1).call.n
    rw [hnb, hM, hD]
    exact Fo.n1
  | ⟨2, _⟩ =>
    show (dimOf S).nb * 2 ^ (dimOf S).lW + (dimOf S).nb * 2 ^ (dimOf S).lX ≤
      2 ^ (callAt S 2).call.n
    rw [hnb, hW, hX]
    exact Fo.n2
  | ⟨3, _⟩ =>
    show (dimOf S).nb * 2 ^ (dimOf S).l4 ≤ 2 ^ (callAt S 3).call.n
    rw [hnb, h4]
    exact Fo.n3

/-- **LaidA at what shapeHid returns.** -/
theorem laidA_of_hid {lid : ℕ} {S : Shape} {fs : Model.Forest.Shape}
    (h : shapeHid lid cf = Except.ok (S, fs)) (U : UsualCalls cf) :
    LaidA S fun q : Fin 4 => callAt S q.val :=
  laidA_of_four (shaped_of_hid h) (tests_of_hid h).1 (four_of_hid h U)

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.place_two
#print axioms OnBytes.Road.L5.shsOf_one
#print axioms OnBytes.Road.L5.usual_of_test
#print axioms OnBytes.Road.L5.tests_of_hid
#print axioms OnBytes.Road.L5.four_of_hid
#print axioms OnBytes.Road.L5.laidA_of_hid
#print axioms OnBytes.Road.L5.kinds_of_four
#print axioms OnBytes.Road.L5.room_of_four
