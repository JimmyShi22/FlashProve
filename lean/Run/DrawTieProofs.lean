-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/DrawTieProofs.lean: the proofs of Run/DrawTie.lean's statements (`Run.drawTie_read`,
`drawTie_all`, `drawTie_ev`, `drawTie_bs`, `drawTie_inj`). Many statements of this library are
written twice: a definition in the namespace `Spec` states a proposition, and a theorem of the same
name outside that namespace proves it (lean/GLOSSARY.md).

`runAt` is a homomorphism: of `ret`, `bind`, `word` it makes the three primitives from which every
draw of Fmt/Rules6.lean is built (`runAt_bind`, `runAt_map`, `runAt_pair`, `runAt_words`).
-/
import Run.DrawTie

set_option autoImplicit false

namespace Run
open Iop

namespace Tr
variable {W C D : Type}

theorem runAt_bind (t : Tr W C) (f : C → Tr W D) (row : ℕ → W) :
    ∀ c, (t.bind f).runAt row c = (f (t.runAt row c).1).runAt row (t.runAt row c).2 := by
  induction t with
  | ret a => exact fun _ => rfl
  | ask k ih => exact fun c => ih (row c) (c + 1)

theorem runAt_map (g : C → D) (t : Tr W C) (row : ℕ → W) (c : ℕ) :
    (t.map g).runAt row c = (g (t.runAt row c).1, (t.runAt row c).2) :=
  runAt_bind t _ row c

theorem runAt_pair (s : Tr W C) (t : Tr W D) (row : ℕ → W) (c : ℕ) :
    (pair s t).runAt row c =
      (((s.runAt row c).1, (t.runAt row (s.runAt row c).2).1),
        (t.runAt row (s.runAt row c).2).2) := by
  show (s.bind fun a => t.map fun b => (a, b)).runAt row c = _
  rw [runAt_bind, runAt_map]

/-- the next n words -/
theorem runAt_words (row : ℕ → W) :
    ∀ (n c : ℕ), (vec n word).runAt row c = ((fun i : Fin n => row (c + i.val)), c + n)
  | 0, c => Prod.ext (funext fun i => i.elim0) rfl
  | n + 1, c => by
    show ((pair word (vec n word)).map fun x => (Fin.cons x.1 x.2 : Fin (n + 1) → W)).runAt row c =
      _
    rw [runAt_map, runAt_pair, runAt_words row n]
    refine Prod.ext (funext fun i => ?_) (by show c + 1 + n = c + (n + 1); omega)
    refine Fin.cases rfl (fun j => ?_) i
    show row (c + 1 + j.val) = row (c + (j.val + 1))
    rw [Nat.add_assoc, Nat.add_comm 1]

theorem ev_runAt (d : W) {t : Tr W C} {K : ℕ} (h : t.Most K) :
    ∀ (u : Fin K → W) (row : ℕ → W) (c : ℕ),
      (∀ i : Fin K, row (c + i.val) = u i) → t.ev d K u = (t.runAt row c).1 := by
  induction h with
  | ret a K =>
    intro u row c _
    cases K <;> rfl
  | ask k K _ ih =>
    intro u row c hu
    show ev d K (k (u 0)) (Fin.tail u) = (runAt (k (row c)) row (c + 1)).1
    have h0 : row c = u 0 := hu 0
    rw [h0]
    refine ih (u 0) (Fin.tail u) row (c + 1) fun i => ?_
    have := hu i.succ
    show row (c + 1 + i.val) = u i.succ
    rw [← this]
    show row (c + 1 + i.val) = row (c + (i.val + 1))
    rw [Nat.add_assoc, Nat.add_comm 1]

end Tr

/-! ### Numbers below p and machine words -/

section
variable {f : _root_.Fmt.Fld}

theorem p_le (f : _root_.Fmt.Fld) : f.p ≤ 2 ^ 64 := by cases f <;> decide

theorem toU_toNat (x : FV f) : (toU x).toNat = x.val := by
  show (UInt64.ofNat x.val).toNat = x.val
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (p_le f))

theorem toU_inj : Function.Injective (toU (f := f)) := fun x y h =>
  Fin.ext (by rw [← toU_toNat x, ← toU_toNat y, h])

theorem toU_mk (x : UInt64) (h : x.toNat < f.p) : toU (⟨x.toNat, h⟩ : FV f) = x :=
  UInt64.ofNat_toNat

theorem toU_z : toU (zF f) = 0 := rfl

theorem toU3_inj : Function.Injective (toU3 (f := f)) := fun x y h => by
  obtain ⟨a, b, c⟩ := x
  obtain ⟨a', b', c'⟩ := y
  have h1 : toU a = toU a' := congrArg (fun e : _root_.Fmt.Ext => e.1) h
  have h2 : toU b = toU b' := congrArg (fun e : _root_.Fmt.Ext => e.2.1) h
  have h3 : toU c = toU c' := congrArg (fun e : _root_.Fmt.Ext => e.2.2) h
  rw [toU_inj h1, toU_inj h2, toU_inj h3]

theorem toU3_z : toU3 (zF f, zF f, zF f) = (0, 0, 0) := rfl

theorem toU3_eq_z (e : EV f) : toU3 e = (0, 0, 0) ↔ e = (zF f, zF f, zF f) :=
  ⟨fun h => toU3_inj (h.trans toU3_z.symm), fun h => by rw [h]; rfl⟩

theorem okF_of_some {w x : UInt64} (h : _root_.Fmt.Fld.tryWord f w = some x) :
    okF f w = some ⟨x.toNat, try_lt f w x h⟩ :=
  (okF_some f w _).2 (by rw [h]; rfl)

theorem okF_of_none {w : UInt64} (h : _root_.Fmt.Fld.tryWord f w = none) : okF f w = none :=
  (okF_none f w).2 (by rw [h]; rfl)

end

/-! ### The kinds of draw -/

theorem tie_FN (f : _root_.Fmt.Fld) (row : _root_.Fmt.Row) :
    ∀ (n c : ℕ), _root_.Fmt.drawFN f n row c =
      (toU ((Tr.tries (okF f) (zF f) n).runAt row c).1, ((Tr.tries (okF f) (zF f) n).runAt row c).2)
  | 0, _ => rfl
  | n + 1, c => by
    cases h : _root_.Fmt.Fld.tryWord f (row c) with
    | some x =>
      have e1 : _root_.Fmt.drawFN f (n + 1) row c = (x, c + 1) := by
        simp only [_root_.Fmt.drawFN, _root_.Fmt.Dr.bind, _root_.Fmt.Dr.word, h, _root_.Fmt.Dr.pure]
      have e2 : (Tr.tries (okF f) (zF f) (n + 1)).runAt row c =
          (⟨x.toNat, try_lt f _ x h⟩, c + 1) := by
        simp only [Tr.tries, Tr.runAt, okF_of_some h]
      rw [e1, e2, toU_mk]
    | none =>
      have e1 : _root_.Fmt.drawFN f (n + 1) row c = _root_.Fmt.drawFN f n row (c + 1) := by
        simp only [_root_.Fmt.drawFN, _root_.Fmt.Dr.bind, _root_.Fmt.Dr.word, h]
      have e2 : (Tr.tries (okF f) (zF f) (n + 1)).runAt row c =
          (Tr.tries (okF f) (zF f) n).runAt row (c + 1) := by
        simp only [Tr.tries, Tr.runAt, okF_of_none h]
      rw [e1, e2]
      exact tie_FN f row n (c + 1)

theorem tie_F (f : _root_.Fmt.Fld) (row : _root_.Fmt.Row) (c : ℕ) :
    _root_.Fmt.drawF f row c =
      (toU ((trF (okF f) (zF f)).runAt row c).1, ((trF (okF f) (zF f)).runAt row c).2) :=
  tie_FN f row 6 c

theorem tie_E (f : _root_.Fmt.Fld) (row : _root_.Fmt.Row) (c : ℕ) :
    _root_.Fmt.drawE f row c =
      (toU3 ((trE (okF f) (zF f)).runAt row c).1, ((trE (okF f) (zF f)).runAt row c).2) := by
  show (((_root_.Fmt.drawF f row c).1,
        (_root_.Fmt.drawF f row (_root_.Fmt.drawF f row c).2).1,
        (_root_.Fmt.drawF f row (_root_.Fmt.drawF f row (_root_.Fmt.drawF f row c).2).2).1),
      (_root_.Fmt.drawF f row (_root_.Fmt.drawF f row (_root_.Fmt.drawF f row c).2).2).2) = _
  unfold trE
  rw [Tr.runAt_pair, Tr.runAt_pair]
  simp only [tie_F]
  rfl

theorem tie_NZ (f : _root_.Fmt.Fld) (row : _root_.Fmt.Row) (c : ℕ) :
    _root_.Fmt.drawNZ f row c =
      (toU3 ((trNZ (okF f) (zF f) (oE f)).runAt row c).1.1,
        ((trNZ (okF f) (zF f) (oE f)).runAt row c).2) := by
  show (if (_root_.Fmt.drawE f row c).1 = (0, 0, 0) then
        (_root_.Fmt.drawE f).bind fun e' =>
          _root_.Fmt.Dr.pure (if e' = (0, 0, 0) then (1, 0, 0) else e')
          else _root_.Fmt.Dr.pure (_root_.Fmt.drawE f row c).1)
      row (_root_.Fmt.drawE f row c).2 = _
  show _ = (toU3 (((trE (okF f) (zF f)).again (zF f, zF f, zF f) (oE f)).runAt row c).1.1,
      (((trE (okF f) (zF f)).again (zF f, zF f, zF f) (oE f)).runAt row c).2)
  unfold Tr.again
  rw [Tr.runAt_bind, tie_E]
  by_cases h : ((trE (okF f) (zF f)).runAt row c).1 = (zF f, zF f, zF f)
  · rw [if_pos ((toU3_eq_z _).2 h), dif_neg (not_not.2 h), Tr.runAt_bind]
    show ((if (_root_.Fmt.drawE f row _).1 = (0, 0, 0) then (1, 0, 0)
          else (_root_.Fmt.drawE f row _).1),
        (_root_.Fmt.drawE f row _).2) = _
    rw [tie_E]
    by_cases h' : ((trE (okF f) (zF f)).runAt row ((trE (okF f) (zF f)).runAt row c).2).1 =
      (zF f, zF f, zF f)
    · rw [if_pos ((toU3_eq_z _).2 h'), dif_neg (not_not.2 h')]
      rfl
    · rw [if_neg (fun hh => h' ((toU3_eq_z _).1 hh)), dif_pos h']
      rfl
  · rw [if_neg (fun hh => h ((toU3_eq_z _).1 hh)), dif_pos h]
    rfl

/-- the next n words, as a list -/
theorem tie_words (row : _root_.Fmt.Row) :
    ∀ (n c : ℕ), _root_.Fmt.drawWords n row c = (List.ofFn fun i : Fin n => row (c + i.val), c + n)
  | 0, _ => rfl
  | n + 1, c => by
    show (row c :: (_root_.Fmt.drawWords n row (c + 1)).1, (_root_.Fmt.drawWords n row (c + 1)).2) =
      _
    rw [tie_words row n (c + 1), List.ofFn_succ]
    refine Prod.ext ?_ (by show c + 1 + n = c + (n + 1); omega)
    show row c :: List.ofFn (fun i : Fin n => row (c + 1 + i.val)) =
      row (c + 0) :: List.ofFn fun i : Fin n => row (c + (i.val + 1))
    congr 2
    funext i
    rw [Nat.add_assoc, Nat.add_comm 1]

/-- a list by runs of 32, in one formula -/
theorem trits_range (g : ℕ → UInt64) :
    ∀ (m s n : ℕ), _root_.Fmt.tritsOf ((List.range m).map fun i => g (s + i)) n =
      (List.range (min n (32 * m))).map fun j => _root_.Fmt.tritAt (g (s + j / 32)) (j % 32)
  | 0, _, n => by simp [_root_.Fmt.tritsOf]
  | m + 1, s, n => by
    have e1 : (List.range (m + 1)).map (fun i => g (s + i)) =
        g s :: (List.range m).map fun i => g (s + 1 + i) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      show g (s + (i + 1)) = g (s + 1 + i)
      rw [Nat.add_assoc, Nat.add_comm 1]
    rw [e1]
    show (List.range (min n 32)).map (_root_.Fmt.tritAt (g s)) ++
        _root_.Fmt.tritsOf ((List.range m).map fun i => g (s + 1 + i)) (n - 32) = _
    rw [trits_range g m (s + 1) (n - 32)]
    have e2 : min n (32 * (m + 1)) = min n 32 + min (n - 32) (32 * m) := by omega
    rw [e2, List.range_add, List.map_append, List.map_map]
    congr 1
    · refine List.map_congr_left fun j hj => ?_
      have hj' : j < 32 := Nat.lt_of_lt_of_le (List.mem_range.1 hj) (Nat.min_le_right _ _)
      rw [Nat.div_eq_of_lt hj', Nat.mod_eq_of_lt hj', Nat.add_zero]
    · refine List.map_congr_left fun j hj => ?_
      have hb : j < min (n - 32) (32 * m) := List.mem_range.1 hj
      have ha : min n 32 = 32 := by omega
      show _root_.Fmt.tritAt (g (s + 1 + j / 32)) (j % 32) =
        _root_.Fmt.tritAt (g (s + (min n 32 + j) / 32)) ((min n 32 + j) % 32)
      rw [ha]
      have d1 : (32 + j) / 32 = 1 + j / 32 := by omega
      have d2 : (32 + j) % 32 = j % 32 := by omega
      rw [d1, d2, Nat.add_assoc]

theorem ofFn_range {α : Type} (n : ℕ) (h : ℕ → α) :
    List.ofFn (fun j : Fin n => h j.val) = (List.range n).map h := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp

theorem tie_trits (n : ℕ) (row : _root_.Fmt.Row) (c : ℕ) :
    _root_.Fmt.drawTrits n row c =
      (List.ofFn fun j => trit (((trMany ((n + 31) / 32) (bitsOf n)).runAt row c).1 j),
        ((trMany ((n + 31) / 32) (bitsOf n)).runAt row c).2) := by
  show (_root_.Fmt.tritsOf (_root_.Fmt.drawWords ((n + 31) / 32) row c).1 n,
      (_root_.Fmt.drawWords ((n + 31) / 32) row c).2) = _
  unfold trMany
  rw [Tr.runAt_map, Tr.runAt_words, tie_words,
    ofFn_range ((n + 31) / 32) (fun i => row (c + i)), trits_range row]
  refine Prod.ext ?_ rfl
  have e : min n (32 * ((n + 31) / 32)) = n := by omega
  show (List.range (min n (32 * ((n + 31) / 32)))).map
      (fun j => _root_.Fmt.tritAt (row (c + j / 32)) (j % 32)) =
    List.ofFn fun j : Fin n => _root_.Fmt.tritAt (row (c + j.val / 32)) (j.val % 32)
  rw [e, ofFn_range n fun j => _root_.Fmt.tritAt (row (c + j / 32)) (j % 32)]

/-! ### Four words and their 32 bytes -/

theorem shr_toNat (a k : UInt64) (n : ℕ) (hk : k.toNat % 64 = n) :
    (a >>> k).toNat = a.toNat / 2 ^ n := by
  rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, hk]

/-- a word is given by its eight bytes -/
theorem bytes_inj (x y : UInt64) (h0 : x.toUInt8 = y.toUInt8)
    (h1 : (x >>> 8).toUInt8 = (y >>> 8).toUInt8) (h2 : (x >>> 16).toUInt8 = (y >>> 16).toUInt8)
    (h3 : (x >>> 24).toUInt8 = (y >>> 24).toUInt8) (h4 : (x >>> 32).toUInt8 = (y >>> 32).toUInt8)
    (h5 : (x >>> 40).toUInt8 = (y >>> 40).toUInt8) (h6 : (x >>> 48).toUInt8 = (y >>> 48).toUInt8)
    (h7 : (x >>> 56).toUInt8 = (y >>> 56).toUInt8) : x = y := by
  have g : ∀ (a b : UInt64),
      a.toUInt8 = b.toUInt8 → a.toNat % 256 = b.toNat % 256 := fun a b e => by
    have := congrArg UInt8.toNat e
    simpa using this
  have k0 := g _ _ h0
  have k1 := g _ _ h1
  have k2 := g _ _ h2
  have k3 := g _ _ h3
  have k4 := g _ _ h4
  have k5 := g _ _ h5
  have k6 := g _ _ h6
  have k7 := g _ _ h7
  rw [shr_toNat _ 8 8 rfl, shr_toNat _ 8 8 rfl] at k1
  rw [shr_toNat _ 16 16 rfl, shr_toNat _ 16 16 rfl] at k2
  rw [shr_toNat _ 24 24 rfl, shr_toNat _ 24 24 rfl] at k3
  rw [shr_toNat _ 32 32 rfl, shr_toNat _ 32 32 rfl] at k4
  rw [shr_toNat _ 40 40 rfl, shr_toNat _ 40 40 rfl] at k5
  rw [shr_toNat _ 48 48 rfl, shr_toNat _ 48 48 rfl] at k6
  rw [shr_toNat _ 56 56 rfl, shr_toNat _ 56 56 rfl] at k7
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  exact UInt64.toNat_inj.1 (by omega)

theorem seal_inj (ws ws' : Fin 4 → UInt64)
    (h : _root_.Fmt.cat ((List.ofFn ws).map _root_.Fmt.u64) =
      _root_.Fmt.cat ((List.ofFn ws').map _root_.Fmt.u64)) : ws = ws' := by
  have hd := congrArg (fun b : ByteArray => b.data.toList) h
  simp [_root_.Fmt.cat, _root_.Fmt.u64, List.ofFn_succ] at hd
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, b4, b5, b6, b7, c0, c1, c2, c3, c4, c5,
      c6, c7, d0, d1, d2, d3, d4, d5, d6, d7⟩ := hd
  funext i
  match i with
  | 0 => exact bytes_inj _ _ a0 a1 a2 a3 a4 a5 a6 a7
  | 1 => exact bytes_inj _ _ b0 b1 b2 b3 b4 b5 b6 b7
  | 2 => exact bytes_inj _ _ c0 c1 c2 c3 c4 c5 c6 c7
  | 3 => exact bytes_inj _ _ d0 d1 d2 d3 d4 d5 d6 d7

/-! ### The statements -/

theorem drawTie_read : Spec.drawTie_read := by
  intro f d row c
  cases d with
  | elem =>
    show (_root_.Fmt.Val.ext (_root_.Fmt.drawE f row c).1, (_root_.Fmt.drawE f row c).2) = _
    rw [tie_E]
    rfl
  | elemNZ =>
    show (_root_.Fmt.Val.ext (_root_.Fmt.drawNZ f row c).1, (_root_.Fmt.drawNZ f row c).2) = _
    rw [tie_NZ]
    rfl
  | pos k => rfl
  | trits n =>
    show (_root_.Fmt.Val.trits (_root_.Fmt.drawTrits n row c).1, (_root_.Fmt.drawTrits n row c).2) =
      _
    rw [tie_trits]
    rfl
  | sealed =>
    show (_root_.Fmt.Val.sealed
          (_root_.Fmt.cat ((_root_.Fmt.drawWords 4 row c).1.map _root_.Fmt.u64)),
        (_root_.Fmt.drawWords 4 row c).2) = _
    rw [tie_words]
    show _ = (out f .sealed ((trMany 4 id).runAt row c).1, ((trMany 4 id).runAt row c).2)
    unfold trMany
    rw [Tr.runAt_map, Tr.runAt_words]
    rfl

theorem drawTie_all : Spec.drawTie_all := by
  intro f ds
  induction ds with
  | nil => exact fun _ _ => rfl
  | cons d ds ih =>
    intro row c
    show ((d.read f row c).1 :: (_root_.Fmt.readAll f ds row (d.read f row c).2).1,
        (_root_.Fmt.readAll f ds row (d.read f row c).2).2) = _
    show _ = (outAll f (d :: ds) (((tree f d).pair (all f ds)).runAt row c).1,
        (((tree f d).pair (all f ds)).runAt row c).2)
    rw [Tr.runAt_pair, drawTie_read f d row c, ih]
    rfl

theorem drawTie_ev : Spec.drawTie_ev := fun _ _ d _ K u h =>
  Tr.ev_runAt d h u (rowFn d u) 0 fun i => by
    show (if h : 0 + i.val < K then u ⟨0 + i.val, h⟩ else d) = u i
    rw [dif_pos (by rw [Nat.zero_add]; exact i.isLt)]
    congr 1
    exact Fin.ext (Nat.zero_add _)

theorem most_tree (f : _root_.Fmt.Fld) : ∀ d : _root_.Fmt.Draw, (tree f d).Most d.most
  | .elem => most_trE _ _
  | .elemNZ => most_trNZ _ _ _
  | .pos _ => Tr.Most.ask _ 0 fun _ => Tr.Most.ret _ 0
  | .trits n => by
    have := Tr.most_map (bitsOf n) (Tr.most_vec (Tr.most_word (W := UInt64)) ((n + 31) / 32))
    rwa [Nat.mul_one] at this
  | .sealed => Tr.most_map id (Tr.most_vec (Tr.most_word (W := UInt64)) 4)

theorem most_all (f : _root_.Fmt.Fld) :
    ∀ ds : List _root_.Fmt.Draw, (all f ds).Most (_root_.Fmt.mostAll ds)
  | [] => Tr.Most.ret _ _
  | d :: ds => Tr.most_pair (most_tree f d) (most_all f ds)

theorem drawTie_bs : Spec.drawTie_bs := by
  intro f ds u
  show outAll f ds
      ((all f ds).ev 0 (4 * ((_root_.Fmt.mostAll ds + 3) / 4))
        (rowOf e64 ((_root_.Fmt.mostAll ds + 3) / 4) u)) = _
  rw [drawTie_ev _ _ 0 (all f ds) _ _ (Tr.most_mono (most_all f ds) (by omega)), drawTie_all]
  rfl

theorem drawTie_inj : Spec.drawTie_inj := by
  intro f d hd
  cases d with
  | elem => exact fun x y h => toU3_inj (_root_.Fmt.Val.ext.inj h)
  | elemNZ => exact fun x y h => Subtype.ext (toU3_inj (_root_.Fmt.Val.ext.inj h))
  | pos k => exact fun x y h => Fin.ext (_root_.Fmt.Val.pos.inj h)
  | trits n => exact absurd rfl (hd n)
  | sealed => exact fun x y h => seal_inj x y (_root_.Fmt.Val.sealed.inj h)

end Run
