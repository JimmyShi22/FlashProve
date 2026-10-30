-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/G6/Rider/Model/OneHotFree.lean: in the field relation of a feed-forward segment the other clauses
do not give identity j10 ("the selector's entries sum to 1").

Definitions, statements and proofs. No protocol occurs here. The relation is `FFSeg.trace`
(Inst/Model/FF/Trace.lean): every cell is small, every key is an entry of its table, every identity
vanishes.

Main names:
  `selOff l' i t`: the cells t with the selector's cells of instance l' at position i set to 0.
  `key_selOff`: which keys read these cells. Of the 34 families all but SEL have the same key at
    `selOff l' i t` as at t, under three premises: the matrices of the routed experts of layer 2 l'
    + 1 are 0; at (l', i) the selector's entries from 1 on are 0; entry 0 times its logit is 0.
  `key_reads`: with no premise: the 28 families other than G, U, D, DD, MR and SEL do not read them.
  `idn_selOff`: no identity but j10 at (l', i) reads these cells.
  `hot_free`: from any trace in the relation that meets the three premises at (l', i), the trace
    with these cells set to 0 has small cells, every key in its table and every identity but j10 at
    (l', i), where the defect is -1.

Limits: `hot_free` is relative: it starts from a trace in the relation that meets the premises. That
there is one is not said here. It asks no validity of (l', i): where l' ≥ D.ne or i ≥ D.T the
identity is no clause of the relation and nothing fails; and over a ring in which 0 = 1 the defect
-1 is 0. The witness is `hot_witness` (Cb/G6/Rider/Model/OneHotFreeRef.lean).

Terms: lean/GLOSSARY.md.

-/
import Inst.Model.FF.Trace

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Rider
open Finset Inst.Model Inst.Model.FFSeg

section Free
variable {R : Type} [CommRing R] (D : Dim) (l' i : ℕ)

/-- The cells t with the selector's cells of instance l' at position i set to 0. -/
def selOff (t : Cell → R) : Cell → R := fun c =>
  if c.X = .sel ∧ c.inst = l' ∧ c.i = i then 0 else t c

variable (t : Cell → R)

theorem selOff_ne {c : Cell} (h : c.X ≠ .sel) : selOff l' i t c = t c := if_neg fun e => h e.1

theorem val_selOff_ne {X : Arr} (h : X ≠ .sel) (n j p : ℕ) :
    val (selOff l' i t) X n j p = val t X n j p := by
  unfold FFSeg.val
  exact congrArg (· + _)
    (sum_congr rfl fun k _ => by rw [selOff_ne l' i t (c := ⟨X, k, n, j, p⟩) h])

theorem val_sel (u : Cell → R) (n e p : ℕ) : val u .sel n e p = u ⟨.sel, 0, n, e, p⟩ := by
  simp [FFSeg.val, Arr.nCell, Arr.off]

theorem val_selOff_at (e : ℕ) : val (selOff l' i t) .sel l' e i = 0 := by
  rw [val_sel]
  exact if_pos ⟨rfl, rfl, rfl⟩

theorem val_selOff_off {n p : ℕ} (h : ¬ (n = l' ∧ p = i)) (e : ℕ) :
    val (selOff l' i t) .sel n e p = val t .sel n e p := by
  rw [val_sel, val_sel]
  exact if_neg fun c => h ⟨c.2.1, c.2.2⟩

theorem streamAt_ne (s : ℕ) : (streamAt D s).1 ≠ .sel := by
  unfold streamAt
  split
  · exact fun h => Arr.noConfusion h
  · split
    · exact fun h => Arr.noConfusion h
    · exact fun h => Arr.noConfusion h

theorem xS_selOff (s j p : ℕ) : xS D (selOff l' i t) s j p = xS D t s j p :=
  val_selOff_ne l' i t (streamAt_ne D s) _ _ _

theorem bS_selOff (s l j p : ℕ) : bS D (selOff l' i t) s l j p = bS D t s l j p :=
  selOff_ne l' i t (c := ⟨(streamAt D s).1, l, (streamAt D s).2, j, p⟩) (streamAt_ne D s)

theorem led_selOff (ν p : ℕ) : led (selOff l' i t) ν p = led t ν p :=
  funext fun _ => val_selOff_ne l' i t (fun h => Arr.noConfusion h) _ _ _

/-- The sum of selector times logit, where the selector's cells are set to 0. -/
theorem mr_selOff_at : mr D (selOff l' i t) l' i = 0 :=
  sum_eq_zero fun e _ => by rw [val_selOff_at, zero_mul]

theorem mr_selOff_off {n p : ℕ} (h : ¬ (n = l' ∧ p = i)) :
    mr D (selOff l' i t) n p = mr D t n p :=
  sum_congr rfl fun e _ => by
    rw [val_selOff_off l' i t h, val_selOff_ne l' i t (fun h => Arr.noConfusion h)]

/-- The three premises at (l', i). -/
structure OffOK (w : ℕ → LW R) : Prop where
  Eg : ∀ e j x, (w (2 * l' + 1)).Eg e j x = 0
  Eu : ∀ e j x, (w (2 * l' + 1)).Eu e j x = 0
  Ed : ∀ e j x, (w (2 * l' + 1)).Ed e j x = 0
  sel : ∀ e, 0 < e → e < D.nx → val t .sel l' e i = 0
  mr0 : val t .sel l' 0 i * val t .lr l' 0 i = 0

variable {l' i t} {w : ℕ → LW R}

theorem OffOK.mr (h : OffOK D l' i t w) : mr D t l' i = 0 :=
  sum_eq_zero fun e hx => by
    rcases Nat.eq_zero_or_pos e with rfl | he
    · exact h.mr0
    · rw [h.sel e he (mem_range.1 hx), zero_mul]

theorem mr_selOff (h : OffOK D l' i t w) (n p : ℕ) : mr D (selOff l' i t) n p = mr D t n p := by
  by_cases c : n = l' ∧ p = i
  · obtain ⟨rfl, rfl⟩ := c
    rw [mr_selOff_at, h.mr]
  · exact mr_selOff_off D l' i t c

theorem layer_of {l : ℕ} (h1 : isExpL l = true) (h2 : l / 2 = l') : l = 2 * l' + 1 := by
  have : l % 2 = 1 := by simpa [isExpL] using h1
  omega

/-- A sum over the experts, each term the selector's entry times a factor that is 0 at layer 2 l' +
1. -/
theorem sel_sum (l p : ℕ) (hl : isExpL l = true) (G G' : ℕ → R) (hG : ∀ e, G' e = G e)
    (h0 : l = 2 * l' + 1 → ∀ e, G e = 0) :
    ∑ e ∈ range D.nx, val (selOff l' i t) .sel (l / 2) e p * G' e =
      ∑ e ∈ range D.nx, val t .sel (l / 2) e p * G e :=
  sum_congr rfl fun e _ => by
    rw [hG]
    by_cases c : l / 2 = l' ∧ p = i
    · rw [h0 (layer_of hl c.1) e, mul_zero, mul_zero]
    · rw [val_selOff_off l' i t c]

theorem hh_selOff (l j p : ℕ) : hh (selOff l' i t) l j p = hh t l j p := by
  unfold hh
  rw [val_selOff_ne l' i t (fun h => Arr.noConfusion h),
    val_selOff_ne l' i t (fun h => Arr.noConfusion h)]

theorem Ag_selOff (h : OffOK D l' i t w) (l x p : ℕ) :
    Ag D (selOff l' i t) w l x p = Ag D t w l x p := by
  unfold Ag
  split
  · next hr =>
    have hl : isExpL l = true := by
      unfold routed at hr
      exact (Bool.and_eq_true _ _ ▸ hr).1
    exact sel_sum D l p hl _ _
      (fun e => sum_congr rfl fun j _ => by
        rw [val_selOff_ne l' i t (fun h => Arr.noConfusion h)])
      fun e0 e => sum_eq_zero fun j _ => by rw [e0, h.Eg, mul_zero]
  · exact sum_congr rfl fun j _ => by rw [val_selOff_ne l' i t (fun h => Arr.noConfusion h)]

theorem Au_selOff (h : OffOK D l' i t w) (l x p : ℕ) :
    Au D (selOff l' i t) w l x p = Au D t w l x p := by
  unfold Au
  split
  · next hr =>
    have hl : isExpL l = true := by
      unfold routed at hr
      exact (Bool.and_eq_true _ _ ▸ hr).1
    exact sel_sum D l p hl _ _
      (fun e => sum_congr rfl fun j _ => by
        rw [val_selOff_ne l' i t (fun h => Arr.noConfusion h)])
      fun e0 e => sum_eq_zero fun j _ => by rw [e0, h.Eu, mul_zero]
  · exact sum_congr rfl fun j _ => by rw [val_selOff_ne l' i t (fun h => Arr.noConfusion h)]

theorem Ad_selOff (h : OffOK D l' i t w) (l x p : ℕ) :
    Ad D (selOff l' i t) w l x p = Ad D t w l x p := by
  unfold Ad
  split
  · next hl =>
    refine congrArg₂ (· + ·) (sum_congr rfl fun j _ => by rw [hh_selOff]) ?_
    exact sel_sum D l p hl _ _ (fun e => sum_congr rfl fun j _ => by rw [hh_selOff])
      fun e0 e => sum_eq_zero fun j _ => by rw [e0, h.Ed, mul_zero]
  · exact sum_congr rfl fun j _ => by rw [hh_selOff]

/-- The selector's entries behind x: 0 on both sides at (l', i). -/
theorem tail_selOff (h : OffOK D l' i t w) (n x p : ℕ) :
    ∑ e ∈ (range D.nx).filter (x < ·), val (selOff l' i t) .sel n e p =
      ∑ e ∈ (range D.nx).filter (x < ·), val t .sel n e p :=
  sum_congr rfl fun e he => by
    by_cases c : n = l' ∧ p = i
    · obtain ⟨rfl, rfl⟩ := c
      rw [val_selOff_at, h.sel e (Nat.lt_of_le_of_lt (Nat.zero_le x) (mem_filter.1 he).2)
        (mem_range.1 (mem_filter.1 he).1)]
    · exact val_selOff_off l' i t c e

theorem Y'_selOff (tb : Tables) (L0 l x p : ℕ) :
    Y' D (selOff l' i t) tb L0 w l x p = Y' D t tb L0 w l x p := by
  have a : ∀ y, AY D (selOff l' i t) w l y p = AY D t w l y p := fun y => by
    unfold AY Aq Ak
    simp (disch := decide) only [val_selOff_ne]
  unfold Y'
  simp only [a]

end Free

/-! ## Which keys and identities read the selector's cells -/

section Keys
variable [scl : Scl] {R : Type} [CommRing R] (D : Dim) {l' i : ℕ} {t : Cell → R} {w : ℕ → LW R}

/-- Under the three premises every family but SEL has the same key. The families that read the
selector's cells at all are G, U, D (through the routed experts), DD, MR and SEL. -/
theorem key_selOff (tb : Tables) (L0 : ℕ) (h : OffOK D l' i t w) (s : Fam) (hs : s ≠ .SEL)
    (l x p : ℕ) : key D (selOff l' i t) tb L0 w s l x p = key D t tb L0 w s l x p := by
  cases s <;>
    first
    | exact absurd rfl hs
    | simp (disch := decide) only [key, gw, lw, Av, Ag_selOff D h, Au_selOff D h, Ad_selOff D h,
        mr_selOff D h, tail_selOff D h, Y'_selOff, xS_selOff, led_selOff, val_selOff_ne]

/-- With no premise at all: the 28 families other than G, U, D, DD, MR and SEL do not read the
selector's cells. -/
theorem key_reads (tb : Tables) (L0 : ℕ) (s : Fam)
    (hs : s ≠ .G ∧ s ≠ .U ∧ s ≠ .D ∧ s ≠ .DD ∧ s ≠ .MR ∧ s ≠ .SEL) (l x p : ℕ) :
    key D (selOff l' i t) tb L0 w s l x p = key D t tb L0 w s l x p := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
  cases s <;>
    first
    | exact absurd rfl h1
    | exact absurd rfl h2
    | exact absurd rfl h3
    | exact absurd rfl h4
    | exact absurd rfl h5
    | exact absurd rfl h6
    | simp (disch := decide) only [key, lw, Av, Y'_selOff, xS_selOff, led_selOff, val_selOff_ne]

omit scl in
/-- 0 is an entry of the table of the family SEL. -/
theorem zero_mem_SEL (tb : Tables) : (0 : R) ∈ lutSet (lut tb (call .SEL)) :=
  ⟨0, by show 0 < 2 ^ 8; norm_num, by show (0 : R) = (((0 : ℕ) : ℤ) : R); simp⟩

/-- The key of the family SEL. -/
theorem key_SEL (u : Cell → R) (tb : Tables) (L0 l x p : ℕ) :
    key D u tb L0 w .SEL l x p = 128 * val u .sel (l / 2) x p := rfl

/-- No identity but j10 at (l', i) reads the selector's cells of (l', i). -/
theorem idn_selOff (emb : ℕ → ℕ → R) (tok : ℕ → ℕ) (j : Idn) (hj : j ≠ .j10 l' i) :
    idnVal D (selOff l' i t) emb tok j = idnVal D t emb tok j := by
  cases j with
  | jn k ν p =>
    show Ledger.idn _ (Ledger.Wsum D.d fun l j => bS D (selOff l' i t) ν l j p) _ k = _
    simp only [bS_selOff, led_selOff]
    rfl
  | j10 n p =>
    have c : ¬ (n = l' ∧ p = i) := fun c => hj (by rw [c.1, c.2])
    show ∑ e ∈ range D.nx, val (selOff l' i t) .sel n e p - 1 = _
    rw [sum_congr rfl fun e _ => val_selOff_off l' i t c e]
    rfl
  | j11 a p =>
    show xS D (selOff l' i t) 0 a p - _ = _
    rw [xS_selOff]
    rfl

/-- The defect of j10 at (l', i), where the selector's cells are set to 0. -/
theorem j10_selOff (emb : ℕ → ℕ → R) (tok : ℕ → ℕ) :
    idnVal D (selOff l' i t) emb tok (.j10 l' i) = -1 := by
  show ∑ e ∈ range D.nx, val (selOff l' i t) .sel l' e i - 1 = -1
  rw [sum_eq_zero fun e _ => val_selOff_at l' i t e, zero_sub]

end Keys

/-! ## The relation without j10 does not give j10 -/

section Rel
variable [scl : Scl] (D : Dim) (l' i : ℕ)

/-- A trace on the valid names, with the selector's cells of instance l' at position i set to 0. -/
def offT (t : {c : Cell // c.Valid D} → ℤ) : {c : Cell // c.Valid D} → ℤ := fun c =>
  if c.1.X = .sel ∧ c.1.inst = l' ∧ c.1.i = i then 0 else t c

omit scl in
theorem rd_offT {R : Type} [CommRing R] (t : {c : Cell // c.Valid D} → ℤ) :
    (rd D (offT D l' i t) : Cell → R) = selOff l' i (rd D t) := funext fun c => by
  unfold rd offT selOff
  by_cases hv : c.Valid D <;> by_cases hc : c.X = .sel ∧ c.inst = l' ∧ c.i = i <;> simp [hv, hc]

/-- From any trace t in the field relation of a feed-forward segment that meets the three premises
at (l', i): the trace with the selector's cells of (l', i) set to 0 has small cells, every key in
its table, and every identity but j10 at (l', i); the defect of j10 at (l', i) is -1. So in this
relation the clauses other than j10 do not give j10, wherever such a t exists, (l', i) is valid and
0 ≠ 1 in F. It asks no validity of (l', i): where l' ≥ D.ne or i ≥ D.T the identity is no clause of
the relation and nothing fails. -/
theorem hot_free (tb : Tables) (kW L0 : ℕ) (first : Bool) {F : Type} [CommRing F] (tok : ℕ → ℕ)
    (W : ℕ → ℕ → F) (t : {c : Cell // c.Valid D} → ℤ)
    (h : (trace D tb kW L0 first F).RF tok W t)
    (ho : OffOK D l' i (rd D t : Cell → F) fun l => layerR D.P kW W (L0 + l)) :
    (∀ c, |offT D l' i t c| < 2 ^ (trace D tb kW L0 first F).β) ∧
      (∀ k, (trace D tb kW L0 first F).key tok W (offT D l' i t) k ∈
        (trace D tb kW L0 first F).table k) ∧
      (∀ j : (trace D tb kW L0 first F).Idn, j.val ≠ .j10 l' i →
        (trace D tb kW L0 first F).idn tok W (offT D l' i t) j = 0) ∧
      idnVal D (rd D (offT D l' i t) : Cell → F) (embR D.P kW W) tok (.j10 l' i) = -1 := by
  refine ⟨fun c => ?_, fun k => ?_, fun j hj => ?_, ?_⟩
  · unfold offT
    split
    · simp
    · exact h.1 c
  · have hk := h.2.1 k
    show key D (rd D (offT D l' i t)) tb L0 _ k.val.1 k.val.2.1 k.val.2.2.1 k.val.2.2.2 ∈
      lutSet (lut tb (call k.val.1))
    rw [rd_offT]
    by_cases hs : k.val.1 = .SEL
    · have hk' : key D (rd D t) tb L0 (fun l => layerR D.P kW W (L0 + l)) k.val.1 k.val.2.1
          k.val.2.2.1 k.val.2.2.2 ∈ lutSet (lut tb (call k.val.1)) := hk
      rw [hs] at hk' ⊢
      rw [key_SEL] at hk' ⊢
      by_cases c : k.val.2.1 / 2 = l' ∧ k.val.2.2.2 = i
      · rw [c.1, c.2, val_selOff_at, mul_zero]
        exact zero_mem_SEL tb
      · rw [val_selOff_off l' i _ c]
        exact hk'
    · rw [key_selOff D tb L0 ho _ hs]
      exact hk
  · have hi := h.2.2 j
    show idnVal D (rd D (offT D l' i t)) _ tok j.val = 0
    rw [rd_offT, idn_selOff D _ tok j.val hj]
    exact hi
  · rw [rd_offT]
    exact j10_selOff D _ tok

end Rel

end Cb.Rider

#print axioms Cb.Rider.key_selOff
#print axioms Cb.Rider.key_reads
#print axioms Cb.Rider.idn_selOff
#print axioms Cb.Rider.hot_free
