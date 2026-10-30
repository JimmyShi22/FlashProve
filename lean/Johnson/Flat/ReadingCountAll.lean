-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ReadingCountAll.lean: the errors of the family of bad verifier messages
`badAll` (Johnson/Flat/ReadingBad.lean), from the degrees to a share of the written messages.

The setting. A stretch of written rounds ds stands behind rounds `pre`. At each round the set into
which a drawn element must not be read is named by A: by the earlier rounds as a view shows them,
by the round's own message, and by the elements drawn before in the round. A round's place is the
number of rounds before it. deg i j bounds the number of typed elements that are read into the set
of element number j of the round at place i.

Main names:
  `CountsAt rd A i ds ε`: as `CountsAll`, but the bound of a round is asked only at lists `pre`
    whose length is the round's place; i is the place of the first round of ds. So a degree that
    depends on the round is paid at its own round alone.
  `badAll_within_at`: under `CountsAt` at the place pre.length the family is within the errors.
  `countsAt_of_all`: `CountsAll` gives `CountsAt` at every place.
  `allErr deg i ds`: at each round `hitBound` (Johnson/Flat/ReadingCount.lean) at the round's
    degrees, times w, the bound on the written messages that give one typed value.
  `countsAt_allErr`: if at most deg pre.length xs.length typed elements are read into A pre vals xs,
    then `CountsAt` holds at `allErr`. `badAll_within_allErr`: so the family is within `allErr`.
  `hitBound_share_enn`: `hitBound_share` as a share.
  `AllHeldEx deg εs i ds`: at each round (the bias of the sampler, by what the round draws) times
    (the sum of the round's degrees / (|E| - 1)) / 2 ^ (the round's bits of work) is at most εs.
  `allErr_below_ex`: then every error of `allErr` is a share of at most εs of the written messages.

Three cases, each as a theorem:
  All degrees 0: `allErr_zero` (every error is a share of at most 0), `allHeldEx_zero`.
  One round that draws one element: `allHeldEx_one`: the condition is
    bias ^ 3 * ((deg i 0 / (|E| - 1)) / 2 ^ work) ≤ εs. `allHeldEx_one_work0`: without work;
    `allHeldEx_one_work1`: with one bit of work, half of it. `toyD w` is such a round with w bits of
    work (`dsOf_toyD`); `toyD_below`: its error is within that share.

Limits. The premise of `countsAt_allErr` is asked at all lists pre, vals and xs, also at such as no
run shows. With two or more elements in a round `hitBound` is a union bound, not the exact count.
Where the sum of the degrees reaches |E| - 1 the share says nothing. Positions have at most 64 bits.
Nothing is said on which sets A a protocol needs, or on their degrees.

-/
import Johnson.Flat.ReadingCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace OnBytes.Flat
open Iop Prob Run OnBytes.Maker OnBytes.Slice

variable {K : Type} (rd : Fmt.Ext → K)
variable (A : List Fmt.RoundView → List Fmt.ItemValue → List Fmt.Ext → Set K)

/-! ### the bound of a round, asked at the round's place alone -/

/-- The counts bear, at each round and whatever stands before it at its place: (the typed values
that hit) times w. The first round of ds has the place i. -/
def CountsAt : ℕ → (ds : List RDT) → Err (uLT (ckP .two) ds) → Prop
  | _, [], _ => True
  | i, d :: ds, (e, ε) =>
    (∀ pre vals, pre.length = i → cnt (fun v : Vals .two (Fmt.dsOf d.entry d.kind) =>
        hitL rd (A pre vals) (drawnOf .two d.entry d.kind v).elems) *
      (bsRound .two d.entry d.kind).w ≤ e) ∧ CountsAt (i + 1) ds ε

/-- `CountsAll` asks more. -/
theorem countsAt_of_all : ∀ (ds : List RDT) (ε : Err (uLT (ckP .two) ds)) (i : ℕ),
    CountsAll rd A ds ε → CountsAt rd A i ds ε
  | [], _, _, _ => trivial
  | _ :: ds, (_, ε), i, h =>
    ⟨fun pre vals _ => h.1 pre vals, countsAt_of_all ds ε (i + 1) h.2⟩

/-- The family is within the errors. The proof is that of `badAll_within`. -/
theorem badAll_within_at : ∀ (ds : List RDT) (pre : List Fmt.RoundView) (ε : Err (uLT (ckP .two) ds)),
    (∀ d ∈ ds, d.entry.logN ≤ 64) → CountsAt rd A pre.length ds ε →
    (badAll rd A ds pre).Within ε
  | [], _, _, _, _ => trivial
  | d :: ds, pre, (e, ε), h, hc =>
    ⟨fun m => by
        refine le_trans ?_
          (hc.1 pre (PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2)) rfl)
        show cnt (fun c : GChal d.entry.work (Fin (bsRound .two d.entry d.kind).b → Dig 256) =>
          GChal.pass c = true ∧
            hitL rd (A pre (PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2)))
              (drawnOf .two d.entry d.kind
                ((bsRound .two d.entry d.kind).φ (GChal.old c))).elems) ≤ _
        rw [GChal.cnt_pass d.entry.work (fun u =>
          hitL rd (A pre (PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2)))
            (drawnOf .two d.entry d.kind ((bsRound .two d.entry d.kind).φ u)).elems)]
        exact cnt_comp_le (bsRound .two d.entry d.kind).φ
          (planDraws_law .two d.entry d.kind (h d (List.mem_cons_self ..))).1.fib
          (fun v => hitL rd (A pre (PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2)))
            (drawnOf .two d.entry d.kind v).elems),
      fun m c => badAll_within_at ds (pre ++ [shownR d m c]) ε
        (fun d' hd' => h d' (List.mem_cons_of_mem _ hd')) (by
          rw [List.length_append, List.length_singleton]
          exact hc.2)⟩

/-! ### the errors from the degrees -/

/-- The errors: at the round at place i the bound on the typed values that hit, at the degrees
deg i, times w. The first round of ds has the place i. -/
noncomputable def allErr (deg : ℕ → ℕ → ℕ) : ℕ → (ds : List RDT) → Err (uLT (ckP .two) ds)
  | _, [] => ()
  | i, d :: ds =>
    (hitBound (deg i) (Fmt.dsOf d.entry d.kind) 0 * (bsRound .two d.entry d.kind).w,
      allErr deg (i + 1) ds)

/-- Sets of at most deg (the round's place) (the element's number) typed elements: the counts
bear at `allErr`. -/
theorem countsAt_allErr (deg : ℕ → ℕ → ℕ)
    (H : ∀ pre vals xs,
      cnt (fun a : EV .two => rd (toU3 a) ∈ A pre vals xs) ≤ deg pre.length xs.length) :
    ∀ (i : ℕ) (ds : List RDT), CountsAt rd A i ds (allErr deg i ds)
  | _, [] => trivial
  | i, d :: ds =>
    ⟨fun pre vals hp => Nat.mul_le_mul_right _
        (cnt_hit_le rd (deg i) (Fmt.dsOf d.entry d.kind) 0 (A pre vals) fun xs => by
          rw [Nat.zero_add, ← hp]
          exact H pre vals xs),
      countsAt_allErr deg H (i + 1) ds⟩

/-- So the family is within `allErr`. -/
theorem badAll_within_allErr (deg : ℕ → ℕ → ℕ)
    (H : ∀ pre vals xs,
      cnt (fun a : EV .two => rd (toU3 a) ∈ A pre vals xs) ≤ deg pre.length xs.length)
    (ds : List RDT) (pre : List Fmt.RoundView) (h : ∀ d ∈ ds, d.entry.logN ≤ 64) :
    (badAll rd A ds pre).Within (allErr deg pre.length ds) :=
  badAll_within_at rd A ds pre _ h (countsAt_allErr rd A deg H pre.length ds)

/-! ### the errors as shares, with the bias and the work -/

/-- `hitBound_share` as a share of the typed values. -/
theorem hitBound_share_enn (deg : ℕ → ℕ) (ds : List Fmt.Draw) (j : ℕ) :
    ((hitBound deg ds j : ℕ) : ℝ≥0∞) ≤
      ((sumDeg deg ds j : ℕ) : ℝ≥0∞) / ((Fintype.card (NZ .two) : ℕ) : ℝ≥0∞) *
        ((Nat.card (Vals .two ds) : ℕ) : ℝ≥0∞) := by
  rw [Nat.card_eq_fintype_card]
  exact share_le _ _ _ _ card_nz_pos (hitBound_share deg ds j)

/-- At each round the sum of the round's degrees over |E| - 1, with the sampler's bias by what the
round draws and the gain from the bits of work, is at most εs. The first round has the place i. -/
def AllHeldEx (deg : ℕ → ℕ → ℕ) (εs : ℝ≥0∞) : ℕ → List RDT → Prop
  | _, [] => True
  | i, d :: ds =>
    kapSl 128 ^ exAll (Fmt.dsOf d.entry d.kind) *
      (((sumDeg (deg i) (Fmt.dsOf d.entry d.kind) 0 : ℕ) : ℝ≥0∞) /
        ((Fintype.card (NZ .two) : ℕ) : ℝ≥0∞) / 2 ^ d.entry.work) ≤ εs ∧
    AllHeldEx deg εs (i + 1) ds

/-- Then every error of `allErr` is a share of at most εs of the round's written messages. -/
theorem allErr_below_ex (deg : ℕ → ℕ → ℕ) {εs : ℝ≥0∞} : ∀ (i : ℕ) (ds : List RDT),
    (∀ d ∈ ds, d.entry.logN ≤ 64) → AllHeldEx deg εs i ds → Err.Below (allErr deg i ds) εs
  | _, [], _, _ => trivial
  | i, d :: ds, h, hh =>
    ⟨(below_round_div_ex (toRD d) (h d (List.mem_cons_self ..)) _ _
        (hitBound_share_enn (deg i) (Fmt.dsOf d.entry d.kind) 0)).trans
        (mul_le_mul' hh.1 le_rfl),
      allErr_below_ex deg (i + 1) ds (fun d' hd' => h d' (List.mem_cons_of_mem _ hd')) hh.2⟩

/-! ### first case: all degrees 0 -/

/-- Every error is 0: a share of at most 0. -/
theorem allErr_zero : ∀ (i : ℕ) (ds : List RDT), Err.Below (allErr (fun _ _ => 0) i ds) 0
  | _, [] => trivial
  | i, d :: ds =>
    ⟨by
        show ((hitBound (fun _ => 0) (Fmt.dsOf d.entry d.kind) 0 *
          (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) ≤ _
        rw [hitBound_zero, Nat.zero_mul, Nat.cast_zero]
        exact zero_le _,
      allErr_zero (i + 1) ds⟩

/-- The condition holds at the share 0. -/
theorem allHeldEx_zero : ∀ (i : ℕ) (ds : List RDT), AllHeldEx (fun _ _ => 0) 0 i ds
  | _, [] => trivial
  | i, d :: ds =>
    ⟨by
        show kapSl 128 ^ exAll (Fmt.dsOf d.entry d.kind) *
          (((sumDeg (fun _ => 0) (Fmt.dsOf d.entry d.kind) 0 : ℕ) : ℝ≥0∞) /
            ((Fintype.card (NZ .two) : ℕ) : ℝ≥0∞) / 2 ^ d.entry.work) ≤ 0
        rw [sumDeg_zero, Nat.cast_zero, ENNReal.zero_div, ENNReal.zero_div, mul_zero],
      allHeldEx_zero (i + 1) ds⟩

/-! ### second and third case: one round that draws one element -/

/-- One round that draws one element and t matrix entries. -/
theorem allHeldEx_one (deg : ℕ → ℕ → ℕ) (εs : ℝ≥0∞) (i : ℕ) (d : RDT) (t : ℕ)
    (hds : Fmt.dsOf d.entry d.kind = [.elem, .trits t]) :
    AllHeldEx deg εs i [d] ↔
      kapSl 128 ^ 3 * (((deg i 0 : ℕ) : ℝ≥0∞) / ((Fintype.card (NZ .two) : ℕ) : ℝ≥0∞) /
        2 ^ d.entry.work) ≤ εs := by
  have e1 : exAll [Fmt.Draw.elem, Fmt.Draw.trits t] = 3 := rfl
  have e2 : sumDeg (deg i) [Fmt.Draw.elem, Fmt.Draw.trits t] 0 = deg i 0 := rfl
  show (kapSl 128 ^ exAll (Fmt.dsOf d.entry d.kind) *
      (((sumDeg (deg i) (Fmt.dsOf d.entry d.kind) 0 : ℕ) : ℝ≥0∞) /
        ((Fintype.card (NZ .two) : ℕ) : ℝ≥0∞) / 2 ^ d.entry.work) ≤ εs ∧ True) ↔ _
  rw [and_true, hds, e1, e2]

/-- Without work: the bias times deg / (|E| - 1). -/
theorem allHeldEx_one_work0 (deg : ℕ → ℕ → ℕ) (εs : ℝ≥0∞) (i : ℕ) (d : RDT) (t : ℕ)
    (hds : Fmt.dsOf d.entry d.kind = [.elem, .trits t]) (hw : d.entry.work = 0) :
    AllHeldEx deg εs i [d] ↔
      kapSl 128 ^ 3 * (((deg i 0 : ℕ) : ℝ≥0∞) / ((Fintype.card (NZ .two) : ℕ) : ℝ≥0∞)) ≤ εs := by
  rw [allHeldEx_one deg εs i d t hds, hw, pow_zero, div_one]

/-- With one bit of work: half of it. -/
theorem allHeldEx_one_work1 (deg : ℕ → ℕ → ℕ) (εs : ℝ≥0∞) (i : ℕ) (d : RDT) (t : ℕ)
    (hds : Fmt.dsOf d.entry d.kind = [.elem, .trits t]) (hw : d.entry.work = 1) :
    AllHeldEx deg εs i [d] ↔
      kapSl 128 ^ 3 * (((deg i 0 : ℕ) : ℝ≥0∞) / ((Fintype.card (NZ .two) : ℕ) : ℝ≥0∞)) / 2 ≤
        εs := by
  rw [allHeldEx_one deg εs i d t hds, hw, pow_one, mul_div_assoc]

/-- A round that draws one element and nothing else, with w bits of work. -/
def toyD (w : ℕ) : RDT := ⟨⟨{ name := "", drawE := 1, work := w }, .elems, [], [], []⟩, []⟩

theorem dsOf_toyD (w : ℕ) : Fmt.dsOf (toyD w).entry (toyD w).kind = [.elem, .trits 0] := rfl

/-- The error of that round is within its share. -/
theorem toyD_below (deg : ℕ → ℕ → ℕ) (i w : ℕ) :
    Err.Below (allErr deg i [toyD w])
      (kapSl 128 ^ 3 * (((deg i 0 : ℕ) : ℝ≥0∞) / ((Fintype.card (NZ .two) : ℕ) : ℝ≥0∞) / 2 ^ w)) :=
  allErr_below_ex deg i [toyD w]
    (fun d hd => by
      rw [List.mem_singleton.1 hd]
      exact Nat.zero_le 64)
    ((allHeldEx_one deg _ i (toyD w) 0 (dsOf_toyD w)).2 le_rfl)

end OnBytes.Flat

#print axioms OnBytes.Flat.countsAt_of_all
#print axioms OnBytes.Flat.badAll_within_at
#print axioms OnBytes.Flat.countsAt_allErr
#print axioms OnBytes.Flat.badAll_within_allErr
#print axioms OnBytes.Flat.hitBound_share_enn
#print axioms OnBytes.Flat.allErr_below_ex
#print axioms OnBytes.Flat.allErr_zero
#print axioms OnBytes.Flat.allHeldEx_zero
#print axioms OnBytes.Flat.allHeldEx_one
#print axioms OnBytes.Flat.allHeldEx_one_work0
#print axioms OnBytes.Flat.allHeldEx_one_work1
#print axioms OnBytes.Flat.dsOf_toyD
#print axioms OnBytes.Flat.toyD_below
