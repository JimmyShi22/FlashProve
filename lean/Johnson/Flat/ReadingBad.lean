-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ReadingBad.lean: from a set of field elements to bad written verifier messages, with
the sampler's bias and the proof of work counted. For proofs in which a chain's blocks are composed
over their own written rounds by families of bad sets (`Iop.BadFam`, Iop/Rbr.lean).

Letters: rd, how an element that a view shows as drawn is read into a type K; B, a set of values of
K.
  `hitV rd B e k v`: at the typed values v of a round, some drawn element is read into B.
  `badElems rd B ds`: the family of bad written messages of a stretch ds: at each round those c
  whose test of the work passes and whose typed values hit B.
  `badErr rd B ds`: at each round (the number of typed values that hit B) times w, the sampler's
  bound.
  `badElems_within`: the family is within these counts, where positions have at most 64 bits.
  `badElems_clean`: on a clean transcript whose tests of the work pass, no element that the
  stretch's rounds show as drawn is read into B.
  `BadHeld εs`, `badErr_below`: if at each round the typed values that hit B are a share of at most
  c (the price with the work not counted) and (1 + 2^-128)^b · (c / 2^work) ≤ εs, b the round's
  number of hash blocks, the counts are shares of at most εs of the written messages.
  `BadHeldEx εs`, `badErr_below_ex`: the same with the bias by what the round draws (`Run.exAll`,
  OnBytes/Slice/RatesEx.lean).
  `hitL`, `shownR`, `badAll`, `CountsAll`, `badAll_within`, `badAll_clean`: the same where the set
  may hang on the earlier rounds as a view shows them, on the round's own message and on the
  elements drawn before in the round; a round may draw several elements.

Why the pass is a premise of the two clean lemmas. A family that had to keep the element out of its
set on every clean transcript would have to hold the messages that fail the test of the work too:
2^work times as many, and the work would cancel.

Limits. How many typed values hit is not counted here. No protocol occurs. One-sided: a bound on
"passes and is read into the set".
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Flat.CarrySMaps
import OnBytes.Slice.RatesEx
import Iop.Rbr

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace OnBytes.Flat
open Iop Prob Run OnBytes.Maker OnBytes.Slice

variable {K : Type} (rd : Fmt.Ext → K) (B : Set K)

/-- At these typed values some drawn element is read into B. -/
def hitV (e : Fmt.Entry) (k : Fmt.Kind) (v : Vals .two (Fmt.dsOf e k)) : Prop :=
  ∃ x ∈ (drawnOf .two e k v).elems, rd x ∈ B

/-- The bad written verifier's messages of a stretch. -/
def badElems : (ds : List RDT) → BadFam (uLT (ckP .two) ds)
  | [] => ()
  | d :: ds =>
    (fun _ => {c | GChal.pass (b := d.entry.work) c = true ∧
        hitV rd B d.entry d.kind (valsOf (toRD d) c)},
      fun _ _ => badElems ds)

/-- Their counts. -/
noncomputable def badErr : (ds : List RDT) → Err (uLT (ckP .two) ds)
  | [] => ()
  | d :: ds => (cnt (hitV rd B d.entry d.kind) * (bsRound .two d.entry d.kind).w, badErr ds)

theorem badElems_within : ∀ (ds : List RDT), (∀ d ∈ ds, d.entry.logN ≤ 64) →
    (badElems rd B ds).Within (badErr rd B ds)
  | [], _ => trivial
  | d :: ds, h =>
    ⟨fun _ => by
        show cnt (fun c : GChal d.entry.work (Fin (bsRound .two d.entry d.kind).b → Dig 256) =>
          GChal.pass c = true ∧
            hitV rd B d.entry d.kind ((bsRound .two d.entry d.kind).φ (GChal.old c))) ≤ _
        rw [GChal.cnt_pass d.entry.work
          (fun u => hitV rd B d.entry d.kind ((bsRound .two d.entry d.kind).φ u))]
        exact cnt_comp_le _
          (planDraws_law .two d.entry d.kind (h d (List.mem_cons_self ..))).1.fib _,
      fun _ _ => badElems_within ds fun d' hd' => h d' (List.mem_cons_of_mem _ hd')⟩

theorem badElems_clean : ∀ (ds : List RDT) (τ : Tr (uLT (ckP .two) ds)),
    (badElems rd B ds).Clean τ → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true →
    ∀ x ∈ (rvT (ckP .two) ds τ).flatMap (·.drawn.elems), rd x ∉ B
  | [], _, _, _ => fun _ hx => nomatch hx
  | d :: ds, (m, c, τ), hc, hp => fun x hx hB => by
      have hp' : (GChal.pass (b := d.entry.work) c &&
        passT (ckP .two) ds (rhoT (ckP .two) ds τ)) = true := hp
      obtain ⟨p1, p2⟩ := Bool.and_eq_true_iff.1 hp'
      obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.1 hx
      have hr' : r ∈ (⟨PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
          drawnOf .two d.entry d.kind (valsOf (toRD d) c)⟩ : PQ.RV) :: rvT (ckP .two) ds τ := hr
      rcases List.mem_cons.1 hr' with rfl | hr2
      · exact hc.1 ⟨p1, x, hxr, hB⟩
      · exact badElems_clean ds τ hc.2 p2 x (List.mem_flatMap.2 ⟨r, hr2, hxr⟩) hB

/-- At each round the typed values that hit B are a share of at most c, and c, with the sampler's
bias and
the gain from the bits of work, is at most εs. -/
def BadHeld (εs : ℝ≥0∞) : List RDT → Prop
  | [] => True
  | d :: ds =>
    (∃ c : ℝ≥0∞, (cnt (hitV rd B d.entry d.kind) : ℝ≥0∞) ≤
        c * (Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) : ℝ≥0∞) ∧
      kapSl 128 ^ (bsRound .two d.entry d.kind).b * (c / 2 ^ d.entry.work) ≤ εs) ∧
    BadHeld εs ds

theorem badErr_below {εs : ℝ≥0∞} : ∀ (ds : List RDT), (∀ d ∈ ds, d.entry.logN ≤ 64) →
    BadHeld rd B εs ds → Err.Below (badErr rd B ds) εs
  | [], _, _ => trivial
  | d :: ds, h, hh => by
      obtain ⟨⟨c, h1, h2⟩, h3⟩ := hh
      exact ⟨(below_round_div (toRD d) (h d (List.mem_cons_self ..)) _ c h1).trans
          (mul_le_mul' h2 le_rfl),
        badErr_below ds (fun d' hd' => h d' (List.mem_cons_of_mem _ hd')) h3⟩

/-- `BadHeld` with the sampler's bias by what the round draws (`Run.exAll`: three factors an element
of the
extension field; none for a position, a matrix entry or a sealing). -/
def BadHeldEx (εs : ℝ≥0∞) : List RDT → Prop
  | [] => True
  | d :: ds =>
    (∃ c : ℝ≥0∞, (cnt (hitV rd B d.entry d.kind) : ℝ≥0∞) ≤
        c * (Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) : ℝ≥0∞) ∧
      kapSl 128 ^ exAll (Fmt.dsOf d.entry d.kind) * (c / 2 ^ d.entry.work) ≤ εs) ∧
    BadHeldEx εs ds

theorem badErr_below_ex {εs : ℝ≥0∞} : ∀ (ds : List RDT), (∀ d ∈ ds, d.entry.logN ≤ 64) →
    BadHeldEx rd B εs ds → Err.Below (badErr rd B ds) εs
  | [], _, _ => trivial
  | d :: ds, h, hh => by
      obtain ⟨⟨c, h1, h2⟩, h3⟩ := hh
      exact ⟨(below_round_div_ex (toRD d) (h d (List.mem_cons_self ..)) _ c h1).trans
          (mul_le_mul' h2 le_rfl),
        badErr_below_ex ds (fun d' hd' => h d' (List.mem_cons_of_mem _ hd')) h3⟩

/-! ### the set may hang on what stands before the element -/

section All
variable (A : List Fmt.RoundView → List Fmt.ItemValue → List Fmt.Ext → Set K)

/-- Some element of the list is read into the set that the elements before it name. -/
def hitL (Bf : List Fmt.Ext → Set K) (l : List Fmt.Ext) : Prop :=
  ∃ xs x ys, l = xs ++ x :: ys ∧ rd x ∈ Bf xs

/-- What a view shows of a written round. -/
def shownR (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal) : Fmt.RoundView :=
  ⟨PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
    drawnOf .two d.entry d.kind (valsOf (toRD d) c)⟩

/-- The bad written verifier's messages of a stretch, behind the rounds `pre` as a view shows them:
at each
round those whose test of the work passes and of whose drawn elements one is read into the set that
the
earlier rounds, the round's own message and the elements before it name. -/
def badAll : (ds : List RDT) → List Fmt.RoundView → BadFam (uLT (ckP .two) ds)
  | [], _ => ()
  | d :: ds, pre =>
    (fun m => {c | GChal.pass (b := d.entry.work) c = true ∧
        hitL rd (A pre (shownR d m c).vals) (shownR d m c).drawn.elems},
      fun m c => badAll ds (pre ++ [shownR d m c]))

/-- The counts bear, at each round and whatever stands before: (the typed values that hit) · w. -/
def CountsAll : (ds : List RDT) → Err (uLT (ckP .two) ds) → Prop
  | [], _ => True
  | d :: ds, (e, ε) =>
    (∀ pre vals, cnt (fun v : Vals .two (Fmt.dsOf d.entry d.kind) =>
        hitL rd (A pre vals) (drawnOf .two d.entry d.kind v).elems) *
      (bsRound .two d.entry d.kind).w ≤ e) ∧ CountsAll ds ε

theorem badAll_within : ∀ (ds : List RDT) (pre : List Fmt.RoundView) (ε : Err (uLT (ckP .two) ds)),
    (∀ d ∈ ds, d.entry.logN ≤ 64) → CountsAll rd A ds ε → (badAll rd A ds pre).Within ε
  | [], _, _, _, _ => trivial
  | d :: ds, pre, (e, ε), h, hc =>
    ⟨fun m => by
        refine le_trans ?_ (hc.1 pre (PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2)))
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
      fun _ _ => badAll_within ds _ ε (fun d' hd' => h d' (List.mem_cons_of_mem _ hd')) hc.2⟩

theorem badAll_clean : ∀ (ds : List RDT) (pre₀ : List Fmt.RoundView) (τ : Tr (uLT (ckP .two) ds)),
    (badAll rd A ds pre₀).Clean τ → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true →
    ∀ pre r post, rvT (ckP .two) ds τ = pre ++ r :: post →
      ∀ xs x ys, r.drawn.elems = xs ++ x :: ys → rd x ∉ A (pre₀ ++ pre) r.vals xs
  | [], _, _, _, _ => fun pre _ _ h => by cases pre <;> cases h
  | d :: ds, pre₀, (m, c, τ), hc, hp => fun pre r post h xs x ys hx hB => by
      have hp' : (GChal.pass (b := d.entry.work) c &&
        passT (ckP .two) ds (rhoT (ckP .two) ds τ)) = true := hp
      obtain ⟨p1, p2⟩ := Bool.and_eq_true_iff.1 hp'
      have h' : shownR d m c :: rvT (ckP .two) ds τ = pre ++ r :: post := h
      cases pre with
      | nil =>
        obtain ⟨rfl, _⟩ := List.cons.inj h'
        rw [List.append_nil] at hB
        exact hc.1 ⟨p1, xs, x, ys, hx, hB⟩
      | cons a pre' =>
        obtain ⟨rfl, h2⟩ := List.cons.inj h'
        refine badAll_clean ds _ τ hc.2 p2 pre' r post h2 xs x ys hx ?_
        rw [List.append_assoc]
        exact hB

end All

end OnBytes.Flat

#print axioms OnBytes.Flat.badElems_within
#print axioms OnBytes.Flat.badElems_clean
#print axioms OnBytes.Flat.badErr_below
#print axioms OnBytes.Flat.badErr_below_ex
#print axioms OnBytes.Flat.badAll_within
#print axioms OnBytes.Flat.badAll_clean
