-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/KitCount.lean: THE COUNT AT THE KIT: "ELEMENT NUMBER i OF WHAT A ROUND SHOWS MEETS
Q'", AT A ROUND THAT DRAWS WHATEVER LIST OF DRAWS, AT TYPED CHALLENGES AND AT STRINGS OF HASH
BLOCKS. Definitions and lemmas; none of the library's goals. Nothing on completeness, soundness or
hiding. No test, no block, no state.

ds: a round's list of draws. i: a number among its elements, in their order. Q': a predicate on
field elements that at most c of them meet. p: the format's second prime.
  `IsEl ds i`   element number i among the draws is drawn by the rule that is uniform over the field
      (`.elem`), not by the rule that never gives 0
  **`typed_count`**   the typed challenges whose element number i meets Q', times p ^ 3, are at most
      c times all typed challenges
  `AtEl i Q' R`   element number i of the drawn value R, read in the field, meets Q'; `atEl_word`:
      so where that element is the word of an x that meets Q'
  `Reduced R`, `collect_ok`   all elements of R are triples of words below the prime; what a typed
      challenge shows is so
  Q: an event on a drawn value that gives `AtEl i Q'` AT REDUCED DRAWN VALUES THAT HAVE AN ELEMENT
  NUMBER i: nothing is asked of it elsewhere
  `atEl_zero`, `atEl_one`, **`kit_zero_blocks`**, **`kit_one_blocks`**   the events "the word at
      place i, as the program reads it (E.ofTriple; the word 0 where there is none), is the word 0",
      "... is the word 1": each has at most the share kapSl 128 ^ exAll (the round's draws) / p ^ 3
      of the strings of hash blocks
  **`kit_count`**, **`kit_count_blocks`**   of a kit's challenges at an entry and a kind, the share
      of those that show a drawn value at which Q holds: at most c / p ^ 3 at Run.ck .two; at most
      kapSl 128 ^ exAll (the round's draws) * c / p ^ 3 at Run.ckP .two, where the entry's positions
      have at most 64 bits
  **`tuple_gate`**, **`tuple_gate_blocks`**   the same two numbers bound the measure (Iop.prRho,
      uniform on that one round's messages) of the messages at which Q holds of what is shown
By: collect_elems, evE_inj (OnBytes/Slice/Draws.lean) · card_EV (OnBytes/Slice/Rates.lean) ·
bsRound_good_ex (OnBytes/Slice/RatesEx.lean) · `prRho_one_le`
(Johnson/Desc/K8/Honest/CountToRho.lean) · `ratio_div` (Johnson/P1K8R/UnitsBlocks.lean).
Limits. AT STRINGS OF HASH BLOCKS THE FACTOR IS THE WHOLE ROUND's: exAll adds 3 for each element
that the round draws, also for those that the event does not read. An element drawn by the rule that
never gives 0 is not covered. One round. The uniform law on one round's messages is named, not
derived. No number is evaluated.

-/
import Johnson.P1K8R.UnitsBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Slice Run
open OnBytes.Maker (RDT uLT drawnT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open Iop
open scoped ENNReal

/-- Element number i among the draws is drawn uniformly over the field. -/
def IsEl : List Fmt.Draw → ℕ → Prop
  | [], _ => False
  | .elem :: _, 0 => True
  | .elem :: ds, i + 1 => IsEl ds i
  | .elemNZ :: _, 0 => False
  | .elemNZ :: ds, i + 1 => IsEl ds i
  | .pos _ :: ds, i => IsEl ds i
  | .trits _ :: ds, i => IsEl ds i
  | .sealed :: ds, i => IsEl ds i

/-- A draw in front that the event does not read is a factor. -/
theorem count_pass {D V : Type} [Finite D] [Finite V] (R : V → Prop) (n P : ℕ)
    (h : Prob.cnt R * P ≤ n * Nat.card V) :
    Prob.cnt (fun x : D × V => R x.2) * P ≤ n * Nat.card (D × V) := by
  classical
  haveI := Fintype.ofFinite D
  haveI := Fintype.ofFinite V
  rw [Prob.cnt_snd, Nat.card_prod, ← Nat.card_eq_fintype_card]
  calc Nat.card D * Prob.cnt R * P = Nat.card D * (Prob.cnt R * P) := Nat.mul_assoc _ _ _
    _ ≤ Nat.card D * (n * Nat.card V) := Nat.mul_le_mul_left _ h
    _ = n * (Nat.card D * Nat.card V) := by ring

/-- The element's own draw. -/
theorem count_here {V : Type} [Finite V] (Q' : Cb.Gl.E → Prop) (c : ℕ) (hc : Prob.cnt Q' ≤ c) :
    Prob.cnt (fun x : EV .two × V => Q' (evE x.1)) * Fmt.Fld.two.p ^ 3 ≤
      c * Nat.card (EV .two × V) := by
  classical
  haveI := Fintype.ofFinite V
  haveI := Fintype.ofFinite (EV .two)
  have h1 : Prob.cnt (fun a : EV .two => Q' (evE a)) ≤ c :=
    ((Prob.cnt_comp_le evE (w := 1)
      (fun _ => Prob.cnt_le_one fun _ _ ha hb => evE_inj (ha.trans hb.symm)) Q').trans
      (by rw [Nat.mul_one])).trans hc
  rw [Prob.cnt_fst (fun a : EV .two => Q' (evE a)), Nat.card_prod, card_EV,
    ← Nat.card_eq_fintype_card]
  calc Prob.cnt (fun a : EV .two => Q' (evE a)) * Nat.card V * Fmt.Fld.two.p ^ 3
      ≤ c * Nat.card V * Fmt.Fld.two.p ^ 3 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
    _ = c * (Fmt.Fld.two.p ^ 3 * Nat.card V) := by ring

/-- **The count of typed challenges.** -/
theorem typed_count (Q' : Cb.Gl.E → Prop) (c : ℕ) (hc : Prob.cnt Q' ≤ c) :
    ∀ (ds : List Fmt.Draw) (i : ℕ), IsEl ds i →
      Prob.cnt (fun v : Vals .two ds => ∃ x, (elemsV ds v)[i]? = some x ∧ Q' x) *
          Fmt.Fld.two.p ^ 3 ≤ c * Nat.card (Vals .two ds)
  | [], _, h => h.elim
  | .elem :: ds, 0, _ => by
    have e : (fun v : Vals .two (.elem :: ds) =>
        ∃ x, (elemsV (.elem :: ds) v)[0]? = some x ∧ Q' x) =
        fun v : EV .two × Vals .two ds => Q' (evE v.1) := by
      funext v
      apply propext
      constructor
      · rintro ⟨x, hx, hq⟩
        have hx' : some (evE v.1) = some x := hx
        rw [Option.some.inj hx']
        exact hq
      · intro hq
        exact ⟨evE v.1, rfl, hq⟩
    rw [e]
    exact count_here Q' c hc
  | .elem :: ds, i + 1, h =>
    count_pass (D := EV .two) (fun v : Vals .two ds => ∃ x, (elemsV ds v)[i]? = some x ∧ Q' x)
      c _ (typed_count Q' c hc ds i h)
  | .elemNZ :: _, 0, h => h.elim
  | .elemNZ :: ds, i + 1, h =>
    count_pass (D := NZ .two) (fun v : Vals .two ds => ∃ x, (elemsV ds v)[i]? = some x ∧ Q' x)
      c _ (typed_count Q' c hc ds i h)
  | .pos k :: ds, i, h =>
    count_pass (D := Fin (2 ^ k))
      (fun v : Vals .two ds => ∃ x, (elemsV ds v)[i]? = some x ∧ Q' x)
      c _ (typed_count Q' c hc ds i h)
  | .trits n :: ds, i, h =>
    count_pass (D := Fin n → Bool × Bool)
      (fun v : Vals .two ds => ∃ x, (elemsV ds v)[i]? = some x ∧ Q' x)
      c _ (typed_count Q' c hc ds i h)
  | .sealed :: ds, i, h =>
    count_pass (D := Fin 4 → UInt64)
      (fun v : Vals .two ds => ∃ x, (elemsV ds v)[i]? = some x ∧ Q' x)
      c _ (typed_count Q' c hc ds i h)

/-- Element number i of a drawn value, read in the field, meets Q'. -/
def AtEl (i : ℕ) (Q' : Cb.Gl.E → Prop) (R : Fmt.Drawn) : Prop :=
  ∃ x, (R.elems.map toE)[i]? = some x ∧ Q' x

/-- Every element that a typed challenge shows is a triple of words below the prime. -/
theorem collect_ok : ∀ (ds : List Fmt.Draw) (v : Vals .two ds) (w : Fmt.Ext3),
    w ∈ (Fmt.collect (outAll .two ds v)).elems → Fmt.Fld.two.okE w = true
  | [], _, _, h => nomatch h
  | .elem :: ds, v, w, h => by
    have h' : w ∈ toU3 v.1 :: (Fmt.collect (outAll .two ds v.2)).elems := h
    rcases List.mem_cons.1 h' with rfl | h''
    · exact okE_toU3 v.1
    · exact collect_ok ds v.2 w h''
  | .elemNZ :: ds, v, w, h => by
    have h' : w ∈ toU3 v.1.1 :: (Fmt.collect (outAll .two ds v.2)).elems := h
    rcases List.mem_cons.1 h' with rfl | h''
    · exact okE_toU3 v.1.1
    · exact collect_ok ds v.2 w h''
  | .pos _ :: ds, v, w, h => collect_ok ds v.2 w h
  | .trits _ :: ds, v, w, h => collect_ok ds v.2 w h
  | .sealed :: ds, v, w, h => collect_ok ds v.2 w h

/-- A typed challenge shows as many elements as the round draws. -/
theorem collect_len (ds : List Fmt.Draw) (v : Vals .two ds) :
    (Fmt.collect (outAll .two ds v)).elems.length = nE ds := by
  have h := congrArg List.length (collect_elems ds v)
  rw [List.length_map, elemsV_length] at h
  exact h

theorem isEl_lt : ∀ (ds : List Fmt.Draw) (i : ℕ), IsEl ds i → i < nE ds
  | [], _, h => h.elim
  | .elem :: ds, 0, _ => Nat.succ_pos (nE ds)
  | .elem :: ds, i + 1, h => Nat.succ_lt_succ (isEl_lt ds i h)
  | .elemNZ :: _, 0, h => h.elim
  | .elemNZ :: ds, i + 1, h => Nat.succ_lt_succ (isEl_lt ds i h)
  | .pos _ :: ds, i, h => isEl_lt ds i h
  | .trits _ :: ds, i, h => isEl_lt ds i h
  | .sealed :: ds, i, h => isEl_lt ds i h

/-- All elements of a drawn value are triples of words below the prime. -/
def Reduced (R : Fmt.Drawn) : Prop := ∀ w ∈ R.elems, Fmt.Fld.two.okE w = true

/-- A test on words: element number i is the word of x. -/
theorem atEl_word (i : ℕ) (Q' : Cb.Gl.E → Prop) (R : Fmt.Drawn) (x : Cb.Gl.E)
    (h : R.elems[i]? = some (Slice.ofE x)) (hq : Q' x) : AtEl i Q' R :=
  ⟨x, by rw [List.getElem?_map, h, Option.map_some, toE_ofE], hq⟩

/-- The word at place i, as the program reads it, is the word 0. -/
theorem atEl_zero (i : ℕ) (R : Fmt.Drawn) (hl : i < R.elems.length)
    (h : isZeroE ((R.elems.map E.ofTriple).getD i zeroE) = true) : AtEl i (· = 0) R := by
  have e1 : (R.elems.map E.ofTriple).getD i zeroE = E.ofTriple R.elems[i] := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hl), List.getElem_map]
  refine ⟨toE R.elems[i], by rw [List.getElem?_map, List.getElem?_eq_getElem hl]; rfl, ?_⟩
  rw [← readE_ofTriple, ← e1]
  exact readE_of_isZeroE _ h

/-- The word at place i, as the program reads it, is the word 1. -/
theorem atEl_one (i : ℕ) (R : Fmt.Drawn) (hl : i < R.elems.length)
    (h : ((R.elems.map E.ofTriple).getD i zeroE == oneE) = true) : AtEl i (· = 1) R := by
  have e1 : (R.elems.map E.ofTriple).getD i zeroE = E.ofTriple R.elems[i] := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hl), List.getElem_map]
  refine ⟨toE R.elems[i], by rw [List.getElem?_map, List.getElem?_eq_getElem hl]; rfl, ?_⟩
  rw [← readE_ofTriple, ← e1, beq_iff_eq.1 h]
  exact readE_one

/-- Arithmetic. -/
theorem frac_le (a b c d : ℕ) (h : a * d ≤ c * b) (hb : b ≠ 0) (hd : d ≠ 0) :
    (a : ℝ≥0∞) / (b : ℝ≥0∞) ≤ (c : ℝ≥0∞) / (d : ℝ≥0∞) := by
  have hb0 : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb
  have hd0 : (d : ℝ≥0∞) ≠ 0 := by exact_mod_cast hd
  have hbt : (b : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hdt : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have key : (a : ℝ≥0∞) * d ≤ c * b := by exact_mod_cast h
  calc (a : ℝ≥0∞) / b = a * d / d / b := by rw [ENNReal.mul_div_cancel_right hd0 hdt]
    _ ≤ c * b / d / b := ENNReal.div_le_div_right (ENNReal.div_le_div_right key _) _
    _ = c * (d : ℝ≥0∞)⁻¹ * (b * (b : ℝ≥0∞)⁻¹) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
    _ = c / d := by rw [ENNReal.mul_inv_cancel hb0 hbt, mul_one, div_eq_mul_inv]

theorem p3_ne : Fmt.Fld.two.p ^ 3 ≠ 0 := by
  rw [← card_EV]
  haveI : Nonempty (EV .two) := ⟨(zF .two, zF .two, zF .two)⟩
  exact (Nat.card_pos).ne'

/-- What the typed kit's count is. -/
theorem typed_at (e : Fmt.Entry) (k : Fmt.Kind) (i : ℕ) (Q' : Cb.Gl.E → Prop) (c : ℕ)
    (hc : Prob.cnt Q' ≤ c) (hi : IsEl (Fmt.dsOf e k) i) (Q : Fmt.Drawn → Prop)
    (hQ : ∀ R, Reduced R → i < R.elems.length → Q R → AtEl i Q' R) :
    Prob.cnt (fun v : Ch .two e k => Q (drawnOf .two e k v)) * Fmt.Fld.two.p ^ 3 ≤
      c * Nat.card (Vals .two (Fmt.dsOf e k)) := by
  refine le_trans (Nat.mul_le_mul_right _ (Prob.cnt_mono fun v hv => ?_))
    (typed_count Q' c hc (Fmt.dsOf e k) i hi)
  have hlen : i < (drawnOf .two e k v).elems.length := by
    show i < (Fmt.collect (outAll .two (Fmt.dsOf e k) v)).elems.length
    rw [collect_len]
    exact isEl_lt _ _ hi
  obtain ⟨x, hx, hq⟩ := hQ _ (collect_ok (Fmt.dsOf e k) v) hlen hv
  refine ⟨x, ?_, hq⟩
  rw [← collect_elems]
  exact hx

theorem vals_ne (e : Fmt.Entry) (k : Fmt.Kind) : Nat.card (Vals .two (Fmt.dsOf e k)) ≠ 0 := by
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_ne_zero

/-- **The share of the kit's challenges: at typed challenges.** -/
theorem kit_count (e : Fmt.Entry) (k : Fmt.Kind) (i : ℕ) (Q' : Cb.Gl.E → Prop) (c : ℕ)
    (hc : Prob.cnt Q' ≤ c) (hi : IsEl (Fmt.dsOf e k) i) (Q : Fmt.Drawn → Prop)
    (hQ : ∀ R, Reduced R → i < R.elems.length → Q R → AtEl i Q' R) :
    (Prob.cnt (fun ch : (_root_.Run.ck .two).Ch e k =>
        Q ((_root_.Run.ck .two).dr e k ch)) : ℝ≥0∞) /
        (Nat.card ((_root_.Run.ck .two).Ch e k) : ℝ≥0∞) ≤
      (c : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) :=
  frac_le _ _ _ _ (typed_at e k i Q' c hc hi Q hQ) (vals_ne e k) p3_ne

/-- **The share of the kit's challenges: at strings of hash blocks.** -/
theorem kit_count_blocks (e : Fmt.Entry) (k : Fmt.Kind) (hlog : e.logN ≤ 64) (i : ℕ)
    (Q' : Cb.Gl.E → Prop) (c : ℕ) (hc : Prob.cnt Q' ≤ c) (hi : IsEl (Fmt.dsOf e k) i)
    (Q : Fmt.Drawn → Prop) (hQ : ∀ R, Reduced R → i < R.elems.length → Q R → AtEl i Q' R) :
    (Prob.cnt (fun ch : (_root_.Run.ckP .two).Ch e k =>
        Q ((_root_.Run.ckP .two).dr e k ch)) : ℝ≥0∞) /
        (Nat.card ((_root_.Run.ckP .two).Ch e k) : ℝ≥0∞) ≤
      kapSl 128 ^ exAll (Fmt.dsOf e k) * (c : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  have hg := bsRound_good_ex e k hlog
  have h1 : Prob.cnt (fun u : Fin (bsRound .two e k).b → Dig 256 =>
      Q (drawnOf .two e k ((bsRound .two e k).φ u))) ≤
      Prob.cnt (fun v : Ch .two e k => Q (drawnOf .two e k v)) * (bsRound .two e k).w :=
    Prob.cnt_comp_le (bsRound .two e k).φ hg.fib (fun v : Ch .two e k => Q (drawnOf .two e k v))
  have hB : Nat.card ((_root_.Run.ckP .two).Ch e k) =
      Fintype.card (Fin (bsRound .two e k).b → Dig 256) := Nat.card_eq_fintype_card
  have hB0 : Fintype.card (Fin (bsRound .two e k).b → Dig 256) ≠ 0 :=
    (Fintype.card_pos_iff.2 ⟨fun _ _ => false⟩).ne'
  have h2 := ratio_div
    (Prob.cnt (fun v : Ch .two e k => Q (drawnOf .two e k v)) : ℝ≥0∞) _ _ _ _ hg.ratio
    (by exact_mod_cast hB0) (ENNReal.natCast_ne_top _)
    (by exact_mod_cast vals_ne e k) (ENNReal.natCast_ne_top _)
  have h3 := frac_le _ _ _ _ (typed_at e k i Q' c hc hi Q hQ) (vals_ne e k) p3_ne
  rw [hB]
  calc (Prob.cnt (fun ch : (_root_.Run.ckP .two).Ch e k =>
          Q ((_root_.Run.ckP .two).dr e k ch)) : ℝ≥0∞) /
        (Fintype.card (Fin (bsRound .two e k).b → Dig 256) : ℝ≥0∞)
      ≤ (Prob.cnt (fun v : Ch .two e k => Q (drawnOf .two e k v)) : ℝ≥0∞) *
          ((bsRound .two e k).w : ℝ≥0∞) /
        (Fintype.card (Fin (bsRound .two e k).b → Dig 256) : ℝ≥0∞) :=
        ENNReal.div_le_div_right (by exact_mod_cast h1) _
    _ ≤ kapSl 128 ^ exAll (Fmt.dsOf e k) *
          (Prob.cnt (fun v : Ch .two e k => Q (drawnOf .two e k v)) : ℝ≥0∞) /
        (Nat.card (Vals .two (Fmt.dsOf e k)) : ℝ≥0∞) := h2
    _ ≤ kapSl 128 ^ exAll (Fmt.dsOf e k) * (c : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
        rw [mul_div_assoc, mul_div_assoc]
        exact mul_le_mul' le_rfl h3

theorem cnt_eq_le (y : Cb.Gl.E) : Prob.cnt (fun x : Cb.Gl.E => x = y) ≤ 1 :=
  Prob.cnt_le_one fun _ _ ha hb => ha.trans hb.symm

/-- **"The word at place i is the word 0": the share at strings of hash blocks.** -/
theorem kit_zero_blocks (e : Fmt.Entry) (k : Fmt.Kind) (hlog : e.logN ≤ 64) (i : ℕ)
    (hi : IsEl (Fmt.dsOf e k) i) :
    (Prob.cnt (fun ch : (_root_.Run.ckP .two).Ch e k =>
        isZeroE ((((_root_.Run.ckP .two).dr e k ch).elems.map E.ofTriple).getD i zeroE) = true) :
        ℝ≥0∞) / (Nat.card ((_root_.Run.ckP .two).Ch e k) : ℝ≥0∞) ≤
      kapSl 128 ^ exAll (Fmt.dsOf e k) * ((1 : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) :=
  kit_count_blocks e k hlog i (· = 0) 1 (cnt_eq_le 0) hi
    (fun R => isZeroE ((R.elems.map E.ofTriple).getD i zeroE) = true)
    (fun R _ hl h => atEl_zero i R hl h)

/-- **"The word at place i is the word 1": the share at strings of hash blocks.** -/
theorem kit_one_blocks (e : Fmt.Entry) (k : Fmt.Kind) (hlog : e.logN ≤ 64) (i : ℕ)
    (hi : IsEl (Fmt.dsOf e k) i) :
    (Prob.cnt (fun ch : (_root_.Run.ckP .two).Ch e k =>
        ((((_root_.Run.ckP .two).dr e k ch).elems.map E.ofTriple).getD i zeroE == oneE) = true) :
        ℝ≥0∞) / (Nat.card ((_root_.Run.ckP .two).Ch e k) : ℝ≥0∞) ≤
      kapSl 128 ^ exAll (Fmt.dsOf e k) * ((1 : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) :=
  kit_count_blocks e k hlog i (· = 1) 1 (cnt_eq_le 1) hi
    (fun R => ((R.elems.map E.ofTriple).getD i zeroE == oneE) = true)
    (fun R _ hl h => atEl_one i R hl h)

/-- **The measure over one round's messages: at typed challenges.** -/
theorem tuple_gate (d : RDT) (i : ℕ) (Q' : Cb.Gl.E → Prop) (c : ℕ) (hc : Prob.cnt Q' ≤ c)
    (hi : IsEl (Fmt.dsOf d.entry d.kind) i) (Q : Fmt.Drawn → Prop)
    (hQ : ∀ R, Reduced R → i < R.elems.length → Q R → AtEl i Q' R) :
    Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ck .two) [d]) |
      ∃ dr, drawnT (_root_.Run.ck .two) [d] ρ = [dr] ∧ Q dr} ≤
      (c : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) :=
  le_trans (prRho_one_le _ d Q _ le_rfl) (kit_count d.entry d.kind i Q' c hc hi Q hQ)

/-- **The measure over one round's messages: at strings of hash blocks.** -/
theorem tuple_gate_blocks (d : RDT) (hlog : d.entry.logN ≤ 64) (i : ℕ) (Q' : Cb.Gl.E → Prop)
    (c : ℕ) (hc : Prob.cnt Q' ≤ c) (hi : IsEl (Fmt.dsOf d.entry d.kind) i)
    (Q : Fmt.Drawn → Prop) (hQ : ∀ R, Reduced R → i < R.elems.length → Q R → AtEl i Q' R) :
    Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ckP .two) [d]) |
      ∃ dr, drawnT (_root_.Run.ckP .two) [d] ρ = [dr] ∧ Q dr} ≤
      kapSl 128 ^ exAll (Fmt.dsOf d.entry d.kind) * (c : ℝ≥0∞) /
        ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) :=
  le_trans (prRho_one_le _ d Q _ le_rfl)
    (kit_count_blocks d.entry d.kind hlog i Q' c hc hi Q hQ)

/-- The exponent: 3 for each element that the round draws. -/
theorem exAll_eq : ∀ ds : List Fmt.Draw, exAll ds = 3 * nE ds
  | [] => rfl
  | .elem :: ds => by
    show 3 + exAll ds = 3 * (nE ds + 1)
    rw [exAll_eq ds]
    ring
  | .elemNZ :: ds => by
    show 3 + exAll ds = 3 * (nE ds + 1)
    rw [exAll_eq ds]
    ring
  | .pos _ :: ds => by
    show 0 + exAll ds = 3 * nE ds
    rw [exAll_eq ds, Nat.zero_add]
  | .trits _ :: ds => by
    show 0 + exAll ds = 3 * nE ds
    rw [exAll_eq ds, Nat.zero_add]
  | .sealed :: ds => by
    show 0 + exAll ds = 3 * nE ds
    rw [exAll_eq ds, Nat.zero_add]

end P1K8

#print axioms P1K8.typed_count
#print axioms P1K8.collect_ok
#print axioms P1K8.atEl_word
#print axioms P1K8.kit_count
#print axioms P1K8.kit_count_blocks
#print axioms P1K8.kit_zero_blocks
#print axioms P1K8.kit_one_blocks
#print axioms P1K8.tuple_gate
#print axioms P1K8.tuple_gate_blocks
#print axioms P1K8.exAll_eq
