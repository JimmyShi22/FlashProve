-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Decode.lean: words, tables of words, and their decoding within a radius e.

A word is a function on the set ι of positions. A table is a family of words, its rows, indexed by
any type R; the rows may come from different oracles. The code is given by its generator matrix G,
with one row for each position and one column for each coordinate of a message. A table f decodes to
the table M of messages at the radius e (`DecodesTo`) if all but at most e columns of f are equal to
the columns of the table of the codewords G M_a. The exceptional columns are common to all rows:
this is the distance of interleaved words. Where distances are measured as fractions ("δ-close"
means that at most δ n positions differ), the radius e of this file is the integer part of δ n. So
"at most δ n positions" is "at most e positions", and "more than δ n positions" is "more than e
positions", that is, at least e + 1.

Sections 1 to 5 are stated for an arbitrary field, an arbitrary matrix and arbitrary finite sets of
positions and coordinates; most of sections 6 and 7 for finite fields. Of the code only two
properties are used, each as an explicit hypothesis:
 * `HasDist G d`: every non-zero message has a codeword with at least d non-zero symbols; together
   with 2 e < d (unique decoding);
 * `Code.MCA` for the range of G, at the radius e: mutual correlated agreement on lines, with at
   most `bad` exceptional values (only for section 6 and `lemma_E10`). (Section 7 also uses msg + r
   ≤ k: `Code.Enc.Props.place`.)
The last section derives both from the properties of a code with encoder (`Code.Enc.Props`), and
states the two main lemmas for such a code, `lemma_E9` and `lemma_E10`.

Errors are counts: the number of values of one message of the verifier that are bad. n is the number
of positions, q a number of positions that the verifier samples. A verifier message that is a pair
or a tuple of such values is handled with `Prob.cnt_fst`, `Prob.cnt_snd` and `Prob.cnt_pi_coord`
(Prob/Count.lean).

The labels (Dc1) to (Dc6), which other files cite, are in the headings of sections 2 to 5 and in the
docstrings; (i), with two assertions, and (ii) in section 6 are the three conjuncts of `lemma_E10`.
Every closure property of section 3 follows from `DecodesTo.of_imp`.

(Dc6), section 6 and section 7 build on Code/Third.lean and Code/Derived.lean.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Prob.Count
import Code.Facts
import Code.Third
import Code.Derived
import Blocks.Basic
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks

open Prob

/-! ## 1. Definitions -/

section Defs

variable {E ι κ : Type} [Field E] [Fintype ι] [Fintype κ]

/-- Column j of the table f is off the table M of messages: in some row, f differs at j from the
codeword of the message. -/
def Off {R : Type} (G : Matrix ι κ E) (f : R → ι → E) (M : R → κ → E) (j : ι) : Prop :=
  ∃ a, f a j ≠ G.mulVec (M a) j

/-- The table f decodes to the messages M at the radius e: at most e columns are off. -/
def DecodesTo {R : Type} (G : Matrix ι κ E) (e : ℕ) (f : R → ι → E) (M : R → κ → E) : Prop :=
  cnt (Off G f M) ≤ e

/-- The table f decodes at the radius e (f is δ-close to the interleaved code). -/
def Decodes {R : Type} (G : Matrix ι κ E) (e : ℕ) (f : R → ι → E) : Prop :=
  ∃ M, DecodesTo G e f M

open Classical in
/-- The decoded messages of a table. For a table that does not decode the value is 0 and has no
meaning. -/
def dec {R : Type} (G : Matrix ι κ E) (e : ℕ) (f : R → ι → E) : R → κ → E :=
  if h : Decodes G e f then h.choose else 0

/-- (P1) Distance, for a generator matrix: every non-zero message has a codeword with at least d
non-zero symbols. -/
def HasDist (G : Matrix ι κ E) (d : ℕ) : Prop :=
  ∀ v : κ → E, v ≠ 0 → d ≤ cnt (fun j => G.mulVec v j ≠ 0)

variable {G : Matrix ι κ E} {e e' d : ℕ} {R R' : Type}

omit [Fintype ι] in
theorem not_off_iff {f : R → ι → E} {M : R → κ → E} {j : ι} :
    ¬ Off G f M j ↔ ∀ a, f a j = G.mulVec (M a) j := by
  unfold Off
  push Not
  exact Iff.rfl

/-- For a single word: it decodes to the message m if it differs from the codeword of m in at most e
positions. -/
theorem decodesTo_word_iff {o : ι → E} {m : κ → E} :
    DecodesTo G e (fun _ : Unit => o) (fun _ => m) ↔ cnt (fun j => o j ≠ G.mulVec m j) ≤ e := by
  unfold DecodesTo
  rw [cnt_congr (Q := fun j => o j ≠ G.mulVec m j) fun j => ⟨fun ⟨_, h⟩ => h, fun h => ⟨(), h⟩⟩]

/-- A single word decodes if it differs from some codeword in at most e positions. -/
theorem decodes_word_iff {o : ι → E} :
    Decodes G e (fun _ : Unit => o) ↔ ∃ m : κ → E, cnt (fun j => o j ≠ G.mulVec m j) ≤ e :=
  ⟨fun ⟨M, hM⟩ => ⟨M (), decodesTo_word_iff.mp hM⟩,
    fun ⟨m, hm⟩ => ⟨fun _ => m, decodesTo_word_iff.mpr hm⟩⟩

/-- A larger radius allows more. -/
theorem DecodesTo.mono {f : R → ι → E} {M : R → κ → E} (h : DecodesTo G e f M) (he : e ≤ e') :
    DecodesTo G e' f M :=
  le_trans h he

theorem Decodes.mono {f : R → ι → E} (h : Decodes G e f) (he : e ≤ e') : Decodes G e' f :=
  h.imp fun _ hM => hM.mono he

/-- The source of all closure properties. Suppose that in every column in which f is equal to the
codewords of M, also f' is equal to the codewords of M'. If f decodes to M, then f' decodes to M',
with the same exceptional columns or fewer. -/
theorem DecodesTo.of_imp {f : R → ι → E} {M : R → κ → E} {f' : R' → ι → E} {M' : R' → κ → E}
    (h : DecodesTo G e f M)
    (himp : ∀ j, (∀ a, f a j = G.mulVec (M a) j) → ∀ b, f' b j = G.mulVec (M' b) j) :
    DecodesTo G e f' M' :=
  le_trans (cnt_mono fun j hj =>
    by_contra fun hc => not_off_iff.mpr (himp j (not_off_iff.mp hc)) hj) h

/-- A table of codewords decodes to its messages, at every radius. -/
theorem decodesTo_mulVec (G : Matrix ι κ E) (e : ℕ) (M : R → κ → E) :
    DecodesTo G e (fun a => G.mulVec (M a)) M := by
  unfold DecodesTo
  rw [cnt_false fun j ⟨_, h⟩ => h rfl]
  exact Nat.zero_le e

/-- The decoded messages of a table that decodes are messages to which it decodes. -/
theorem Decodes.decodesTo_dec {f : R → ι → E} (h : Decodes G e f) :
    DecodesTo G e f (dec G e f) := by
  unfold dec
  rw [dif_pos h]
  exact h.choose_spec

theorem dec_of_not_decodes {f : R → ι → E} (h : ¬ Decodes G e f) : dec G e f = 0 := by
  unfold dec
  rw [dif_neg h]

end Defs

/-! ## 2. Unique decoding: (Dc1) and (Dc5) -/

section Unique

variable {E ι κ : Type} [Field E] [Fintype ι] [Fintype κ] {G : Matrix ι κ E}
  {e e' d : ℕ} {R R' : Type}

/-- If G has distance d (`HasDist G d`), the codewords of two different messages differ in at least
d positions. -/
theorem HasDist.le_cnt_ne (hd : HasDist G d) {u v : κ → E} (huv : u ≠ v) :
    d ≤ cnt (fun j => G.mulVec u j ≠ G.mulVec v j) := by
  refine (hd (u - v) (sub_ne_zero.mpr huv)).trans (cnt_mono fun j hj h0 => hj ?_)
  rw [Matrix.mulVec_sub, Pi.sub_apply, h0, sub_self]

/-- (Dc1), second half: the generator is injective, if `HasDist G d` and 0 < d. -/
theorem HasDist.injective (hd : HasDist G d) (hpos : 0 < d) : Function.Injective G.mulVec := by
  intro u v huv
  by_contra hne
  have h1 := hd.le_cnt_ne hne
  rw [cnt_false fun j hj => hj (by rw [huv])] at h1
  omega

theorem HasDist.mono (hd : HasDist G d) {d' : ℕ} (h : d' ≤ d) : HasDist G d' := fun v hv =>
  h.trans (hd v hv)

/-- (Dc5), in general form. If a word is a row of two tables, of which one decodes at the radius e
and the other at the radius e', and e + e' < d, where `HasDist G d`, then the word has the same
message in both. -/
theorem DecodesTo.row_unique (hd : HasDist G d) (hee : e + e' < d) {f : R → ι → E} {M : R → κ → E}
    {f' : R' → ι → E} {M' : R' → κ → E} (h : DecodesTo G e f M) (h' : DecodesTo G e' f' M') {a : R}
    {a' : R'} (hrow : f a = f' a') : M a = M' a' := by
  by_contra hne
  have h1 := hd.le_cnt_ne hne
  have h2 : cnt (fun j => G.mulVec (M a) j ≠ G.mulVec (M' a') j) ≤
      cnt (Off G f M) + cnt (Off G f' M') :=
    cnt_le_add fun j hj => by
      by_cases hc : f a j = G.mulVec (M a) j
      · exact Or.inr ⟨a', fun hc' => hj (by rw [← hc, hrow, hc'])⟩
      · exact Or.inl ⟨a, hc⟩
  unfold DecodesTo at h h'
  omega

/-- (Dc1), first half: a table has at most one table of messages within the radius e, if
`HasDist G d` and 2 e < d. -/
theorem DecodesTo.unique (hd : HasDist G d) (h2 : 2 * e < d) {f : R → ι → E} {M M' : R → κ → E}
    (h : DecodesTo G e f M) (h' : DecodesTo G e f M') : M = M' :=
  funext fun _ => DecodesTo.row_unique hd (by omega) h h' rfl

/-- (Dc1) for codewords: a table has at most one table of codewords within the radius e, if
`HasDist G d` and 2 e < d. -/
theorem DecodesTo.codewords_unique (hd : HasDist G d) (h2 : 2 * e < d) {f : R → ι → E}
    {M M' : R → κ → E} (h : DecodesTo G e f M) (h' : DecodesTo G e f M') :
    (fun a => G.mulVec (M a)) = fun a => G.mulVec (M' a) := by
  rw [h.unique hd h2 h']

/-- If `HasDist G d` and 2 e < d, whatever a table decodes to is its decoded table of messages. -/
theorem DecodesTo.dec_eq (hd : HasDist G d) (h2 : 2 * e < d) {f : R → ι → E}
    {M : R → κ → E} (h : DecodesTo G e f M) : dec G e f = M :=
  (Decodes.decodesTo_dec ⟨M, h⟩).unique hd h2 h

theorem decodesTo_iff_dec_eq (hd : HasDist G d) (h2 : 2 * e < d) {f : R → ι → E} {M : R → κ → E} :
    DecodesTo G e f M ↔ Decodes G e f ∧ dec G e f = M :=
  ⟨fun h => ⟨⟨M, h⟩, h.dec_eq hd h2⟩, fun ⟨h, hM⟩ => hM ▸ h.decodesTo_dec⟩

/-- If `HasDist G d` and 2 e < d, a table of codewords is decoded to its messages. -/
theorem dec_mulVec (hd : HasDist G d) (h2 : 2 * e < d) (M : R → κ → E) :
    dec G e (fun a => G.mulVec (M a)) = M :=
  (decodesTo_mulVec G e M).dec_eq hd h2

/-- (Dc5). Let `HasDist G d` and 2 e < d. If a word is a row of two tables that both decode, it has
the same decoded message in both. -/
theorem dec_row_eq (hd : HasDist G d) (h2 : 2 * e < d) {f : R → ι → E} {f' : R' → ι → E}
    (h : Decodes G e f) (h' : Decodes G e f') {a : R} {a' : R'} (hrow : f a = f' a') :
    dec G e f a = dec G e f' a' :=
  DecodesTo.row_unique hd (by omega) h.decodesTo_dec h'.decodesTo_dec hrow

end Unique

/-! ## 3. Combinations and sub-tables: (Dc2) -/

section Comb

variable {E ι κ : Type} [Field E] [Fintype ι] [Fintype κ] {G : Matrix ι κ E}
  {e d : ℕ} {R R' I : Type}

omit [Fintype ι] in
/-- Encoding is linear. -/
theorem mulVec_comb [Fintype R] (G : Matrix ι κ E) (c : R → E) (M : R → κ → E) :
    G.mulVec (∑ a, c a • M a) = ∑ a, c a • G.mulVec (M a) := by
  simp only [← Matrix.mulVecLin_apply, map_sum, map_smul]

omit [Fintype ι] [Fintype κ] in
/-- A combination of functions, written out entry by entry. The protocols are written in this
form. -/
theorem comb_eq [Fintype R] {X : Type} (c : R → E) (f : R → X → E) :
    ∑ a, c a • f a = fun x => ∑ a, c a * f a x := by
  funext x
  rw [Finset.sum_apply]
  rfl

/-- (Dc2), sub-tables. Any selection of rows of a table that decodes to M, with or without
repetition, decodes to the same messages. -/
theorem DecodesTo.comp {f : R → ι → E} {M : R → κ → E} (h : DecodesTo G e f M) (σ : R' → R) :
    DecodesTo G e (fun b => f (σ b)) (fun b => M (σ b)) :=
  h.of_imp fun _ hj b => hj (σ b)

/-- One row, as a table of one row. -/
theorem DecodesTo.row {f : R → ι → E} {M : R → κ → E} (h : DecodesTo G e f M) (a : R) :
    DecodesTo G e (fun _ : Unit => f a) (fun _ => M a) :=
  h.comp fun _ => a

/-- (Dc2), combinations, for a whole table of combinations at once: if f decodes to M, the table of
the words ∑_a c_(b,a) f_a, b ∈ R', decodes to the messages ∑_a c_(b,a) M_a. -/
theorem DecodesTo.combs [Fintype R] {f : R → ι → E} {M : R → κ → E}
    (h : DecodesTo G e f M) (c : R' → R → E) :
    DecodesTo G e (fun b => ∑ a, c b a • f a) (fun b => ∑ a, c b a • M a) :=
  h.of_imp fun j hj b => by
    rw [mulVec_comb, Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => by rw [Pi.smul_apply, Pi.smul_apply, hj a]

/-- (Dc2), one combination: if f decodes to M, the word ∑_a c_a f_a decodes to ∑_a c_a M_a. -/
theorem DecodesTo.comb [Fintype R] {f : R → ι → E} {M : R → κ → E}
    (h : DecodesTo G e f M) (c : R → E) :
    DecodesTo G e (fun _ : Unit => ∑ a, c a • f a) (fun _ => ∑ a, c a • M a) :=
  h.combs fun _ => c

/-- Every point of the line through two tables that decode together decodes, to the point of the
line through the messages. -/
theorem DecodesTo.line {f₀ f₁ : R → ι → E} {M₀ M₁ : R → κ → E}
    (h : DecodesTo G e (Sum.elim f₀ f₁) (Sum.elim M₀ M₁)) (ν : E) :
    DecodesTo G e (fun a => f₀ a + ν • f₁ a) (fun a => M₀ a + ν • M₁ a) :=
  h.of_imp fun j hj a => by
    have h0 := hj (Sum.inl a)
    have h1 := hj (Sum.inr a)
    simp only [Sum.elim_inl, Sum.elim_inr] at h0 h1
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.add_apply,
      Pi.smul_apply, Pi.smul_apply, h0, h1]

/-- A first table with the coefficient 1 plus a combination of further tables. The tables f₀ and
f_i, i ∈ I, have rows indexed by R. -/
theorem DecodesTo.one_comb [Fintype I] {f₀ : R → ι → E} {f : I → R → ι → E} {M₀ : R → κ → E}
    {M : I → R → κ → E}
    (h : DecodesTo G e (fun p : Option I × R => (p.1.elim f₀ f) p.2) (fun p => (p.1.elim M₀ M) p.2))
    (c : I → E) :
    DecodesTo G e (fun r => f₀ r + ∑ i, c i • f i r) (fun r => M₀ r + ∑ i, c i • M i r) :=
  h.of_imp fun j hj r => by
    have h0 : f₀ r j = G.mulVec (M₀ r) j := hj (none, r)
    have h1 : ∀ i, f i r j = G.mulVec (M i r) j := fun i => hj (some i, r)
    rw [Matrix.mulVec_add, mulVec_comb, Pi.add_apply, Pi.add_apply,
      Finset.sum_apply, Finset.sum_apply, h0]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, Pi.smul_apply, h1 i])

theorem Decodes.comp {f : R → ι → E} (h : Decodes G e f) (σ : R' → R) :
    Decodes G e fun b => f (σ b) :=
  let ⟨_, hM⟩ := h; ⟨_, hM.comp σ⟩

theorem Decodes.row {f : R → ι → E} (h : Decodes G e f) (a : R) : Decodes G e fun _ : Unit => f a :=
  h.comp fun _ => a

theorem Decodes.combs [Fintype R] {f : R → ι → E} (h : Decodes G e f) (c : R' → R → E) :
    Decodes G e fun b => ∑ a, c b a • f a :=
  let ⟨_, hM⟩ := h; ⟨_, hM.combs c⟩

theorem Decodes.comb [Fintype R] {f : R → ι → E} (h : Decodes G e f) (c : R → E) :
    Decodes G e fun _ : Unit => ∑ a, c a • f a :=
  h.combs fun _ => c

/-- Whether a table decodes does not depend on the names of its rows. -/
theorem decodes_comp_equiv (σ : R' ≃ R) {f : R → ι → E} :
    (Decodes G e fun b => f (σ b)) ↔ Decodes G e f :=
  ⟨fun h => by simpa using h.comp σ.symm, fun h => h.comp σ⟩

/-- Two tables decode together if and only if they decode to messages with a common set of at most e
exceptional columns. -/
theorem decodes_sumElim_iff {f₀ : R → ι → E} {f₁ : R' → ι → E} :
    Decodes G e (Sum.elim f₀ f₁) ↔ ∃ M₀ M₁, DecodesTo G e (Sum.elim f₀ f₁) (Sum.elim M₀ M₁) :=
  ⟨fun ⟨M, hM⟩ => ⟨fun a => M (Sum.inl a), fun b => M (Sum.inr b), by
      have : Sum.elim (fun a => M (Sum.inl a)) (fun b => M (Sum.inr b)) = M := by
        funext x
        cases x <;> rfl
      rwa [this]⟩,
    fun ⟨_, _, h⟩ => ⟨_, h⟩⟩

theorem Decodes.line {f₀ f₁ : R → ι → E} (h : Decodes G e (Sum.elim f₀ f₁)) (ν : E) :
    Decodes G e fun a => f₀ a + ν • f₁ a :=
  let ⟨_, _, hM⟩ := decodes_sumElim_iff.mp h; ⟨_, hM.line ν⟩

/-- (Dc2) for the decoded messages: sub-tables. -/
theorem dec_comp (hd : HasDist G d) (h2 : 2 * e < d) {f : R → ι → E}
    (h : Decodes G e f) (σ : R' → R) :
    dec G e (fun b => f (σ b)) = fun b => dec G e f (σ b) :=
  (h.decodesTo_dec.comp σ).dec_eq hd h2

/-- (Dc2) for the decoded messages: combinations. -/
theorem dec_combs [Fintype R] (hd : HasDist G d) (h2 : 2 * e < d) {f : R → ι → E}
    (h : Decodes G e f) (c : R' → R → E) :
    dec G e (fun b => ∑ a, c b a • f a) = fun b => ∑ a, c b a • dec G e f a :=
  (h.decodesTo_dec.combs c).dec_eq hd h2

theorem dec_comb [Fintype R] (hd : HasDist G d) (h2 : 2 * e < d) {f : R → ι → E}
    (h : Decodes G e f) (c : R → E) :
    dec G e (fun _ : Unit => ∑ a, c a • f a) () = ∑ a, c a • dec G e f a :=
  congrFun (dec_combs hd h2 h fun _ : Unit => c) ()

/-- The decoded messages of a point of a line. -/
theorem dec_line (hd : HasDist G d) (h2 : 2 * e < d) {f₀ f₁ : R → ι → E}
    (h : Decodes G e (Sum.elim f₀ f₁)) (ν : E) :
    dec G e (fun a => f₀ a + ν • f₁ a) = fun a => dec G e f₀ a + ν • dec G e f₁ a := by
  obtain ⟨M₀, M₁, hM⟩ := decodes_sumElim_iff.mp h
  have h0 : dec G e f₀ = M₀ := (hM.comp Sum.inl).dec_eq hd h2
  have h1 : dec G e f₁ = M₁ := (hM.comp Sum.inr).dec_eq hd h2
  rw [h0, h1]
  exact (hM.line ν).dec_eq hd h2

end Comb

/-! ## 4. Wrong messages are caught: (Dc3) and (Dc4) -/

section Catch

variable {E ι κ : Type} [Field E] [Fintype ι] [Fintype κ] {G : Matrix ι κ E} {e d : ℕ} {R : Type}

/-- (Dc3). Let `HasDist G d` and 2 e < d. If a table does not decode, or its decoded messages are
not M, then more than e of its columns are off M. -/
theorem lt_cnt_off (hd : HasDist G d) (h2 : 2 * e < d) {f : R → ι → E} {M : R → κ → E}
    (h : ¬ Decodes G e f ∨ dec G e f ≠ M) : e < cnt (Off G f M) :=
  not_le.mp fun hc => h.elim (fun h1 => h1 ⟨M, hc⟩) fun h1 => h1 (DecodesTo.dec_eq hd h2 hc)

/-- (Dc3), the first case alone. It needs nothing of the code. -/
theorem lt_cnt_off_of_not_decodes {f : R → ι → E} (h : ¬ Decodes G e f) (M : R → κ → E) :
    e < cnt (Off G f M) :=
  not_le.mp fun hc => h ⟨M, hc⟩

/-- (Dc3), the second case with the number from its proof: if `HasDist G d` and f decodes to M, then
at least d - e columns of f are off any other table of messages. -/
theorem DecodesTo.le_cnt_off_add
    (hd : HasDist G d) {f : R → ι → E} {M M' : R → κ → E} (h : DecodesTo G e f M) (hne : M' ≠ M) :
    d ≤ cnt (Off G f M') + e := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
  have h1 := hd.le_cnt_ne ha
  have h2 : cnt (fun j => G.mulVec (M' a) j ≠ G.mulVec (M a) j) ≤
      cnt (Off G f M') + cnt (Off G f M) :=
    cnt_le_add fun j hj => by
      by_cases hc : f a j = G.mulVec (M' a) j
      · exact Or.inr ⟨a, fun hc' => hj (by rw [← hc, hc'])⟩
      · exact Or.inl ⟨a, hc⟩
  unfold DecodesTo at h
  omega

omit [Field E] [Fintype κ] in
/-- (Dc4), as a count. Of the n^q lists of q positions, at most (n - w)^q miss a given set of at
least w positions. -/
theorem cnt_miss_le {P : ι → Prop} {w : ℕ} (h : w ≤ cnt P) (q : ℕ) :
    cnt (fun Q : Fin q → ι => ∀ i, ¬ P (Q i)) ≤ (Fintype.card ι - w) ^ q := by
  rw [cnt_forall_pow (fun j => ¬ P j)]
  refine Nat.pow_le_pow_left ?_ q
  have := cnt_add_cnt_not P
  omega

omit [Field E] [Fintype κ] in
/-- (Dc4) for a set of more than e positions: at most (n - e - 1)^q lists of q positions miss it.
With e the integer part of δ n we have e + 1 > δ n, so one position misses with probability at most
(n - e - 1) / n < 1 - δ, and this gives the bound (1 - δ)^q. -/
theorem cnt_miss_le_of_lt {P : ι → Prop} (h : e < cnt P) (q : ℕ) :
    cnt (fun Q : Fin q → ι => ∀ i, ¬ P (Q i)) ≤ (Fintype.card ι - e - 1) ^ q := by
  rw [Nat.sub_sub]
  exact cnt_miss_le h q

/-- (Dc3) and (Dc4) together: the check at q positions. If f does not decode to M, then at most (n -
e - 1)^q lists of q positions show only columns in which f is equal to the codewords of M. -/
theorem cnt_pass_le {f : R → ι → E} {M : R → κ → E} (h : ¬ DecodesTo G e f M) (q : ℕ) :
    cnt (fun Q : Fin q → ι => ∀ i a, f a (Q i) = G.mulVec (M a) (Q i)) ≤
      (Fintype.card ι - e - 1) ^ q := by
  refine le_trans (cnt_mono fun Q hQ i => ?_) (cnt_miss_le_of_lt (P := Off G f M) (not_le.mp h) q)
  exact not_off_iff.mpr (hQ i)

/-- The check at q positions, if `HasDist G d` and f decodes, but to other messages than M': at most
(n + e - d)^q lists pass. -/
theorem DecodesTo.cnt_pass_le (hd : HasDist G d) {f : R → ι → E} {M M' : R → κ → E}
    (h : DecodesTo G e f M) (hne : M' ≠ M) (q : ℕ) :
    cnt (fun Q : Fin q → ι => ∀ i a, f a (Q i) = G.mulVec (M' a) (Q i)) ≤
      (Fintype.card ι + e - d) ^ q := by
  have h1 := h.le_cnt_off_add hd hne
  refine le_trans (cnt_mono fun Q hQ i => ?_)
    ((cnt_miss_le (P := Off G f M') (w := d - e) (by omega) q).trans ?_)
  · exact not_off_iff.mpr (hQ i)
  · exact Nat.pow_le_pow_left (by omega) q

end Catch

/-! ## 5. Tables over a subfield: (Dc6) -/

section Subfield

variable {F E ι κ : Type} [Field F] [Field E] [Algebra F E] [Fintype ι] [Fintype κ]
  {G : Matrix ι κ F} {e d : ℕ} {R : Type}

/-- A table over F that decodes over F decodes over E, to the same messages, read over E. -/
theorem DecodesTo.map {f : R → ι → F} {M : R → κ → F} (h : DecodesTo G e f M) :
    DecodesTo (G.map (algebraMap F E)) e (fun a => Code.liftWord E (f a))
      (fun a => Code.liftWord E (M a)) := by
  refine le_trans (cnt_mono ?_) h
  rintro j ⟨a, ha⟩
  refine ⟨a, fun hc => ha ?_⟩
  rw [Code.mulVec_map_liftWord]
  exact congrArg (algebraMap F E) hc

/-- Let φ be an F-linear map from E to F that is the identity on F. If a table over F decodes over E
to M, then it decodes over F to φ(M). -/
theorem DecodesTo.form {f : R → ι → F} {M : R → κ → E}
    (h : DecodesTo (G.map (algebraMap F E)) e (fun a => Code.liftWord E (f a)) M) (φ : E →ₗ[F] F)
    (hφ : ∀ x : F, φ (algebraMap F E x) = x) : DecodesTo G e f (fun a i => φ (M a i)) := by
  refine le_trans (cnt_mono ?_) h
  rintro j ⟨a, ha⟩
  refine ⟨a, fun hc => ha ?_⟩
  have h1 := congrArg φ hc
  rw [Code.form_mulVec_map] at h1
  rw [← h1]
  exact (hφ (f a j)).symm

/-- A table over F decodes over E if and only if it decodes over F. -/
theorem decodes_map_iff {f : R → ι → F} :
    Decodes (G.map (algebraMap F E)) e (fun a => Code.liftWord E (f a)) ↔ Decodes G e f := by
  obtain ⟨φ, hφ⟩ := Code.exists_form_algebraMap F E
  exact ⟨fun ⟨_, hM⟩ => ⟨_, hM.form φ hφ⟩, fun ⟨_, hM⟩ => ⟨_, hM.map⟩⟩

/-- The generator over E has the distance of the generator over F. -/
theorem HasDist.map (hd : HasDist G d) : HasDist (G.map (algebraMap F E)) d :=
  fun v hv => Code.dist_mulVec_map hd v hv

/-- (Dc6). Let `HasDist G d` and 2 e < d. If the rows of a table that decodes are over F, so are the
decoded messages; and the table decodes to them over F. -/
theorem DecodesTo.exists_liftWord (hd : HasDist G d) (h2 : 2 * e < d) {f : R → ι → F}
    {M : R → κ → E} (h : DecodesTo (G.map (algebraMap F E)) e (fun a => Code.liftWord E (f a)) M) :
    ∃ M₀ : R → κ → F, DecodesTo G e f M₀ ∧ M = fun a => Code.liftWord E (M₀ a) := by
  obtain ⟨φ, hφ⟩ := Code.exists_form_algebraMap F E
  exact ⟨_, h.form φ hφ, h.unique hd.map h2 (h.form φ hφ).map⟩

/-- (Dc6) for one row, under `HasDist G d` and 2 e < d: if one row of a table over E that decodes is
over F, then so is its message. -/
theorem DecodesTo.row_exists_liftWord (hd : HasDist G d) (h2 : 2 * e < d)
    {f : R → ι → E} {M : R → κ → E} (h : DecodesTo (G.map (algebraMap F E)) e f M)
    {a : R} {w : ι → F} (hw : f a = Code.liftWord E w) :
    ∃ m : κ → F, DecodesTo G e (fun _ : Unit => w) (fun _ => m) ∧ M a = Code.liftWord E m := by
  have h1 := h.row a
  rw [hw] at h1
  obtain ⟨M₀, hM₀, hM⟩ := DecodesTo.exists_liftWord hd h2 (f := fun _ : Unit => w) h1
  exact ⟨M₀ (), hM₀, congrFun hM ()⟩

/-- (Dc6) for the decoder, under `HasDist G d` and 2 e < d: decoding over E of a table over F is
decoding over F. -/
theorem dec_map (hd : HasDist G d) (h2 : 2 * e < d) (f : R → ι → F) :
    dec (G.map (algebraMap F E)) e (fun a => Code.liftWord E (f a)) =
      fun a => Code.liftWord E (dec G e f a) := by
  by_cases h : Decodes G e f
  · exact h.decodesTo_dec.map.dec_eq hd.map h2
  · rw [dec_of_not_decodes h, dec_of_not_decodes (fun hc => h (decodes_map_iff.mp hc))]
    funext a i
    exact (map_zero (algebraMap F E)).symm

end Subfield

/-! ## 6. Combinations and lines of tables that do not decode -/

section Far

variable {E ι κ : Type} [Field E] [Fintype ι] [Fintype κ] {G : Matrix ι κ E}
  {e bad : ℕ} {R I : Type}

/-- `Decodes` is closeness to the interleaved code, for the code that is the range of the generator
matrix. -/
theorem decodes_iff_close {f : R → ι → E} :
    Decodes G e f ↔ Code.Close (LinearMap.range G.mulVecLin) e f := by
  rw [Code.close_iff_cnt]
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨fun a => G.mulVec (M a), fun a => ⟨M a, rfl⟩, hM⟩
  · rintro ⟨g, hg, hfg⟩
    choose M hM using hg
    obtain rfl : (fun a => G.mulVec (M a)) = g := funext hM
    exact ⟨M, hfg⟩

/-- Combinations and lines, (ii). Under `Code.MCA` with the count `bad` (`hm`): if the two tables
f₀, f₁ do not decode together, then f₀ + ν f₁ decodes for at most `bad` values of ν. -/
theorem cnt_decodes_line [Finite E] [Finite R] (hm : Code.MCA (LinearMap.range G.mulVecLin) e bad)
    {f₀ f₁ : R → ι → E} (hf : ¬ Decodes G e (Sum.elim f₀ f₁)) :
    cnt (fun ν : E => Decodes G e fun a => f₀ a + ν • f₁ a) ≤ bad := by
  simp only [decodes_iff_close] at hf ⊢
  exact (hm.mcaFor R).cnt_close_line hf

variable [Fintype E] [Fintype I]

/-- Combinations and lines, (i), first assertion, for tables. Under `Code.MCA` with the count `bad`
(`hm`): if f₀ and the f_i, i ∈ I, do not decode together, then (number of a ∈ E^I such that f₀ + ∑
a_i f_i decodes) · (|E| - 1) ≤ bad · |E|^|I|. As a probability: (bad / |E|) (1 - 1/|E|)^(-1). -/
theorem cnt_decodes_one_comb_mul [Finite R] (hm : Code.MCA (LinearMap.range G.mulVecLin) e bad)
    {f₀ : R → ι → E} {f : I → R → ι → E}
    (hf : ¬ Decodes G e fun p : Option I × R => (p.1.elim f₀ f) p.2) :
    cnt (fun a : I → E => Decodes G e fun r => f₀ r + ∑ i, a i • f i r) * (Fintype.card E - 1) ≤
      bad * Fintype.card E ^ Fintype.card I := by
  simp only [decodes_iff_close] at hf ⊢
  exact (hm.mcaFor R).cnt_close_one_comb_mul hf

/-- `cnt_decodes_one_comb_mul` with the factor 2 in the place of (1 - 1/|E|)^(-1). -/
theorem cnt_decodes_one_comb_mul_two [Finite R] (hm : Code.MCA (LinearMap.range G.mulVecLin) e bad)
    {f₀ : R → ι → E} {f : I → R → ι → E}
    (hf : ¬ Decodes G e fun p : Option I × R => (p.1.elim f₀ f) p.2) :
    cnt (fun a : I → E => Decodes G e fun r => f₀ r + ∑ i, a i • f i r) * Fintype.card E ≤
      2 * bad * Fintype.card E ^ Fintype.card I := by
  simp only [decodes_iff_close] at hf ⊢
  exact (hm.mcaFor R).cnt_close_one_comb_mul_two hf

/-- Combinations and lines, (i), second assertion, for tables. Under `Code.MCA` with the count `bad`
(`hm`): if the f_i, i ∈ I, do not decode together, then (number of a ∈ E^I such that ∑ a_i f_i
decodes) · (|E| - 1) ≤ bad · |E|^|I|. -/
theorem cnt_decodes_comb_mul [Finite R] (hm : Code.MCA (LinearMap.range G.mulVecLin) e bad)
    {f : I → R → ι → E} (hf : ¬ Decodes G e fun p : I × R => f p.1 p.2) :
    cnt (fun a : I → E => Decodes G e fun r => ∑ i, a i • f i r) * (Fintype.card E - 1) ≤
      bad * Fintype.card E ^ Fintype.card I := by
  simp only [decodes_iff_close] at hf ⊢
  exact (hm.mcaFor R).cnt_close_comb_mul hf

/-- `cnt_decodes_comb_mul` with the factor 2 in the place of (1 - 1/|E|)^(-1). -/
theorem cnt_decodes_comb_mul_two [Finite R] (hm : Code.MCA (LinearMap.range G.mulVecLin) e bad)
    {f : I → R → ι → E} (hf : ¬ Decodes G e fun p : I × R => f p.1 p.2) :
    cnt (fun a : I → E => Decodes G e fun r => ∑ i, a i • f i r) * Fintype.card E ≤
      2 * bad * Fintype.card E ^ Fintype.card I := by
  simp only [decodes_iff_close] at hf ⊢
  exact (hm.mcaFor R).cnt_close_comb_mul_two hf

/-- Combinations and lines, (i), first assertion, for words. Under `Code.MCA` with the count `bad`
(`hm`): if the table (o₀, o_i : i ∈ I) does not decode, then the word o₀ + ∑ a_i o_i decodes for at
most a fraction (bad / |E|) (1 - 1/|E|)^(-1) of the a ∈ E^I. -/
theorem cnt_decodes_word_one_comb_mul (hm : Code.MCA (LinearMap.range G.mulVecLin) e bad)
    {o₀ : ι → E} {o : I → ι → E} (hf : ¬ Decodes G e fun x : Option I => x.elim o₀ o) :
    cnt (fun a : I → E => Decodes G e fun _ : Unit => o₀ + ∑ i, a i • o i) * (Fintype.card E - 1) ≤
      bad * Fintype.card E ^ Fintype.card I := by
  refine cnt_decodes_one_comb_mul (R := Unit) hm (f₀ := fun _ => o₀)
    (f := fun i _ => o i) fun hc => hf ?_
  have h1 := hc.comp fun x : Option I => (x, ())
  have h2 : (fun x : Option I => (Option.elim x (fun _ : Unit => o₀) fun i _ => o i) ()) =
      fun x : Option I => x.elim o₀ o := by
    funext x
    cases x <;> rfl
  rwa [h2] at h1

/-- `cnt_decodes_word_one_comb_mul` with the factor 2 in the place of (1 - 1/|E|)^(-1). -/
theorem cnt_decodes_word_one_comb_mul_two (hm : Code.MCA (LinearMap.range G.mulVecLin) e bad)
    {o₀ : ι → E} {o : I → ι → E} (hf : ¬ Decodes G e fun x : Option I => x.elim o₀ o) :
    cnt (fun a : I → E => Decodes G e fun _ : Unit => o₀ + ∑ i, a i • o i) * Fintype.card E ≤
      2 * bad * Fintype.card E ^ Fintype.card I := by
  rw [mul_assoc]
  exact Code.mul_le_two_mul_of_mul_pred_le Fintype.one_lt_card (cnt_decodes_word_one_comb_mul hm hf)

/-- Combinations and lines, (i), second assertion, for words. Under `Code.MCA` with the count `bad`
(`hm`): if the table (o_i : i ∈ I) does not decode, then the word ∑ a_i o_i decodes for at most a
fraction (bad / |E|) (1 - 1/|E|)^(-1) of the a ∈ E^I. -/
theorem cnt_decodes_word_comb_mul
    (hm : Code.MCA (LinearMap.range G.mulVecLin) e bad) {o : I → ι → E} (hf : ¬ Decodes G e o) :
    cnt (fun a : I → E => Decodes G e fun _ : Unit => ∑ i, a i • o i) * (Fintype.card E - 1) ≤
      bad * Fintype.card E ^ Fintype.card I :=
  cnt_decodes_comb_mul (R := Unit) hm (f := fun i _ => o i) fun hc =>
    hf (hc.comp fun i : I => (i, ()))

/-- `cnt_decodes_word_comb_mul` with the factor 2 in the place of (1 - 1/|E|)^(-1). -/
theorem cnt_decodes_word_comb_mul_two
    (hm : Code.MCA (LinearMap.range G.mulVecLin) e bad) {o : I → ι → E} (hf : ¬ Decodes G e o) :
    cnt (fun a : I → E => Decodes G e fun _ : Unit => ∑ i, a i • o i) * Fintype.card E ≤
      2 * bad * Fintype.card E ^ Fintype.card I := by
  rw [mul_assoc]
  exact Code.mul_le_two_mul_of_mul_pred_le Fintype.one_lt_card (cnt_decodes_word_comb_mul hm hf)

omit [Fintype E] [Fintype I] in
/-- Combinations and lines, (ii), for words. Under `Code.MCA` with the count `bad` (`hm`): if the
table (o₀, o₁) does not decode, then o₀ + ν o₁ decodes for at most `bad` values of ν. -/
theorem cnt_decodes_word_line [Finite E] (hm : Code.MCA (LinearMap.range G.mulVecLin) e bad)
    {o₀ o₁ : ι → E} (hf : ¬ Decodes G e fun b : Bool => if b then o₁ else o₀) :
    cnt (fun ν : E => Decodes G e fun _ : Unit => o₀ + ν • o₁) ≤ bad := by
  refine cnt_decodes_line (R := Unit) hm (f₀ := fun _ => o₀) (f₁ := fun _ => o₁) fun hc => hf ?_
  have h1 := hc.comp fun b : Bool => if b then Sum.inr () else Sum.inl ()
  have h2 : (fun b : Bool =>
        Sum.elim (fun _ : Unit => o₀) (fun _ : Unit => o₁) (if b then Sum.inr () else Sum.inl ())) =
      fun b : Bool => if b then o₁ else o₀ := by
    funext b
    cases b <;> rfl
  rwa [h2] at h1

end Far

/-! ## 7. Codes with encoder -/

section Interface

variable {F : Type} [Field F] {C : Code.Enc F} {E : Type} [Field E] [Algebra F E]

/-- The message part of a full message (the message parts form the decoded vector): its first `msg`
coordinates. (If the code had fewer coordinates than that, which the properties of a code with
encoder exclude, the missing ones would be read as 0.) -/
def msgPart (C : Code.Enc F) {K : Type} [Zero K] (v : Fin C.k → K) : Fin C.msg → K :=
  fun s => if h : (s : ℕ) < C.k then v ⟨s, h⟩ else 0

omit [Field F] in
/-- If msg + r ≤ k (`hp`), the message part of the full message that the encoder forms is the
message. -/
theorem msgPart_fm {K : Type} [Zero K] (hp : C.msg + C.r ≤ C.k)
    (m : Fin C.msg → K) (ρ : Fin C.r → K) : msgPart C (C.fm m ρ) = m := by
  funext s
  have hs : (s : ℕ) < C.k := lt_of_lt_of_le s.2 (le_trans (Nat.le_add_right _ _) hp)
  unfold msgPart
  rw [dif_pos hs]
  exact C.fm_msg m ρ s hs

omit [Field F] in
/-- The statements on the protocols write a message part as `nat v j`. This is the same. -/
theorem msgPart_eq_nat {K : Type} [Zero K] (v : Fin C.k → K) (s : Fin C.msg) :
    msgPart C v s = nat v s.val := rfl

omit [Field F] [Algebra F E] in
/-- The message part is linear. -/
theorem msgPart_comb {R : Type} [Fintype R] (c : R → E) (M : R → Fin C.k → E) :
    msgPart C (∑ a, c a • M a) = ∑ a, c a • msgPart C (M a) := by
  funext s
  unfold msgPart
  by_cases h : (s : ℕ) < C.k
  · simp only [dif_pos h, Finset.sum_apply, Pi.smul_apply]
  · simp only [dif_neg h, Finset.sum_apply, Pi.smul_apply, smul_zero, Finset.sum_const_zero]

/-- The message part of a full message over F, read over E. -/
theorem msgPart_liftWord (v : Fin C.k → F) :
    msgPart C (Code.liftWord E v) = Code.liftWord E (msgPart C v) := by
  funext s
  unfold msgPart Code.liftWord
  by_cases h : (s : ℕ) < C.k
  · simp only [dif_pos h]
  · simp only [dif_neg h, map_zero]

variable [Fintype F]

/-- If C has `Code.Enc.Props` (`h`), the generator over F has the distance of the code. -/
theorem hasDist_G [Finite E] (h : C.Props E) : HasDist C.G C.d := h.dist

/-- If C has `Code.Enc.Props` (`h`), the generator over E has the distance of the code. -/
theorem hasDist_GE [Finite E] (h : C.Props E) : HasDist (C.GE E) C.d := h.distE

/-- If C has `Code.Enc.Props` (`h`), the code over E has mutual correlated agreement on lines, in
the form in which section 6 of this file takes it as a hypothesis. -/
theorem mca_range_GE [Finite E] (h : C.Props E) :
    Code.MCA (LinearMap.range (C.GE E).mulVecLin) C.e C.mca :=
  (C.mca_iff (E := E) C.e C.mca).mp h.mca

omit [Fintype F] in
/-- An honest encoding decodes, at every radius, to the full messages that the encoder forms. -/
theorem decodesTo_encE {R : Type} (e : ℕ) (m : R → Fin C.msg → E) (ρ : R → Fin C.r → E) :
    DecodesTo (C.GE E) e (fun a => C.encE E (m a) (ρ a)) (fun a => C.fm (m a) (ρ a)) :=
  decodesTo_mulVec (C.GE E) e fun a => C.fm (m a) (ρ a)

/-- If C has `Code.Enc.Props` (`h`), the decoded vector of an honest encoding is the vector. -/
theorem msgPart_dec_encE [Finite E] (h : C.Props E) {R : Type} (m : R → Fin C.msg → E)
    (ρ : R → Fin C.r → E) (a : R) :
    msgPart C (dec (C.GE E) C.e (fun a => C.encE E (m a) (ρ a)) a) = m a := by
  rw [(decodesTo_encE C.e m ρ).dec_eq (hasDist_GE h) h.unique]
  exact msgPart_fm h.place (m a) (ρ a)

/-- Decoding, for a code with encoder that has the properties Code.Enc.Props. Words and tables are
over E, the radius is that of the code, n is the number of positions. -/
theorem lemma_E9 [Finite E] (h : C.Props E) :
    -- (Dc1) a table has at most one table of messages within the radius, and the generator is
    -- injective
    (∀ (R : Type) (f : R → Fin C.n → E) (M M' : R → Fin C.k → E),
      DecodesTo (C.GE E) C.e f M → DecodesTo (C.GE E) C.e f M' → M = M') ∧
    Function.Injective (C.GE E).mulVec ∧
    -- (Dc2) combinations and sub-tables of a table that decodes
    (∀ (R : Type) [Fintype R] (f : R → Fin C.n → E) (c : R → E), Decodes (C.GE E) C.e f →
      Decodes (C.GE E) C.e (fun _ : Unit => ∑ a, c a • f a) ∧
      dec (C.GE E) C.e (fun _ : Unit => ∑ a, c a • f a) () = ∑ a, c a • dec (C.GE E) C.e f a) ∧
    (∀ (R R' : Type) (f : R → Fin C.n → E) (σ : R' → R), Decodes (C.GE E) C.e f →
      Decodes (C.GE E) C.e (fun b => f (σ b)) ∧
      dec (C.GE E) C.e (fun b => f (σ b)) = fun b => dec (C.GE E) C.e f (σ b)) ∧
    -- (Dc3) a word that does not decode, or decodes to another message than a, differs from the
    -- codeword of a in more than e positions
    (∀ (o : Fin C.n → E) (a : Fin C.k → E),
      (¬ Decodes (C.GE E) C.e (fun _ : Unit => o) ∨ dec (C.GE E) C.e (fun _ : Unit => o) () ≠ a) →
      C.e < cnt (fun j => o j ≠ (C.GE E).mulVec a j)) ∧
    -- (Dc4) lists of q positions that miss a set of more than e positions
    (∀ (P : Fin C.n → Prop) (q : ℕ),
      C.e < cnt P → cnt (fun Q : Fin q → Fin C.n => ∀ i, ¬ P (Q i)) ≤ (C.n - C.e - 1) ^ q) ∧
    -- (Dc5) a word that is a row of two tables that decode
    (∀ (R R' : Type) (f : R → Fin C.n → E) (f' : R' → Fin C.n → E) (a : R) (a' : R'),
      Decodes (C.GE E) C.e f → Decodes (C.GE E) C.e f' → f a = f' a' →
      dec (C.GE E) C.e f a = dec (C.GE E) C.e f' a') ∧
    -- (Dc6) rows over F have messages over F
    (∀ (R : Type) (f : R → Fin C.n → F) (M : R → Fin C.k → E),
      DecodesTo (C.GE E) C.e (fun a => Code.liftWord E (f a)) M →
      ∃ M₀ : R → Fin C.k → F, DecodesTo C.G C.e f M₀ ∧ M = fun a => Code.liftWord E (M₀ a)) := by
  have hd := hasDist_GE h
  have h2 := h.unique
  refine ⟨fun R f M M' h1 h1' => h1.unique hd h2 h1',
    hd.injective h.d_pos,
    fun R _ f c hf => ⟨hf.comb c, dec_comb hd h2 hf c⟩,
    fun R R' f σ hf => ⟨hf.comp σ, dec_comp hd h2 hf σ⟩,
    ?_, ?_,
    fun R R' f f' a a' hf hf' hrow => dec_row_eq hd h2 hf hf' hrow,
    fun R f M hM => DecodesTo.exists_liftWord (hasDist_G h) h2 hM⟩
  · intro o a ho
    refine not_le.mp fun hc => ?_
    have h1 : DecodesTo (C.GE E) C.e (fun _ : Unit => o) (fun _ => a) := decodesTo_word_iff.mpr hc
    exact ho.elim (fun h3 => h3 ⟨_, h1⟩) fun h3 => h3 (congrFun (h1.dec_eq hd h2) ())
  · intro P q hP
    have h1 := cnt_miss_le_of_lt hP q
    rwa [Fintype.card_fin] at h1

/-- Combinations and lines, for a code with encoder that has the properties Code.Enc.Props. The
count of the code for lines is C.mca.
In (i) the bound ε (1 - 1/|E|)^(-1), with ε = C.mca / |E|, appears with all denominators cleared. -/
theorem lemma_E10 [Fintype E] (h : C.Props E) :
    (∀ (I : Type) [Fintype I] (o₀ : Fin C.n → E) (o : I → Fin C.n → E),
      ¬ Decodes (C.GE E) C.e (fun x : Option I => x.elim o₀ o) →
      cnt (fun a : I → E => Decodes (C.GE E) C.e fun _ : Unit => o₀ + ∑ i, a i • o i) *
          (Fintype.card E - 1) ≤
        C.mca * Fintype.card E ^ Fintype.card I) ∧
    (∀ (I : Type) [Fintype I] (o : I → Fin C.n → E), ¬ Decodes (C.GE E) C.e o →
      cnt (fun a : I → E => Decodes (C.GE E) C.e fun _ : Unit => ∑ i, a i • o i) *
          (Fintype.card E - 1) ≤
        C.mca * Fintype.card E ^ Fintype.card I) ∧
    (∀ o₀ o₁ : Fin C.n → E, ¬ Decodes (C.GE E) C.e (fun b : Bool => if b then o₁ else o₀) →
      cnt (fun ν : E => Decodes (C.GE E) C.e fun _ : Unit => o₀ + ν • o₁) ≤ C.mca) :=
  ⟨fun _ _ _ _ hf => cnt_decodes_word_one_comb_mul (mca_range_GE h) hf,
    fun _ _ _ hf => cnt_decodes_word_comb_mul (mca_range_GE h) hf,
    fun _ _ hf => cnt_decodes_word_line (mca_range_GE h) hf⟩

end Interface

end Blocks
