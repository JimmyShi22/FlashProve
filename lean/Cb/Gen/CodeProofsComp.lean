-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/CodeProofsComp.lean: the proofs of the statements of Cb/Gen/Code.lean, second part, each
under the hypotheses of its statement: one component (what decoding means, decoding undoes
encoding, unique decoding, any b columns are uniform, hiding, the full code) and a complex (laws
and hiding, component by component).

The generic statements (pairs, families, parts) are proved in Cb/Gen/CodeProofs.lean.
Nothing is defined here that a statement reads. The lemmas before the theorems only say where
message and randomness stand in a full message, and unfold the decoder of a component, but for
`pmf_subsingleton`, `Comp.tab_enc` and `uniform_rows`.

Limits: this file says nothing beyond the `Cb.Spec` statements of Cb/Gen/Code.lean and the lemmas
before the theorems, and nothing on running times. On proximity gaps no theorem of this file
concludes anything, but that `full_props` hands the field `mca` on from its premise
(`mca := h.mca`).
Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.CodeProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Blocks Hiop

/-! ## Where message and randomness stand -/

section Parts
variable {F : Type} (C : Code.Enc F) {K : Type} [Zero K]

theorem msgPart_of_lt (v : Fin C.k → K) (s : Fin C.msg) (h : (s : ℕ) < C.k) :
    msgPart C v s = v ⟨s, h⟩ := dif_pos h

theorem rndPart_of_lt (v : Fin C.k → K) (t : Fin C.r) (h : C.msg + (t : ℕ) < C.k) :
    rndPart C v t = v ⟨C.msg + t, h⟩ := dif_pos h

/-- Under `hp`, the randomness part of the full message that the encoder forms is the randomness.
-/
theorem rndPart_fm (hp : C.msg + C.r ≤ C.k) (m : Fin C.msg → K) (ρ : Fin C.r → K) :
    rndPart C (C.fm m ρ) = ρ := by
  funext t
  have ht : C.msg + (t : ℕ) < C.k := by
    have := t.2
    omega
  rw [rndPart_of_lt C _ t ht]
  exact C.fm_rand m ρ t ht

/-- Under the full code the message part is the whole full message. -/
theorem msgPart_full (v : Fin C.k → K) (s : Fin C.k) : msgPart (fullCode C) v s = v s := dif_pos s.2

end Parts

/-- On a type with at most one element there is at most one law. -/
theorem pmf_subsingleton {α : Type} [Subsingleton α] (p q : PMF α) : p = q := by
  have key : ∀ (p : PMF α) (a : α), p a = 1 := fun p a => by
    have h := p.tsum_coe
    rwa [tsum_eq_single a fun b hb => absurd (Subsingleton.elim b a) hb] at h
  exact PMF.ext fun a => by rw [key p a, key q a]

section
variable {F : Type} [Field F] [Fintype F] {E : Type} [Field E] [Fintype E] [Algebra F E]

/-! ## The decoder of a component, unfolded -/

theorem Comp.dec_pos (c : Comp F) (y : (c.ext E).Str)
    (h : Decodes (c.code.GE E) c.code.e (c.tab y)) :
    (c.enc E).dec y =
      some (fun i j => Kf.ofE (msgPart c.code (dec (c.code.GE E) c.code.e (c.tab y) i) j),
        fun i t => Kf.ofE (rndPart c.code (dec (c.code.GE E) c.code.e (c.tab y) i) t)) := if_pos h

theorem Comp.dec_neg (c : Comp F) (y : (c.ext E).Str)
    (h : ¬ Decodes (c.code.GE E) c.code.e (c.tab y)) : (c.enc E).dec y = none := if_neg h

/-- Read in E, an encoding is the table of the codewords of the full messages that the encoder
forms. -/
theorem Comp.tab_enc (c : Comp F) (m : c.Msg E) (r : c.Rnd E) :
    c.tab ((c.enc E).enc m r) =
      fun i => (c.code.GE E).mulVec (c.code.fm (fun j => (m i j).toE) fun t => (r i t).toE) :=
  funext fun i => funext fun p => toE_encK c.code (m i) (r i) p

/-- Under `hC`: any b columns of a table of encodings are uniform, over the field of the rows. -/
theorem uniform_rows {C : Code.Enc F} (hC : C.Props E) {R : Type} [Fintype R] [DecidableEq R] :
    ∀ (b : Bool) (S : Finset (Fin C.n)), S.card ≤ C.b →
      ∀ m : R → Fin C.msg → Kf F E b,
        (unif (R → Fin C.r → Kf F E b)).map (fun ρ => fun (j : S) (a : R) => encK C (m a) (ρ a) j) =
          unif (S → R → Kf F E b)
  | true, S, hS, m => hC.hides_table S hS m
  | false, S, hS, m => hC.hidesE_table S hS m

end

/-! ## The statements -/

section
variable (F : Type) [Field F] [Fintype F] (E : Type) [Field E] [Fintype E] [Algebra F E]

theorem comp_dec_iff : Spec.comp_dec_iff F E := by
  intro c hc y m r
  constructor
  · intro h
    by_cases hd : Decodes (c.code.GE E) c.code.e (c.tab y)
    · rw [c.dec_pos y hd] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨_, hd.decodesTo_dec, fun i j => toE_ofE_of_decodes hc y _ hd.decodesTo_dec i j.val,
        fun i t => toE_ofE_of_decodes hc y _ hd.decodesTo_dec i (c.code.msg + t.val)⟩
    · rw [c.dec_neg y hd] at h
      exact absurd h (by simp)
  · rintro ⟨M, hM, h1, h2⟩
    rw [c.dec_pos y ⟨M, hM⟩, hM.dec_eq (hasDist_GE hc) hc.unique]
    refine congrArg some
      (Prod.ext (funext fun i => funext fun j => ?_) (funext fun i => funext fun t => ?_))
    · show Kf.ofE (msgPart c.code (M i) j) = m i j
      rw [← h1, Kf.ofE_toE]
    · show Kf.ofE (rndPart c.code (M i) t) = r i t
      rw [← h2, Kf.ofE_toE]

theorem comp_close : Spec.comp_close F E := by
  intro c hc y m r h
  refine (comp_dec_iff F E c hc y m r).2 ⟨fun i =>
      c.code.fm (fun j => (m i j).toE) fun t => (r i t).toE,
    le_trans (cnt_mono ?_) h,
    fun i j => (congrFun (msgPart_fm hc.place (fun j => (m i j).toE) fun t => (r i t).toE) j).symm,
    fun i t =>
      (congrFun (rndPart_fm c.code hc.place (fun j => (m i j).toE) fun t => (r i t).toE) t).symm⟩
  rintro p ⟨i, hi⟩ hp
  refine hi ?_
  show (y p i).toE = _
  rw [hp]
  exact toE_encK c.code (m i) (r i) p

theorem comp_laws : Spec.comp_laws F E := fun c hc => ⟨fun m r => comp_close F E c hc _ m r (by
  rw [cnt_false fun p hp => hp rfl]
  exact Nat.zero_le _)⟩

theorem comp_uniform : Spec.comp_uniform F E := fun c hc S hS m => uniform_rows hc c.overF S hS m

theorem comp_hides : Spec.comp_hides F E := fun c hc S hS m m' =>
  (comp_uniform F E c hc S hS m).trans (comp_uniform F E c hc S hS m').symm

theorem full_props : Spec.full_props F E := fun C h =>
  { place := le_refl C.k
    dist := h.dist
    unique := h.unique
    mca := h.mca
    hides := fun S hS m => by
      obtain rfl : S = ∅ := Finset.card_eq_zero.1 (Nat.eq_zero_of_le_zero hS)
      exact pmf_subsingleton _ _ }

theorem comp_full : Spec.comp_full F E := by
  intro c hc y
  by_cases hd : Decodes (c.code.GE E) c.code.e (c.tab y)
  · rw [c.dec_pos y hd, c.full.dec_pos y hd]
    refine congrArg some
      (Prod.ext (funext fun i => funext fun j => ?_) (funext fun i => funext fun t => ?_))
    · have hj : (j : ℕ) < c.code.k := by
        have := j.2
        have := hc.place
        omega
      show Kf.ofE (msgPart c.code (dec (c.code.GE E) c.code.e (c.tab y) i) j) =
        msgPart c.code
          (fun s : Fin c.code.k =>
            (Kf.ofE (msgPart (fullCode c.code)
                (dec (c.code.GE E) c.code.e (c.tab y) i) s) : Kf F E c.overF)) j
      rw [msgPart_of_lt c.code _ j hj, msgPart_of_lt c.code _ j hj, msgPart_full]
    · have ht : c.code.msg + (t : ℕ) < c.code.k := by
        have := t.2
        have := hc.place
        omega
      show Kf.ofE (rndPart c.code (dec (c.code.GE E) c.code.e (c.tab y) i) t) =
        rndPart c.code
          (fun s : Fin c.code.k =>
            (Kf.ofE (msgPart (fullCode c.code)
                (dec (c.code.GE E) c.code.e (c.tab y) i) s) : Kf F E c.overF)) t
      rw [rndPart_of_lt c.code _ t ht, rndPart_of_lt c.code _ t ht, msgPart_full]
  · rw [c.dec_neg y hd, c.full.dec_neg y hd]
    rfl

theorem cx_laws : Spec.cx_laws F E := fun K h =>
  laws_fam K.A _ _ fun a => comp_laws F E (K.comp a) (h a)

theorem cx_hides : Spec.cx_hides F E := fun K h =>
  hides_fam K.A _ _ _ fun a => comp_hides F E (K.comp a) (h a)

end
end Cb
