-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/CodeOnto.lean: for a code with `Code.Enc.Props`, where message and randomness fill the
dimension, "decoding in the whole code" is "decoding in the image of the encoder".

Statement and proof. A component (`Comp`, Cb/Gen/Code.lean) has interleaved rows under one code
with encoder (`Code.Enc`, Code/Iface.lean), with the radius e. The encoder applies the generator to
a vector of length k (the dimension): msg coordinates of message, then r of randomness, then zeros.

Cb/Gen/Code.lean decodes a component in the whole code: a word decodes if it is within e columns of
codewords of any vectors of length k, and message and randomness are read off these vectors
(`Spec.comp_dec_iff`). A print of this protocol's technical report (lean/CREDITS.md)
decodes in the IMAGE OF THE ENCODER: a word decodes if it is within the radius of an ENCODING.
The two differ only if the generator has coordinates beyond message and randomness (msg + r < k).

Main names:
  `Spec.comp_dec_onto`: for a component c with `c.code.Props E` and msg + r = k,
    dec y = some (m, ρ) if and only if y differs from the encoding of m under ρ in at most e
    symbols (columns).

So for such components the declared difference "decoding in the whole code" (the head of
Cb/Gen/Code.lean) is empty.

Limits: for the encoded index "message" is here all coordinates before the randomness, also the
places between the entries of an index and the randomness, which an honest encoder fills with zeros
(the head of Cb/Gen/Code.lean). That difference is not touched by this file.
Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.CodeProofsComp

set_option autoImplicit false

namespace Cb
open Iop Prob Blocks Hiop

/-- If msg + r = k, every vector of length k is the full message that the encoder forms
(`Code.Enc.fm`) of its two parts (`msgPart`, `rndPart`). -/
theorem fm_parts {F : Type} [Field F] (C : Code.Enc F) (h : C.msg + C.r = C.k) {K : Type}
    [Zero K] (v : Fin C.k → K) :
    C.fm (msgPart C v) (rndPart C v) = v := by
  funext i
  unfold Code.Enc.fm
  have hi := i.isLt
  split_ifs with h1 h2
  · show (if h : i.val < C.k then v ⟨i.val, h⟩ else 0) = v i
    rw [dif_pos hi]
  · show nat v (C.msg + (i.val - C.msg)) = v i
    have e : C.msg + (i.val - C.msg) = i.val := by omega
    rw [e]
    show (if h : i.val < C.k then v ⟨i.val, h⟩ else 0) = v i
    rw [dif_pos hi]
  · omega

namespace Spec
variable (F : Type) [Field F] [Fintype F] (E : Type) [Field E] [Fintype E] [Algebra F E]

/-- Decoding in the image of the encoder. -/
def comp_dec_onto : Prop :=
  ∀ c : Comp F, c.code.Props E → c.code.msg + c.code.r = c.code.k →
    ∀ (y : (c.ext E).Str) (m : c.Msg E) (r : c.Rnd E),
      (c.enc E).dec y = some (m, r) ↔ cnt (fun p => y p ≠ (c.enc E).enc m r p) ≤ c.code.e

end Spec

variable (F : Type) [Field F] [Fintype F] (E : Type) [Field E] [Fintype E] [Algebra F E]

theorem comp_dec_onto : Spec.comp_dec_onto F E := by
  intro c hc hk y m r
  refine ⟨fun h => ?_, comp_close F E c hc y m r⟩
  obtain ⟨M, hM, h1, h2⟩ := (comp_dec_iff F E c hc y m r).1 h
  have hfm : ∀ i, c.code.fm (fun j => (m i j).toE) (fun t => (r i t).toE) = M i := fun i => by
    rw [← fm_parts c.code hk (M i)]
    congr 1
    · exact funext fun j => h1 i j
    · exact funext fun t => h2 i t
  refine le_trans (cnt_mono fun p hp => ?_) hM
  by_contra hoff
  refine hp (funext fun i => ?_)
  have h3 : (y p i).toE = (c.code.GE E).mulVec (M i) p := by
    by_contra hne
    exact hoff ⟨i, hne⟩
  have h4 : (((c.enc E).enc m r) p i).toE = (c.code.GE E).mulVec (M i) p := by
    rw [← hfm i]
    exact toE_encK c.code (m i) (r i) p
  rw [← Kf.ofE_toE (y p i), ← Kf.ofE_toE (((c.enc E).enc m r) p i), h3, h4]

end Cb
