-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/Halves.lean: the plain statements of Johnson/Meaning/Says.lean cut in two: what the
24 sub-proofs of the layers must say, and what the output head's sub-proof must say.

The two halves meet in one family of integers: the stream behind the last layer.
  SaysLayers pp w x S   the first five clauses of Says: the stream S begins as the embedding of the
                        request's tokens, and each of the 48 layers' two blocks runs on it and
                        yields its next index. It reads of the request the 1,024 tokens alone.
  SaysHead nf pol H x X the last three clauses, of a last stream X and an output matrix H: the final
                        normalisation runs on X; the request has its form; the policy's three
                        clauses hold of the logits, logit t v = Σ_j NORM.out(X t) j * H j v.

Main theorems:
  says_iff_halves: Says is the two halves, joined at X = S (2 * layers) and H = w.H.
  says_of_halves: the same where the head's sub-proof holds a copy X of the last stream: it is
    enough that X agrees with S (2 * layers) at the positions below T and the coordinates below d,
    and that H agrees with w.H at the rows below d.
  last_bound: where the final normalisation runs, every coordinate of the last stream is below 2^39
    in absolute value. (The library's statement on the layers alone, Cm/TargetPLayers.lean, asks
    this bound of a head.)

What is not claimed: as in Johnson/Meaning/Says.lean.
-/
import Johnson.Meaning.Says

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model Inst.Model.All

/-- The logits that a last stream X and an output matrix H give. -/
def logitAt (nf : NormPar) (H : Mat) (X : ℕ → Vec) (pos ι : ℕ) : ℤ :=
  dot ppref.d (NORM.out nf ppref.d (X pos)) fun j => H j ι

/-- **What the layers' sub-proofs must say.** -/
structure SaysLayers (pp : ScalesAndPolicy) (w : Weights) (x : Instance ppref) (S : ℕ → ℕ → Vec) : Prop where
  emb : ∀ pos (h : pos < ppref.T), ∀ j < ppref.d, S 0 pos j = w.Emb (x.prompt ⟨pos, h⟩) j
  attOK : ∀ L < ppref.layers, Att.OK (ppref.at (pp.kap L)) tbRef (w.layer L) L (S (2 * L))
  att : ∀ L < ppref.layers,
    Agree ppref (S (2 * L + 1)) (Att.x' (ppref.at (pp.kap L)) tbRef (w.layer L) L (S (2 * L)))
  ffOK : ∀ L < ppref.layers, FF.OK (ppref.at (pp.kap L)) tbRef (w.layer L) L (S (2 * L + 1))
  ff : ∀ L < ppref.layers,
    Agree ppref (S (2 * L + 2)) (FF.x'' (ppref.at (pp.kap L)) tbRef (w.layer L) L (S (2 * L + 1)))

/-- **What the output head's sub-proof must say**, of the last stream X and the output matrix H. -/
structure SaysHead (nf : NormPar) (pol : AcceptancePolicy) (H : Mat) (x : Instance ppref) (X : ℕ → Vec) :
    Prop where
  normOK : ∀ pos < ppref.T, NORM.OK nf ppref.d (X pos)
  form : Head3 x
  policy : PolOK (logitAt nf H X) pol x

variable {pp : ScalesAndPolicy} {w : Weights} {x : Instance ppref} {S : ℕ → ℕ → Vec}

/-- **Says is the two halves.** -/
theorem says_iff_halves :
    Says pp w x S ↔
      SaysLayers pp w x S ∧ SaysHead pp.nf pp.pol w.H x (S (2 * ppref.layers)) :=
  ⟨fun H => ⟨⟨H.emb, H.attOK, H.att, H.ffOK, H.ff⟩, ⟨H.normOK, H.form, H.policy⟩⟩,
    fun H => ⟨H.1.emb, H.1.attOK, H.1.att, H.1.ffOK, H.1.ff, H.2.normOK, H.2.form, H.2.policy⟩⟩

/-- The head's half reads the stream and the output matrix inside their ranges alone. -/
theorem SaysHead.congr {nf : NormPar} {pol : AcceptancePolicy} {H H' : Mat} {X X' : ℕ → Vec}
    (hX : Agree ppref X X') (hH : ∀ j < ppref.d, ∀ v, H j v = H' j v)
    (A : SaysHead nf pol H x X) : SaysHead nf pol H' x X' where
  normOK pos hp := (norm_OK nf fun k hk => hX pos hp k hk).1 (A.normOK pos hp)
  form := A.form
  policy := polOK_congr (fun t ht => funext fun v => by
    unfold logitAt dot
    exact Finset.sum_congr rfl fun j hj => by
      rw [norm_out nf (fun k hk => hX t ht k hk) (Finset.mem_range.1 hj)]
      show _ * H j v = _ * H' j v
      rw [hH j (Finset.mem_range.1 hj) v]) A.policy

/-- **The two halves, where the head holds a copy of the last stream.** -/
theorem says_of_halves {H : Mat} {X : ℕ → Vec} (L : SaysLayers pp w x S)
    (A : SaysHead pp.nf pp.pol H x X) (hX : Agree ppref X (S (2 * ppref.layers)))
    (hH : ∀ j < ppref.d, ∀ v, H j v = w.H j v) : Says pp w x S :=
  says_iff_halves.2 ⟨L, A.congr hX hH⟩

/-- **Where the final normalisation runs, the last stream is below 2^39.** -/
theorem last_bound {nf : NormPar} (h0 : 0 ≤ nf.eps) {X : ℕ → Vec}
    (A : ∀ pos < ppref.T, NORM.OK nf ppref.d (X pos)) :
    ∀ i < ppref.T, ∀ j < ppref.d, |X i j| < 2 ^ 39 := by
  intro i hi j hj
  have h1 : NORM.V ppref.d (X i) + nf.eps < 2 ^ 78 := (A i hi).1
  have h2 : X i j ^ 2 ≤ NORM.V ppref.d (X i) :=
    Finset.single_le_sum (f := fun k => X i k ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_range.2 hj)
  have h3 : X i j ^ 2 < (2 ^ 39 : ℤ) ^ 2 := by
    have e : ((2 : ℤ) ^ 39) ^ 2 = 2 ^ 78 := by norm_num
    rw [e]
    omega
  exact abs_lt_of_sq_lt_sq h3 (by norm_num)

end Meaning

#print axioms Meaning.says_iff_halves
#print axioms Meaning.says_of_halves
#print axioms Meaning.last_bound
