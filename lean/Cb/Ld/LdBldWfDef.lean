-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldWfDef.lean: weights-formedness is the sub-protocol for the relation that an encoded index
is the encoding of a message that holds an index. Of the conditions on its data, as the builder
makes them (Cb/Ld/LdBldWf.lean, Cb/Ld/LdBldWfSpec.lean), this file has the clauses that hold by the
definitions and by numbers.

The sub-protocol uses lookups: for each forest f its data have keys `X.key f U`, computed from the
message U of the encoded index, and a table `X.tab f`; the prover's messages contain vectors of
multiplicities, in binary digits. `X : BldWf F E Fp` (Cb/Ld/LdBldWf.lean) has the builder's
parameters, `X.Room p` (Cb/Ld/LdBldWfSpec.lean) its conditions, and `(X.Zw hpl).Rest2 p`
(Cb/Ld/LdWfEnd.lean) is a record of conditions on the data that the builder makes.
`X.P.InT f U` says that every key of forest f is an entry of its table. `Valid n T w W key t M`
(Cb/Ld/LdLkpMult.lean) says that the entries M u j with u < 2^T and j < 2^w are bits, 0 at the
positions j from W on, and that for every value x the numbers that the bits of the table entries u
with t u = x write add up to the number of keys b < 2^n with key b = x.
Theorems bldWfD_<field>, one for each of these fields of `(X.Zw hpl).Rest2 p`: val, lin, lks.v,
lks.adm, lks.rows, lks.mult, deg, zOK, fair, multOf, tie; and, of the six clauses on the standard
sender's data, for wfStd, wfBody, wfBd, wfAtB, wfNoPad. Each under `X.Room p` or less; the last five
take `hpl : X.Hpl`, the others are stated in the builder's own terms (`X.P`, `X.W`, `X.K`), to which
the fields of `X.Zw hpl` reduce. Generic: any finite fields, any number of forests. Nothing assumed
beyond the hypotheses of the statements and whatever the arguments hold as proofs.

Main names (for forests f ≤ `X.P.n`):
  `bldWfD_val`: there is an encoded index (`X.Cf.conf.E0.Str` is not empty).
  `bldWfD_lin`: the key maps are affine in the columns of the index's matrix: five families of
    equations, by definition.
  `bldWfD_v`, `bldWfD_adm`, both under `h : X.Room p`, and `bldWfD_rows`: the lookups' numbers:
    rv + k = v' + 1 (by the field pos of `X.Room`: every forest has a key variable); the three
    conditions on numbers (from the field adm of `X.Room`); the number of rows filed.
  `bldWfD_mult`: under `h : X.Room p`, "the digits at their places write a valid vector" for `X.key`
    ⇒ the assembled lookup's exact clause at the tuple (message of the index, messages).
  `bldWfD_multOf`: under `h : X.Room p`, the keys of forest f lie in its table ⇒ the honest data
    hold a valid vector.
  `bldWfD_tie`: `X.mat U` is the index matrix of U in the layout of the encoded index.

Limits: this file does not say the clauses on places (Cb/Ld/LdBldWfPlace.lean). "describes" is a
field of `X.Room`. This file does not say that `X.Room p` can be met.


Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBldWfSpec
import Cb.Ld.LdWfKeys
import Cb.Ld.LdWfBlocksProofs
import Cb.Part.LdPartLkpProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp Cb.Lkp Finset

/-- `Valid` (Cb/Ld/LdLkpMult.lean) reads the keys below 2^n only. -/
theorem bldWfD_validKeys {E : Type} [Field E] {n T w W : ℕ} {ky ky' t : ℕ → E} {M : ℕ → ℕ → E}
    (h : ∀ b < 2 ^ n, ky b = ky' b) (hv : Valid n T w W ky t M) : Valid n T w W ky' t M := by
  classical
  refine ⟨hv.1, hv.2.1, fun x => ?_⟩
  rw [hv.2.2 x]
  exact congrArg Finset.card (filter_congr fun b hb => by rw [h b (mem_range.1 hb)])

section
variable {F E Fp : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
  [Fintype Fp] [Algebra Fp E] (X : BldWf F E Fp)

theorem bldWfD_val : Nonempty X.Cf.conf.E0.Str := ⟨X.Cf.conf.enc X.p0.1.1 X.p0.1.2⟩

theorem bldWfD_lin : X.P.LinKeys X.rv X.o X.co :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem bldWfD_v {p : ℕ} (h : X.Room p) : ∀ f, f ≤ X.P.n → X.P.v f = X.K.v' f + 1 := by
  intro f hf
  have h1 := h.pos f hf
  show X.rv f + X.num.k = X.rv f + X.num.k - 1 + 1
  omega

theorem bldWfD_adm {p : ℕ} (h : X.Room p) : ∀ f, f ≤ X.P.n → (X.K.asm f).H.lkb.Adm p := by
  intro f hf
  obtain ⟨a1, a2, a3⟩ := h.adm f hf
  refine ⟨a1, ?_, a3⟩
  show 2 ^ (X.K.v' f + 1) < 2 ^ (X.nd f + 1)
  rw [← bldWfD_v X h f hf]
  exact a2

theorem bldWfD_rows : ∀ f, f ≤ X.P.n → X.P.nR f = (X.K.asm f).nRows := fun _ _ => rfl

/-- For f ≤ `X.P.n` and b < 2^(rv + k), the lookup's own key (public constant plus tensor form at a
corner, `X.P.keyE`) is `X.key`. -/
theorem bldWfD_key (f : ℕ) (hf : f ≤ X.P.n) (U : X.Cf.conf.Msg) (b : ℕ) (hb : b < 2 ^ X.P.v f) :
    X.key f U b = X.P.keyE f (X.mat U) b := by
  have h := ldWfK_keyLin E X.Cf.conf X.P X.rv X.o X.co (bldWfD_lin X) f hf U (X.P.cz (X.P.v f) b)
  have e : Blocks.ext (X.P.v f) (X.P.key f U) (X.P.cz (X.P.v f) b) = X.P.key f U b := by
    show Blocks.ext (X.P.v f) (X.P.key f U) (Blocks.nat (Alg.corner (Alg.bits (X.P.v f) b))) = _
    rw [Cb.Req.ext_nat E (X.P.v f) (X.P.key f U) (Alg.corner (Alg.bits (X.P.v f) b)),
      Alg.mle_corner, Alg.num_bits hb]
  exact e.symm.trans h

theorem bldWfD_mult {p : ℕ} (h : X.Room p) :
    ∀ f, f ≤ X.P.n →
      ∀ (st : X.P.WSt) (U : X.Cf.conf.Msg) (m : X.P.S.Msg),
        X.P.mult f U (X.P.body m) → (X.K.asm f).ValidMu st (X.P.msg (U, m)) := by
  intro f hf st U m hm
  have hm' : Valid (X.P.v f) (X.d f) (X.w f) (X.nd f + 1) (X.key f U)
      (X.tab f) (X.bitOf (X.Y.dataOf m) f) := hm
  show Valid (X.K.v' f + 1) (X.d f) (X.w f) (X.nd f + 1) (X.P.keyE f (X.mat U))
    (X.tab f) (X.bitOf (X.Y.dataOf m) f)
  rw [← bldWfD_v X h f hf]
  exact bldWfD_validKeys (fun b hb => bldWfD_key X f hf U b hb) hm'

theorem bldWfD_deg : 2 ≤ X.P.deg := le_refl 2

theorem bldWfD_zOK {p : ℕ} (h : X.Room p) : X.P.Z.OK := h.zOK

theorem bldWfD_fair {p : ℕ} (h : X.Room p) : X.P.Sd.Fair := h.fair

/-- The name of a digit inside the ranges: for f ≤ `X.n`, u < 2^(d f) and j < 2^(w f),
`X.bitB f u j` is the digit (f, u, j) itself. -/
theorem bldWfD_bitB {f u j : ℕ} (hf : f ≤ X.n) (hu : u < 2 ^ X.d f) (hj : j < 2 ^ X.w f) :
    X.bitB f u j = ⟨⟨f, hf⟩, (⟨u, hu⟩, ⟨j, hj⟩)⟩ := by
  unfold BldWf.bitB
  rw [dif_pos hf]
  congr 1
  exact Prod.ext (Fin.ext (Nat.mod_eq_of_lt hu)) (Fin.ext (Nat.mod_eq_of_lt hj))

/-- The honest datum at the place of a digit: under `hi` (the placing `X.pB` is injective), the
honest data `X.bodyOf U` have, at the place `X.pB b` of a digit b, the honest digit `hbit` of b. -/
theorem bldWfD_body (hi : Function.Injective X.pB) (U : X.Cf.conf.Msg) (b : X.num.Bit) :
    X.bodyOf U (X.pB b).1 (X.pB b).2 =
      hbit (X.rv b.1.1 + X.num.k) (X.nd b.1.1 + 1) (X.key b.1.1 U) (X.tab b.1.1) b.2.1 b.2.2 := by
  have hex : ∃ b' : X.num.Bit, X.pB b' = ⟨(X.pB b).1, (X.pB b).2⟩ := ⟨b, rfl⟩
  unfold BldWf.bodyOf
  rw [dif_pos hex]
  have e : hex.choose = b := hi hex.choose_spec
  rw [e]

theorem bldWfD_multOf {p : ℕ} (h : X.Room p) :
    ∀ U f, f ≤ X.P.n → X.P.InT f U → X.P.mult f U (X.P.bodyOf U) := by
  intro U f hf hin
  obtain ⟨a1, a2, _⟩ := h.adm f hf
  show Valid (X.rv f + X.num.k) (X.d f) (X.w f) (X.nd f + 1) (X.key f U)
    (X.tab f) (X.bitOf (X.bodyOf U) f)
  refine ldPartLk_validBits E a1 (fun u hu j hj => ?_)
    (ldLkpMult_honest E (X.rv f + X.num.k) (X.d f) (X.w f) (X.nd f + 1)
      (X.key f U) (X.tab f) a2 hin)
  show X.bodyOf U (X.pB (X.bitB f u j)).1 (X.pB (X.bitB f u j)).2 = _
  rw [bldWfD_body X h.injB U, bldWfD_bitB X hf hu hj]

theorem bldWfD_tie : X.W.Tie := by
  intro U r c
  show X.Cf.upM U (fun i => c (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i))),
      Sum.inl (X.lay (r, fun i => c (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i)))))) = _
  simp only [Equiv.symm_apply_apply]
  rfl

/-! ### The standard sender's data -/

theorem bldWfD_wfStd (hpl : X.Hpl) :
    (⟨(X.Zw hpl).D, (X.Zw hpl).X⟩ : Σ D, (X.Zw hpl).K.MaskPl D (X.Zw hpl).Rl) =
      ⟨(X.Zw hpl).W.P.stdD (X.V hpl).Y (X.V hpl).dat (X.V hpl).w0,
        @LdWfP.Lks.stdX E _ _ _ _ (X.Zw hpl).K Fp _ _ _ (X.Zw hpl).Rl X.finWfI (X.V hpl).Y
          (X.V hpl).dat (X.V hpl).w0 (X.V hpl).nAt (X.V hpl).RdW (X.V hpl).atL
          (X.V hpl).pl (X.V hpl).hpl⟩ := rfl

theorem bldWfD_wfBody (hpl : X.Hpl) :
    ∀ m, (X.Zw hpl).W.P.body m = (X.V hpl).bd ((X.V hpl).Y.dataOf m) := fun _ => rfl

theorem bldWfD_wfBd (hpl : X.Hpl) : ∀ b, (X.V hpl).bd ((X.V hpl).dat b) = b := fun _ => rfl

theorem bldWfD_wfAtB (hpl : X.Hpl) :
    ∀ i, (X.V hpl).nAt ((X.Zw hpl).W.P.wAt i) = (X.V hpl).Y.entF ((X.V hpl).pl none i) :=
  fun _ => rfl

theorem bldWfD_wfNoPad (hpl : X.Hpl) : ∀ n, (X.V hpl).RdW n → (X.V hpl).Y.NoPad n := fun _ h => h

end
end Cb
