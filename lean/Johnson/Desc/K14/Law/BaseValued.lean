-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/BaseValued.lean: what a decoder of a stored table returns is base-valued, below
the code's distance: COROLLARIES OF ONE LEMMA, Cb.ldFc_overF (Cb/Ld/LdFoldEqCode.lean: "for e
below the distance, every member of the list of a table over F is over F"), at the format's own
generator matrix (OnBytes/Slice/CodeFacts.lean: rsCode, genOf_eq_GE, hasDist_rsCode).

  overF_genOf     that lemma at genOf C: every table of messages within e columns of a table
                  over the base field is over the base field, for e < 2 ^ a - (r + l) + 1.
  dec_overF       so what an index's decoder over genOf C (Cb/Ld/LdFoldEq.lean: LdIx.dec) returns at
                  such a table: by the decoder's own text: the view of a table within the radius.
  dcd_base        so what the decoder of a stored table with a record returns
                  (OnBytes/Slice/DecoderRec.lean: DecR.dcd): DecR's reading of a stored table IS the
                  up-cast of a table of base words, by Dec.up's text (rfl).
  dcd_base_full   so at every decoder frS.toDecR Z cut of the full size's written numbers
                  (OnBytes/Slice/FullRecLink.lean: a = 32, r + l = 446693375,
                  eM = 2852142980 < 3848273922): three comparisons, evaluated in Lean's kernel.
What is not claimed. Nothing at a radius from the distance on. Which member the decoder returns. No
soundness of a verifier.

-/
import OnBytes.Slice.CodeFacts
import OnBytes.Slice.LinkAtRec
import OnBytes.Slice.FullRecLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes.Slice Blocks

/-- **Cb.ldFc_overF at the format's generator matrix.** -/
theorem overF_genOf {R : Type} (C : Fmt.M1.Code) (ha : C.a ≤ 32) (hk : C.r + C.l ≤ 2 ^ C.a) (e : ℕ)
    (he : e < 2 ^ C.a - (C.r + C.l) + 1) (f₀ : R → Fin (2 ^ C.a) → GF)
    (M : R → Fin (C.r + C.l) → GE)
    (hM : DecodesTo (genOf C) e (fun a => Code.liftWord GE (f₀ a)) M) :
    ∃ M₀ : R → Fin (C.r + C.l) → GF, M = fun a => Code.liftWord GE (M₀ a) := by
  rw [genOf_eq_GE] at hM
  obtain ⟨M₀, -, h⟩ := Cb.ldFc_overF GF GE (rsCode C) e (hasDist_rsCode C ha hk) he R f₀ M hM
  exact ⟨M₀, h⟩

/-- **What an index's decoder over the format's code returns at a table over the base field.** -/
theorem dec_overF {J : Type} [Fintype J] (C : Fmt.M1.Code) (ha : C.a ≤ 32)
    (hk : C.r + C.l ≤ 2 ^ C.a) (X : Cb.LdIx GE (Fin (2 ^ C.a)) (Fin (C.r + C.l)) J)
    (hX : X.G = genOf C) (he : X.eM < 2 ^ C.a - (C.r + C.l) + 1)
    (f₀ : X.Row → Fin (2 ^ C.a) → GF) (rec : X.Rec) (U : X.Row × J → GE)
    (h : X.dec (fun a => Code.liftWord GE (f₀ a)) rec = some U) :
    ∀ n, ∃ b : GF, U n = algebraMap GF GE b := by
  unfold Cb.LdIx.dec Cb.Ood.decMinS Cb.Ood.decMin at h
  split at h
  · rename_i hex
    obtain ⟨M, hd, hv⟩ : ∃ M, DecodesTo X.G X.eM (fun a => Code.liftWord GE (f₀ a)) M ∧
        X.view M = U := ⟨hex.choose, hex.choose_spec.2, Option.some.inj h⟩
    rw [hX] at hd
    obtain ⟨M₀, rfl⟩ := overF_genOf C ha hk X.eM he f₀ M hd
    intro n
    rw [← hv]
    exact ⟨M₀ n.1 (X.pl n.2), rfl⟩
  · cases h

/-- **What the decoder of a stored table with a record returns is base-valued.** -/
theorem dcd_base (D : DecR) (ha : D.T.a ≤ 32) (hk : D.T.r + D.T.l ≤ 2 ^ D.T.a)
    (he : D.eM < 2 ^ D.T.a - (D.T.r + D.T.l) + 1) (y : D.toDec.Pos → Run.PQ.SgX) (r : D.Rec)
    (u : D.ix.Row × D.toDec.En → GE) (h : D.dcd y r = some u) :
    ∀ n, ∃ b : GF, u n = algebraMap GF GE b :=
  dec_overF D.T ha hk D.ix rfl he (fun r j => toF ((y j).2.getD (Sz.rowNo r) 0)) r u h

/-- **At the full size's written numbers.** -/
theorem dcd_base_full (Z : Cb.Ood.Sample GE frS.En) (cut : ℕ)
    (y : (frS.toDecR Z cut).toDec.Pos → Run.PQ.SgX) (r : (frS.toDecR Z cut).Rec)
    (u : (frS.toDecR Z cut).ix.Row × (frS.toDecR Z cut).toDec.En → GE)
    (h : (frS.toDecR Z cut).dcd y r = some u) : ∀ n, ∃ b : GF, u n = algebraMap GF GE b :=
  dcd_base (frS.toDecR Z cut)
    (show frS.P.T.a ≤ 32 by decide +kernel)
    (show frS.P.T.r + frS.P.T.l ≤ 2 ^ frS.P.T.a by decide +kernel)
    (show frS.eM < 2 ^ frS.P.T.a - (frS.P.T.r + frS.P.T.l) + 1 by decide +kernel) y r u h

end Desc.K14.Law
