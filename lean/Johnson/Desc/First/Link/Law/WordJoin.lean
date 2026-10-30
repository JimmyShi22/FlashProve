-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/WordJoin.lean: THE TEXT's FOLDED SYMBOLS AND THE TYPED FOLDED WORD,
JOINED AT ONE NATIVE POSITION: the four sorts of symbol of the folded complex with kept slots (main
row · kept rows · carried mask · fresh mask), each as the reading in the field of what the text lays
(LongText.lean), FROM WHAT STANDS IN THE TEXT's TABLES AGAINST WHAT `view` SHOWS. General in the
group R. Theorems. No text already in the library turns.

  `cube_join`: ∑ over the cube of eqk * ‹what the row at the vertex b holds› is ∑ over the numbers
    below 2 ^ k of eqW * ‹the table's entry›, where the table holds at rowNo b what the vertex b's
    row holds, and 0 where it has none (by `sum_rowNo`, `eqW_rowNo`).
  `main_symbol`: **the folded word's main row at p = readE ((foldLow T gamma)[0])**, where T has
    2 ^ (h + g) entries and holds at rowNo b what `view` shows of the row `ord b`, 0 where there is
    none. `mask_symbol`: the like for the carried mask, at gamma's first h and `ordZ`.
    `fresh_symbol`: the like for the fresh mask: where the mask's word z holds at (b, x) the table's
    entry number rowNo b. `kept_symbol`: the folded word's slot κ is what `view` shows of the kept
    row κ (the weights add up to 1).
Limits. The premises on the tables are LongTables.lean's matter (the main table; the layout's first
rows must be R.oM) and `view`'s (what it shows of a member's own word): not paid here. Nothing on
soundness.
-/
import Johnson.Desc.First.Link.Law.ArrangedWord
import Johnson.Desc.First.Link.Law.LongText

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice Cb Iop IOR Johnson.Top.H
open VerifiableInference.Desc.First.Close (foldedAt)

/-- A sum over the cube against a sum over a table. -/
theorem cube_join {ρ : Type} (k : ℕ) (z : ℕ → GE) (T : Array E)
    (at' : (Fin k → Bool) → Option ρ) (sym : ρ → GE)
    (h1 : ∀ b r, at' b = some r → readV T (Sz.rowNo b) = sym r)
    (h0 : ∀ b, at' b = none → readV T (Sz.rowNo b) = 0) :
    (∑ b : Fin k → Bool, Alg.eqk (fun t : Fin k => z t.val) b * (at' b).elim 0 sym) =
      ∑ i ∈ Finset.range (2 ^ k), eqW k z i * readV T i := by
  rw [← sum_rowNo k fun i => eqW k z i * readV T i]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [eqW_rowNo]
  congr 1
  cases e : at' b with
  | none => exact (h0 _ e).symm
  | some r => exact (h1 _ r e).symm

section
variable {S : Sig GE} (R : RowsK S) (W : R.G.C.Word) (z : R.Sh.par.Cw.Word) (gamma : List E)

theorem main_symbol (hg : gamma.length = R.s.h + R.s.g) {T : Array E}
    (hT : T.size = 2 ^ (R.s.h + R.s.g)) (p : R.Sh.Cb.NP) (x : R.Sh.Cb.NS p)
    (h1 : ∀ b r, R.Sh.ord b = some r →
      readV T (Sz.rowNo b) = R.Sh.view.wd W ⟨r.1, .inl p⟩ (r.2, x))
    (h0 : ∀ b, R.Sh.ord b = none → readV T (Sz.rowNo b) = 0) :
    foldedAt R.Sh.par (readP (R.s.h + R.s.g) gamma) (R.Sh.rho.wd W) z (.inl p) (none, x) =
      readE ((foldLow T gamma).getD 0 zeroE) := by
  rw [main_field hg hT, ← cube_join (R.s.h + R.s.g) (readL gamma) T R.Sh.ord
    (fun r => R.Sh.view.wd W ⟨r.1, .inl p⟩ (r.2, x)) h1 h0, folded_main]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact congrArg (fun v => Alg.eqk (readP (R.s.h + R.s.g) gamma) b * v) (rho_main R.Sh W p b x)

theorem kept_symbol (g : Fin (R.s.h + R.s.g) → GE) (p : R.Sh.Cb.NP) (κ : R.Kp)
    (x : R.Sh.Cb.NS p) :
    foldedAt R.Sh.par g (R.Sh.rho.wd W) z (.inl p) (some κ, x) =
      R.Sh.view.wd W ⟨(R.kept κ).1, .inl p⟩ ((R.kept κ).2, x) := by
  rw [folded_main]
  calc (∑ b, Alg.eqk g b * R.Sh.rho.wd W (.inl p) (b, (some κ, x)))
      = ∑ b, Alg.eqk g b * R.Sh.view.wd W ⟨(R.kept κ).1, .inl p⟩ ((R.kept κ).2, x) :=
        Finset.sum_congr rfl fun b _ => congrArg (Alg.eqk g b * ·) (rho_kept R.Sh W p b κ x)
    _ = (∑ b, Alg.eqk g b) * R.Sh.view.wd W ⟨(R.kept κ).1, .inl p⟩ ((R.kept κ).2, x) :=
        (Finset.sum_mul _ _ _).symm
    _ = _ := by rw [Alg.sum_eqk, one_mul]

theorem mask_symbol (hg : gamma.length = R.s.h + R.s.g) {T : Array E} (hT : T.size = 2 ^ R.s.h)
    (p : R.Sh.Zb.NP) (x : R.Sh.Zb.NS p)
    (h1 : ∀ b r, R.Sh.ordZ b = some r →
      readV T (Sz.rowNo b) = R.Sh.view.wd W ⟨r.1, .inr p⟩ (r.2, x))
    (h0 : ∀ b, R.Sh.ordZ b = none → readV T (Sz.rowNo b) = 0) :
    foldedAt R.Sh.par (readP (R.s.h + R.s.g) gamma) (R.Sh.rho.wd W) z (.inr (.inl p)) x =
      readE ((foldLow T (gamma.take R.s.h)).getD 0 zeroE) := by
  rw [readE_foldLowPart (s := R.s) (gamma := gamma) (hg := hg) (t := T) hT,
    ← cube_join R.s.h (readL gamma) T R.Sh.ordZ
      (fun r => R.Sh.view.wd W ⟨r.1, .inr p⟩ (r.2, x)) h1 h0, folded_mask]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact congrArg (fun v => Alg.eqk (R.Sh.par.pre (readP (R.s.h + R.s.g) gamma)) b * v)
    (rho_mask R.Sh W p b x)

theorem fresh_symbol (hg : gamma.length = R.s.h + R.s.g) {T : Array E} (hT : T.size = 2 ^ R.s.h)
    (y : R.Sh.par.Cin.Word) (p : R.Sh.par.Zw.NP) (x : R.Sh.par.Zw.NS p)
    (h1 : ∀ b : Fin R.s.h → Bool, z p (b, x) = readV T (Sz.rowNo b)) :
    foldedAt R.Sh.par (readP (R.s.h + R.s.g) gamma) y z (.inr (.inr p)) x =
      readE ((foldLow T (gamma.take R.s.h)).getD 0 zeroE) := by
  rw [readE_foldLowPart (s := R.s) (gamma := gamma) (hg := hg) (t := T) hT,
    ← sum_rowNo R.s.h fun i => eqW R.s.h (readL gamma) i * readV T i, folded_fresh]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [eqW_rowNo]
  exact congrArg (fun v => Alg.eqk (R.Sh.par.pre (readP (R.s.h + R.s.g) gamma)) b * v) (h1 b)

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.cube_join
#print axioms VerifiableInference.Desc.LinkJoin.main_symbol
#print axioms VerifiableInference.Desc.LinkJoin.kept_symbol
#print axioms VerifiableInference.Desc.LinkJoin.mask_symbol
#print axioms VerifiableInference.Desc.LinkJoin.fresh_symbol
