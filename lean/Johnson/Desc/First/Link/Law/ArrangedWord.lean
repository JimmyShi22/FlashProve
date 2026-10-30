-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/ArrangedWord.lean: THE TYPED SIDE OF «THE OPEN WORD IS THE FOLD OF THE
MEMBERS' WORDS»: what the library's arrangement `GShape.rho` (Cb/Ld/LdGroupFold.lean) lays at a
native position, and what the fold of the three tables (`foldedAt`,
Johnson/Desc/First/Close/Law/Carry.lean) holds there, written out as sums. General in the group's
shape. Theorems, by unfolding. No text already in the library turns.

  `offCnt_congr`: two words with the same long symbols are equally far from every word.
  `rho_main`: the arranged word at a main position p, super-row b, slot none: the row that `ord b`
    names, as `view` shows it at p; 0 where `ord b` names none. `rho_kept`: slot some κ: the kept
    row κ, at every super-row. `rho_mask`: at a mask position, row b: the row that `ordZ b` names.
  `folded_main`, `folded_mask`, `folded_fresh`: **the folded word at a native position: ∑ b, eqk g b
    * ‹the word's entry at super-row b›; the carried mask's and the fresh mask's the like over the
    cube of h variables at `pre g`.**
Limits. What `view` shows of a member's own word is not said. Nothing on the text. Nothing on
soundness.
-/
import Johnson.Desc.First.Close.Law.Carry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open Cb Iop IOR
open VerifiableInference.Desc.First.Close (foldedAt)

theorem offCnt_congr {Ex : ExtSpec} [Finite Ex.Pos] {y y₂ : Ex.Str}
    (h : ∀ p, Ex.rd y p = Ex.rd y₂ p) (y' : Ex.Str) : offCnt y y' = offCnt y₂ y' := by
  unfold offCnt
  simp only [h]

section
variable {E : Type} [Field E] {S : Sig E} {G : Grp S} (Sh : GShape G) (W : G.C.Word)

theorem rho_main (p : Sh.Cb.NP) (b : Fin (Sh.h + Sh.g) → Bool) (x : Sh.Cb.NS p) :
    Sh.rho.wd W (.inl p) (b, (none, x)) =
      (Sh.ord b).elim 0 fun r => Sh.view.wd W ⟨r.1, .inl p⟩ (r.2, x) := by
  have h : Sh.rho.wd W (.inl p) (b, (none, x)) =
      Sh.am.spread (LdCode.fstW (Sh.flat.wd W) p) ((b, none), x) := rfl
  have e : Sh.am.src ((b, (none : Option Sh.Kp)), x).1 = Sh.ord b := rfl
  rw [h]
  unfold Arr.spread
  rw [e]
  cases Sh.ord b <;> rfl

theorem rho_kept (p : Sh.Cb.NP) (b : Fin (Sh.h + Sh.g) → Bool) (κ : Sh.Kp) (x : Sh.Cb.NS p) :
    Sh.rho.wd W (.inl p) (b, (some κ, x)) =
      Sh.view.wd W ⟨(Sh.kept κ).1, .inl p⟩ ((Sh.kept κ).2, x) := rfl

theorem rho_mask (p : Sh.Zb.NP) (b : Fin Sh.h → Bool) (x : Sh.Zb.NS p) :
    Sh.rho.wd W (.inr p) (b, x) =
      (Sh.ordZ b).elim 0 fun r => Sh.view.wd W ⟨r.1, .inr p⟩ (r.2, x) := by
  have h : Sh.rho.wd W (.inr p) (b, x) =
      Sh.az.spread (LdCode.sndW (Sh.flat.wd W) p) (b, x) := rfl
  have e : Sh.az.src (b, x).1 = Sh.ordZ b := rfl
  rw [h]
  unfold Arr.spread
  rw [e]
  cases Sh.ordZ b <;> rfl

end

section
variable {K P : Type} [Field K] [Fintype K] [Fintype P] (Y : SumPar K P) (g : Fin Y.k → K)
  (y : Y.Cin.Word) (z : Y.Cw.Word)

theorem folded_main (p : Y.C.NP) (x : Y.C.NS p) :
    foldedAt Y g y z (.inl p) x = ∑ b, Alg.eqk g b * y (.inl p) (b, x) := rfl

theorem folded_mask (p : Y.Z.NP) (x : Y.Z.NS p) :
    foldedAt Y g y z (.inr (.inl p)) x = ∑ b, Alg.eqk (Y.pre g) b * y (.inr p) (b, x) := rfl

theorem folded_fresh (p : Y.Zw.NP) (x : Y.Zw.NS p) :
    foldedAt Y g y z (.inr (.inr p)) x = ∑ b, Alg.eqk (Y.pre g) b * z p (b, x) := rfl

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.offCnt_congr
#print axioms VerifiableInference.Desc.LinkJoin.rho_main
#print axioms VerifiableInference.Desc.LinkJoin.rho_kept
#print axioms VerifiableInference.Desc.LinkJoin.rho_mask
#print axioms VerifiableInference.Desc.LinkJoin.folded_main
#print axioms VerifiableInference.Desc.LinkJoin.folded_mask
#print axioms VerifiableInference.Desc.LinkJoin.folded_fresh
