--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/HonestTab.lean: at a stored table that is the code's words of rows M, with a
key whose record holds M's true answers at the key's seeds, the table decodes to M's message parts
and no point of the fold is bad.

  honest_tab     the decoder's answer; DecX2; for every point, not BadX2
                 (Johnson/Desc/K14/Law/PointKey2.lean). The two radii together stay below the code's
                 distance 2 ^ logN - (r + ell) + 1.
  honest_TabX2   what TabX2 is then, by numbers.

By the library's theorems ldFe_honest and ldFe_none (Cb/Ld/LdFoldEqProofs.lean) and hasDist_genOf
(OnBytes/Slice/CodeFacts.lean).

What is not claimed. That any stored table is of that form. Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Desc.K14.Law.PointKey2
import OnBytes.Slice.CodeFacts
import Cb.Ld.LdFoldEqProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain

/-- **At a stored table that IS the code's words of rows M, with a key whose record holds M's true
answers at the key's seeds: the table decodes, to M's message parts, and NO POINT IS BAD.** The two
radii together stay below the code's distance. -/
theorem honest_tab (p : Par) (err eM e' : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (tab : Nat → List UInt64) (key : TableKey)
    (M : (Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE)
    (ha : p.S.fold.index.code.logN ≤ 32)
    (hk : p.S.fold.index.code.r + p.S.fold.index.code.ell ≤ 2 ^ p.S.fold.index.code.logN)
    (he : e' + eM < 2 ^ p.S.fold.index.code.logN -
      (p.S.fold.index.code.r + p.S.fold.index.code.ell) + 1)
    (htab : tabF OnBytes.Model.Reading.gl p.S.fold.index tab =
      fun r => (genOf (codeOf p.S.fold.index.code)).mulVec (M r))
    (hrec : (recOf p.S.fold.index fun k =>
        OnBytes.Model.Reading.gl.val (key.record.getD k zeroE)) =
      (ixOf2 p.S.fold err eM rank).ZR.val (seedsFn OnBytes.Model.Reading.gl p.S.fold.index key)
        ((ixOf2 p.S.fold err eM rank).view M)) :
    (ixOf2 p.S.fold err eM rank).dec (tabF OnBytes.Model.Reading.gl p.S.fold.index tab)
        (seedsFn OnBytes.Model.Reading.gl p.S.fold.index key,
          recOf p.S.fold.index fun k =>
            OnBytes.Model.Reading.gl.val (key.record.getD k zeroE)) =
        some ((ixOf2 p.S.fold err eM rank).view M) ∧
      DecX2 p err eM rank tab key ∧ ∀ gam, ¬ BadX2 p err eM rank e' tab key gam := by
  have hd := hasDist_genOf (codeOf p.S.fold.index.code) ha hk
  have hdec := Cb.ldFe_honest (ixOf2 p.S.fold err eM rank) _ M
    (seedsFn OnBytes.Model.Reading.gl p.S.fold.index key) hd (by
      show eM < _
      exact lt_of_le_of_lt (Nat.le_add_left _ _) he)
  have hdec' : (ixOf2 p.S.fold err eM rank).dec
      (tabF OnBytes.Model.Reading.gl p.S.fold.index tab)
      (seedsFn OnBytes.Model.Reading.gl p.S.fold.index key,
        recOf p.S.fold.index fun k =>
          OnBytes.Model.Reading.gl.val (key.record.getD k zeroE)) =
      some ((ixOf2 p.S.fold err eM rank).view M) := by
    rw [htab, hrec]
    exact hdec
  refine ⟨hdec', ?_, ?_⟩
  · unfold DecX2
    rw [hdec']
    rfl
  · intro gam
    unfold BadX2
    exact Cb.ldFe_none (ixOf2 p.S.fold err eM rank) _ e' _ _ hd he
      (fun hn => nomatch hdec'.symm.trans hn) gam

/-- What it decodes to, by numbers. -/
theorem honest_TabX2 (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (tab : Nat → List UInt64) (key : TableKey)
    (M : (Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE)
    (hdec : (ixOf2 p.S.fold err eM rank).dec (tabF OnBytes.Model.Reading.gl p.S.fold.index tab)
        (seedsFn OnBytes.Model.Reading.gl p.S.fold.index key,
          recOf p.S.fold.index fun k =>
            OnBytes.Model.Reading.gl.val (key.record.getD k zeroE)) =
        some ((ixOf2 p.S.fold err eM rank).view M))
    (r k : Nat) (h : k < p.S.fold.index.code.ell) :
    TabX2 p err eM rank tab key r k =
      M (bitsOf p.S.fold.index.v r) (Fin.natAdd p.S.fold.index.code.r ⟨k, h⟩) := by
  unfold TabX2
  rw [hdec]
  simp only [dif_pos h]
  rfl

end Desc.K14.Law
