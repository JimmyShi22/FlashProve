-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysRet.lean: if the end of the batched sumcheck returns, the forms of the panels'
sides are there.

A panel's side may be given as forms: a function that returns a form at (row, column), or nothing.
The share of a panel (shareP in Johnson/Road/FormsKeysPort.lean) reads 0 where it returns nothing,
so the comparisons of the shares with the library's ask that the forms are there (Returns). The
verifier's stackEndOf (OnBytes/Model/LayerPanels.lean) takes every form of a panel without selector
and without a never-sent vector, at every row and column, and returns nothing if one is absent. So
the hypothesis follows from a line of the verifier's own run.

Every statement is on the verifier's side alone.

Main theorems: returns_of_stackEndOf (one panel), returns_of_stackEnd (all panels of the list).
Beside them powers_two: the two factors with which the batched sumcheck joins its two claims, as
SubM.batch 2 (OnBytes/Model/Hide.lean) returns them, read as 1 and as the drawn element.

The hypothesis hB, that a panel with a weight claim has no forms on its B side: plain
(OnBytes/Model/LayerPanels.lean) gives a panel a weight claim exactly if it is given no B side.

What is not claimed. Nothing is said of what the forms are worth, of a panel with the selector,
whose column factor is an array of forms, or of the panel whose A side is a never-sent vector. The
program does not import this file.
-/
import Johnson.Road.FormsKeysPort

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model (Aff eqLow eqLowAt)
open OnBytes.Model.Layer (Lay SBlk StackEnd stackEndOf stackEnd)

variable {y : Lay} {rs : Array E} {lam : ℕ} {om H1 V : Array E} {s s' : StackEnd} {b : SBlk}

/-- A panel without selector and without a never-sent vector that stackEndOf has not refused has all
the forms of its sides. hB: if it has a weight claim, its B side is not given as forms. -/
theorem returns_of_stackEndOf (ht : b.tri = false) (hk : b.virt = none)
    (hB : ∀ v0, b.v0 = some v0 → b.B = none)
    (h : stackEndOf y rs lam om H1 V s b = some s') : Returns b := by
  have hc := stackEndOf_ok h
  unfold stackEndOf at h
  cases h0 : b.v0 with
  | some v0 =>
    rw [hc, ht, hk, h0] at h
    have h' : (do
        let A ← b.A
        (List.range b.ni).foldlM (fun s i => do
          let s ← (List.range b.ny).foldlM (fun (s : StackEnd) yv => do
            let a ← A i yv
            pure { s with Alin := s.Alin.addMul a (mulE (mulE (mulE (mulE (mulE
              (eqLowAt rs b.w lam (b.off / 2 ^ b.w)) (om.getD b.claim zeroE)) b.ec)
              (b.wt.getD i zeroE)) ((eqLow rs b.wy b.w).getD i zeroE))
              ((eqLow rs 0 b.wy).getD yv zeroE)) }) s
          pure { s with Bs := addE s.Bs (mulE (mulE (eqLowAt rs b.w lam (b.off / 2 ^ b.w))
            ((eqLow rs b.wy b.w).getD i zeroE)) (V.getD (v0 + i) zeroE)) }) s) = some s' := h
    obtain ⟨A, hA, h'⟩ := bind_some h'
    refine ⟨fun A' hA' i hi yv hy => ?_, fun B' hB' => ?_⟩
    · have e : A = A' := Option.some.inj (hA.symm.trans hA')
      subst e
      obtain ⟨s1, s2, g1⟩ := foldlM_each _ _ _ _ h' i (List.mem_range.mpr hi)
      obtain ⟨s3, g2, _⟩ := bind_some g1
      obtain ⟨t1, t2, g3⟩ := foldlM_each _ _ _ _ g2 yv (List.mem_range.mpr hy)
      obtain ⟨a, ha, _⟩ := bind_some g3
      exact ⟨a, ha⟩
    · rw [hB v0 h0] at hB'
      cases hB'
  | none =>
    rw [hc, ht, hk, h0] at h
    cases hBb : b.B with
    | none =>
      rw [hBb] at h
      have h' : (do
          let A ← b.A
          (List.range b.ni).foldlM (fun s i => do
            let s ← (List.range b.ny).foldlM (fun (_ : StackEnd) yv => do
              let _ ← A i yv
              none) s
            pure s) s) = some s' := h
      obtain ⟨A, hA, h'⟩ := bind_some h'
      refine ⟨fun A' hA' i hi yv hy => ?_, fun B' hB' => by rw [hBb] at hB'; cases hB'⟩
      obtain ⟨s1, s2, g1⟩ := foldlM_each _ _ _ _ h' i (List.mem_range.mpr hi)
      obtain ⟨s3, g2, _⟩ := bind_some g1
      obtain ⟨t1, t2, g3⟩ := foldlM_each _ _ _ _ g2 yv (List.mem_range.mpr hy)
      obtain ⟨a, _, g4⟩ := bind_some g3
      cases g4
    | some B =>
      rw [hBb] at h
      have h' : (do
          let A ← b.A
          (List.range b.ni).foldlM (fun s i => do
            let s ← (List.range b.ny).foldlM (fun (s : StackEnd) yv => do
              let a ← A i yv
              let c ← B i yv
              pure { s with
                Alin := s.Alin.addMul a (mulE (mulE (mulE (mulE (mulE
                  (eqLowAt rs b.w lam (b.off / 2 ^ b.w)) (om.getD b.claim zeroE)) b.ec)
                  (b.wt.getD i zeroE)) ((eqLow rs b.wy b.w).getD i zeroE))
                  ((eqLow rs 0 b.wy).getD yv zeroE))
                Blin := s.Blin.addMul c (mulE (mulE (eqLowAt rs b.w lam (b.off / 2 ^ b.w))
                  ((eqLow rs b.wy b.w).getD i zeroE)) ((eqLow rs 0 b.wy).getD yv zeroE)) }) s
            pure s) s) = some s' := h
      obtain ⟨A, hA, h'⟩ := bind_some h'
      have both : ∀ i, i < b.ni → ∀ yv, yv < b.ny →
          (∃ a, A i yv = some a) ∧ ∃ c, B i yv = some c := by
        intro i hi yv hy
        obtain ⟨s1, s2, g1⟩ := foldlM_each _ _ _ _ h' i (List.mem_range.mpr hi)
        obtain ⟨s3, g2, _⟩ := bind_some g1
        obtain ⟨t1, t2, g3⟩ := foldlM_each _ _ _ _ g2 yv (List.mem_range.mpr hy)
        obtain ⟨a, ha, g4⟩ := bind_some g3
        obtain ⟨c, hc', _⟩ := bind_some g4
        exact ⟨⟨a, ha⟩, ⟨c, hc'⟩⟩
      refine ⟨fun A' hA' i hi yv hy => ?_, fun B' hB' i hi yv hy => ?_⟩
      · have e : A = A' := Option.some.inj (hA.symm.trans hA')
        subst e
        exact (both i hi yv hy).1
      · have e : B = B' := Option.some.inj (hBb.symm.trans hB')
        subst e
        exact (both i hi yv hy).2

/-- The same for every such panel of a list on which stackEnd returns. -/
theorem returns_of_stackEnd {bl : Array SBlk} {shownA shownB : E}
    (h : stackEnd y bl rs lam om H1 V shownA shownB = some s') :
    ∀ b ∈ bl.toList, b.tri = false → b.virt = none → (∀ v0, b.v0 = some v0 → b.B = none) →
      Returns b := by
  intro b hb ht hk hB
  obtain ⟨s1, s2, g⟩ := stackEnd_each h b hb
  exact returns_of_stackEndOf ht hk hB g

/-- The two powers of a drawn element x, from its power 0 (powers in OnBytes/Model/Frame.lean), read
as 1 and as x. -/
theorem powers_two {K : Type} [Field K] (ρ : OnBytes.Model.Reading K) (x : E) :
    ρ.val ((OnBytes.Model.powers x 2).getD 0 zeroE) = 1 ∧
      ρ.val ((OnBytes.Model.powers x 2).getD 1 zeroE) = ρ.val x := by
  have e0 : (OnBytes.Model.powers x 2).getD 0 zeroE = oneE := rfl
  have e1 : (OnBytes.Model.powers x 2).getD 1 zeroE = mulE oneE x := rfl
  rw [e0, e1, ρ.mul, ρ.one, one_mul]
  exact ⟨rfl, rfl⟩

#print axioms powers_two
#print axioms returns_of_stackEndOf
#print axioms returns_of_stackEnd

end OnBytes.Road
