-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/Draw.lean: which drawn bits are which entry of the matrix of a smallness test:
the typed challenge of the block (Cb/Pv/Tail/Size.lean) against the list that the Lean verifier
reads.

The format draws the matrix as one list of columns * tau entries (Fmt.drawTrits, Fmt/Rules6.lean):
entry j is made of two bits of word j / 32. The verifier's sub-proofs read that list at the index
(first + c) * tau + u for column c of a matrix and combination u, where first is the number of
columns of the matrices before (foldSums and foldColumn, OnBytes/Model/Tail.lean). The typed
challenge Dr s has a coefficient for each matrix, combination and column. Here the two are tied by
a bijection with that rule. Definitions, statements and proofs.

Main names:
  `firstCol s μ`: the number of columns of the matrices before matrix μ.
  `portIndex s μ c u`: the index (firstCol s μ + c) * tau + u, as an element of
    Fin (columns * tau). `portIndex_val`: its value.
  `cellIndex s`, `byCell s`: the two steps of which the bijection is made.
  `flatPort s`: the bijection from Dr s to lists of columns * tau coefficients that puts the
    coefficient of (μ, u, c) at portIndex s μ c u. `flatPort_apply`: that rule.
  `listOf β`: the list of matrix entries that β stands for. `listOf_get`: read at the verifier's
    index, with the verifier's fallback 0, it gives the value of β's coefficient at (μ, u, c).
  `tritsOf_get`: entry j of the format's list is the value of the coefficient made of bits
    2 (j % 32) and 2 (j % 32) + 1 of word j / 32.

Limits: nothing here speaks of a run of the verifier: that the array which the sub-proofs read is
the format's list, and that their first is firstCol at the sizes of a given sub-proof, is read off
the text and not proved here.
-/
import OnBytes.Tie.Pv.Tail.Rng
import Cb.Pv.Tail.Size

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open Cb.Pv.Tail

/-- The number of columns of the matrices before matrix μ. -/
def firstCol (s : Size) (μ : Fin s.NM) : ℕ := ∑ ν : Fin μ.val, s.k (Fin.castLE μ.isLt.le ν)

/-- The place of column c of matrix μ among the columns of all matrices. -/
def colIndex (s : Size) (μ : Fin s.NM) (c : Fin (s.k μ)) : Fin s.columns :=
  finSigmaFinEquiv (n := fun ν : Fin s.NM => s.k ν) ⟨μ, c⟩

theorem colIndex_val (s : Size) (μ : Fin s.NM) (c : Fin (s.k μ)) :
    (colIndex s μ c).val = firstCol s μ + c.val :=
  finSigmaFinEquiv_apply (n := fun ν : Fin s.NM => s.k ν) ⟨μ, c⟩

/-- Column and combination against the place in one list: the combinations of a column stand side
by side. -/
def cellIndex (s : Size) :
    (Σ μ : Fin s.NM, Fin (s.k μ)) × Fin s.tau ≃ Fin (s.columns * s.tau) :=
  (Equiv.prodCongr (finSigmaFinEquiv (n := fun ν : Fin s.NM => s.k ν)) (Equiv.refl _)).trans
    finProdFinEquiv

/-- The verifier's index of the entry of column c of matrix μ in combination u. -/
def portIndex (s : Size) (μ : Fin s.NM) (c : Fin (s.k μ)) (u : Fin s.tau) :
    Fin (s.columns * s.tau) := cellIndex s (⟨μ, c⟩, u)

theorem portIndex_val (s : Size) (μ : Fin s.NM) (c : Fin (s.k μ)) (u : Fin s.tau) :
    (portIndex s μ c u).val = (firstCol s μ + c.val) * s.tau + u.val := by
  show u.val + s.tau * (colIndex s μ c).val = _
  rw [colIndex_val]
  ring

/-- The typed challenge as a function of column and combination. -/
def byCell (s : Size) : Dr s ≃ ((Σ μ : Fin s.NM, Fin (s.k μ)) × Fin s.tau → Prob.Coef) where
  toFun β x := β x.1.1 x.2 x.1.2
  invFun g μ u c := g (⟨μ, c⟩, u)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The typed challenge as one list of coefficients, by the verifier's index. -/
def flatPort (s : Size) : Dr s ≃ (Fin (s.columns * s.tau) → Prob.Coef) :=
  (byCell s).trans (Equiv.arrowCongr (cellIndex s) (Equiv.refl _))

/-- The rule of the bijection. -/
theorem flatPort_apply (s : Size) (β : Dr s) (μ : Fin s.NM) (c : Fin (s.k μ)) (u : Fin s.tau) :
    flatPort s β (portIndex s μ c u) = β μ u c := by
  show byCell s β ((cellIndex s).symm (cellIndex s (⟨μ, c⟩, u))) = β μ u c
  rw [Equiv.symm_apply_apply]
  rfl

/-- The list of matrix entries that a typed challenge stands for. -/
def listOf {s : Size} (β : Dr s) : Array Int :=
  Array.ofFn fun j => (flatPort s β j).val

/-- Read at the verifier's index, with the verifier's fallback 0, the list gives the value of the
coefficient at (μ, u, c). -/
theorem listOf_get {s : Size} (β : Dr s) (μ : Fin s.NM) (c : Fin (s.k μ)) (u : Fin s.tau) :
    (listOf β).getD ((firstCol s μ + c.val) * s.tau + u.val) 0 = (β μ u c).val := by
  rw [← portIndex_val, ← flatPort_apply s β μ c u]
  simp [listOf, Array.getD]

/-- Entry j of the format's list of n matrix entries. -/
theorem tritsOf_get : ∀ (ws : List UInt64) (n j : ℕ), j < n → j / 32 < ws.length →
    (Fmt.tritsOf ws n)[j]? =
      some (Prob.Coef.val ((ws.getD (j / 32) 0).toNat.testBit (2 * (j % 32)),
        (ws.getD (j / 32) 0).toNat.testBit (2 * (j % 32) + 1)))
  | [], _, _, _, h => absurd h (by simp)
  | w :: ws, n, j, hj, hl => by
    unfold Fmt.tritsOf
    by_cases h32 : j < 32
    · have hm : j < min n 32 := by omega
      rw [List.getElem?_append_left (by simpa using hm)]
      have h0 : j / 32 = 0 := by omega
      have h1 : j % 32 = j := by omega
      simp [h0, h1, hm, tritAt_eq]
    · have hn : 32 ≤ n := by omega
      have hlen : ((List.range (min n 32)).map (Fmt.tritAt w)).length = 32 := by
        simp [hn]
      rw [List.getElem?_append_right (by omega), hlen]
      have hd : j / 32 = (j - 32) / 32 + 1 := by omega
      have hr : j % 32 = (j - 32) % 32 := by omega
      have hl' : (j - 32) / 32 < ws.length := by
        simp only [List.length_cons] at hl
        omega
      rw [tritsOf_get ws (n - 32) (j - 32) (by omega) hl', hd, hr]
      simp

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.portIndex_val
#print axioms OnBytes.Tie.Pv.Tail.flatPort_apply
#print axioms OnBytes.Tie.Pv.Tail.listOf_get
#print axioms OnBytes.Tie.Pv.Tail.tritsOf_get
