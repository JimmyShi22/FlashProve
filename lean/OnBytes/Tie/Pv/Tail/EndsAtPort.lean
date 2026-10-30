-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/EndsAtPort.lean: the premise `AtA` of OnBytes/Tie/Pv/Tail/EndsAt.lean at the
letters that OnBytes/Tie/Pv/Tail/LettersAt.lean reads off a lay of the committed entries.

Definitions, statements and proofs.
Main names:
  `cellsOf Y tl m u`: the arrays' entries that the early entries m and the other entries u give.
  `PortOK tl K3 ws`: premises on public numbers and on what was drawn: the record's number of
    matrices is the length of its list; each matrix has its symbol array in the list; U3 is there;
    every place that a read names lies below K3; the record's drawn entries are the format's list
    of the words ws, its first columns the running sums of the matrices' columns; there are words
    enough.
  `signOf_coef`: on the value of a coefficient the sign is the value.
  `ata_port`: `AtA` at `thetaAt`, at the typed challenge `drawnOf` of the words, and at digits that
    are the cells of ZZ in the verifier's columns.
  `relOut_port`: so, if every row of the list holds at these cells and the digits are in their
    tables, the relation after the round holds at these letters.
Limits: `PortOK` is a premise. That the digits are read off ZZ is a premise on Z here.
-/
import OnBytes.Tie.Pv.Tail.EndsAt
import OnBytes.Tie.Pv.Tail.LettersAt
import OnBytes.Tie.Pv.Tail.DrawPort
import OnBytes.Tie.Pv.Tail.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model OnBytes.Road.Rows

open Finset Cb.Pv.Tail Iop

variable {K J : Type} [Field K] [Fintype J] (ρ : Reading K) (Y : Lay J) (tl : HTailF2)

/-- The arrays' entries that the committed entries give. -/
def cellsOf (m : JE Y tl → K) (u : JL Y tl → K) : Nat → Nat → Nat → K :=
  fun t r c => Y.cellAt (glue Y tl m u) t r c

/-- Premises on public numbers and on what was drawn. -/
structure PortOK (K3 : Nat) (ws : List UInt64) : Prop where
  nm : tl.NM = tl.mats.size
  gt : tl.NM ≤ tl.gtTree.size
  u3 : ∃ t, tl.ix.U[2]? = some (some t)
  pos : ∀ y ∈ readsList tl tl.funs, ∀ d, d < (tl.mats.getD y.1.mat {}).k →
    posOf tl y.1 y.2 d < K3
  cf : tl.cfF = (Fmt.tritsOf ws ((sizeOf tl).size.columns * (sizeOf tl).size.tau)).toArray
  first : tl.cfFirst = tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0]
  words : ((sizeOf tl).size.columns * (sizeOf tl).size.tau + 31) / 32 ≤ ws.length

omit [Fintype J] in
/-- On the value of a coefficient the sign is the value. -/
theorem signOf_coef (a : Prob.Coef) : signOf (K := K) a.val = ((a.val : ℤ) : K) := by
  rcases a with ⟨_ | _, _ | _⟩ <;> simp [signOf, Prob.Coef.val]

variable {tl}

theorem early_sym {μ : Nat} (h : μ < tl.gtTree.size) (r c : Nat) :
    early tl (.cell (tl.gtTree.getD μ 0) r c) = true := by
  have e : tl.gtTree.getD μ 0 ∈ tl.gtTree.toList := by
    have e1 : tl.gtTree.getD μ 0 = tl.gtTree.toList[μ]'(by simpa using h) := by
      simp [Array.getD, h]
    rw [e1]
    exact List.getElem_mem _
  show (decide (tl.gtTree.getD μ 0 ∈ tl.gtTree.toList) || _) = true
  rw [decide_eq_true e, Bool.true_or]

theorem early_u3 (h : ∃ t, tl.ix.U[2]? = some (some t)) (r c : Nat) :
    early tl (.cell (u3Of tl) r c) = true := by
  obtain ⟨t, ht⟩ := h
  have e0 : u3Of tl = t := by
    unfold u3Of
    rw [Array.getD_eq_getD_getElem?, ht]
    rfl
  have e : some t ∈ tl.ix.U.toList.take 4 := by
    refine List.mem_iff_getElem?.2 ⟨2, ?_⟩
    rw [List.getElem?_take_of_lt (by norm_num), Array.getElem?_toList, ht]
  simp [early, e0, e]

variable (tl)

/-- `AtA` at the letters of OnBytes/Tie/Pv/Tail/LettersAt.lean. -/
theorem ata_port (K3 : Nat) (ws : List UInt64) (ok : PortOK tl K3 ws) (X : Type) (Ex : ExtSpec)
    (W₀ : Type) (ride : X × Ex.Str → (JE Y tl → K) → Dig K (sizeOf tl).size × W₀ → Prop) (x : X)
    (m : JE Y tl → K) (u : JL Y tl → K) (Z : Dig K (sizeOf tl).size)
    (hzl : ∀ μ v i, Z.zl μ v i =
      cellsOf Y tl m u tl.ix.ZZ v ((tl.zzCol μ 0 0).getD 0 + i))
    (hzh : ∀ μ v i, Z.zh μ v i =
      cellsOf Y tl m u tl.ix.ZZ v ((tl.zzCol μ 1 0).getD 0 + i)) :
    AtA ρ tl (thetaAt ρ Y tl (u3Of tl) K3 X Ex W₀ ride) x m Z (drawnOf (sizeOf tl).size ws)
      (cellsOf Y tl m u) where
  phi := fun n Fn hn j _ => by
    show phiAt ρ tl n j = _
    unfold phiAt
    have e : tl.funs.getD n default = Fn := by
      rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hn]
      rfl
    rw [e]
  sym := fun μ i' c hμ _ _ =>
    cellAt_glue Y tl m _ u _ _ _ (early_sym (Nat.lt_of_lt_of_le hμ ok.gt) i' c)
  u3 := fun y hy d hd => by
    show u3At Y tl (u3Of tl) K3 m _ = _
    unfold u3At
    rw [Nat.div_eq_of_lt (ok.pos y hy d hd), Nat.mod_eq_of_lt (ok.pos y hy d hd)]
    exact cellAt_glue Y tl m _ u _ _ _ (early_u3 ok.u3 _ _)
  zl := hzl
  zh := hzh
  th := fun μ v c => by
    rw [ok.cf, ok.first, cfFirst_eq tl ok.nm μ]
    have e := entry_of_words (sizeOf tl).size ws ok.words μ c v
    rw [show tl.tau = (sizeOf tl).size.tau from rfl, e, signOf_coef]

/-- If every row of the list holds at the cells that the committed entries give, and the digits,
which are cells of ZZ, are in their tables, then the relation after the round holds at the letters
of OnBytes/Tie/Pv/Tail/LettersAt.lean. -/
theorem relOut_port (K3 : Nat) (ws : List UInt64) (ok : PortOK tl K3 ws) (X : Type) (Ex : ExtSpec)
    (W₀ : Type) (ride : X × Ex.Str → (JE Y tl → K) → Dig K (sizeOf tl).size × W₀ → Prop) (x : X)
    (m : JE Y tl → K) (u : JL Y tl → K) (Z : Dig K (sizeOf tl).size)
    (hzl : ∀ μ v i, Z.zl μ v i =
      cellsOf Y tl m u tl.ix.ZZ v ((tl.zzCol μ 0 0).getD 0 + i))
    (hzh : ∀ μ v i, Z.zh μ v i =
      cellsOf Y tl m u tl.ix.ZZ v ((tl.zzCol μ 1 0).getD 0 + i))
    (hfit : Fits tl) (htree : ∀ Fn ∈ tl.funs.toList, Fn.tree = 2)
    (hdig : ∀ μ v i, Cb.Rng.InTab (sizeOf tl).size.lo (Z.zl μ v i) ∧
      Cb.Rng.InTab (sizeOf tl).size.hi (Z.zh μ v i))
    (pc : Nat) (h : ∀ r ∈ rowsTail ρ tl tl.funs pc, r.2 (cellsOf Y tl m u) = 0) :
    relOut (thetaAt ρ Y tl (u3Of tl) K3 X Ex W₀ ride).letters x (drawnOf (sizeOf tl).size ws) m
      Z :=
  relOut_of_rows pc (ata_port ρ Y tl K3 ws ok X Ex W₀ ride x m u Z hzl hzh) hfit htree hdig h

end OnBytes.Tie.Pv.Tail.Port

#print axioms OnBytes.Tie.Pv.Tail.Port.relOut_port
#print axioms OnBytes.Tie.Pv.Tail.Port.ata_port
