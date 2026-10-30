-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/KeptJoin.lean: the code switch: the generator row of a KEPT main row,
as the program lays it, is the typed library's generator row at that row's coordinate, entry by
entry.

GenJoin.lean joins the main row and the two mask rows. Here the rows in between. A kept row's
message lies in its member's new message, at row + 2 ^ rowBits * place, but the entries at the
places of the member's old pad lie in the rest of g; its tail lies in the rest of g. THE TEXT's
SIDE: genKept_new, genKept_g, genKept_other and formAt_keptForm (Johnson/Top/H0/H2K/GenRowsAt.lean).
THE TYPED SIDE: genVec_row (GenJoin.lean). THE DICTIONARY: keptAt, pushTo_names and readAt_kept
(Johnson/Top/H/SwitchMaps.lean), pushTo_at (Johnson/Top/H/SwitchNames.lean).
Main names:
  row_sum      of the entries of one row of a table, at most one stands at a given index: sum_row of
               Johnson/Top/H/SwitchMaps.lean, at the weights wM
  NamesK       what is asked of the kept slots: which row of which member a slot holds (mem, row,
               pl); the member's new message; its pad; where the row's tail begins; where its
               entries lie
  kept_reads   THE JOIN for a kept row
LIMITS. NamesK, like FrameOK and Names, is a PREMISE: nothing here says that a switch of the
programs meets it (brought further, not paid: Paid.lean's paid_namesK makes it from the record
AtSwitch, a premise); mem, row, pl, aKept are letters. ReadsAs speaks of the entries of the new
sending alone. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hands.GenJoin
import Johnson.Top.H.SwitchMaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Slice Cb Johnson.Pack Johnson.Top.H H2K.Lift

/-- Of the entries of row b of a table, at most one stands at the index J. -/
theorem row_sum (C : Fmt.M1.Code) (x b rb J : ℕ) (hb : b < 2 ^ rb) :
    (∑ j : Fin C.l, if b + 2 ^ rb * j.val = J then wM C x j.val else 0) =
      if J % 2 ^ rb = b then wM C x (J / 2 ^ rb) else 0 := by
  rw [sum_row rb b C.l hb (fun j => wM C x j.val) J]
  by_cases h : J % 2 ^ rb = b
  · rw [if_pos h, if_pos h]
    unfold onNat
    split
    · rfl
    · rename_i hl
      exact (wM_of_le (Nat.le_of_not_lt hl) x).symm
  · rw [if_neg h, if_neg h]

section Join
variable (s : Sg) (K : Type) [Fintype K] [DecidableEq K] (cs : Codes) (l : List (OracleShape × ℕ))
  (iJ : (s.cKept K).J → (sigOf cs l).Ent) (iQ : (s.cKept K).Q → (sigOf cs l).Ent)

/-- What is asked of the kept slots. The slot κ holds the row number row κ of the kept member number
mem κ, whose record in the frame is pl κ; aKept κ: where that row's tail begins in the rest. -/
structure NamesK (W : SwitchFrame) (ids : ℕ → ℕ) (mem row : K → ℕ) (pl : K → KeptPlace)
    (aKept : K → ℕ) : Prop where
  rowLt : ∀ κ, row κ < 2 ^ (pl κ).rowBits
  anewIs : ∀ κ (n : (sigOf cs l).Ent),
    ids (entAt cs l n).1 = (pl κ).anew ↔ (entAt cs l n).1 = 1 + mem κ
  notG : ∀ κ, (pl κ).anew ≠ W.g
  padNodup : ∀ κ, ((pl κ).pad.map (·.index)).Nodup
  padIn : ∀ κ q, q < (pl κ).pad.length →
    ((pl κ).pad.getD q default).index < 2 ^ ((pl κ).rowBits + W.code.logEll)
  keptIn : ∀ κ (n : (sigOf cs l).Ent), (entAt cs l n).1 = 1 + mem κ →
    (entAt cs l n).2.1 = Part.main → (entAt cs l n).2.2 < 2 ^ ((pl κ).rowBits + W.code.logEll)
  tailPieces : ∀ κ, W.keptTail.getD (rowsBefore W.kept (mem κ) + row κ) [] =
    switchPieces W.places (aKept κ) W.code.r
  tailInc : ∀ κ i j, i < j → j < W.code.r →
    W.places.get (aKept κ + i) < W.places.get (aKept κ + j)
  keptMsg : ∀ κ (j : Fin s.C.l), entAt cs l (iJ (.inl (some κ, j))) =
    keptAt W (mem κ) (pl κ) (row κ) j.val
  keptTail : ∀ κ (q : Fin s.C.r), entAt cs l (iQ (.inl (some κ, q))) =
    (0, W.restPart, W.places.get (aKept κ + q.val))

end Join

section Join
variable {s : Sg} {K : Type} [Fintype K] [DecidableEq K] {cs : Codes} {l : List (OracleShape × ℕ)}
  {iJ : (s.cKept K).J → (sigOf cs l).Ent} {iQ : (s.cKept K).Q → (sigOf cs l).Ent}
  {W : SwitchFrame} {ids : ℕ → ℕ} {aMain aM0 aT0 aM1 aT1 : ℕ} {mem row : K → ℕ}
  {pl : K → KeptPlace} {aKept : K → ℕ}

/-- **A kept row.** -/
theorem kept_reads (F : FrameOK W aMain aM0 aT0 aM1 aT1)
    (D : Names s K cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1)
    (DK : NamesK s K cs l iJ iQ W ids mem row pl aKept) (κ : K) (x : ℕ)
    (hx : x < 2 ^ W.code.logN) (t : OnBytes.E) :
    ReadsAs cs l ids (genKept W (pl κ) (row κ) (rowsBefore W.kept (mem κ) + row κ) x t)
      (genVec s K iJ iQ x (.inl (some κ, ()))) := by
  intro n
  have hr : W.code.r = s.C.r := by rw [D.codeC]; rfl
  have hJ := (pushTo_names cs l (fun j : Fin s.C.l => iJ (.inl (some κ, j))) _ (DK.keptMsg κ)
    (fun j => wM s.C x j.val) n).trans
    (readAt_kept W (mem κ) (pl κ) (row κ) s.C.l (fun j => wM s.C x j.val) (DK.padNodup κ)
      (entAt cs l n).1 (entAt cs l n).2.1 (entAt cs l n).2.2)
  have form : ∀ J, J < 2 ^ ((pl κ).rowBits + W.code.logEll) →
      formAt (keptForm W (pl κ) (row κ) x) J =
        ∑ j : Fin s.C.l, if row κ + 2 ^ (pl κ).rowBits * j.val = J then wM s.C x j.val else 0 := by
    intro J hJ'
    rw [formAt_keptForm W (pl κ) (row κ) x J F.pow F.logC hx (DK.rowLt κ) hJ', ← D.codeC,
      row_sum s.C x (row κ) (pl κ).rowBits J (DK.rowLt κ)]
  rw [genVec_row, hJ, pushTo_at cs l _ _ 0 W.restPart _ (DK.keptTail κ) n]
  by_cases cA : (entAt cs l n).1 = 1 + mem κ ∧ (entAt cs l n).2.1 = Part.main
  · have n0 : ¬ ((entAt cs l n).1 = 0 ∧ (entAt cs l n).2.1 = W.restPart) := fun c => by
      have := cA.1
      omega
    rw [if_pos cA, if_neg n0, if_neg n0, add_zero, add_zero, (DK.anewIs κ n).2 cA.1, cA.2,
      genKept_new W (pl κ) (row κ) _ (aKept κ) (DK.tailPieces κ) (DK.tailInc κ) F.logC x hx t
        (DK.notG κ) (DK.padNodup κ)]
    by_cases hp : (entAt cs l n).2.2 ∈ (pl κ).pad.map (·.index)
    · rw [if_pos hp, if_pos hp]
    · rw [if_neg hp, if_neg hp]
      exact form _ (DK.keptIn κ n cA.1 cA.2)
  · rw [if_neg cA, zero_add]
    by_cases cB : (entAt cs l n).1 = 0 ∧ (entAt cs l n).2.1 = W.restPart
    · rw [if_pos cB, if_pos cB, (D.gIs n).2 cB.1, cB.2,
        genKept_g W (pl κ) (row κ) _ (aKept κ) (DK.tailPieces κ) (DK.tailInc κ) F.logC x hx t
          (DK.notG κ)]
      refine congrArg₂ (· + ·) (stretchAt_congr _ _ _ _ _ (fun q hq => form _ (DK.padIn κ q hq)) _)
        ?_
      rw [hr, ← D.codeC]
      unfold stretchAt
      exact Finset.sum_range _
    · rw [if_neg cB, if_neg cB, add_zero]
      exact genKept_other W (pl κ) (row κ) _ (aKept κ) (DK.tailPieces κ) (DK.tailInc κ) F.logC x hx
          t
        _ _ (fun c => cA ⟨(DK.anewIs κ n).1 c.1, c.2⟩) (fun c => cB ⟨(D.gIs n).1 c.1, c.2⟩) _

end Join

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.row_sum
#print axioms VerifiableInference.Desc.First.K2Hands.kept_reads
