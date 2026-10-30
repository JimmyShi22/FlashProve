-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyState.lean: WHAT A PROVER HOLDS AT A STAGE OF THE PROXIMITY TEST, BY INDEX,
and how it passes from a stage to the next. Definitions, statements and proofs. No dependent type
stands in the state: the four typed letters μ ρ φ ψ of this folder's laws are read off it.

  PS                 the stage's main table and carried mask table by the table's index · these
                     rows' tails · the further table's rows and tails · at the last stage: the
                     second message's main row and its tail
  μOf, ρOf, φOf, ψOf the four letters off a state; by their text the six premises hM | hZ | hTM |
                     hTZ | hF | hT of hy_stage and switch_V hold (muOf_main ... psiOf_at: each rfl)
  nextPS             behind a fold at γ and a switch: the new tables are gMain | gMask
                     (Johnson/Prover/Link/SwitchMsg.lean) at the folded messages and tails; all
                     else is handed in
  muOf_next          μOf s' (nextPS ...) = gMsg hf (foldMsg ...) (foldTl ...) fr
  firstPS            the link's first stage: the two members' rows and tails on their blocks
  muOf_first, rhoOf_first   μOf | ρOf of it are mu0 | rho0 (FrontMsg.lean, FrontCols.lean)
  first_mem ... first_psi   the eight premises on μ ρ φ ψ of hy_first and switch_V_first, at it

Not shown here. That any strategy holds such a state, or sends what this folder's laws ask.
Nothing on how a tail, a further table or free room is chosen; nothing on what any entry discloses
or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FrontCols
import Johnson.Prover.Link.FoldEnc

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice Cb

/-- **What a prover holds at a stage.** -/
structure PS where
  tabM : ℕ → GE
  tabZ : ℕ → GE
  tM : ℕ → ℕ → GE
  tZ : ℕ → ℕ → GE
  fM : ℕ → ℕ → GE
  fT : ℕ → ℕ → GE
  /-- at the last stage alone: the second message's main row, and its tail -/
  sM : ℕ → GE
  sT : ℕ → GE

def μOf (s : Sg) (P : PS) : s.cIn.J → GE
  | .inl x => P.tabM (Sz.rowNo x.1 + 2 ^ (s.h + s.g) * x.2.val)
  | .inr x => P.tabZ (Sz.rowNo x.1 + 2 ^ s.h * x.2.val)

def ρOf (s : Sg) (P : PS) : s.cIn.Q → GE
  | .inl x => P.tM (Sz.rowNo x.1) x.2.val
  | .inr x => P.tZ (Sz.rowNo x.1) x.2.val

def φOf (s : Sg) (P : PS) : s.cFr.J → GE := fun x => P.fM (Sz.rowNo x.1) x.2.val
def ψOf (s : Sg) (P : PS) : s.cFr.Q → GE := fun x => P.fT (Sz.rowNo x.1) x.2.val

theorem muOf_main (s : Sg) (P : PS) (b j) :
    μOf s P (.inl (b, j)) = P.tabM (Sz.rowNo b + 2 ^ (s.h + s.g) * j.val) := rfl
theorem muOf_mask (s : Sg) (P : PS) (b j) :
    μOf s P (.inr (b, j)) = P.tabZ (Sz.rowNo b + 2 ^ s.h * j.val) := rfl
theorem rhoOf_main (s : Sg) (P : PS) (b q) : ρOf s P (.inl (b, q)) = P.tM (Sz.rowNo b) q.val := rfl
theorem rhoOf_mask (s : Sg) (P : PS) (b q) : ρOf s P (.inr (b, q)) = P.tZ (Sz.rowNo b) q.val := rfl
theorem phiOf_at (s : Sg) (P : PS) (b j) : φOf s P (b, j) = P.fM (Sz.rowNo b) j.val := rfl
theorem psiOf_at (s : Sg) (P : PS) (b q) : ψOf s P (b, q) = P.fT (Sz.rowNo b) q.val := rfl

/-- **From a stage to the next.** new: the new rows' tails, the next further table, the last
stage's second message. -/
def nextPS (s : Sg) (γ : Fin (s.h + s.g) → GE) (fr : ℕ → GE) (new P : PS) : PS :=
  { new with
    tabM := gMain s (foldMsg s (μOf s P) (φOf s P) γ)
    tabZ := gMask s (foldMsg s (μOf s P) (φOf s P) γ) (foldTl s (ρOf s P) (ψOf s P) γ) fr }

theorem muOf_next {s s' : Sg} (hf : CsFit s s') (γ : Fin (s.h + s.g) → GE) (fr : ℕ → GE)
    (new P : PS) :
    μOf s' (nextPS s γ fr new P) =
      gMsg hf (foldMsg s (μOf s P) (φOf s P) γ) (foldTl s (ρOf s P) (ψOf s P) γ) fr := by
  funext j
  rw [gMsg_tab]
  rcases j with x | x <;> rfl

/-! ## The link's first stage -/

variable (S : Sz) (t : ℕ) (m : Bool → S.MJ → GE) (tN : Bool → ℕ → ℕ → GE) (φN ψN : ℕ → GE)

/-- The link's first stage: two members' blocks of 2 ^ aR rows side by side. THE WRITTEN 0: on a
block's rows from R on (tabM, tM); on the whole carried mask table and its tails (tabZ, tZ); on the
last stage's two fields (sM, sT). -/
def firstPS : PS where
  tabM := fun i =>
    if i % 2 ^ (S.P.aR + 1) % 2 ^ S.P.aR < S.P.R then
      membN S m (decide (2 ^ S.P.aR ≤ i % 2 ^ (S.P.aR + 1))) (i % 2 ^ (S.P.aR + 1) % 2 ^ S.P.aR)
        (i / 2 ^ (S.P.aR + 1))
    else 0
  tabZ := fun _ => 0
  tM := fun n q => if n % 2 ^ S.P.aR < S.P.R then tN (decide (2 ^ S.P.aR ≤ n)) (n % 2 ^ S.P.aR) q
    else 0
  tZ := fun _ _ => 0
  fM := fun _ => φN
  fT := fun _ => ψN
  sM := fun _ => 0
  sT := fun _ => 0

theorem rhoOf_first : ρOf (S.sg t) (firstPS S m tN φN ψN) = rho0 S t tN := by
  funext x
  rcases x with x | x <;> rfl

theorem muOf_first : μOf (S.sg t) (firstPS S m tN φN ψN) = mu0 S t m := by
  funext x
  rcases x with x | x
  · have hlt : Sz.rowNo x.1 < 2 ^ (S.P.aR + 1) :=
      lt_of_lt_of_eq (rowNo_lt x.1) (by show 2 ^ (0 + (S.P.aR + 1)) = _; rw [Nat.zero_add])
    have hp : 0 < 2 ^ (S.P.aR + 1) := Nat.pos_of_ne_zero (by positivity)
    have e1 : (Sz.rowNo x.1 + 2 ^ (S.P.aR + 1) * x.2.val) % 2 ^ (S.P.aR + 1) = Sz.rowNo x.1 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    have e2 : (Sz.rowNo x.1 + 2 ^ (S.P.aR + 1) * x.2.val) / 2 ^ (S.P.aR + 1) = x.2.val := by
      rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hlt, Nat.zero_add]
    have e0 : Sz.rowNo x.1 + 2 ^ (0 + (S.P.aR + 1)) * x.2.val =
        Sz.rowNo x.1 + 2 ^ (S.P.aR + 1) * x.2.val := by
      have : 0 + (S.P.aR + 1) = S.P.aR + 1 := Nat.zero_add _
      exact congrArg (fun n => Sz.rowNo x.1 + 2 ^ n * x.2.val) this
    refine (congrArg (firstPS S m tN φN ψN).tabM e0).trans ?_
    show (if (Sz.rowNo x.1 + 2 ^ (S.P.aR + 1) * x.2.val) % 2 ^ (S.P.aR + 1) % 2 ^ S.P.aR < S.P.R
      then _ else _) = (if h : Sz.rowNo x.1 % 2 ^ S.P.aR < S.P.R then _ else _)
    rw [e1, e2]
    by_cases c : Sz.rowNo x.1 % 2 ^ S.P.aR < S.P.R
    · rw [if_pos c, dif_pos c]
      unfold membN
      rw [dif_pos ⟨c, x.2.isLt⟩]
    · rw [if_neg c, dif_neg c]
  · rfl

theorem first_mem (a : Bool) (i : ℕ) (hi : i < S.P.R) (j) :
    μOf (S.sg t) (firstPS S m tN φN ψN) (.inl (memRow S t a i, j)) = membN S m a i j.val := by
  rw [muOf_first]
  refine (mu0_atJ S t m a (.inl (⟨i, hi⟩, j))).trans ?_
  unfold membN
  rw [dif_pos ⟨hi, j.isLt⟩]

theorem first_free : FreeZero S t (μOf (S.sg t) (firstPS S m tN φN ψN)) := by
  rw [muOf_first]
  exact free_mu0 S t m

theorem first_mask (j) : μOf (S.sg t) (firstPS S m tN φN ψN) (.inr j) = 0 := rfl

theorem first_tail (a : Bool) (i : ℕ) (hi : i < S.P.R) (q) :
    ρOf (S.sg t) (firstPS S m tN φN ψN) (.inl (memRow S t a i, q)) = tN a i q.val := by
  obtain ⟨e1, e2⟩ := rowNo_split S t a i (lt_of_lt_of_le hi (le_two_pow_clog S.P.R))
  show (if Sz.rowNo (memRow S t a i) % 2 ^ S.P.aR < S.P.R then _ else _) = _
  rw [e1, e2, if_pos hi]

theorem first_tail_free (a : Bool) (i : ℕ) (q) (h1 : S.P.R ≤ i) (h2 : i < 2 ^ S.P.aR) :
    ρOf (S.sg t) (firstPS S m tN φN ψN) (.inl (memRow S t a i, q)) = 0 := by
  show (if Sz.rowNo (memRow S t a i) % 2 ^ S.P.aR < S.P.R then _ else _) = _
  rw [(rowNo_split S t a i h2).1, if_neg (Nat.not_lt.2 h1)]

theorem first_tail_mask (q) : ρOf (S.sg t) (firstPS S m tN φN ψN) (.inr q) = 0 := rfl
theorem first_phi (b j) : φOf (S.sg t) (firstPS S m tN φN ψN) (b, j) = φN j.val := rfl
theorem first_psi (b q) : ψOf (S.sg t) (firstPS S m tN φN ψN) (b, q) = ψN q.val := rfl

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.PS
#print axioms Johnson.Prover.Link.muOf_next
#print axioms Johnson.Prover.Link.rhoOf_first
#print axioms Johnson.Prover.Link.muOf_first
#print axioms Johnson.Prover.Link.first_mem
#print axioms Johnson.Prover.Link.first_free
#print axioms Johnson.Prover.Link.first_mask
#print axioms Johnson.Prover.Link.first_tail
#print axioms Johnson.Prover.Link.first_tail_free
#print axioms Johnson.Prover.Link.first_tail_mask
#print axioms Johnson.Prover.Link.first_phi
#print axioms Johnson.Prover.Link.first_psi
