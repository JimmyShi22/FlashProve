-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/Own.lean: THE TREES THAT A PROXIMITY TEST's CHAIN SENDS ITSELF, BY NUMBER; a
chain's transcript cut into blocks and joined again; lists of rounds that are equal by an equation.
Statements and proofs.

  `joinT_splitT`, `trL_blOf`: a chain's transcript over the list of its rounds, cut into the blocks'
    transcripts (`blOf`, Johnson/Desc/K12/Law/K12Lemma.lean) and joined again, is itself. (That file
    has the other way round.)
  `ownCols_of`: `OwnCols` (Src.lean) from the columns of a transcript by tree number, by
    `colAtS_block_zero` | `_succ` (OnBytes/Slice/ManyView.lean).
  `castT`, `castE`, `doomed_castL`, `rvSL_cast`, `pass_cast`, `colAtS_cast`, `errList_cast`: along
    an equation of two lists of rounds.
A tool.
-/
import Johnson.Desc.K12.Coin.Src
import Johnson.Desc.K12.Coin.Sheet
import OnBytes.Slice.ManyView

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob _root_.Run
open H2K.JointK (splitT blOf)

theorem joinT_splitT : ∀ (ds₁ ds₂ : List PQ.RD) (τ : Tr (PQ.uL (ckP .two) (ds₁ ++ ds₂))),
    joinT ds₁ ds₂ (splitT ds₁ ds₂ τ).1 (splitT ds₁ ds₂ τ).2 = τ
  | [], _, _ => rfl
  | _ :: ds₁, ds₂, (m, c, τ) => by
    show (m, c, joinT ds₁ ds₂ (splitT ds₁ ds₂ τ).1 (splitT ds₁ ds₂ τ).2) = (m, c, τ)
    rw [joinT_splitT ds₁ ds₂ τ]

theorem trL_blOf {s : Sg} (c : OnBytes.Slice.Chain s) :
    ∀ τ : Tr (PQ.uL (ckP .two) c.rds), c.trL (blOf c τ) = τ := by
  induction c with
  | last s e dL dB fu fs εb => intro τ; rfl
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    intro τ
    show joinT (foldRds s dE dT) ([dS, dC] ++ next.rds)
      (splitT (foldRds s dE dT) ([dS, dC] ++ next.rds) τ).1
      (joinT [dS, dC] next.rds
        (splitT [dS, dC] next.rds (splitT (foldRds s dE dT) ([dS, dC] ++ next.rds) τ).2).1
        (next.trL (blOf next
          (splitT [dS, dC] next.rds (splitT (foldRds s dE dT) ([dS, dC] ++ next.rds) τ).2).2))) = τ
    rw [ih, joinT_splitT, joinT_splitT]

/-- `OwnCols` from the columns of a transcript by tree number: the chain's k-th tree is the tree of
own number n + k. -/
theorem ownCols_of (P : ToldO → ℕ → List UInt64 → Prop) {s : Sg} (c : OnBytes.Slice.Chain s)
    (hc : c.Trees) (b : c.Bl) (n : ℕ)
    (hP : ∀ k (o : ToldO), o.2 = .own (n + k) → ∀ x col, P o x col →
      PQ.colAtS (ckP .two) c.rds (c.trL b) k x = some col) : OwnCols P n c b := by
  induction c generalizing n with
  | last s e dL dB fu fs εb => trivial
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    obtain ⟨hE, hT, hS, hC, hN⟩ := hc
    refine ⟨fun o ho x col hp => ?_, ih hN b.2.2 (n + 1) fun k o ho x col hp => ?_⟩
    · have h0 := hP 0 o ho x col hp
      have h1 : PQ.colAtS (ckP .two) (foldRds s dE dT ++ ([dS, dC] ++ next.rds))
          (joinT (foldRds s dE dT) _ b.1 (joinT [dS, dC] next.rds b.2.1 (next.trL b.2.2))) 0 x =
          some col := h0
      rw [colAtS_block_zero s dE dT dS dC next.rds hE hT hS] at h1
      exact treeCol_some dS b.2.1.1 x col h1
    · have h0 := hP (k + 1) o (by rw [ho]; congr 1; omega) x col hp
      have h1 : PQ.colAtS (ckP .two) (foldRds s dE dT ++ ([dS, dC] ++ next.rds))
          (joinT (foldRds s dE dT) _ b.1 (joinT [dS, dC] next.rds b.2.1 (next.trL b.2.2))) (k + 1)
          x = some col := h0
      rwa [colAtS_block_succ s dE dT dS dC next.rds hE hT hS hC] at h1

/-! ## Along an equation of two lists of rounds -/

def castT {R R' : List PQ.RD} (h : R = R') (τ : Tr (PQ.uL (ckP .two) R)) :
    Tr (PQ.uL (ckP .two) R') := h ▸ τ

def castE {R R' : List PQ.RD} (h : R = R') (ε : Err (PQ.uL (ckP .two) R)) :
    Err (PQ.uL (ckP .two) R') := h ▸ ε

theorem doomed_castL {R R' : List PQ.RD} (h : R = R') (ε : Err (PQ.uL (ckP .two) R))
    (bad : Tr (PQ.uL (ckP .two) R) → Prop) (H : Doomed (PQ.uL (ckP .two) R) ε bad) :
    Doomed (PQ.uL (ckP .two) R') (castE h ε) fun τ => bad (castT h.symm τ) := by
  subst h
  exact H

theorem rvSL_cast {R R' : List PQ.RD} (h : R = R') (τ : Tr (PQ.uL (ckP .two) R)) :
    PQ.rvSL (ckP .two) R' (castT h τ) = PQ.rvSL (ckP .two) R τ := by
  subst h
  rfl

theorem pass_cast {R R' : List PQ.RD} (h : R = R') (τ : Tr (PQ.uL (ckP .two) R)) :
    PQ.passSL (ckP .two) R' (PQ.rhoSL (ckP .two) R' (castT h τ)) =
      PQ.passSL (ckP .two) R (PQ.rhoSL (ckP .two) R τ) := by
  subst h
  rfl

theorem colAtS_cast {R R' : List PQ.RD} (h : R = R') (τ : Tr (PQ.uL (ckP .two) R)) (n x : ℕ) :
    PQ.colAtS (ckP .two) R' (castT h τ) n x = PQ.colAtS (ckP .two) R τ n x := by
  subst h
  rfl

theorem errList_cast {R R' : List PQ.RD} (h : R = R') (ε : Err (PQ.uL (ckP .two) R)) :
    errList _ (castE h ε) = errList _ ε := by
  subst h
  rfl

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.trL_blOf
#print axioms VerifiableInference.Desc.K12.Coin.ownCols_of
#print axioms VerifiableInference.Desc.K12.Coin.doomed_castL
