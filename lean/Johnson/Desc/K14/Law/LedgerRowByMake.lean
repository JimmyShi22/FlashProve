-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerRowByMake.lean: THE SHARED ROW's TWELVE PIECES, BY NAME, WITH ALL THAT
THE
LEDGER AT THE CAP ASKS OF HOW THEY ARE MADE: at the maker's own value piecesAt, at any description
whose shared chain has twelve blocks. No kind's law, no chance, no word of a kind.
  eleven_of_length   a list of eleven is eleven letters
  row_by_make        F.data file = .ok D · F.sealLast · the three chains' blocks by name · twelve
                     blocks on the shared chain · AtCap rest₂ · the first of them says "ok" and
                     declares no round · N.lo = D.t₁ ⊢ THERE ARE pt x2 … x11 with
                     (1) the row behind its first piece IS [pt, x2, …, x11]
                     (2) hps: the twelve pieces hold the chain's own blocks, below and lifted
                     (3) ht: they tile the chain (Tiled)
                     (4) hop · hf1 · hfb · hcap at f := the first piece, PT := pt,
                         MM := [x2, …, x11]: four_at_data (Johnson/Desc/K14/Law/LedgerOpensOwn.lean)
OBJECT   (atDesc F (piecesAt …)).p₂ :: .l₂
USER     the ledger's top at the seat (ledger_at_seat | row_forms_all): its hps
         comes by rewriting b₂ :: l₂ as the seated chain's list at the concrete description: not
         called here
What is not claimed. That the seated description's T is piecesAt at the cap. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerOpensOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open _root_.Iop (Err)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Shared

/-- A list of eleven is eleven letters. -/
theorem eleven_of_length {α : Type} (l : List α) (h : l.length = 11) :
    ∃ pt x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, l = [pt, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] := by
  match l, h with
  | [pt, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11], _ => exact ⟨pt, x2, x3, x4, x5, x6, x7, x8, x9,
      x10, x11, rfl⟩

/-- **THE SHARED ROW BY MAKE.** -/
theorem row_by_make {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (hD : F.data file = .ok D) (hs : F.sealLast = true) (C : CK) (b₁ : Block F.S₁ F.Cl)
    (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl) (l₂ : List (Block F.S₂ F.Cl))
    (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl)) (h₁ : F.first.blocksInOrder = b₁ :: l₁)
    (h₂ : F.shared.blocksInOrder = b₂ :: l₂) (h₃ : F.second.blocksInOrder = b₃ :: l₃)
    (h12 : (b₂ :: l₂).length = 12)
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (hc : AtCap rest₂) (hok : ∀ s rs gs, b₂.decide s rs gs = .ok s)
    (hr : b₂.rounds = []) (N : NumbersS) (hlo : N.lo = D.t₁) :
    ∃ pt x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Piece C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁)
        × F.S₂) F.Cl W,
      (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₂ =
        [pt, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] ∧
      ((atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₂ ::
        [pt, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11]).map (·.b) =
          ((b₂ :: l₂).map below).map (Block.lift Prod.snd fun t s => (t.1, s)) ∧
      Tiled (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₂
        [pt, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] ∧
      (∀ x ∈ [x2, x3, x4, x5, x6, x7, x8, x9, x10, x11], ∀ d₀ ∈ x.ds, ∀ j ∈ d₀.opens, N.lo ≤ j) ∧
      (∀ a τ b, (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d
          wEnd)).p₂.ior.red.out
        a τ = some b → b.1 = a.1) ∧
      pt.base = (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₂.base ∧
      EachCapped 128 ((atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₂ ::
        pt :: [x2, x3, x4, x5, x6, x7, x8, x9, x10, x11]) := by
  obtain ⟨hO, hf, -⟩ := paidAtDesc Xi W F file D hD hs C b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃ rest₁ rest₂
    rest₃ d wEnd
  have hb : ((atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₂ ::
      (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₂).map (·.b) =
      ((b₂ :: l₂).map below).map (Block.lift Prod.snd fun t s => (t.1, s)) := by
    rw [← h₂]
    exact hO.b₂
  have hlen : (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₂.length = 11
      := by
    have h := congrArg List.length hb
    simp only [List.length_map, List.length_cons] at h h12
    omega
  obtain ⟨pt, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, hl⟩ := eleven_of_length _ hlen
  obtain ⟨k1, k2, k3, k4⟩ := four_at_data F file D hD hs C b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃ rest₁ rest₂
    rest₃ d wEnd hc hok hr N hlo _ pt [x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] rfl hl
  refine ⟨pt, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, hl, ?_, ?_, k1, k2, k3, k4⟩
  · rw [← hl]
    exact hb
  · rw [← hl]
    exact hf.tiled₂

end Desc.K14.Law
