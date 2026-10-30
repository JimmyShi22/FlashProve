-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerOpensOwn.lean: THE LAST CALL FOR THE LEDGER's PREMISE hop ("no tree below
lo is opened at the ten pieces"): the premise hown of four_at_pieces
(Johnson/Desc/K14/Law/LedgerByMake.lean) IS A THEOREM OF K12's FILES, from F.data's yes alone:
opens_own_stretch (Johnson/Desc/K12/Law/OpensOwn.lean): CALLED.
  hown_of_data   F.data file = .ok D ⊢ ∀ d ∈ D.ds₂, ∀ j ∈ d.opens, D.t₁ ≤ j
  four_at_data   four_at_pieces without hown: hop · hf1 · hfb · hcap, to the letter
LEFT     F.data file = .ok D · F.sealLast = true · the three chains' blocks by name · AtCap rest₂ ·
the
         shared chain's first block says "ok" and declares no round · N.lo = D.t₁ · the two
         equations of letters.
What is not claimed. That the seated description's T is the maker's at the cap. Nothing on
soundness.

-/
import Johnson.Desc.K14.Law.LedgerByMake
import Johnson.Desc.K12.Law.OpensOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open _root_.Iop (Err)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Shared

/-- **The shared chain's data open no tree of the first chain.** -/
theorem hown_of_data {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) : ∀ d ∈ D.ds₂, ∀ j ∈ d.opens, D.t₁ ≤ j := fun d hd =>
  H2K.JointK.opens_own_stretch F file D h 0 D.ds₂.length d (by simpa using hd)

/-- **THE FOUR BINDERS FROM THE DATA's YES.** -/
theorem four_at_data {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (hD : F.data file = .ok D) (hs : F.sealLast = true) (C : CK) (b₁ : Block F.S₁ F.Cl)
    (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl) (l₂ : List (Block F.S₂ F.Cl))
    (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl)) (h₁ : F.first.blocksInOrder = b₁ :: l₁)
    (h₂ : F.shared.blocksInOrder = b₂ :: l₂) (h₃ : F.second.blocksInOrder = b₃ :: l₃)
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (hc : AtCap rest₂) (hok : ∀ s rs gs, b₂.decide s rs gs = .ok s)
    (hr : b₂.rounds = []) (N : NumbersS)
    (hlo : N.lo = D.t₁)
    (f PT : Piece C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) F.Cl W)
    (MM : List (Piece C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) F.Cl W))
    (hp : (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₂ = f)
    (hl : (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₂ = PT :: MM) :
    (∀ x ∈ MM, ∀ d₀ ∈ x.ds, ∀ j ∈ d₀.opens, N.lo ≤ j) ∧
      (∀ a τ b, f.ior.red.out a τ = some b → b.1 = a.1) ∧ PT.base = f.base ∧
      EachCapped 128 (f :: PT :: MM) :=
  four_at_pieces F file D hD hs C b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃ rest₁ rest₂ rest₃ d wEnd hc hok hr
    (hown_of_data F file D hD) N hlo f PT MM hp hl

end Desc.K14.Law
