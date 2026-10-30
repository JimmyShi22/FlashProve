-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerRowAlong.lean: THE SHARED ROW's PIECES BY MAKE: EACH PIECE's WRITTEN
ROUNDS
ARE ITS OWN BLOCK's DECLARED ROUNDS' DATA: so that what the ledger at the cap asks of the letters
d21 d22 · d4 · d51 d52 · d7 (entries, kinds, stored tables, trees opened, trees sent) becomes a fact
on
the blocks' declared rounds. A call of stretchOfData (Johnson/Desc/Sound/Stretch.lean) at
the maker's own value piecesAt.
  row_along      ∀ p ∈ the shared row, Along (RoundIs (numAt D.t₁ D.t₂ 1)) p.b.rounds p.ds
  roundIs_one    at a piece with one declared and one written round: RoundIs r d: d.entry = r.entry
  ·
                 Fmt.kindOf r.entry.name = some d.kind · d.items = r.items · d.stored = r.stored ·
                 d.opens = r.opens.map … · d.trees.length = r.entry.roots
  roundIs_two    the like at two
OBJECT   (atDesc F (piecesAt …)).p₂ :: .l₂
USER     the join of row_by_make (Johnson/Desc/K14/Law/LedgerRowByMake.lean) with the ledger's top
at
         the seat: not called here
What is not claimed. Which entries the kind's blocks declare at the written plan. Nothing on
soundness.

-/
import Johnson.Desc.K14.Law.LedgerRowByMake
import Johnson.Desc.Sound.Stretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Shared

/-- **Along every piece of the shared row.** -/
theorem row_along {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (hD : F.data file = .ok D) (C : CK) (b₁ : Block F.S₁ F.Cl)
    (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl) (l₂ : List (Block F.S₂ F.Cl))
    (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl)) (h₁ : F.first.blocksInOrder = b₁ :: l₁)
    (h₂ : F.shared.blocksInOrder = b₂ :: l₂) (h₃ : F.second.blocksInOrder = b₃ :: l₃)
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) :
    ∀ p ∈ (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₂ ::
        (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₂,
      Along (RoundIs (numAt D.t₁ D.t₂ 1)) p.b.rounds p.ds :=
  (stretchOfData Xi F file D hD C _ _ _ _ _ _ _ _
    (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd))
    (held b₁) (l₁.map held) (held b₂) (l₂.map held) (held b₃) (l₃.map held) rest₁ rest₂ rest₃
    sealRound (by rw [h₁]; exact held_map_rounds (b₁ :: l₁))
    (by rw [h₂]; exact held_map_rounds (b₂ :: l₂))
    (by rw [h₃]; exact held_map_rounds (b₃ :: l₃)) ⟨rfl, rfl, rfl⟩).2.1

theorem roundIs_one {num : Fmt.TreeSource → ℕ} {r : Fmt.DeclaredRound} {d : RDT}
    (h : Along (RoundIs num) [r] [d]) : RoundIs num r d := h.1

theorem roundIs_two {num : Fmt.TreeSource → ℕ} {r₁ r₂ : Fmt.DeclaredRound} {d₁ d₂ : RDT}
    (h : Along (RoundIs num) [r₁, r₂] [d₁, d₂]) : RoundIs num r₁ d₁ ∧ RoundIs num r₂ d₂ :=
  ⟨h.1, h.2.1⟩

end Desc.K14.Law
