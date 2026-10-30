-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/RowLaw.lean: THE CALL AT THE MAKER's ROW, WITH THE PIECE IN CLOSED FORM: `keepsAt_of_lawⱼ` (PieceSame.lean) and `rowAtⱼ` (RowCut.lean) joined. Book-keeping, general in the description.
Main names. `keepsAt_at₁` | `₂` | `₃`: where a kind's law is shown AT `pieceOf (held b) (cutBase …) (cutDs …) (cutPut …) x`, b the chain's n-th block, x its own extractor and errors at that stretch, with `Err.le x.err (restⱼ n (cutDs …)).err`: that is the field `KeepsAt on L ‹the row› n`. What the base and the stretch ARE: `cutBase_eq` · `cutDs_inner` | `cutDs_last` · `cutPut_inner` | `cutPut_last` (RowCut.lean).
Nothing on soundness.

-/
import Johnson.Top.Fire.Code.PieceSame
import Johnson.Top.Fire.Code.RowCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open _root_.Iop (Err)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

section
variable {Xi W : Type} (C : CK) (F : FileDescription Xi) (D : WholeD)
    (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
    (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (dW wEnd : W)

/-- **The call at chain 1's row, the piece in closed form.** -/
theorem keepsAt_at₁ (on L) (n : ℕ)
    (law : ∀ b : Block F.S₁ F.Cl, (c₁ :: k₁)[n]? = some b →
      ∃ x : Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W (cutDs D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n),
        (pieceOf (held b) (cutBase 0 D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n) (cutDs D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n) (cutPut [sealRound] (k₁.map (held (P := F.XiPub))) n) x).ior.red.Keeps
          (on n) (on (n + 1)) (L n) (L (n + 1)) x.err ∧ Err.le x.err (rest₁ n (cutDs D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n)).err) :
    KeepsAt on L ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) n := fun p hp => by
  obtain ⟨b, hb, rfl⟩ := rowAt₁ C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd n p hp
  obtain ⟨x, hx, hle⟩ := law b hb
  exact keeps_same (pieceOf (held b) _ _ _ x) (rest₁ n _) hx hle

/-- **The call at chain 2's row, the piece in closed form.** -/
theorem keepsAt_at₂ (on L) (n : ℕ)
    (law : ∀ b : Block F.S₂ F.Cl, (c₂ :: k₂)[n]? = some b →
      ∃ x : Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W (cutDs D.ds₂ (held c₂ : Block ((F.XiPub × F.S₁) × F.S₂) F.Cl) (k₂.map held) n),
        (pieceOf (held b) (cutBase D.t₁ D.ds₂ (held c₂ : Block ((F.XiPub × F.S₁) × F.S₂) F.Cl) (k₂.map held) n) (cutDs D.ds₂ (held c₂ : Block ((F.XiPub × F.S₁) × F.S₂) F.Cl) (k₂.map held) n) (cutPut [] (k₂.map (held (P := (F.XiPub × F.S₁)))) n) x).ior.red.Keeps
          (on n) (on (n + 1)) (L n) (L (n + 1)) x.err ∧ Err.le x.err (rest₂ n (cutDs D.ds₂ (held c₂ : Block ((F.XiPub × F.S₁) × F.S₂) F.Cl) (k₂.map held) n)).err) :
    KeepsAt on L ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) n := fun p hp => by
  obtain ⟨b, hb, rfl⟩ := rowAt₂ C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd n p hp
  obtain ⟨x, hx, hle⟩ := law b hb
  exact keeps_same (pieceOf (held b) _ _ _ x) (rest₂ n _) hx hle

/-- **The call at chain 3's row, the piece in closed form.** -/
theorem keepsAt_at₃ (on L) (n : ℕ)
    (law : ∀ b : Block F.S₃ F.Cl, (c₃ :: k₃)[n]? = some b →
      ∃ x : Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W (cutDs D.ds₃ (held c₃ : Block ((F.XiPub × F.S₁ × F.S₂) × F.S₃) F.Cl) (k₃.map held) n),
        (pieceOf (held b) (cutBase (D.t₁ + D.t₂) D.ds₃ (held c₃ : Block ((F.XiPub × F.S₁ × F.S₂) × F.S₃) F.Cl) (k₃.map held) n) (cutDs D.ds₃ (held c₃ : Block ((F.XiPub × F.S₁ × F.S₂) × F.S₃) F.Cl) (k₃.map held) n) (cutPut [] (k₃.map (held (P := (F.XiPub × F.S₁ × F.S₂)))) n) x).ior.red.Keeps
          (on n) (on (n + 1)) (L n) (L (n + 1)) x.err ∧ Err.le x.err (rest₃ n (cutDs D.ds₃ (held c₃ : Block ((F.XiPub × F.S₁ × F.S₂) × F.S₃) F.Cl) (k₃.map held) n)).err) :
    KeepsAt on L ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃) n := fun p hp => by
  obtain ⟨b, hb, rfl⟩ := rowAt₃ C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd n p hp
  obtain ⟨x, hx, hle⟩ := law b hb
  exact keeps_same (pieceOf (held b) _ _ _ x) (rest₃ n _) hx hle

end

end LPFD

#print axioms LPFD.keepsAt_at₁
#print axioms LPFD.keepsAt_at₂
#print axioms LPFD.keepsAt_at₃
