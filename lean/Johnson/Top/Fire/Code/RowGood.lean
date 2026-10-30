-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/RowGood.lean: A GENERAL JOINT, for a row that is no sending: FROM A KIND's Piece.GoodIn (Johnson/Desc/Sound/GoodIn.lean: the form with a witness) AT THE KIND's OWN RELATIONS TO THE FIELD KeepsAt AT THE MAKER's ROW AND AT THE TABLES' RELATIONS. General in the description.
  GoodIn.change     a change of relations, for a piece whose extractor hands the witness on: behind: the tables' gives the kind's; in front: the kind's gives the tables' (both may use the promises, the yes, and the tables' behind)
  keepsAt_good₁     (THE KIND's WITNESS TYPE W' NEED NOT BE THE MAKER's W: a piece's reduction does not read its extractor) at chain 1's row n: the block is b₀ · the stretch is ds₀ · nothing is put back · GoodIn at pieceOf (held b₀) ‹the cut's base› ds₀ [] x · x's errors are at most the maker's: KeepsAt on (fun k a => ∃ w, Rw k a w) ‹the row› n
Book-keeping: keepsAt_at₁ (RowLaw.lean) and keeps_of_goodIn (Johnson/Desc/Plain/FromGood.lean). Nothing on soundness.
-/
import Johnson.Top.Fire.Code.RowLaw
import Johnson.Desc.Plain.FromGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open _root_.Iop (Err Doomed)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

section
variable {S Cl W : Type} {C : CK} {Fr : Frame}

theorem GoodIn.change {p : Piece C Fr S Cl W} {on on' : S × Fr.E.Str → Prop} {R R' Rn Rn' : S × Fr.E.Str → W → Prop}
    (h : p.GoodIn on on' R R') (hx : ∀ a τ w, p.ext a τ w = w)
    (hbehind : ∀ a τ b w, on a → p.ior.red.out a τ = some b → on' b → Rn' b w → R' b w)
    (hfront : ∀ a τ b w, on a → p.ior.red.out a τ = some b → on' b → Rn' b w → R a w → Rn a w) :
    p.GoodIn on on' Rn Rn' := fun a ha =>
  Doomed.mono _ _ (fun τ hτ b hb => ⟨(hτ b hb).1, fun w hw => by
    have h1 := (hτ b hb).2 w (hbehind a τ b w ha hb (hτ b hb).1 hw)
    rw [hx] at h1 ⊢
    exact hfront a τ b w ha hb (hτ b hb).1 hw h1⟩) (h a ha)

end

section
variable {Xi W : Type} (C : CK) (F : FileDescription Xi) (D : WholeD)
    (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
    (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (dW wEnd : W)

theorem keepsAt_good₁ {W' : Type} (on : ℕ → (F.XiPub × F.S₁) × (frameAt D (allOf D) D.key₁ 0).E.Str → Prop)
    (Rw : ℕ → (F.XiPub × F.S₁) × (frameAt D (allOf D) D.key₁ 0).E.Str → W' → Prop) (n : ℕ) (b₀ : Block F.S₁ F.Cl)
    (hb : ∀ b, (c₁ :: k₁)[n]? = some b → b = b₀) (ds₀ : List RDT)
    (hds : cutDs D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n = ds₀)
    (hput : cutPut [sealRound] (k₁.map (held (P := F.XiPub))) n = [])
    (x : Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W' ds₀)
    (G : (pieceOf (held b₀) (cutBase 0 D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n) ds₀ [] x).GoodIn (on n) (on (n + 1)) (Rw n) (Rw (n + 1)))
    (hle : Err.le x.err (rest₁ n ds₀).err) :
    KeepsAt on (fun k a => ∃ w, Rw k a w) ((atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) n := by
  subst hds
  refine keepsAt_at₁ C F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd on _ n fun b hb' => ?_
  obtain rfl := hb b hb'
  rw [hput]
  exact ⟨⟨fun _ _ w => w, x.err⟩, keeps_of_goodIn _ _ _ _ _ G, hle⟩

end

end LPFD

#print axioms LPFD.GoodIn.change
#print axioms LPFD.keepsAt_good₁
