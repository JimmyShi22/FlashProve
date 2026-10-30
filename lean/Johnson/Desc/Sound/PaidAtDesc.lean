-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/PaidAtDesc.lean: THREE PREMISES OF THE RULES keySoundOfLaws | proofSoundOfLaws
(the pieces hold the description's own blocks: OfDesc · their stretches are the
file's three chains: Fits · RowFit) PAID TOGETHER AT ONE VALUE, for every description F, FROM TWO
FACTS ON VALUES: F.data file = .ok D and F.sealLast = true. A JOINING: no new mathematics: the maker
(cutRow, Three.ofCuts) and the laws (cutBlocks · cutBack · fitsOfData · rowFitOfData) are the rule
of composition's files' (Johnson/Desc/Sound/Tiles*.lean).
  held b       a block of the description as OfDesc asks that a piece holds it: «below b», lifted to
  the pair of what was handed to the chain and the chain's own record
  besideAt     what a Three holds beside its pieces, at the filling that is meant (atDesc lays the
  same six functions over it)
  piecesAt     the three rows of pieces: Three.ofCuts at the held blocks, at ft = 0 | 0 |
  F.lastChainFirstTreeNumber, all := allOf D, the sealing round put back behind the first chain; ext | err: the
  letters rest₁ rest₂ rest₃, block by block
  PaidAtDesc   the statement · paidAtDesc: its proof
Limits. The three flat lists' heads are letters with equations (flatSome gives that
there are such). Nothing on any block's law; nothing on soundness.

-/
import Johnson.Desc.Sound.TilesMaker
import Johnson.Desc.Sound.DescThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)

/-- A block of a description as a piece holds it. -/
def held {P S Cl : Type} (b : Block S Cl) : Block (P × S) Cl := (below b).lift Prod.snd fun t s =>
  (t.1, s)

theorem held_map_rounds {P S Cl : Type} (l : List (Block S Cl)) :
    (l.map (held (P := P))).map (·.rounds) = l.map (·.rounds) := by
  rw [List.map_map]; rfl

theorem held_map {P S Cl : Type} (l : List (Block S Cl)) :
    l.map (held (P := P)) = (l.map below).map (Block.lift Prod.snd fun t s => (t.1, s)) := by
  rw [List.map_map]; rfl

variable {Xi W : Type}

/-- What a `Three` holds beside its pieces, at the filling that is meant. -/
def besideAt (F : FileDescription Xi) (d wEnd : W) :
    Beside Xi (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) (F.XiPub ×
        F.S₁)
      (F.XiPub × F.S₁ × F.S₂) W where
  n₁ := "the first chain"
  n₂ := "the shared chain"
  n₃ := "the second chain"
  in₁ := fun x => (F.pub x, F.start₁ (F.pub x))
  out₁ := fun _ s => s
  in₂ := fun a => (a, F.start₂ a.1)
  out₂ := fun _ s => (s.1.1, s.1.2, s.2)
  in₃ := fun a => ((F.start₃ a.1 a.2.1 a.2.2).toOption).map fun s => (a, s)
  fin := fun _ _ => true
  d := d
  wEnd := wEnd

/-- **The three rows of pieces at a description and the data of its written rounds.** -/
def piecesAt (C : CK) (F : FileDescription Xi) (D : WholeD)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl) (l₂ : List (Block
        F.S₂ F.Cl))
    (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W
        ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) ×
        F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) : ThreeAt C D (allOf D) F (F.XiPub × F.S₁) (F.XiPub × F.S₁ × F.S₂) W :=
  Three.ofCuts C D (allOf D) 0 0 F.lastChainFirstTreeNumber (held b₁) (l₁.map held) (held b₂) (l₂.map held) (held
                    b₃)
    (l₃.map held) rest₁ rest₂ rest₃ sealRound (besideAt F d wEnd)

/-- **Three premises, paid together at one value.** -/
def PaidAtDesc : Prop :=
  ∀ (Xi W : Type) (F : FileDescription Xi) (file : String) (D : WholeD), F.data file = .ok D → F.sealLast =
      true →
    ∀ (C : CK) (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
      (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl)),
      F.first.blocksInOrder = b₁ :: l₁ → F.shared.blocksInOrder = b₂ :: l₂ → F.second.blocksInOrder = b₃ :: l₃ →
      ∀ rest₁ rest₂ rest₃ (d wEnd : W),
        OfDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd) ∧
        (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).Fits ∧
        RowFit D (allOf D) (allOf D)

theorem paidAtDesc : PaidAtDesc := by
  intro Xi W F file D h hs C b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃ rest₁ rest₂ rest₃ d wEnd
  refine ⟨⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, rowFitOfData Xi F file D h⟩
  · rw [h₁, ← held_map]; exact cutBlocks _ _ _ _ _ rest₁ [sealRound] (l₁.map held) (held b₁) 0 0
        D.ds₁
  · rw [h₂, ← held_map]; exact cutBlocks _ _ _ _ _ rest₂ [] (l₂.map held) (held b₂) 0 D.t₁ D.ds₂
  · rw [h₃, ← held_map]; exact cutBlocks _ _ _ _ _ rest₃ [] (l₃.map held) (held b₃) 0 (D.t₁ + D.t₂)
        D.ds₃
  · exact cutBack _ _ _ _ _ rest₁ [sealRound] (l₁.map held) (held b₁) 0 0 D.ds₁
  · exact cutBack _ _ _ _ _ rest₂ [] (l₂.map held) (held b₂) 0 D.t₁ D.ds₂
  · exact cutBack _ _ _ _ _ rest₃ [] (l₃.map held) (held b₃) 0 (D.t₁ + D.t₂) D.ds₃
  · refine fitsOfData Xi F file D h hs C _ _ _ _ _ _ _ _ _ (held b₁) (l₁.map held) (held b₂) (l₂.map
        held)
      (held b₃) (l₃.map held) rest₁ rest₂ rest₃ sealRound ?_ ?_ ?_ ⟨rfl, rfl, rfl⟩
    · rw [h₁]; exact held_map_rounds (b₁ :: l₁)
    · rw [h₂]; exact held_map_rounds (b₂ :: l₂)
    · rw [h₃]; exact held_map_rounds (b₃ :: l₃)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.paidAtDesc
