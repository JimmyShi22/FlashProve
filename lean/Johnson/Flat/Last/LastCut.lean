-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/LastCut.lean: THE LAST CHAIN's FOUR PIECES AS THE MAKER OF PIECES CUTS THEM (cutRow, Johnson/Desc/Sound/Tiles.lean) AGAINST THE LIST OF eachOwn_last (LastOnePage.lean): [x₀, x₁, pieceTwoT …, x₃]. A rule under named facts of make.

  cutRow_four: the maker at four blocks, unfolded: four pieces, each with its base and its stretch in closed form (by rfl).
  base₂ | ds₂: the third piece's base and stretch.
  **third_is_pieceTwoT**: the third piece IS pieceTwoT, from FOUR PLAIN FACTS OF MAKE: hb: the third block is (below ((proximityTestKind guardedProximityTestParts π).inside enter leave)).lift Prod.snd … · hbase · hds: its stretch is dB :: dt · hrest: what the list's "rest" hands at (its number, dB :: dt) is
    the row's own extractor and the errors (e₀, εt). The extractor's and the errors' types hang on the stretch: they cross because "rest" is ONE function of the number and the stretch: no HEq is typed.
  **last_list_at**: AT A DESCRIPTION F AND THE DATA D OF ITS WRITTEN ROUNDS: the last chain's pieces of atDesc F (piecesAt (ckP .two) F D … c₀ [c₁, c₂, c₃] … rest₃ …) (Johnson/Desc/Sound/PaidAtDesc.lean · DescThree.lean) ARE [pieceZeroAt …, pieceOneAt …, pieceTwoT …, pieceThreeAt …], the three the maker's own
    pieces over held c₀ | c₁ | c₃, by name: from THREE facts of make (the base is the maker's own: baseTwoAt).

Every "there is", walked: no statement has one.
Limits. A RULE: the four facts are shown at no description. hrest is a CHOICE where the list's rest is a letter under "there is": whoever fills it lays the row's extractor at number i + 2. Nothing on soundness.

-/
import Johnson.Flat.Last.LastOnePage
import Johnson.Desc.Sound.PaidAtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles.Last
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Fo.Peel Cb Johnson.Pack
open Iop Prob _root_.Run
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last

section
variable {C : CK} {F : Frame} {S Cl W : Type} (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds) (putBack : List Fmt.RoundView)
  (i base : ℕ) (ds : List RDT) (b₀ b₁ b₂ b₃ : Block S Cl)

/-- The second, third and fourth pieces' bases and what is left of the data in front of each. -/
def base₁ : ℕ := base + nTrees (ds.take b₀.rounds.length)
def left₁ : List RDT := ds.drop b₀.rounds.length
def base₂ : ℕ := base₁ base ds b₀ + nTrees ((left₁ ds b₀).take b₁.rounds.length)
def left₂ : List RDT := (left₁ ds b₀).drop b₁.rounds.length
def ds₂ : List RDT := (left₂ ds b₀ b₁).take b₂.rounds.length
def base₃ : ℕ := base₂ base ds b₀ b₁ + nTrees (ds₂ ds b₀ b₁ b₂)
def left₃ : List RDT := (left₂ ds b₀ b₁).drop b₂.rounds.length

/-- **The maker at four blocks.** -/
theorem cutRow_four :
    (cutRow rest putBack i base ds b₀ [b₁, b₂, b₃]).1 :: (cutRow rest putBack i base ds b₀ [b₁, b₂, b₃]).2 =
      [pieceOf b₀ base (ds.take b₀.rounds.length) [] (rest i (ds.take b₀.rounds.length)),
        pieceOf b₁ (base₁ base ds b₀) ((left₁ ds b₀).take b₁.rounds.length) [] (rest (i + 1) ((left₁ ds b₀).take b₁.rounds.length)),
        pieceOf b₂ (base₂ base ds b₀ b₁) (ds₂ ds b₀ b₁ b₂) [] (rest (i + 1 + 1) (ds₂ ds b₀ b₁ b₂)),
        pieceOf b₃ (base₃ base ds b₀ b₁ b₂) (left₃ ds b₀ b₁ b₂) putBack (rest (i + 1 + 1 + 1) (left₃ ds b₀ b₁ b₂))] := rfl

end

section
variable {P S₁ S₂ S₃ Cells Tok Cl : Type} {Fr : Frame}
  (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : ((P × S₁ × S₂) × S₃) → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → ((P × S₁ × S₂) × S₃) → Option Cells) (c₀ : Cells)
  (π : P12) (base' : ℕ) (dB : RDT) (dt : List RDT) (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
  (enter : S₃ → Except String T12) (leave : S₃ → T12 → Except String S₃) (mine : List Mem)
  (rest : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) Fr ((P × S₁ × S₂) × S₃) (Wit Cells Tok MsgT) ds)

/-- **The third piece is block 2's piece, from four plain facts of make.** -/
theorem third_is_pieceTwoT (k bs : ℕ) (dsx : List RDT) (b : Block ((P × S₁ × S₂) × S₃) Cl)
    (hb : b = (below ((proximityTestKind guardedProximityTestParts π : Block T12 Cl).inside enter leave)).lift Prod.snd fun t s => (t.1, s))
    (hbase : bs = base') (hds : dsx = dB :: dt)
    (hrest : rest k (dB :: dt) =
      ⟨fun a _ w => extAt cs G arr smp decT c₀ mine [] false none a.1 (strsOf Fr a.2) w, (e₀, εt)⟩) :
    pieceOf b bs dsx [] (rest k dsx) = pieceTwoT cs G arr smp decT c₀ π base' dB dt e₀ εt enter leave mine := by
  subst hb hbase hds
  rw [hrest]
  rfl

end

/-! ## At a description -/

section
variable {Xi Cells Tok : Type} (F : FileDescription Xi) (D : WholeD)
  (a₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (a₂ : Block F.S₂ F.Cl) (k₂ : List (Block F.S₂ F.Cl))
  (c₀ c₁ c₂ c₃ : Block F.S₃ F.Cl)
  (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) (Wit Cells Tok MsgT) ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) (Wit Cells Tok MsgT) ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) (Wit Cells Tok MsgT) ds)
  (d wEnd : Wit Cells Tok MsgT)
  (cs : OnBytes.Codes) {Xi' : Type} (G : FileDescription Xi') (arr : ℕ → ℕ → ℕ)
  (smp : ((F.XiPub × F.S₁ × F.S₂) × F.S₃) → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → ((F.XiPub × F.S₁ × F.S₂) × F.S₃) → Option Cells) (c₀' : Cells)
  (π : P12) (dB : RDT) (dt : List RDT) (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
  (enter : F.S₃ → Except String T12) (leave : F.S₃ → T12 → Except String F.S₃) (mine : List Mem)

/-- The last chain's first tree's number through the file, and the third piece's base there. -/
def baseTwoAt : ℕ := base₂ (D.t₁ + D.t₂) D.ds₃ (held (P := F.XiPub × F.S₁ × F.S₂) c₀) (held (P := F.XiPub × F.S₁ × F.S₂) c₁)

/-- The maker's own first, second and fourth pieces of the last chain. -/
def pieceZeroAt : Piece (ckP .two) (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) F.Cl (Wit Cells Tok MsgT) :=
  pieceOf (held c₀) (D.t₁ + D.t₂) (D.ds₃.take (held (P := F.XiPub × F.S₁ × F.S₂) c₀).rounds.length) [] (rest₃ 0 _)
def pieceOneAt : Piece (ckP .two) (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) F.Cl (Wit Cells Tok MsgT) :=
  pieceOf (held c₁) (base₁ (D.t₁ + D.t₂) D.ds₃ (held (P := F.XiPub × F.S₁ × F.S₂) c₀))
    ((left₁ D.ds₃ (held (P := F.XiPub × F.S₁ × F.S₂) c₀)).take (held (P := F.XiPub × F.S₁ × F.S₂) c₁).rounds.length) [] (rest₃ (0 + 1) _)
def pieceThreeAt : Piece (ckP .two) (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) F.Cl (Wit Cells Tok MsgT) :=
  pieceOf (held c₃) (base₃ (D.t₁ + D.t₂) D.ds₃ (held (P := F.XiPub × F.S₁ × F.S₂) c₀) (held c₁) (held c₂))
    (left₃ D.ds₃ (held (P := F.XiPub × F.S₁ × F.S₂) c₀) (held c₁) (held c₂)) [] (rest₃ (0 + 1 + 1 + 1) _)

/-- **THE LIST OF THE LAST CHAIN's PIECES AT A DESCRIPTION IS [x₀, x₁, pieceTwoT …, x₃]**, from three facts of make: the third block of the last chain's flat list is the kind K12's block at a seat · the third stretch of the written rounds' data is dB :: dt · the list's
rest₃ hands at (2, dB :: dt) the row's own extractor and the errors (e₀, εt). -/
theorem last_list_at
    (hc : c₂ = (proximityTestKind guardedProximityTestParts π : Block T12 F.Cl).inside enter leave)
    (hds : ds₂ D.ds₃ (held (P := F.XiPub × F.S₁ × F.S₂) c₀) (held (P := F.XiPub × F.S₁ × F.S₂) c₁) (held (P := F.XiPub × F.S₁ × F.S₂) c₂) = dB :: dt)
    (hrest : rest₃ 2 (dB :: dt) =
      ⟨fun a _ w => extAt cs G arr smp decT c₀' mine [] false none a.1 (strsOf _ a.2) w, (e₀, εt)⟩) :
    (atDesc F (piecesAt (ckP .two) F D a₁ k₁ a₂ k₂ c₀ [c₁, c₂, c₃] rest₁ rest₂ rest₃ d wEnd)).p₃ ::
        (atDesc F (piecesAt (ckP .two) F D a₁ k₁ a₂ k₂ c₀ [c₁, c₂, c₃] rest₁ rest₂ rest₃ d wEnd)).l₃ =
      [pieceZeroAt F D c₀ rest₃, pieceOneAt F D c₀ c₁ rest₃,
        pieceTwoT cs G arr smp decT c₀' π (baseTwoAt F D c₀ c₁) dB dt e₀ εt enter leave mine, pieceThreeAt F D c₀ c₁ c₂ c₃ rest₃] := by
  show (cutRow rest₃ [] 0 (D.t₁ + D.t₂) D.ds₃ (held c₀) [held c₁, held c₂, held c₃]).1 ::
    (cutRow rest₃ [] 0 (D.t₁ + D.t₂) D.ds₃ (held c₀) [held c₁, held c₂, held c₃]).2 = _
  rw [cutRow_four, third_is_pieceTwoT cs G arr smp decT c₀' π (baseTwoAt F D c₀ c₁) dB dt e₀ εt enter leave mine rest₃ (0 + 1 + 1)
    (base₂ (D.t₁ + D.t₂) D.ds₃ (held (P := F.XiPub × F.S₁ × F.S₂) c₀) (held c₁)) _
    (held c₂) (by rw [hc]; rfl) rfl hds hrest]
  rfl

end

end VerifiableInference.OnPublicFiles.Last

#print axioms VerifiableInference.OnPublicFiles.Last.cutRow_four
#print axioms VerifiableInference.OnPublicFiles.Last.third_is_pieceTwoT
#print axioms VerifiableInference.OnPublicFiles.Last.last_list_at
