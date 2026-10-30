-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row11.lean: THE KEY FILE's ROW 1.1 (msg.1.send) TAKEN THE WHOLE ROAD UP TO THE FIELD r1_1 OF The35 (The35.lean), BY ROW 1.0's PATTERN AS IT STANDS AT ITS LEVEL 6, IN ONE FILE.
OBJECT: The35.r1_1 · USER: The21's filler · LETTERS: X N P · the maker's cut and rests · B at_ R coll · b₁ (the chain's second block) · ρ.
  second_block | decide11 | rounds11   PROVED: under q₁ the maker's second block IS bareOf (sendOwnMessage …) (msg_at, Johnson/RunOne/KeySendAtDesc.lean); it decides as that block and declares the sending kind's own two rounds (rounds_msg, Johnson/RunOne/KeySendCond.lean)
  isSend11    PROVED: the sending kind's law's premise hS at held b₁: isSend_msgAt (Johnson/RunOne/KeySendIs.lean), through isSend_of_decide | isSend_held (KeyRow10Send.lean)
  Left11      WHAT IS LEFT
  three_of    PROVED: behind the piece the statement has just three messages: the letter On' that is handed to send_goodIn
  r1_1_at     PROVED FROM q₁, hb AND Left11
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row10Six
import Johnson.RunOne.KeyRow11
import Johnson.RunOne.KeySendCond

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace LPFD
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃ seam₁_at_fk seam₂_at_fk ends_at_fk)
open Johnson.RunOne.KeyRows1 (FirstLetters firstOn_of firstClaim_of CollCell ReadsL open₁)
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₃)

open Johnson.RunOne.KeyRows1 (RecStays isSend_held isSend_of_decide Public11 SmpOwn parMsg' keeps_send1 size3_of_yes shape₁' held_of)
open VerifiableInference.Desc.K1 (Par condPort IsSend sendPiece send_goodIn Sealed shapeAt shapesOf sampledAt errPort seedMaps seedEntry seeds_one seed_draws)
open Johnson.Pack (portOmZ)
open Johnson.RunOne.KeySendErr (shareB belowB below_send)

section
variable {Cells M Smp Rec : Type} (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD) {W : Type}
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) ((Fk X N P).XiPub × (Fk X N P).S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₂ 0) (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₃ (Fk X N P).lastChainFirstTreeNumber)
      (((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N P).S₂) × (Fk X N P).S₃) W ds)
    (dW wEnd : W)
    (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
    (coll : Strs → Rec → Prop) (off₂ off₃ : ℕ → ℕ)


/-- The groups told at the own message's place. -/
abbrev g11 : List (List ℕ) := groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 2) (rootsAt X.Y.D.1 2)

/-- The sending kind's parameters at the key file's second place. -/
def par11 : Par := parMsg' (oneAt X) pieces (g11 X)

/-- The description's own second block, in front of Chain.blocksInOrder. -/
def send11 : Block FirstState Claim := sendOwnMessage (oneAt X) pieces (g11 X)

variable (b₁ : Block (Fk X N P).S₁ (Fk X N P).Cl)

theorem second_block (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hb : (c₁ :: k₁)[1]? = some b₁) : b₁ = Johnson.RunOne.KeySendGood.bareOf (send11 X) := by
  have h := Johnson.RunOne.KeySendGood.msg_at X N P
  have h' : ((Fk X N P).first.blocksInOrder)[1]? = some (Johnson.RunOne.KeySendGood.bareOf (send11 X)) := h
  rw [q₁] at h'
  exact Option.some.inj (hb.symm.trans h')

theorem decide11 (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hb : (c₁ :: k₁)[1]? = some b₁) : b₁.decide = (send11 X).decide := by
  rw [second_block X N P c₁ k₁ b₁ q₁ hb]
  rfl

theorem rounds11 (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hb : (c₁ :: k₁)[1]? = some b₁) : b₁.rounds = K1.rounds (par11 X) := by
  rw [second_block X N P c₁ k₁ b₁ q₁ hb]
  exact Johnson.RunOne.KeySendGood.rounds_msg X

theorem isSend11 (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hb : (c₁ :: k₁)[1]? = some b₁) :
    IsSend (par11 X) (fun a : Xi × FirstState => a.2.d.st) (held b₁ : Block (Xi × FirstState) Claim) :=
  isSend_held _ _ b₁ (isSend_of_decide _ _ (send11 X) b₁ (decide11 X N P c₁ k₁ b₁ q₁ hb) (Johnson.RunOne.KeyKeeps.isSend_msgAt _ _ _))

variable {Kr : Type} [CommRing Kr] (ρ : OnBytes.Model.Reading Kr)

/-- **WHAT IS LEFT OF ROW 1.1.** -/
structure Left11 where
  d₁ : RDT
  d₂ : RDT
  /-- THE FRAME's: where the maker lays the second piece: its stretch, what is put behind, its base -/
  data : cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 1 = [d₁, d₂]
  put : cutPut [sealRound] (k₁.map (held (P := (Fk X N P).XiPub))) 1 = []
  baseIs : cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 1 = 1
  entry : d₁.entry = seedEntry (par11 X)
  kind : d₁.kind = .seeds
  rad : ℕ → ℕ
  cond : condPort (par11 X) rad = true
  K : ℕ
  share : shareB K (par11 X) rad = true
  below : belowB K (par11 X) = true
  cap : (rest₁ 1 [d₁, d₂]).err = Err.cap 128 (uLT (ckP .two) [d₁, d₂])
  fOf : (fr₁ (DK.at frS.P.T.a)).E.Str → ∀ k, (portOmZ (par11 X).codes (shapeAt (par11 X) k) (rad k.val)).Str
  fIn : (fr₁ (DK.at frS.P.T.a)).E.Str → (wT d₁).Msg → ∀ k, (portOmZ (par11 X).codes (shapeAt (par11 X) k) (rad k.val)).Str
  words : ∀ y τ, fOf ((sendPiece (W := W) (F := fr₁ (DK.at frS.P.T.a)) (held b₁ : Block (Xi × FirstState) Claim) 1 d₁ d₂ (par11 X).coordinates (errPort (par11 X) rad)).ior.imp y τ) = fIn y τ.1
  cs : OnBytes.Codes
  m : List (OnBytes.OracleShape × ℕ)
  fam : Fin m.length → ℕ × ℕ
  fits : Sound.SeatFits (Fk X N P) cs m fam
  i : Fin m.length
  seatIs : fam i = at_ 1
  sh : _root_.Fmt.Shape
  tree : treeShT [d₁, d₂] 0 = some sh
  shownAll : (pieceOf (held b₁ : Block (Xi × FirstState) Claim) 1 [d₁, d₂] [] (rest₁ 1 [d₁, d₂])).ShownAll (Fk X N P) cs m fam
  /-- PUBLIC: the plan at the place -/
  pub : Public11 (oneAt X) pieces (g11 X)
  seat0 : at_ 0 = (0, 0)
  seat1 : at_ 1 = (1, 0)
  /-- CONDITIONS ON LETTERS -/
  cell : CollCell coll
  same : R.same = fun a b => ρ.val a = ρ.val b
  smpOwn : SmpOwn B.h₁ at_ (oneAt X)
  k₀ : Fin (shapesOf (par11 X)).length
  sampledAt : sampledAt (par11 X) k₀
  /-- AT A STATEMENT WITH JUST THREE MESSAGES -/
  tieS : ∀ a' : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str, a'.1.2.d.st.oracles.size = 3 →
      Sealed (par11 X).codes (shapeAt (par11 X) k₀) (rad k₀.val) (fOf a'.2 k₀) a'.1.2.d.st (a'.1.2.d.st.oracles.size - (shapesOf (par11 X)).length + k₀.val) →
      hasSmp B.h₁ (at_ 1).1 (at_ 1).2 a'.1 = true ∧ NoColl (Fk X N P) B.h₁ (at_ 1).1 (at_ 1).2 a'.1 (strsOf (fr₁ (DK.at frS.P.T.a)) a'.2)

/-- **Behind the second sending's piece the statement has just three messages.** -/
theorem three_of (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hb : (c₁ :: k₁)[1]? = some b₁) (Pb : Public11 (oneAt X) pieces (g11 X))
    (pc : Piece (ckP .two) (fr₁ (DK.at frS.P.T.a)) (Xi × FirstState) Claim W) (hpc : pc.b = held b₁)
    (a x : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str) (τ : _root_.Iop.Tr (uLT (ckP .two) pc.ds))
    (ha : On₁ X N P (DK.at frS.P.T.a) B at_ R coll 1 a) (hx : pc.ior.red.out a τ = some x) : x.1.2.d.st.oracles.size = 3 := by
  have hd := piece_decides_at pc a τ x hx
  have hf := (piece_fits_at pc a τ x hx).1
  rw [hpc] at hd hf
  have hd2 := (held_decide b₁ a.1 _ _ x.1 hd).2
  have hn := Johnson.RunOne.KeyRows1.on₁_two (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll 1 a ha
  have hr := ha.resolve_left (fun hu => hu rfl)
  have h1 : shape₁' (oneAt X) 1 a.1.2 = true := by
    have := hr.1
    rw [hn] at this
    exact this
  exact size3_of_yes (oneAt X) pieces _ Pb b₁ (decide11 X N P c₁ k₁ b₁ q₁ hb) (rounds11 X N P c₁ k₁ b₁ q₁ hb) a.1.2 x.1.2 _ _ hf hd2 h1 hr.2.2.1.2.2.2.2.2.2.1

/-- **THE FIELD r1_1 OF The35 AT THE KEY FILE's OWN DESCRIPTION, FROM WHAT IS LEFT.** -/
theorem r1_1_at (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hb : (c₁ :: k₁)[1]? = some b₁) (H : Left11 X N P DK c₁ k₁ rest₁ B at_ R coll b₁ ρ) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 1 :=
  KeepsAt.reached _ _ (rowBlocksF₁ q₁ 1)
    (keepsAt_of_law₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd
      (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) 1 fun b base ds back hb' hp => by
        have eb : b₁ = b := Option.some.inj (hb.symm.trans hb')
        subst eb
        obtain ⟨b', -, e⟩ := rowAt₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 1 _ hp
        obtain rfl : base = 1 := (congrArg Piece.base e).trans H.baseIs
        obtain rfl : ds = [H.d₁, H.d₂] := (congrArg Piece.ds e).trans H.data
        obtain rfl : back = [] := (congrArg Piece.back e).trans H.put
        have h1 := seeds_one (par11 X) H.rad H.cond
        obtain ⟨a1, a2, a3, a4, a5⟩ := seed_draws (par11 X) h1 H.d₁ H.entry H.kind
        refine ⟨⟨fun _ _ w => w, (seedMaps H.d₁ H.d₂ (par11 X).coordinates).err ((errPort (par11 X) H.rad, ()) : ℕ × Unit)⟩,
          keeps_send1 (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll ρ H.same _ b₁ (held_of _ _ b₁ rfl) rfl pieces (g11 X) H.pub
            (decide11 X N P c₁ k₁ b₁ q₁ hb) (rounds11 X N P c₁ k₁ b₁ q₁ hb) (by rw [H.seat0]; exact Nat.zero_lt_one) H.seat1 (recStays_base B) H.smpOwn H.cell
            (fun a τ a' _ hx => by
              rw [out_behind' (fr₁ (DK.at frS.P.T.a)) _ a a' τ hx]
              exact shown_tie (Fk X N P) H.cs H.m H.fam H.fits at_ 1 H.i H.seatIs _ (H.shownAll a.2 τ H.i 0 H.sh (by rw [H.seatIs, H.seat1]; rfl) H.tree))
            _ (fun _ _ => True) (fun _ _ => True)
            (send_goodIn (par11 X) H.rad H.cond h1 (held b₁ : Block (Xi × FirstState) Claim) (fun a => a.2.d.st) (isSend11 X N P c₁ k₁ b₁ q₁ hb) 1 H.d₁ H.d₂ a1 a2 a3 a4 a5
              (errPort (par11 X) H.rad) (Nat.le_refl _) H.fOf H.fIn H.words
              (On₁ X N P (DK.at frS.P.T.a) B at_ R coll 1) (fun x => x.1.2.d.st.oracles.size = 3) (fun _ _ => True) (fun _ _ => True)
              (fun a τ x ha hx => three_of X N P DK c₁ k₁ B at_ R coll b₁ q₁ hb H.pub _ rfl a x τ ha hx) (fun _ _ _ _ _ _ _ => trivial))
            (fun a' h => H.tieS a' h.1 (h.2 H.k₀ H.sampledAt)),
          H.cap ▸ Err.le_cap_of_below_inv 128 _ (below_send H.K (par11 X) H.rad h1 H.d₁ H.d₂ ⟨H.entry, by rw [H.kind]; decide⟩ H.share H.below)⟩)

end

end LPFD

#print axioms LPFD.second_block
#print axioms LPFD.isSend11
#print axioms LPFD.three_of
#print axioms LPFD.r1_1_at
