-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row117.lean: THE KEY FILE's ROW 1.17 (w.1.send) TAKEN THE WHOLE ROAD UP TO THE FIELD r1_17 OF The35 (The35.lean), BY ROW 1.1's PATTERN (Row11.lean), IN ONE FILE.
OBJECT: The35.r1_17 · USER: The21's filler · LETTERS: X N P · the maker's cut and rests · B at_ R coll · bw (the seat's block) · ρ.
  g17 | sent17 | par17     the groups told and the trees sent in front, at W's place; the sending kind's parameters there
  block17 | decide17 | rounds17   PROVED: under q₁, hl and hw the maker's block 17 IS bareOf bw; it decides as bw and declares the sending kind's own two rounds (w_rounds, Johnson/RunOne/KeySendRound.lean)
  isSend17    PROVED: the sending kind's law's premise hS at the held block: isSend_wAt (Johnson/RunOne/KeySendIs.lean), through isSend_of_decide | isSend_held (KeyRow10Send.lean)
  Left117     WHAT IS LEFT
  sizeW_of    PROVED: behind the piece the statement has just wAt + 2 messages: the letter On' that is handed to send_goodIn
  r1_17_at    PROVED FROM q₁, hl, hw AND Left117
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row11
import Johnson.RunOne.KeyRow117

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

open Johnson.RunOne.KeyRows1 (RecStays isSend_held isSend_of_decide Public117 SmpOwn parW' wAt keeps_send17 sizeW_of_yes shape₁' held_of)
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



/-- The groups told at W's place. -/
abbrev g17 : List (List ℕ) := groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))

/-- The trees that the chain has sent in front of the batching. -/
abbrev sent17 : ℕ := rootsBefore X.Y.D.1 (batchRound X.Y.D.1)

variable (bw b₁₇ : Block FirstState Claim)

theorem block17 (one : OnBytes.Params.OneTime) (D : List _root_.Fmt.DeclaredRound) (told : List ProofFile.Root) (set : OnBytes.Params.Setting) (N' : H2U.PlaceNums) (x₀ x₁ : Lookup)
    (hl : lookupsOf one = [x₀, x₁]) (bw : Block FirstState Claim)
    (hw : sendW one pieces (rootsBefore D (batchRound D)) (groupsTold told (rootsBefore D (lastSendRound D)) (rootsAt D (lastSendRound D))) = some bw)
    (b : Block FirstState Claim) (h : (firstChain one D told set N').blocksInOrder[17]? = some b) : b = Johnson.RunOne.KeySendGood.bareOf bw := by
  simp only [firstChain, hl, hw] at h
  have e : _ = b := Option.some.inj h
  exact e.symm

/-- The sending kind's parameters at W's place, at the two notices. -/
abbrev par17 (n₁ n₂ : OnBytes.OracleNotice) : Par := parW' (oneAt X) pieces (g17 X) #[n₁, n₂]

theorem block17_at (x₀ x₁ : Lookup) (hl : lookupsOf (oneAt X) = [x₀, x₁]) (hw : sendW (oneAt X) pieces (sent17 X) (g17 X) = some bw)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hb : (c₁ :: k₁)[17]? = some b₁₇) : b₁₇ = Johnson.RunOne.KeySendGood.bareOf bw :=
  block17 (oneAt X) X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl bw hw b₁₇ (by rw [← q₁] at hb; exact hb)

theorem decide17 (x₀ x₁ : Lookup) (hl : lookupsOf (oneAt X) = [x₀, x₁]) (hw : sendW (oneAt X) pieces (sent17 X) (g17 X) = some bw)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hb : (c₁ :: k₁)[17]? = some b₁₇) : b₁₇.decide = bw.decide := by
  rw [block17_at X N P c₁ k₁ bw b₁₇ x₀ x₁ hl hw q₁ hb]
  rfl

theorem rounds17 (x₀ x₁ : Lookup) (hl : lookupsOf (oneAt X) = [x₀, x₁]) (hw : sendW (oneAt X) pieces (sent17 X) (g17 X) = some bw)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hb : (c₁ :: k₁)[17]? = some b₁₇) (n₁ n₂ : OnBytes.OracleNotice) (hm : linMessageW (oneAt X).lin = some #[n₁, n₂]) :
    b₁₇.rounds = K1.rounds (par17 X n₁ n₂) := by
  rw [block17_at X N P c₁ k₁ bw b₁₇ x₀ x₁ hl hw q₁ hb]
  exact Johnson.RunOne.KeySendGood.rounds_w hm hw

theorem isSend17 (x₀ x₁ : Lookup) (hl : lookupsOf (oneAt X) = [x₀, x₁]) (hw : sendW (oneAt X) pieces (sent17 X) (g17 X) = some bw)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hb : (c₁ :: k₁)[17]? = some b₁₇) (n₁ n₂ : OnBytes.OracleNotice) (hm : linMessageW (oneAt X).lin = some #[n₁, n₂]) :
    IsSend (par17 X n₁ n₂) (fun a : Xi × FirstState => a.2.d.st) (held b₁₇ : Block (Xi × FirstState) Claim) := by
  obtain ⟨msg, hmsg, hS⟩ := Johnson.RunOne.KeyKeeps.isSend_wAt hw
  obtain rfl : #[n₁, n₂] = msg := Option.some.inj (hm.symm.trans hmsg)
  exact isSend_held _ _ b₁₇ (isSend_of_decide _ _ bw b₁₇ (decide17 X N P c₁ k₁ bw b₁₇ x₀ x₁ hl hw q₁ hb) hS)

variable {Kr : Type} [CommRing Kr] (ρ : OnBytes.Model.Reading Kr)

/-- **WHAT IS LEFT OF ROW 1.17**, at the two rounds' data d₁ d₂ of the maker's stretch. -/
structure Left117 (d₁ d₂ : RDT) where
  /-- PUBLIC: the plan at the place -/
  pub : Public117 (oneAt X) pieces (g17 X)
  small : wAt (oneAt X) + 1 < noId
  entry : d₁.entry = seedEntry (par17 X pub.n₁ pub.n₂)
  kind : d₁.kind = .seeds
  radW : ℕ → ℕ
  cond : condPort (par17 X pub.n₁ pub.n₂) radW = true
  K : ℕ
  share : shareB K (par17 X pub.n₁ pub.n₂) radW = true
  below : belowB K (par17 X pub.n₁ pub.n₂) = true
  cap : (rest₁ 17 [d₁, d₂]).err = Err.cap 128 (uLT (ckP .two) [d₁, d₂])
  fOf : (fr₁ (DK.at frS.P.T.a)).E.Str → ∀ k, (portOmZ (par17 X pub.n₁ pub.n₂).codes (shapeAt (par17 X pub.n₁ pub.n₂) k) (radW k.val)).Str
  fIn : (fr₁ (DK.at frS.P.T.a)).E.Str → (wT d₁).Msg → ∀ k, (portOmZ (par17 X pub.n₁ pub.n₂).codes (shapeAt (par17 X pub.n₁ pub.n₂) k) (radW k.val)).Str
  words : ∀ y τ, fOf ((sendPiece (W := W) (F := fr₁ (DK.at frS.P.T.a)) (held b₁₇ : Block (Xi × FirstState) Claim) (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17) d₁ d₂ (par17 X pub.n₁ pub.n₂).coordinates (errPort (par17 X pub.n₁ pub.n₂) radW)).ior.imp y τ) = fIn y τ.1
  cs : OnBytes.Codes
  m : List (OnBytes.OracleShape × ℕ)
  fam : Fin m.length → ℕ × ℕ
  fits : Sound.SeatFits (Fk X N P) cs m fam
  i : Fin m.length
  seatIs : fam i = at_ 2
  sh : _root_.Fmt.Shape
  tree : treeShT [d₁, d₂] 0 = some sh
  shownAll : (pieceOf (held b₁₇ : Block (Xi × FirstState) Claim) (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17) [d₁, d₂] [] (rest₁ 17 [d₁, d₂])).ShownAll (Fk X N P) cs m fam
  /-- where the tables seat the witness's messages 0 and 2 -/
  base0 : (at_ 0).1 < (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17)
  seat2 : at_ 2 = ((oneAt X).ranges.stages.length + 1, 0)
  treeAt : (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17) = (oneAt X).ranges.stages.length + 1
  /-- CONDITIONS ON LETTERS -/
  cell : CollCell coll
  same : R.same = fun a b => ρ.val a = ρ.val b
  smpOwn : SmpOwn B.h₁ at_ (oneAt X)
  k₀ : Fin (shapesOf (par17 X pub.n₁ pub.n₂)).length
  sampledAt : sampledAt (par17 X pub.n₁ pub.n₂) k₀
  /-- AT A STATEMENT WITH JUST wAt + 2 MESSAGES -/
  tieS : ∀ a' : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str, a'.1.2.d.st.oracles.size = wAt (oneAt X) + 2 →
      Sealed (par17 X pub.n₁ pub.n₂).codes (shapeAt (par17 X pub.n₁ pub.n₂) k₀) (radW k₀.val) (fOf a'.2 k₀) a'.1.2.d.st (a'.1.2.d.st.oracles.size - (shapesOf (par17 X pub.n₁ pub.n₂)).length + k₀.val) →
      hasSmp B.h₁ (at_ 2).1 (at_ 2).2 a'.1 = true ∧ NoColl (Fk X N P) B.h₁ (at_ 2).1 (at_ 2).2 a'.1 (strsOf (fr₁ (DK.at frS.P.T.a)) a'.2)

/-- **Behind W's sending's piece the statement has just wAt + 2 messages.** -/
theorem sizeW_of (x₀ x₁ : Lookup) (hl : lookupsOf (oneAt X) = [x₀, x₁]) (hw : sendW (oneAt X) pieces (sent17 X) (g17 X) = some bw)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hb : (c₁ :: k₁)[17]? = some b₁₇) (Pb : Public117 (oneAt X) pieces (g17 X))
    (pc : Piece (ckP .two) (fr₁ (DK.at frS.P.T.a)) (Xi × FirstState) Claim W) (hpc : pc.b = held b₁₇)
    (a x : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str) (τ : _root_.Iop.Tr (uLT (ckP .two) pc.ds))
    (ha : On₁ X N P (DK.at frS.P.T.a) B at_ R coll 17 a) (hx : pc.ior.red.out a τ = some x) : x.1.2.d.st.oracles.size = wAt (oneAt X) + 2 := by
  have hd := piece_decides_at pc a τ x hx
  have hf := (piece_fits_at pc a τ x hx).1
  rw [hpc] at hd hf
  have hd2 := (held_decide b₁₇ a.1 _ _ x.1 hd).2
  have hn := Johnson.RunOne.KeyRows1.on₁_two (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll 17 a ha
  have hr := ha.resolve_left (fun hu => hu rfl)
  have h1 : shape₁' (oneAt X) 17 a.1.2 = true := by
    have := hr.1
    rw [hn] at this
    exact this
  exact sizeW_of_yes (oneAt X) pieces (sent17 X) _ Pb bw hw b₁₇ (decide17 X N P c₁ k₁ bw b₁₇ x₀ x₁ hl hw q₁ hb) (rounds17 X N P c₁ k₁ bw b₁₇ x₀ x₁ hl hw q₁ hb _ _ Pb.two) a.1.2 x.1.2 _ _ hf hd2 h1 hr.2.2.1.2.2.2.2.2.2.1

/-- **THE FIELD r1_17 OF The35 AT THE KEY FILE's OWN DESCRIPTION, FROM WHAT IS LEFT.** -/
theorem r1_17_at (x₀ x₁ : Lookup) (hl : lookupsOf (oneAt X) = [x₀, x₁]) (hw : sendW (oneAt X) pieces (sent17 X) (g17 X) = some bw)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hb : (c₁ :: k₁)[17]? = some b₁₇) (d₁ d₂ : RDT)
    (data : cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17 = [d₁, d₂])
    (put : cutPut [sealRound] (k₁.map (held (P := (Fk X N P).XiPub))) 17 = [])
    (H : Left117 X N P DK c₁ k₁ rest₁ B at_ R coll b₁₇ ρ d₁ d₂) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 17 :=
  KeepsAt.reached _ _ (rowBlocksF₁ q₁ 17)
    (keepsAt_of_law₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd
      (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) 17 fun b base ds back hb' hp => by
        have eb : b₁₇ = b := Option.some.inj (hb.symm.trans hb')
        subst eb
        obtain ⟨b', -, e⟩ := rowAt₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 17 _ hp
        obtain rfl : base = _ := congrArg Piece.base e
        obtain rfl : ds = [d₁, d₂] := (congrArg Piece.ds e).trans data
        obtain rfl : back = [] := (congrArg Piece.back e).trans put
        have h1 := seeds_one (par17 X H.pub.n₁ H.pub.n₂) H.radW H.cond
        obtain ⟨a1, a2, a3, a4, a5⟩ := seed_draws (par17 X H.pub.n₁ H.pub.n₂) h1 d₁ H.entry H.kind
        refine ⟨⟨fun _ _ w => w, (seedMaps d₁ d₂ (par17 X H.pub.n₁ H.pub.n₂).coordinates).err ((errPort (par17 X H.pub.n₁ H.pub.n₂) H.radW, ()) : ℕ × Unit)⟩,
          keeps_send17 (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll ρ H.same _ b₁₇ (held_of _ _ b₁₇ rfl) rfl pieces (sent17 X) (g17 X) H.pub H.small bw hw
            (decide17 X N P c₁ k₁ bw b₁₇ x₀ x₁ hl hw q₁ hb) (rounds17 X N P c₁ k₁ bw b₁₇ x₀ x₁ hl hw q₁ hb _ _ H.pub.two) H.base0 H.seat2 (recStays_base B) H.smpOwn H.cell
            (fun a τ a' _ hx => by
              rw [out_behind' (fr₁ (DK.at frS.P.T.a)) _ a a' τ hx]
              exact shown_tie (Fk X N P) H.cs H.m H.fam H.fits at_ 2 H.i H.seatIs _ (H.shownAll a.2 τ H.i 0 H.sh (by rw [H.seatIs, H.seat2, H.treeAt]; rfl) H.tree))
            _ (fun _ _ => True) (fun _ _ => True)
            (send_goodIn (par17 X H.pub.n₁ H.pub.n₂) H.radW H.cond h1 (held b₁₇ : Block (Xi × FirstState) Claim) (fun a => a.2.d.st) (isSend17 X N P c₁ k₁ bw b₁₇ x₀ x₁ hl hw q₁ hb _ _ H.pub.two) _ d₁ d₂ a1 a2 a3 a4 a5
              (errPort (par17 X H.pub.n₁ H.pub.n₂) H.radW) (Nat.le_refl _) H.fOf H.fIn H.words
              (On₁ X N P (DK.at frS.P.T.a) B at_ R coll 17) (fun x => x.1.2.d.st.oracles.size = wAt (oneAt X) + 2) (fun _ _ => True) (fun _ _ => True)
              (fun a τ x ha hx => sizeW_of X N P DK c₁ k₁ B at_ R coll bw b₁₇ x₀ x₁ hl hw q₁ hb H.pub _ rfl a x τ ha hx) (fun _ _ _ _ _ _ _ => trivial))
            (fun a' h => H.tieS a' h.1 (h.2 H.k₀ H.sampledAt)),
          H.cap ▸ Err.le_cap_of_below_inv 128 _ (below_send H.K (par17 X H.pub.n₁ H.pub.n₂) H.radW h1 d₁ d₂ ⟨H.entry, by rw [H.kind]; decide⟩ H.share H.below)⟩)

end

end LPFD

#print axioms LPFD.sizeW_of
#print axioms LPFD.r1_17_at
#print axioms LPFD.block17
#print axioms LPFD.rounds17
#print axioms LPFD.isSend17
