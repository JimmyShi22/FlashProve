-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastRowZeroB.lean: CUT OUT OF LastRowZero.lean,
TEXTS UNTURNED [by program], SO THAT THE LAW WITH ROW 0's DEBT AS ONE PREMISE DRAWS NO FILE OF ROW
0's OWN LAWS: the ledger of the last chain's field at K14's own shared seat, at the
closed book-keeping with a layer X on the shared chain's last state. THE DEFINITION
`endedX` LIES IN PlmCode.lean (it comes in through
LastLayerS.lean).
  `seatK Z N`: the shared seat that the description's own seat lays (`sharedSeatAt_is`).
  `beside_is_fill`: the layer beside the book-keeping IS the book-keeping at a narrower "ended":
    `besideL (fillAt p R hand ended) X = fillAt p R hand (ended, where X says yes)`. `endedX X`:
    K14's end carried by `sharedOfEnd`, where X says yes.
  `LastLeftB`: `LastRest` at that seat, at hand := `firstOfS` of what `get` reads and ended :=
    `endedX X`, WITH row0B (ROW 0's DEBT, `RowZeroOwed` at the book-keeping with the layer X, AS ONE
    PREMISE, in its payer's own conclusion's form) and earn₀ (row 0's accepting run earns the layer
    Y at border 1).
  `LastLeftB.left`: it gives `LastLeft`: row0B is lifted to the layer Y (`ownLiftS`, `framesLiftS`).
    `own3_of_leftB`, `e3_of_leftB`: so the field, in the two forms.
Limits: those of LastLedger.lean. NO MEMBER. Nothing on soundness.
-/
import Johnson.LLT25R.LastLedger
import Johnson.Desc.ProofFile.Lot.K14SeatAtZ

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace LLT25
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Fo.Peel Cb
    Johnson.Pack
open Iop Prob _root_.Run
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn)
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers openSets sampledIn start)
open VerifiableInference.Desc.K13 (Where)
open _root_.Desc.K14 (St)
open VerifiableInference.Desc.Third (P₁₄)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At)

/-- **The shared seat that the description's own seat lays, where the places are N.** -/
def seatK (Z : ProofFile.Pub) (N : H2U.Places4) : SharedSeat :=
  _root_.Desc.K14.sharedSeatOf Z.p.chains (_root_.Desc.K14.beforePointOf N)
    (fun _ => VerifiableInference.Desc.K12.Seat.tests N) []
    VerifiableInference.Desc.K12.Seat.last (OkD.AtC.beside Z.p.X Z.p.chains)

theorem sharedSeatAt_is (Z : ProofFile.Pub) (N : H2U.Places4) (h : H2U.placesOfMade Z.made = .ok N) :
    _root_.Desc.K14.sharedSeatAt Z = some (seatK Z N) := by
  unfold _root_.Desc.K14.sharedSeatAt
  rw [h]
  rfl

/-- **The layer beside the book-keeping is the book-keeping at a narrower "ended"**: a test X on the
shared chain's last state, laid beside `fillAt … hand ended`, is `fillAt` at "ended, where X says
yes". -/
theorem beside_is_fill {S₂ P₁ : Type} (p : P₁₄) (R : List Fmt.DeclaredRound) (hand : P₁ → Option Handed)
    (ended : S₂ → Option SharedOut) (X : S₂ → Bool) :
    besideL (fillAt p R hand ended) X =
      fillAt p R hand (fun d => if X d = true then ended d else none) := by
  unfold besideL fillAt
  simp only [PromMeaningL.mk.injEq, and_true]
  funext k x e s
  cases hX : X e <;> cases hand x <;> cases ended e <;> simp

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4)
  (c : Chain S Cl) {Cells Tok P₀ : Type} (D : WholeD)
  (cs : OnBytes.Codes) {Xi' : Type} (G : FileDescription Xi') (arr : ℕ → ℕ → ℕ)
  (smp : (((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ × St) × (FL o mk Z
      (seatK Z N) N c).S₃) → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om
      i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → (((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z
      N) N c).S₁ × St) × (FL o mk Z (seatK Z N) N c).S₃) → Option Cells)
  (c₀' : Cells) (dB : RDT) (dt : List RDT) (mine : List Mem)
  (get : (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ → P₀ × First.S)
  (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms₁ ms₂ : List Mem) (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ × First.S → Option Cells)
  (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
  (M₁ : Meaning P₀ (Wit Cells Tok MsgT)) (MS : MeaningS St ((FL o mk Z (seatK Z N) N c).XiPub × (FL
      o mk Z (seatK Z N) N c).S₁) (Wit Cells Tok MsgT))
  (ML : MeaningL (FL o mk Z (seatK Z N) N c).S₃ (Wit Cells Tok MsgT)) (stOf : St →
      OnBytes.Statement)
  (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS)
  (links : List ModelPart) (ps : List VerifiableInference.Desc.Place)
  (Oc : (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ → Strs → Prop)
  (Y : ℕ → (FL o mk Z (seatK Z N) N c).S₃ → Bool)
  (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rd : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ)
  (Pw : Where) (t₁ t₂ : ℕ) (X : St → Bool) (wSeat : ℕ × ℕ)

/-- **THE SAME WITH ROW 0's DEBT AS ONE PREMISE, IN ITS PAYER's OWN CONCLUSION's FORM**: whichever
law of
row 0's files ends in `RowZeroOwed` at the book-keeping with the layer X (`fillAt … (endedX X)`,
which is
`besideL (fillZ …) X`) is laid here as it lies. -/
structure LastLeftB : Prop extends LastRest o mk Z (seatK Z N) N c D cs G arr smp dB dt mine get
    smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS ML stOf bookOf Pm₀ N₁ Ns links ps Oc Y (fun q => firstOfS
    (get q).2) (endedX X) num no rd r where
  /-- ROW 0's DEBT at the book-keeping with the layer X; the layer Y is not in it. -/
  row0B : RowZeroOwed (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁)
      (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillAt
      (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) Oc (pieceZeroAt (FL o mk Z
      (seatK Z N) N c) D (c0 Z) (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D cs G
      arr smp decT c₀' mine)))
  /-- ON THE LAYER Y: ROW 0's ACCEPTING RUN EARNS IT AT BORDER 1. -/
  earn₀ : ∀ a τ b, onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber))
      (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G
      arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2
      N).rounds (fun q => firstOfS (get q).2) (endedX X)) Oc 0 a → Y 0 a.1.2 = true → (pieceZeroAt
      (FL o mk Z (seatK Z N) N c) D (c0 Z) (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N
      c) D cs G arr smp decT c₀' mine))).ior.red.out a τ = some b → Y 1 b.1.2 = true

variable {o mk Z N c D cs G arr smp dB dt mine get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS ML stOf
    bookOf Pm₀ N₁ Ns links ps Oc Y num no rd r Pw t₁ t₂ X wSeat}

/-- **It gives the ledger's structure**: row 0's debt is lifted to the layer Y. -/
theorem LastLeftB.left (L : LastLeftB o mk Z N c D cs G arr smp decT c₀' dB dt mine get smp₁ smp₂
    ms₁ ms₂ decT₁ decT₂ M₁ MS ML stOf bookOf Pm₀ N₁ Ns links ps Oc Y num no rd r X) : LastLeft o mk
    Z (seatK Z N) N c D cs G arr smp decT c₀' dB dt mine get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS ML
    stOf bookOf Pm₀ N₁ Ns links ps Oc Y (fun q => firstOfS (get q).2) (endedX X) num no rd r where
  toLastRest := L.toLastRest
  row0 := ⟨ownLiftS _ _ _ _ _ _ Y 0 _ _ _ L.earn₀ L.row0B.1,
    framesLiftS _ _ _ _ _ _ Y 0 _ _ _ L.row0B.2⟩

variable (a₁ : Block (FL o mk Z (seatK Z N) N c).S₁ (FL o mk Z (seatK Z N) N c).Cl) (k₁ : List
    (Block (FL o mk Z (seatK Z N) N c).S₁ (FL o mk Z (seatK Z N) N c).Cl))
  (a₂ : Block St (FL o mk Z (seatK Z N) N c).Cl) (k₂ : List (Block St (FL o mk Z (seatK Z N) N
      c).Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) ((FL o mk Z
      (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁) (Wit Cells Tok MsgT) ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0) (((FL o mk Z
      (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁) × St) (Wit Cells Tok MsgT) ds)
  (d wEnd : Wit Cells Tok MsgT)

/-- **The same from the structure with row 0's debt as one premise.** -/
theorem e3_of_leftB (L : LastLeftB o mk Z N c D cs G arr smp decT c₀' dB dt mine get smp₁ smp₂ ms₁
    ms₂ decT₁ decT₂ M₁ MS ML stOf bookOf Pm₀ N₁ Ns links ps Oc Y num no rd r X) (b₀ : Block (FL o mk
    Z (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl) (l : List (Block (FL o mk Z (seatK Z N) N
    c).S₃ (FL o mk Z (seatK Z N) N c).Cl)) (hflat : (FL o mk Z (seatK Z N) N c).second.blocksInOrder = b₀ ::
    l) (hds : ds₂ D.ds₃ (held (P := (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N
    c).S₁ × St) (c0 Z)) (held (P := (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N
    c).S₁ × St) (c1 N)) (held (P := (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N
    c).S₁ × St) (c2 N)) = dB :: dt) : EachLeads (onQ₃ (Fr := frameAt D (allOf D) D.key₃ (atDesc (FL
    o mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l
    rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D cs G arr smp decT c₀'
    mine)) d wEnd)).ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁
    M₁) (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (besideS
    (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) Y) Oc) (stepQ₃ (atDesc
    (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l
    rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D cs G arr smp decT c₀'
    mine)) d wEnd)) (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁)
    (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (besideS
    (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) Y) Oc) 0 ((atDesc (FL
    o mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l
    rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D cs G arr smp decT c₀'
    mine)) d wEnd)).p₃ :: (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK
    Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N)
    N c) D cs G arr smp decT c₀' mine)) d wEnd)).l₃) :=
  e3_of_left a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd (L.left decT c₀') b₀ l hflat hds

/-- **The same from the structure with row 0's debt as one premise.** -/
theorem own3_of_leftB (L : LastLeftB o mk Z N c D cs G arr smp decT c₀' dB dt mine get smp₁ smp₂ ms₁
    ms₂ decT₁ decT₂ M₁ MS ML stOf bookOf Pm₀ N₁ Ns links ps Oc Y num no rd r X) (b₀ : Block (FL o mk
    Z (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl) (l : List (Block (FL o mk Z (seatK Z N) N
    c).S₃ (FL o mk Z (seatK Z N) N c).Cl)) (hflat : (FL o mk Z (seatK Z N) N c).second.blocksInOrder = b₀ ::
    l) (hds : ds₂ D.ds₃ (held (P := (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N
    c).S₁ × St) (c0 Z)) (held (P := (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N
    c).S₁ × St) (c1 N)) (held (P := (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N
    c).S₁ × St) (c2 N)) = dB :: dt) : EachOwn (onQ₃ (Fr := frameAt D (allOf D) D.key₃ (atDesc (FL o
    mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁
    rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D cs G arr smp decT c₀' mine))
    d wEnd)).ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁)
    (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (besideS
    (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) Y) Oc) (meansQ₃
    (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G
    arr smp₂ ms₂ decT₂ MS)) ML) insQ₃ outsQ₃ (· ∈ startLast) 0 ((atDesc (FL o mk Z (seatK Z N) N c)
    (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap
    (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D cs G arr smp decT c₀' mine)) d wEnd)).p₃ ::
    (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂
    k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D cs G arr smp
    decT c₀' mine)) d wEnd)).l₃) :=
  own3_of_left a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd (L.left decT c₀') b₀ l hflat hds

end LLT25

#print axioms LLT25.e3_of_leftB
#print axioms LLT25.own3_of_leftB
#print axioms LLT25.sharedSeatAt_is
