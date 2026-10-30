-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/Own3EndAtSh.lean: THE LAST CHAIN's FIELD IN THE FORM MEANT FOR THE
JOIN (`own3_at_end`, Johnson/LLT25R/LastEnd.lean: at the unpulled description FU o mk Z N c; hflat
fallen) WITH ITS PREMISE row0B GONE: AT M₁ := mgAll 𝔇 Mg · G := 𝔇.G · arr := 𝔇.arr · Cells := CellsQ
rows₀ cols₀ · links := Sound.linksFull · X := Sh.X (planAt Z N 𝔇.G) 12. Two theorems.


  ht₁_of_first     the premise ht₁ of row0B_of_sh from PlanOk₃'s dataIs and planOk and ONE equation:
  G's
                   first chain tells what the proof file's own description's first chain tells (by
                   rfl where G is FL …, FU … or a pull of it); by Sound.toldCount.
  own3_end_at_sh   own3_at_end called with row0B_of_sh (P2LawR/RowZeroBOfSh.lean). The statement is
                   own3_at_end's own, turned by program (whole tokens put in; the binder row0B taken
                   out; nine premises of row0B_of_sh laid in its place). row0B_of_sh is stated at FL
                   …, own3_at_end at FU …: that the one's end is the other's binder is Lean's to
                   take, by unfolding.
PREMISES. own3_at_end's six that stay: hSig · hRc · hP · hX · hS · hN. In row0B's place, nine: hcs ·
ht₁ · hSZ · h13 · hMg · hsh · hseat · hB · hdot.
IS IT EMPTY? NO MEMBER: as the heads of Johnson/LLT25R/LastEnd.lean and
Johnson/P2LawR/RowZeroBOfSh.lean say. Nothing on soundness.
-/
import Johnson.LLT25R.LastEnd
import Johnson.P2LawR.RowZeroBOfSh

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P2Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker OnBytes.Flat Fo.Peel
    Cb Johnson.Pack
open Iop Prob _root_.Run
open LLT25
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers openSets sampledIn start)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.K13.Law (vecAt)
open VerifiableInference.Desc.K1 (shapeAt)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law (DotEq gLaid parO omegaShapes_pos)
open _root_.Desc.K14.Law.Sh (planAt)
open _root_.Desc.K14.Law (Sh.X Sh.sentU Sh.layU Sh.layO Sh.mem)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At)

/-- **ht₁ from the plan's tests**: where G's first chain tells what the proof file's own
description's first chain tells. -/
theorem ht₁_of_first {Xi' : Type} (G : FileDescription Xi') (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub)
    (N : H2U.Places4) (c : Chain S Cl) (D : WholeD)
    (hD : ∃ file, (FL o mk Z (seatK Z N) N c).data file = .ok D)
    (hp : (FL o mk Z (seatK Z N) N c).planOk = true)
    (hfirst : oraclesOf G.first.blocksInOrder = oraclesOf (FL o mk Z (seatK Z N) N c).first.blocksInOrder) :
    (oraclesOf G.first.blocksInOrder).length = D.t₁ := by
  obtain ⟨file, hD⟩ := hD
  rw [hfirst]
  exact (Sound.toldCount _ _ file D hD).1 (Book.blocksOk_of_planOk _ hp).1

/-- **The last chain's field, at the unpulled description, with row 0's debt met by
row0B_of_sh (Johnson/P2LawR/RowZeroBOfSh.lean).** -/
theorem own3_end_at_sh {Tok P₀ Xi : Type} {rows₀ cols₀ nR : ℕ} {X₀ : OnBytes.Model.Verify.Public} (𝔇
    : MgData Xi P₀ Tok rows₀ cols₀ nR X₀) (Mg : Meaning P₀ (Wit (CellsQ rows₀ cols₀) Tok MsgT))
    (seats : List (ℕ × ℕ)) (oNo : Mem → ℕ) (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (N :
          H2U.Places4) (c : Chain S Cl) (D : WholeD) (dB : RDT) (dt : List RDT) (get : (FU o mk Z N
          c).XiPub × (FU o mk Z N c).S₁ → P₀ × First.S) (ms₁ ms₂ : List Mem) (decT₁ : (ℕ → Option (ℕ ×
          List UInt64)) → P₀ × First.S → Option (CellsQ rows₀ cols₀)) (decT₂ : (ℕ → Option (ℕ × List
          UInt64)) → St → Option (CellsQ rows₀ cols₀)) (MS : MeaningS St ((FU o mk Z N c).XiPub × (FU o mk
          Z N c).S₁) (Wit (CellsQ rows₀ cols₀) Tok MsgT)) (stOf : St → OnBytes.Statement) (bookOf : St →
          OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS) (r : Fmt.M1.Stage → ℕ)
    (Ld : VerifiableInference.Desc.K12.Door.Laid) (decT : (ℕ → Option (ℕ × List UInt64)) → (((FU o
    mk Z N c).XiPub × (FU o mk Z N c).S₁ × St) × (FU o mk Z N c).S₃) → Option (CellsQ rows₀ cols₀))
    (c₀' : (CellsQ rows₀ cols₀)) (a₁ : Block (FU o mk Z N c).S₁ (FU o mk Z N c).Cl) (k₁ : List
    (Block (FU o mk Z N c).S₁ (FU o mk Z N c).Cl)) (a₂ : Block St (FU o mk Z N c).Cl) (k₂ : List
    (Block St (FU o mk Z N c).Cl)) (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D
    (allOf D) D.key₁ 0) ((FU o mk Z N c).XiPub × (FU o mk Z N c).S₁) (Wit (CellsQ rows₀ cols₀) Tok
    MsgT) ds) (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0)
    (((FU o mk Z N c).XiPub × (FU o mk Z N c).S₁) × St) (Wit (CellsQ rows₀ cols₀) Tok MsgT) ds) (d
    wEnd : Wit (CellsQ rows₀ cols₀) Tok MsgT) (Rc : (FU o mk Z N c).XiPub × (FU o mk Z N c).S₁ →
    Prop) (hSig : meaningSig (p14At Z).codes 𝔇.G 𝔇.arr (smpNamed (p14At Z).codes seats) ms₁ decT₁
    (mgAll 𝔇 Mg) = (mgAll 𝔇 Mg)) (hRc : ∀ q y, ocEnd get N₁ (mgAll 𝔇 Mg) Sound.linksFull
    (First.flatPlaces true Sound.linksFull true) q y → Rc q → (get q).2.failed = none →
    ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At Z).codes (get q).2 = true) (hP : PlanOk₃ o mk Z N c D
    𝔇.G 𝔇.arr dB dt ms₁ ms₂ N₁ Ns Sound.linksFull (First.flatPlaces true Sound.linksFull true) r
    (N₁.treesAt none) 0 1 (vAt Z N₁) Ld) (hX : XSamples (p14At Z).codes (p14At Z).S (Sh.X (planAt Z
    N 𝔇.G) 12)) (hS : ∀ q y, ocEnd get N₁ (mgAll 𝔇 Mg) Sound.linksFull (First.flatPlaces true
    Sound.linksFull true) q y → Rc q → (get q).2.failed = none → ∀ f, firstOfS (get q).2 = some f →
    SeatsNumber seats f.book) (hN : ∀ x ∈ (mineOf ms₁ ms₂ N₁ Ns), seatOf x = (D.t₁ + 1, 0) → ∀ d,
    (Sh.X (planAt Z N 𝔇.G) 12) d = true → oNo x = d.loc.oOmega) (hcs : 𝔇.cs = (p14At Z).codes) (ht₁
    : (oraclesOf 𝔇.G.first.blocksInOrder).length = D.t₁) (hSZ : (VerifiableInference.Desc.K13.whereOf Z).lin
             = (P2Third.lastPar Z).S) (h13 : 𝔇.P13 = VerifiableInference.Desc.K13.whereOf Z) (hMg : Mg.more =
             {}) (xW : Mem) (hsh : 𝔇.P13.lin.w = (xW.1.l.get xW.2).1) (hseat : xW.1.seat xW.2 = 𝔇.N.w) (hB :
             ∀ q, Rc q → (get q).2.failed = none → NumberedBook 0 (get q).2.book ∧ BookFits (get q).2.book ∧
             ∀ o, o < (get q).2.st.oracles.size → ∃ r : ℕ × ℕ, (get q).2.book.place[o]? = some r) (hdot : ∀ q
             (s : St) y w, DotEq (P2Third.lastPar Z).S.matrixRows (P2Third.lastPar Z).S.kCol (gLaid 𝔇.P13 get
             q) (omLast 𝔇.arr (Sh.mem (planAt Z N 𝔇.G)) (planAt Z N 𝔇.G).Q (Sh.sentU (planAt Z N 𝔇.G)) w)
             (s.loc.psiSh.map OnBytes.Model.Reading.gl.val) (vecAt (linLayW 𝔇.cs 𝔇.P13.lin) (xW.1.l.get
             xW.2).1 (wTab 𝔇.cs 𝔇.arr xW w)) → MS.dot q s y w) :
    EachOwn (onQ₃ (Fr := frameAt D (allOf D) D.key₃ (atDesc (FU o mk Z N c) (piecesAt (ckP .two) (FU
    o mk Z N c) D a₁ k₁ a₂ k₂ (c0 Z) [c1 N, c2 N, c3 Z N] rest₁ rest₂ (restCap (extsLast (Tok :=
    Tok) (FU o mk Z N c) D (p14At Z).codes 𝔇.G 𝔇.arr (smpLast (p14At Z).codes (smpNamed (p14At
    Z).codes seats) (smpSt (p14At Z).codes oNo stSh) get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d
    wEnd)).ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get (mgAll 𝔇 Mg) (meaningSigS (p14At Z).codes 𝔇.G
    𝔇.arr (smpSt (p14At Z).codes oNo stSh) ms₂ decT₂ MS)) (promSigS (p14At Z).codes 𝔇.G (smpSt
    (p14At Z).codes oNo stSh) ms₂ stOf bookOf Pm₀) (besideS (fillAt (p14At Z) (c2 N).rounds (fun q
    => firstOfS (get q).2) (endedX (Sh.X (planAt Z N 𝔇.G) 12))) (yTree (p14At Z).codes (p14At Z).S))
    (fun q y => ocEnd get N₁ (mgAll 𝔇 Mg) Sound.linksFull (First.flatPlaces true Sound.linksFull
    true) q y ∧ Rc q)) (meansQ₃ (tiedNumbers N₁ Ns) (tiedMeaning get (mgAll 𝔇 Mg) (meaningSigS
    (p14At Z).codes 𝔇.G 𝔇.arr (smpSt (p14At Z).codes oNo stSh) ms₂ decT₂ MS)) (⟨rowsOpen (p14At
    Z).codes 𝔇.arr D.t₁ D.t₂⟩ : MeaningL (FU o mk Z N c).S₃ (Wit (CellsQ rows₀ cols₀) Tok MsgT)))
    insQ₃ outsQ₃ (· ∈ startLast) 0 ((atDesc (FU o mk Z N c) (piecesAt (ckP .two) (FU o mk Z N c) D
    a₁ k₁ a₂ k₂ (c0 Z) [c1 N, c2 N, c3 Z N] rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FU o mk Z N
    c) D (p14At Z).codes 𝔇.G 𝔇.arr (smpLast (p14At Z).codes (smpNamed (p14At Z).codes seats) (smpSt
    (p14At Z).codes oNo stSh) get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).p₃ :: (atDesc (FU o
    mk Z N c) (piecesAt (ckP .two) (FU o mk Z N c) D a₁ k₁ a₂ k₂ (c0 Z) [c1 N, c2 N, c3 Z N] rest₁
    rest₂ (restCap (extsLast (Tok := Tok) (FU o mk Z N c) D (p14At Z).codes 𝔇.G 𝔇.arr (smpLast
    (p14At Z).codes (smpNamed (p14At Z).codes seats) (smpSt (p14At Z).codes oNo stSh) get Ns) decT
    c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).l₃) :=
  own3_at_end seats oNo o mk Z N c D 𝔇.G 𝔇.arr dB dt get ms₁ ms₂ decT₁ decT₂ (mgAll 𝔇 Mg) MS stOf
    bookOf Pm₀ N₁ Ns Sound.linksFull (Sh.X (planAt Z N 𝔇.G) 12) r Ld decT c₀' a₁ k₁ a₂ k₂ rest₁
    rest₂ d wEnd Rc hSig hRc hP hX hS hN (row0B_of_sh seats oNo o mk Z N c D 𝔇 Mg dB dt get ms₁ ms₂
    decT₂ MS stOf bookOf Pm₀ N₁ Ns r Ld decT c₀' Rc hP hcs ht₁ hSZ h13 hMg xW hsh hseat hB hdot)

end P2Law

#print axioms P2Law.ht₁_of_first
#print axioms P2Law.own3_end_at_sh
