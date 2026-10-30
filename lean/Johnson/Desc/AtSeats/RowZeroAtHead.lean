-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/RowZeroAtHead.lean: ROW 0's DEBT OF THE LAST TABLE AT THE FIRST
AND THE SHARED TABLE's CLOSED LETTERS, UNDER THE ONE HEAD h : P5J.AtMgA …, WITH EVERY
PREMISE PAID THAT THE HEAD PAYS. Four theorems: joinings.

rowZeroOwed_atZ_shP (Johnson/Flat/Last/RowZeroAtShXPlan.lean; 17 premises) AT 𝔇 := h.𝔇 · Mg :=
mgBase · Z N G := Zp Np (seatF …) · get | N₁ | Rc := the shared table's open letters' (Sh.openAll
h (Sh.eCodes_at h)) · MS := Sh.mg A O · xW := Sh.xW A O · mem := Sh.mem A · lay₀ := linLayW
h.𝔇.cs h.𝔇.P13.lin.

  second_ok · hsec_at_head  the last chain's first sub-protocol's own test on its public
                            parameters accepts, off the head's laid.planOk.
  rowZeroOwed_atHead        **the top, in the tight form.** PAID: hSZ (P2R0.hSZ_of:
                            no pin) · h13 · hMg · hlay (rfl) · hsec (hsec_at_head) · hdot
                            (Sh.hdot_at, Johnson/Desc/K14/Law/SharedConstDotAt.lean, at eCodes_at
                            h · rfl · rfl) · hB (hB_of_facts,
                            Johnson/Desc/Book/LastBook.lean, from hB3). LEFT: h · hr · hI · hV ·
                            omega · rows · hsh · hB3 · hseat · hm · hent · hten.
hB3: THREE TESTS WITH CODE on every last state of the first chain of which O.R holds (reached, at
a typed instance's public part) and that bears no mark: each tree's number is its place in the
book (atFirstBook 0) · the book's two tables fit (bookFitsB) · as many places as oracle messages.
The form with hRO : Sh.ReachOwed … L asks two
tests more (the codes; the seats), of which nothing is spent, and whose payer brings a pin back.
rowZeroOwed_atHead_owed: that form, as a corollary.
What is not claimed. NO MEMBER. That the head can be met. That the conclusion's meaningSigS
h.𝔇.cs … can be read at A.Q.codes without carrying smp₂ along eCodes_at h. No soundness.

-/
import Johnson.Flat.Last.RowZeroAtShXPlan
import Johnson.Desc.K14.Law.SharedConstDotAt
import Johnson.Desc.K14.Law.SharedConstReachOwed
import Johnson.Desc.Book.LastBook
import Johnson.Desc.AtSeats.ShJointAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles.Last
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker OnBytes.Flat Fo.Peel Cb
open Johnson.Pack
open Iop Prob _root_.Run
open OnBytes.Means (Words)
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers openSets start)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.Third (S₃ P₁₄)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf vecAt wSitsMore wSits_open_all placeSeal)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law (DotEq omegaOf gLaid WSits hW_at_ocEnd)

open VerifiableInference.Desc.K1 (shapesOf shapeAt)
open _root_.Desc.K14 (P14 withOmega)
open _root_.Desc.K14.Law (XK XK_iff codY_of_codX codY_iff omWK rdK omegaTie wordsSh_is shape_omega
  omegaInRange_of_lengths parO)


open _root_.Desc.K14.Law (withOmega_pos omegaShapes_pos ShPlan XW_iff shape_omega)
open _root_.Desc.K14.Law.Sh (planAt)
open _root_.Desc.K14.Law (Sh.X Sh.sentU Sh.layU Sh.layO Sh.Y)

open VerifiableInference.Desc.Third (batchLinearConstraintsSecondPart second_planOk secondB)

open _root_.Desc.K14.Law (secondAt)
open _root_.Desc.K14.Law.Sh (seatF openAll eCodes_at ReachOwed front2_at_seat)
open _root_.Desc.K14.Law (Sh.mg Sh.xW Sh.mem Sh.hdot_at)
open P5J (AtMgA colsAt)
open OnBytes.Maker (WholeD)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain First.S ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- Where the tests on the plan accept, blocksOk accepts the last chain's flat list. -/
theorem second_ok {Xi : Type} (F : FileDescription Xi) (h : F.planOk = true) :
    blocksOk F.second.blocksInOrder = true := by
  unfold FileDescription.planOk FileDescription.planOkCore at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hb⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  exact hb

/-- The last chain's first sub-protocol's own test accepts, off the head. -/
theorem hsec_at_head {Cl : Type} (h : AtMgA o Z D r₀ Zp Np cF x₀) :
    (batchLinearConstraintsSecondPart (Cl := Cl) (P2Third.lastPar Zp)).planOk = true := by
  have h1 := P2R0.first_ok _ (second_ok _ h.laid.planOk)
  obtain ⟨y, y', e⟩ : ∃ y y' : Bool, (P5J.F0T o Zp Np cF).second.first.planOk =
      ((secondB (P2Third.lastPar Zp).codes (P2Third.lastPar Zp).S && y) && y') := ⟨_, _, rfl⟩
  rw [e] at h1
  rw [second_planOk]
  exact (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h1).1).1

/-- **Row 0's debt at the closed letters, under the head: the tight form.** -/
theorem rowZeroOwed_atHead {Cl : Type} {Fr : Frame} (h : AtMgA o Z D r₀ Zp Np cF x₀) (smp₂ :
    St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf h.𝔇.cs s.l).om i).Smp) (ms₂ : List
    Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option (CellsQ numsFull.rows (colsAt
    numsFull))) (stOf : St → OnBytes.Statement) (bookOf : St → OnBytes.TreeBook) (Pm₀ :
    PromMeaning St) (Ns : NumbersS) (R : List Fmt.DeclaredRound) (ML : MeaningL S₃ (Wit (CellsQ
        numsFull.rows (colsAt numsFull)) P5J.At.Tok MsgT)) (t₁ t₂ base : ℕ) (ds : List RDT) (back :
        List Fmt.RoundView) (r : Rest (ckP .two) Fr ((ProofFile.InstPub × First.S × St) × S₃) (Wit (CellsQ
                     numsFull.rows (colsAt numsFull)) P5J.At.Tok MsgT) ds) (hr : ∀ a τ w, r.ext a τ w = w) (hI :
                     (openAll h (eCodes_at h)).N₁.index.1 < base) (hV : (openAll h (eCodes_at h)).N₁.w.1 < base)
    (omega : (Ns.tenant .oOmega).1 < base) (rows : ∀ b w, onOcX Fr h.𝔇.cs h.𝔇.G h.𝔇.arr
    (openAll h (eCodes_at h)).get smp₂ ms₂ decT₂ (mgAll h.𝔇 mgBase) (Sh.mg (planAt Zp Np (seatF o
    Zp Np (secondAt Zp Np) cF)) (openAll h (eCodes_at h))) stOf bookOf Pm₀ (openAll h (eCodes_at
    h)).N₁ Ns (P2Third.lastPar Zp) R (Sh.X (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)) 12)
    (fun q y => ocEnd (openAll h (eCodes_at h)).get (openAll h (eCodes_at h)).N₁ (mgAll h.𝔇
    mgBase) Sound.linksFull (First.flatPlaces true Sound.linksFull true) q y ∧ (openAll h
    (eCodes_at h)).R q) 1 b → ML.rows b.1.2 w → ∃ t, VerifiableInference.Desc.K12.Seat.enterOwn
    b.1.2 = .ok t ∧ ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i
    (OnBytes.Means.wordsOn t.st (tabAt (P2Third.lastPar Zp).codes h.𝔇.arr (seatBy (noLast t₁ t₂
    b.1.2.loc.firstTree) b.1.2.book) t.st w))) (hsh : h.𝔇.P13.lin.w = ((Sh.xW (planAt Zp Np
    (seatF o Zp Np (secondAt Zp Np) cF)) (openAll h (eCodes_at h))).1.l.get (Sh.xW (planAt Zp Np
    (seatF o Zp Np (secondAt Zp Np) cF)) (openAll h (eCodes_at h))).2).1) (hB3 : ∀ p, (openAll h
    (eCodes_at h)).R p → ((openAll h (eCodes_at h)).get p).2.failed = none →
    VerifiableInference.Desc.K12.Door.atFirstBook 0 ((openAll h (eCodes_at h)).get p).2 = true ∧
    bookFitsB ((openAll h (eCodes_at h)).get p).2.book = true ∧ ((openAll h (eCodes_at h)).get
    p).2.book.place.size = ((openAll h (eCodes_at h)).get p).2.st.oracles.size) (hseat : (Sh.xW
    (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)) (openAll h (eCodes_at h))).1.seat (Sh.xW
    (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)) (openAll h (eCodes_at h))).2 = h.𝔇.N.w) (x
    : Mem) (hm : (Sh.mem (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF))) (Sh.sentU (planAt Zp
    Np (seatF o Zp Np (secondAt Zp Np) cF))).size = some x) (hent : (x.1.l.get x.2).1 = shapeAt
    (parO (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)).Q) ⟨0, (omegaShapes_pos (planAt Zp Np
    (seatF o Zp Np (secondAt Zp Np) cF)).Q)⟩) (hten : x.1.seat x.2 = (t₁ + ((planAt Zp Np (seatF o
    Zp Np (secondAt Zp Np) cF)).Q.par.toGPar.firstTree + ((Sh.layU (planAt Zp Np (seatF o Zp Np
    (secondAt Zp Np) cF))).shapes.size + (Sh.layO (planAt Zp Np (seatF o Zp Np (secondAt Zp Np)
    cF))).tree.getD 0 0)), (Sh.layO (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF))).part.getD
    0 0)) : RowZeroOwed (tiedNumbers (openAll h (eCodes_at h)).N₁ Ns) (tiedMeaning (openAll h
    (eCodes_at h)).get (mgAll h.𝔇 mgBase) (meaningSigS h.𝔇.cs h.𝔇.G h.𝔇.arr smp₂ ms₂ decT₂
    (Sh.mg (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)) (openAll h (eCodes_at h))))) ML
    (promSigS h.𝔇.cs h.𝔇.G smp₂ ms₂ stOf bookOf Pm₀) (besideL (fillZ (P2Third.lastPar Zp) R fun
    q => ((openAll h (eCodes_at h)).get q).2) (Sh.X (planAt Zp Np (seatF o Zp Np (secondAt Zp Np)
    cF)) 12)) (fun q y => ocEnd (openAll h (eCodes_at h)).get (openAll h (eCodes_at h)).N₁ (mgAll
    h.𝔇 mgBase) Sound.linksFull (First.flatPlaces true Sound.linksFull true) q y ∧ (openAll h
    (eCodes_at h)).R q) (pieceOf (heldZero (P := ProofFile.InstPub × First.S × St) (Cl := Cl)
    (P2Third.lastPar Zp)) base ds back r) :=
  rowZeroOwed_atZ_shP h.𝔇 mgBase (openAll h (eCodes_at h)).get smp₂ ms₂ decT₂
    (Sh.mg (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)) (openAll h (eCodes_at h))) stOf
        bookOf Pm₀
    (openAll h (eCodes_at h)).N₁ Ns Zp Np (seatF o Zp Np (secondAt Zp Np) cF)
    (P2R0.hSZ_of h.laid.pub (front2_at_seat Np (secondAt Zp Np) cF h.laid.planOk)) rfl R
    (Sh.mem (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF))) ML t₁ t₂ base ds back r hr
    (openAll h (eCodes_at h)).R rfl hI hV omega rows
    (Sh.xW (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)) (openAll h (eCodes_at h))) _ rfl hsh
        hseat
    (VerifiableInference.Desc.Book.hB_of_facts _ _ hB3)
    x hm hent hten (hsec_at_head h)
    (Sh.hdot_at (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)) (openAll h (eCodes_at h)) h.𝔇
        (eCodes_at h) rfl rfl
      _ rfl)

/-- Its corollary from the shared table's constant's "owed" (which asks two tests more). -/
theorem rowZeroOwed_atHead_owed {Cl : Type} {Fr : Frame} (h : AtMgA o Z D r₀ Zp Np cF x₀)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf h.𝔇.cs s.l).om i).Smp)
    (ms₂ : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option (CellsQ numsFull.rows
    (colsAt numsFull))) (stOf : St → OnBytes.Statement) (bookOf : St → OnBytes.TreeBook) (Pm₀ :
    PromMeaning St) (Ns : NumbersS) (R : List Fmt.DeclaredRound) (ML : MeaningL S₃ (Wit (CellsQ
        numsFull.rows (colsAt numsFull)) P5J.At.Tok MsgT)) (t₁ t₂ base : ℕ) (ds : List RDT) (back :
        List Fmt.RoundView) (r : Rest (ckP .two) Fr ((ProofFile.InstPub × First.S × St) × S₃) (Wit (CellsQ
                     numsFull.rows (colsAt numsFull)) P5J.At.Tok MsgT) ds) (hr : ∀ a τ w, r.ext a τ w = w) (hI :
                     (openAll h (eCodes_at h)).N₁.index.1 < base) (hV : (openAll h (eCodes_at h)).N₁.w.1 < base)
    (omega : (Ns.tenant .oOmega).1 < base) (rows : ∀ b w, onOcX Fr h.𝔇.cs h.𝔇.G h.𝔇.arr
    (openAll h (eCodes_at h)).get smp₂ ms₂ decT₂ (mgAll h.𝔇 mgBase) (Sh.mg (planAt Zp Np (seatF o
    Zp Np (secondAt Zp Np) cF)) (openAll h (eCodes_at h))) stOf bookOf Pm₀ (openAll h (eCodes_at
    h)).N₁ Ns (P2Third.lastPar Zp) R (Sh.X (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)) 12)
    (fun q y => ocEnd (openAll h (eCodes_at h)).get (openAll h (eCodes_at h)).N₁ (mgAll h.𝔇
    mgBase) Sound.linksFull (First.flatPlaces true Sound.linksFull true) q y ∧ (openAll h
    (eCodes_at h)).R q) 1 b → ML.rows b.1.2 w → ∃ t, VerifiableInference.Desc.K12.Seat.enterOwn
    b.1.2 = .ok t ∧ ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i
    (OnBytes.Means.wordsOn t.st (tabAt (P2Third.lastPar Zp).codes h.𝔇.arr (seatBy (noLast t₁ t₂
    b.1.2.loc.firstTree) b.1.2.book) t.st w))) (hsh : h.𝔇.P13.lin.w = ((Sh.xW (planAt Zp Np
    (seatF o Zp Np (secondAt Zp Np) cF)) (openAll h (eCodes_at h))).1.l.get (Sh.xW (planAt Zp Np
    (seatF o Zp Np (secondAt Zp Np) cF)) (openAll h (eCodes_at h))).2).1) (L :
    VerifiableInference.Desc.K12.Door.Laid) (hRO : ReachOwed o Zp Np (secondAt Zp Np) cF L) (hseat
    : (Sh.xW (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)) (openAll h (eCodes_at h))).1.seat
    (Sh.xW (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)) (openAll h (eCodes_at h))).2 =
    h.𝔇.N.w) (x : Mem) (hm : (Sh.mem (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)))
    (Sh.sentU (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF))).size = some x) (hent :
    (x.1.l.get x.2).1 = shapeAt (parO (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)).Q) ⟨0,
    (omegaShapes_pos (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)).Q)⟩) (hten : x.1.seat x.2
    = (t₁ + ((planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)).Q.par.toGPar.firstTree + ((Sh.layU
    (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF))).shapes.size + (Sh.layO (planAt Zp Np
    (seatF o Zp Np (secondAt Zp Np) cF))).tree.getD 0 0)), (Sh.layO (planAt Zp Np (seatF o Zp Np
    (secondAt Zp Np) cF))).part.getD 0 0)) : RowZeroOwed (tiedNumbers (openAll h (eCodes_at h)).N₁
    Ns) (tiedMeaning (openAll h (eCodes_at h)).get (mgAll h.𝔇 mgBase) (meaningSigS h.𝔇.cs h.𝔇.G
    h.𝔇.arr smp₂ ms₂ decT₂ (Sh.mg (planAt Zp Np (seatF o Zp Np (secondAt Zp Np) cF)) (openAll h
    (eCodes_at h))))) ML (promSigS h.𝔇.cs h.𝔇.G smp₂ ms₂ stOf bookOf Pm₀) (besideL (fillZ
    (P2Third.lastPar Zp) R fun q => ((openAll h (eCodes_at h)).get q).2) (Sh.X (planAt Zp Np
    (seatF o Zp Np (secondAt Zp Np) cF)) 12)) (fun q y => ocEnd (openAll h (eCodes_at h)).get
    (openAll h (eCodes_at h)).N₁ (mgAll h.𝔇 mgBase) Sound.linksFull (First.flatPlaces true
    Sound.linksFull true) q y ∧ (openAll h (eCodes_at h)).R q) (pieceOf (heldZero (P :=
    ProofFile.InstPub × First.S × St) (Cl := Cl) (P2Third.lastPar Zp)) base ds back r) :=
  rowZeroOwed_atHead h smp₂ ms₂ decT₂ stOf bookOf Pm₀ Ns R ML t₁ t₂ base ds back r hr hI hV omega
      rows
    hsh
    (fun p hp hm => ⟨(hRO p hp.1 hp.2 hm).1, (hRO p hp.1 hp.2 hm).2.1, (hRO p hp.1 hp.2 hm).2.2.1⟩)
    hseat x hm hent hten

end VerifiableInference.OnPublicFiles.Last
