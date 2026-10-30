-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/NewAtTwoPaid.lean: K01_law's BINDERS
hNew0 · hNewW WITH hholds AND htie PAID AS AT THE KIND's FIFTY LATER PLACES. Two theorems:
joinings.

  hNewW_paid · hNew0_paid  hNewW_of | hNew0_of (NewAtTwo.lean) with hholds := hholds_of
                           (BookHoldsAt.lean: off a public test on the book that is open in
                           front of the place) and htie := htie_at (HtieAt.lean: at the named
                           reader of OOD samples). IN THEIR PLACE: fI · fB · hfB · hfits · hopen
                           (the test says "the book fits"; it is open at the border in front) ·
                           seats · hsmp (the reader is smpNamed cs seats) · hsam (every message of
                           the place has an OOD sample) · hCond · hNd · hpl (the list of seats has
                           the place's seats at the table's numbers).
What is not claimed. That the test on the book is open in front of number 2 or 356 at any list of
extra public tests; where that name has left the list, hholds is had of reached states instead.
Nothing on soundness.
Every premise and binder that names d₁ d₂ has an antecedent
behind the two tags: d₁ d₂ are the two rounds that the written data hold at the place. Why: asked
at every d₁ d₂ with the two tags a premise could not be met (planAt_all_false [not in this library]:
at a d₁ without a tree PlanAt's field tree is false): the laws above would be true and empty.

-/
import Johnson.Desc.K1.Law.NewAtTwo
import Johnson.Desc.K1.Law.BookHoldsAt
import Johnson.Desc.K1.Law.HtieAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model Johnson.G Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat KObj OnBytes.Slice
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Sound (CellsQ smpNamed)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More start flatPlacesOf)
open VerifiableInference.Desc.K13 (whereOf atM4)
open VerifiableInference.Desc.K13.Law (openAt wSitsItem wSitsB atM4_booked)
open OnBytes.Params (Rounds)
open Johnson.Desc.First.Walk (LayPar)
open ProofFile (Cl)
open VerifiableInference.Desc.Book (BookFits)

/-- **hNewW, its two premises on the state paid as at the fifty.** -/
theorem hNewW_paid {Z : ProofFile.Pub} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} {aN : ℕ} {R₁ R₂ R₃ : Rounds} {all : List LeftT} {X₁ X₂ Xi Tok : Type}
    {rows cols : ℕ}
    {T : ThreeAt (ckP .two) (dataOf aN R₁ R₂ R₃) all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Wit (CellsQ rows cols) Tok MsgT)}
    (cs : Codes) (G : FileDescription Xi)
    (smp : ProofFile.InstPub × S → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (N : Numbers) (Mg : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))
    (hheld : Mg.held = fun j t a => smpHeld a.2.st a.2.book j t)
    (hshown : Mg.shown = shownJT cs G ms) (hnoColl : Mg.noColl = noCollJT cs G smp ms)
    (msgW : Array OracleNotice) (radW : ℕ → ℕ)
    (HP : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Z msgW) → d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 356)).take 2 = [d₁, d₂] →
      PlanAt (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) cs G ms
        (parWZ Z msgW) radW (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ [N.w])
    (hbase : N.treesAt psF[356]? = (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))))
    (fI : Pub) (fB : TreeBook → Bool) (hfB : ∀ Bk, fB Bk = true ↔ BookFits Bk)
    (hfits : ∀ a, Mg.pub fI a = fB a.2.book)
    (hopen : fI ∈ (First.pubSets Mg.more Sound.linksFull psF)[356]?.getD [])
    (seats : List (ℕ × ℕ)) (hsmp : smp = smpNamed cs seats)
    (hsam : ∀ j : Fin (shapesOf (parWZ Z msgW)).length, sampledAt (parWZ Z msgW) j)
    (hCond : condPort (parWZ Z msgW) radW = true) (hNd : seats.Nodup)
    (hpl : ∀ j : Fin (shapesOf (parWZ Z msgW)).length,
      seats[N.msgsAt psF[356]? + j.val]? =
        some (seatOfMsg (parWZ Z msgW) (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) j.val)) :
    ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Z msgW) → d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 356)).take 2 = [d₁, d₂] →
      ∃ (fOf : (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str →
          ∀ j, (portOmZ (parWZ Z msgW).codes (shapeAt (parWZ Z msgW) j) (radW j.val)).Str)
        (fIn : (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str →
          (wT d₁).Msg →
          ∀ j, (portOmZ (parWZ Z msgW).codes (shapeAt (parWZ Z msgW) j) (radW j.val)).Str),
      ∀ c' : Block S Cl, c'.UnderR (atM4 (whereOf Z) (sendAtS (parWZ Z msgW))) →
      (∀ y τ, fOf ((sendPiece (W := Wit (CellsQ rows cols) Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ (parWZ Z msgW).coordinates
        (errPort (parWZ Z msgW) radW)).ior.imp y τ) = fIn y τ.1) ∧
      ∀ (z : ProofFile.InstPub) a τ x,
      onQ N Mg Sound.linksFull psF (fun s : S => (z, s)) 356 a → a.1.failed = none →
      (sendPiece (W := Wit (CellsQ rows cols) Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ (parWZ Z msgW).coordinates
        (errPort (parWZ Z msgW) radW)).ior.red.out a τ = some x →
      (∀ j, sampledAt (parWZ Z msgW) j →
        Sealed (parWZ Z msgW).codes (shapeAt (parWZ Z msgW) j) (radW j.val) (fOf x.2 j) x.1.st
          (x.1.st.oracles.size - (shapesOf (parWZ Z msgW)).length + j.val)) →
      (wSitsItem ∈ (First.pubSets Mg.more Sound.linksFull psF)[356 + 1]?.getD [] →
        wSitsB (parWZ Z msgW).codes (whereOf Z) x.1 = true ∧
          x.1.book.place[x.1.st.oracles.size - (shapesOf (parWZ Z msgW)).length]? = some N.w) →
      Mg.held N.w.1 N.w.2 (z, x.1) = true ∧
        Mg.noColl N.w.1 N.w.2 (z, x.1)
          (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2) :=
  hNewW_of cs G smp ms N Mg hheld hshown hnoColl msgW radW HP hbase
    (fun z a ha hm => hholds_of N Mg _ _ 356 z fI fB hfB hfits hopen a ha hm)
    (fun d₁ d₂ he hk hds c' hu z => by
      rw [hsmp]
      exact htie_at cs seats ms N Mg _ _ 356 (parWZ Z msgW) radW radW _ d₁ d₂ (HP d₁ d₂ he hk hds).mems
        (fun j _ _ _ => hsam j) hCond hNd hpl
        (atM4 (whereOf Z) (sendAtS (parWZ Z msgW)) : Block S Unit) rfl
        (fun s s' r₁ r₂ gs h => atM4_booked h) c' hu _ z)

/-- **hNew0, likewise.** -/
theorem hNew0_paid {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} {aN : ℕ} {R₁ R₂ R₃ : Rounds} {all : List LeftT} {X₁ X₂ Xi Tok : Type}
    {rows cols : ℕ}
    {T : ThreeAt (ckP .two) (dataOf aN R₁ R₂ R₃) all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Wit (CellsQ rows cols) Tok MsgT)}
    (cs : Codes) (G : FileDescription Xi)
    (smp : ProofFile.InstPub × S → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (N : Numbers) (Mg : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))
    (hheld : Mg.held = fun j t a => smpHeld a.2.st a.2.book j t)
    (hshown : Mg.shown = shownJT cs G ms) (hnoColl : Mg.noColl = noCollJT cs G smp ms)
    (X0 : LayPar)
    (HP : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (firstPar Bs.G₀.first (gpOf Z)) →
      d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 2)).take 2 = [d₁, d₂] →
      PlanAt (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) cs G ms
        (firstPar Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar Bs.G₀.first (gpOf Z)))
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))) d₁ d₂
        (First.sampledIn N (openAt Sound.linksFull psF (2 + 1))))
    (hbase : N.treesAt psF[2]? = (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))))
    (fI : Pub) (fB : TreeBook → Bool) (hfB : ∀ Bk, fB Bk = true ↔ BookFits Bk)
    (hfits : ∀ a, Mg.pub fI a = fB a.2.book)
    (hopen : fI ∈ (First.pubSets Mg.more Sound.linksFull psF)[2]?.getD [])
    (seats : List (ℕ × ℕ)) (hsmp : smp = smpNamed cs seats)
    (hsam : ∀ j : Fin (shapesOf (firstPar Bs.G₀.first (gpOf Z))).length, sampledAt (firstPar Bs.G₀.first (gpOf Z)) j)
    (hCond : condPort (firstPar Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar Bs.G₀.first (gpOf Z))) = true) (hNd : seats.Nodup)
    (hpl : ∀ j : Fin (shapesOf (firstPar Bs.G₀.first (gpOf Z))).length,
      seats[N.msgsAt psF[2]? + j.val]? =
        some (seatOfMsg (firstPar Bs.G₀.first (gpOf Z)) (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))) j.val)) :
    ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (firstPar Bs.G₀.first (gpOf Z)) →
      d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 2)).take 2 = [d₁, d₂] →
      ∃ (fOf : (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str →
          ∀ j, (portOmZ (firstPar Bs.G₀.first (gpOf Z)).codes
            (shapeAt (firstPar Bs.G₀.first (gpOf Z)) j) ((radRec 0 (firstPar Bs.G₀.first (gpOf Z))) j.val)).Str)
        (fIn : (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str →
          (wT d₁).Msg →
          ∀ j, (portOmZ (firstPar Bs.G₀.first (gpOf Z)).codes
            (shapeAt (firstPar Bs.G₀.first (gpOf Z)) j) ((radRec 0 (firstPar Bs.G₀.first (gpOf Z))) j.val)).Str),
      ∀ (nm : String) (c' : Block S Cl), c'.UnderR (openingZero Bs.G₀.first (gpOf Z) nm X0
        (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol) →
      (∀ y τ, fOf ((sendPiece (W := Wit (CellsQ rows cols) Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))) d₁ d₂
        (firstPar Bs.G₀.first (gpOf Z)).coordinates
        (errPort (firstPar Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar Bs.G₀.first (gpOf Z))))).ior.imp y τ) = fIn y τ.1) ∧
      ∀ (z : ProofFile.InstPub) a τ x,
      onQ N Mg Sound.linksFull psF (fun s : S => (z, s)) 2 a → a.1.failed = none →
      (sendPiece (W := Wit (CellsQ rows cols) Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))) d₁ d₂
        (firstPar Bs.G₀.first (gpOf Z)).coordinates
        (errPort (firstPar Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar Bs.G₀.first (gpOf Z))))).ior.red.out a τ = some x →
      (∀ j, sampledAt (firstPar Bs.G₀.first (gpOf Z)) j →
        Sealed (firstPar Bs.G₀.first (gpOf Z)).codes
          (shapeAt (firstPar Bs.G₀.first (gpOf Z)) j) ((radRec 0 (firstPar Bs.G₀.first (gpOf Z))) j.val) (fOf x.2 j) x.1.st
          (x.1.st.oracles.size - (shapesOf (firstPar Bs.G₀.first (gpOf Z))).length + j.val)) →
      ∀ t ∈ First.sampledIn N (openAt Sound.linksFull psF (2 + 1)),
        Mg.held t.1 t.2 (z, x.1) = true ∧
          Mg.shown t.1 t.2
            (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2) ∧
          Mg.noColl t.1 t.2 (z, x.1)
            (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2) :=
  hNew0_of cs G smp ms N Mg hheld hshown hnoColl X0 HP hbase
    (fun z a ha hm => hholds_of N Mg _ _ 2 z fI fB hfB hfits hopen a ha hm)
    (fun d₁ d₂ he hk hds nm c' hu z => by
      rw [hsmp]
      exact htie_at cs seats ms N Mg _ _ 2 (firstPar Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar Bs.G₀.first (gpOf Z)))
        (radRec 0 (firstPar Bs.G₀.first (gpOf Z))) _ d₁ d₂ (HP d₁ d₂ he hk hds).mems
        (fun j _ _ _ => hsam j) hCond hNd hpl
        (openingZero Bs.G₀.first (gpOf Z) nm X0
          (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol : Block S Unit) rfl
        (fun s s' r₁ r₂ gs h => (openingZero_rec h).2.2.2.2.1) c' hu _ z)

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hNewW_paid
#print axioms VerifiableInference.Desc.K1.hNew0_paid
