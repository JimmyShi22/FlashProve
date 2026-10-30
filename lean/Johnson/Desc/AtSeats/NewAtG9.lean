-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/NewAtG9.lean: THE PAYER OF THE PREMISE hNew OF THE TIE AT THE FIRST SEGMENT's
OPENING (number 2), IN A FORM THAT CAN BE MET THERE. Statements with their proofs: calls. The like
of Johnson/Desc/AtSeats/NewAtW9.lean. WHY. `hNew0_paid` (Johnson/Desc/K1/Law/NewAtTwoPaid.lean)
asks hsam: EVERY message of the place has an OOD sample. By a print (not shown here) the
opening's message number 3 (the fold's mask) has none: so at the release's own list of rounds that
premise is false and the payer says nothing. `hNew0_weak`: the same statement with hsam in the
  weaker form that `htie_at` itself asks: a message at whose seat a member of ms sits has an OOD
  sample. Made by program out of `hNew0_paid`'s own text: one binder and one argument turn.
  `bookFits_open2`, `bookFits_openG`: "the book fits" is open in front of number 2 at the wider
  door: by the kernel. So hopen falls at `plusG D d dk (mgAll 𝔇 mgBase)`.
What is not claimed. The premises. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.NewAtTwoPaid
import Johnson.Desc.AtSeats.DoorAt9WG

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

/-- **hNew0, with what its payers ask and no more.** -/
theorem hNew0_weak {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {c : Chain S Cl} {A : ProofFile.SharedSeat}
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
    (hsam : ∀ j : Fin (shapesOf (firstPar Bs.G₀.first (gpOf Z))).length, ∀ m' ∈ ms,
      SitsAt m' (seatOfMsg (firstPar Bs.G₀.first (gpOf Z)) (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take
          (inFront c 2))) j.val).1
        (seatOfMsg (firstPar Bs.G₀.first (gpOf Z)) (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c
            2))) j.val).2 →
      sampledAt (firstPar Bs.G₀.first (gpOf Z)) j)
    (hCond : condPort (firstPar Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar Bs.G₀.first (gpOf Z))) =
        true) (hNd : seats.Nodup)
    (hpl : ∀ j : Fin (shapesOf (firstPar Bs.G₀.first (gpOf Z))).length,
      seats[N.msgsAt psF[2]? + j.val]? =
        some (seatOfMsg (firstPar Bs.G₀.first (gpOf Z)) (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take
            (inFront c 2))) j.val)) :
    ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (firstPar Bs.G₀.first (gpOf Z)) →
      d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 2)).take 2 = [d₁, d₂] →
      ∃ (fOf : (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str →
          ∀ j, (portOmZ (firstPar Bs.G₀.first (gpOf Z)).codes
            (shapeAt (firstPar Bs.G₀.first (gpOf Z)) j) ((radRec 0 (firstPar Bs.G₀.first (gpOf Z)))
                j.val)).Str)
        (fIn : (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str →
          (wT d₁).Msg →
          ∀ j, (portOmZ (firstPar Bs.G₀.first (gpOf Z)).codes
            (shapeAt (firstPar Bs.G₀.first (gpOf Z)) j) ((radRec 0 (firstPar Bs.G₀.first (gpOf Z)))
                j.val)).Str),
      ∀ (nm : String) (c' : Block S Cl), c'.UnderR (openingZero Bs.G₀.first (gpOf Z) nm X0
        (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol) →
      (∀ y τ, fOf ((sendPiece (W := Wit (CellsQ rows cols) Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))) d₁ d₂
        (firstPar Bs.G₀.first (gpOf Z)).coordinates
        (errPort (firstPar Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar Bs.G₀.first (gpOf
            Z))))).ior.imp y τ) = fIn y τ.1) ∧
      ∀ (z : ProofFile.InstPub) a τ x,
      onQ N Mg Sound.linksFull psF (fun s : S => (z, s)) 2 a → a.1.failed = none →
      (sendPiece (W := Wit (CellsQ rows cols) Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))) d₁ d₂
        (firstPar Bs.G₀.first (gpOf Z)).coordinates
        (errPort (firstPar Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar Bs.G₀.first (gpOf
            Z))))).ior.red.out a τ = some x →
      (∀ j, sampledAt (firstPar Bs.G₀.first (gpOf Z)) j →
        Sealed (firstPar Bs.G₀.first (gpOf Z)).codes
          (shapeAt (firstPar Bs.G₀.first (gpOf Z)) j) ((radRec 0 (firstPar Bs.G₀.first (gpOf Z)))
              j.val) (fOf x.2 j) x.1.st
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
      exact htie_at cs seats ms N Mg _ _ 2 (firstPar Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar
          Bs.G₀.first (gpOf Z)))
        (radRec 0 (firstPar Bs.G₀.first (gpOf Z))) _ d₁ d₂ (HP d₁ d₂ he hk hds).mems
        hsam hCond hNd hpl
        (openingZero Bs.G₀.first (gpOf Z) nm X0
          (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol : Block S Unit) rfl
        (fun s s' r₁ r₂ gs h => (openingZero_rec h).2.2.2.2.1) c' hu _ z)

set_option maxRecDepth 1000000 in
/-- "The book fits" is open in front of number 2 at the wider door. -/
theorem bookFits_open2 : K13.Law.bookFitsItem ∈ K13.Law.qAt9 2 := by
  decide +kernel

/-- So at the wider filling over the composed one over its closed base. -/
theorem bookFits_openG {Xi Pp Tok : Type} {rows cols nD nR : ℕ} {XV : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi Pp Tok rows cols nD XV)
    (D : K13.Law.DataK13 Pp (Wit (CellsQ rows cols) Tok MsgT) nR) (d : K12.Door.K12Data)
    (dk : First.Look.K3Data) :
    K13.Law.bookFitsItem ∈ (First.pubSets (K13.Law.plusG D d dk (mgAll 𝔇 mgBase)).more
      Sound.linksFull psF)[2]?.getD [] := by
  rw [K13.Law.plusG_more, K13.Law.plus13_moreW, mgAll_more_base]
  exact bookFits_open2

end VerifiableInference.Desc.K1
