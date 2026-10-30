-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/NewAtTwo.lean: K01_law's THREE BINDERS ON
THE NEW TENANTS AT THE KIND's TWO OTHER PLACES: hNew0 (number 2: the first chain's opening
sending) · hNewW · hshownW (number 356: W's sending), TO THE LETTER of k01_law_whole's head
(K01LawWhole.lean), AS CALLS. Six theorems: three at letters for the numbers and the
meaning, three at the wider meaning over the composed one.

How. The binders have "there are fOf, fIn" IN FRONT OF "for every sub-protocol c' under the law's"
(and every name, every value of the public part). new_of (NewAtSending.lean) has them
behind: its "there are" cannot be carried over the "for every". But its two witnesses hang on
neither: fOfAt G P rad base and fInAt … d₁. So they are given outright, and new_of's OWN THREE
BRICKS are called: hf_at · sealed_at_new · shown_at_new. Nothing is typed anew.

PAID HERE, beyond new_of's own form: "the sub-protocol's accept books the place's messages"
(Booked): at W's sending by atM4_booked (Johnson/Desc/K13/Law/AtRecord.lean), at the opening by
openingZero_rec (Johnson/Desc/K1/Law/OpeningZero.lean); "it declares two rounds": by rfl; the
promise's clause on the book: onQ_book.

OBJECT   the pieces number 2 and 356 of the first chain.
USER     k01_law_whole's binders hNew0 · hNewW · hshownW; HW_of | H0_of's hNew | hshown.
FIELD    K01_law (ProofSound).

  hNewW_of · hshownW_of · hNew0_of    at letters N, Mg with the three equations of fields (held ·
                                      shown · noColl are the fillings by signature).
  hNewW_at9 · hshownW_at9 · hNew0_at9 **at N := Dm.N and Mg := plus13 (d13 Dm) dk (mgAll Dm
                                      Mg₀)**, general in Dm, dk, Mg₀: the three equations by rfl.
LEFT, BY NAME, AT EACH PLACE: HP (PlanAt: ten tests on the public parameters, at all d₁ d₂ with
the seeds' tags) · hbase (the piece's base is the table's number of trees in front) · hholds
(BookHolds of the book in front: every place of the book names a tree that the book holds) · htie
(SmpTie at the members at the new seats: on the reader smp). hshownW_of asks HP alone.
What is not claimed. That PlanAt has a member at either place; that hholds or htie can be met.
Nothing on soundness.
Every premise and binder that names d₁ d₂ has an antecedent
behind the two tags: d₁ d₂ are the two rounds that the written data hold at the place. Why: asked
at every d₁ d₂ with the two tags a premise could not be met (planAt_all_false [not in this library]:
at a d₁ without a tree PlanAt's field tree is false): the laws above would be true and empty.

-/
import Johnson.Desc.K1.Law.H0Of
import Johnson.Desc.K1.Law.NewAtSending
import Johnson.Desc.K1.Law.FillsAtPlus13
import Johnson.Desc.K1.Law.OpeningZero
import Johnson.Desc.K13.Law.AtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model Johnson.G Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat KObj OnBytes.Slice
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Sound (CellsQ MgData mgAll d13)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More start flatPlacesOf)
open VerifiableInference.Desc.K13 (whereOf atM4)
open VerifiableInference.Desc.K13.Law (openAt wSitsItem wSitsB atM4_booked plus13)
open VerifiableInference.Desc.K12.Door (K12Data)
open OnBytes.Params (Rounds)
open Johnson.Desc.First.Walk (LayPar)
open ProofFile (Cl)

/-- **hNewW, as a call.** -/
theorem hNewW_of {Z : ProofFile.Pub} {c : Chain S Cl} {A : ProofFile.SharedSeat}
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
    (hholds : ∀ (z : ProofFile.InstPub)
      (a : S × (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str),
      onQ N Mg Sound.linksFull psF (fun s : S => (z, s)) 356 a → a.1.failed = none →
      BookHolds a.1.book)
    (htie : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Z msgW) → d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 356)).take 2 = [d₁, d₂] →
      ∀ c' : Block S Cl, c'.UnderR (atM4 (whereOf Z) (sendAtS (parWZ Z msgW))) →
      ∀ (z : ProofFile.InstPub) a τ x,
      onQ N Mg Sound.linksFull psF (fun s : S => (z, s)) 356 a → a.1.failed = none →
      (sendPiece (W := (Wit (CellsQ rows cols) Tok MsgT))
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ (parWZ Z msgW).coordinates
        (errPort (parWZ Z msgW) radW)).ior.red.out a τ = some x →
      ∀ j : Fin (shapesOf (parWZ Z msgW)).length, ∀ m ∈ ms,
        SitsAt m (seatOfMsg (parWZ Z msgW) (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) j.val).1
          (seatOfMsg (parWZ Z msgW) (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) j.val).2 →
        SmpTie cs smp (z, x.1) m x.1.st
          (x.1.st.oracles.size - (shapesOf (parWZ Z msgW)).length + j.val)) :
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
          (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2) := by
  intro d₁ d₂ he hk hds
  have H := HP d₁ d₂ he hk hds
  refine ⟨fOfAt G (parWZ Z msgW) radW _, fun _ m => fInAt _ G (parWZ Z msgW) radW _ d₁ m, fun c' hu =>
    ⟨fun y τ => hf_at G _ radW c' _ d₁ d₂ _ _ H.tree y τ, ?_⟩⟩
  intro z a τ x ha hm hx hS _
  obtain ⟨b1, b2⟩ := onQ_book N Mg _ _ 356 z a ha hm
  rw [hheld, hnoColl]
  exact sealed_at_new H smp c' (by rw [hu.1]; rfl)
    (fun s s' r₁ r₂ gs h => atM4_booked (hu.2 _ _ _ _ h)) _ z a τ x hx b1 (b2.trans hbase)
    (hholds z a ha hm) (htie d₁ d₂ he hk hds c' hu z a τ x ha hm hx) hS N.w (List.mem_singleton.2 rfl)

/-- **hshownW, as a call.** -/
theorem hshownW_of {Z : ProofFile.Pub} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} {aN : ℕ} {R₁ R₂ R₃ : Rounds} {all : List LeftT} {X₁ X₂ Xi Tok : Type}
    {rows cols : ℕ}
    {T : ThreeAt (ckP .two) (dataOf aN R₁ R₂ R₃) all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Wit (CellsQ rows cols) Tok MsgT)}
    (cs : Codes) (G : FileDescription Xi)
    (smp : ProofFile.InstPub × S → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (N : Numbers) (Mg : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))
    (hshown : Mg.shown = shownJT cs G ms)
    (msgW : Array OracleNotice) (radW : ℕ → ℕ)
    (HP : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Z msgW) → d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 356)).take 2 = [d₁, d₂] →
      PlanAt (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) cs G ms
        (parWZ Z msgW) radW (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ [N.w]) :
    ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Z msgW) → d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 356)).take 2 = [d₁, d₂] →
      ∀ c' : Block S Cl, c'.UnderR (atM4 (whereOf Z) (sendAtS (parWZ Z msgW))) →
      ∀ (z : ProofFile.InstPub) a τ x,
      onQ N Mg Sound.linksFull psF (fun s : S => (z, s)) 356 a → a.1.failed = none →
      (sendPiece (W := Wit (CellsQ rows cols) Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ (parWZ Z msgW).coordinates
        (errPort (parWZ Z msgW) radW)).ior.red.out a τ = some x →
      Mg.shown N.w.1 N.w.2
        (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2) := by
  intro d₁ d₂ he hk hds c' _ z a τ x _ _ hx
  rw [hshown]
  exact shown_at_new (HP d₁ d₂ he hk hds) c' _ a τ x hx N.w (List.mem_singleton.2 rfl)

/-- **hNew0, as a call.** -/
theorem hNew0_of {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {c : Chain S Cl} {A : ProofFile.SharedSeat}
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
    (hholds : ∀ (z : ProofFile.InstPub)
      (a : S × (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str),
      onQ N Mg Sound.linksFull psF (fun s : S => (z, s)) 2 a → a.1.failed = none →
      BookHolds a.1.book)
    (htie : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (firstPar Bs.G₀.first (gpOf Z)) →
      d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 2)).take 2 = [d₁, d₂] →
      ∀ (nm : String) (c' : Block S Cl), c'.UnderR (openingZero Bs.G₀.first (gpOf Z) nm X0
        (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol) →
      ∀ (z : ProofFile.InstPub) a τ x,
      onQ N Mg Sound.linksFull psF (fun s : S => (z, s)) 2 a → a.1.failed = none →
      (sendPiece (W := (Wit (CellsQ rows cols) Tok MsgT))
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))) d₁ d₂
        (firstPar Bs.G₀.first (gpOf Z)).coordinates
        (errPort (firstPar Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar Bs.G₀.first (gpOf Z))))).ior.red.out a τ = some x →
      ∀ j : Fin (shapesOf (firstPar Bs.G₀.first (gpOf Z))).length, ∀ m ∈ ms,
        SitsAt m (seatOfMsg (firstPar Bs.G₀.first (gpOf Z)) (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))) j.val).1
          (seatOfMsg (firstPar Bs.G₀.first (gpOf Z)) (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))) j.val).2 →
        SmpTie cs smp (z, x.1) m x.1.st
          (x.1.st.oracles.size - (shapesOf (firstPar Bs.G₀.first (gpOf Z))).length + j.val)) :
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
            (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2) := by
  intro d₁ d₂ he hk hds
  have H := HP d₁ d₂ he hk hds
  refine ⟨fOfAt G (firstPar Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar Bs.G₀.first (gpOf Z))) _,
    fun _ m => fInAt _ G (firstPar Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar Bs.G₀.first (gpOf Z))) _ d₁ m,
    fun nm c' hu => ⟨fun y τ => hf_at G _ _ c' _ d₁ d₂ _ _ H.tree y τ, ?_⟩⟩
  intro z a τ x ha hm hx hS t ht
  obtain ⟨b1, b2⟩ := onQ_book N Mg _ _ 2 z a ha hm
  have h1 := sealed_at_new H smp c' (by rw [hu.1]; rfl)
    (fun s s' r₁ r₂ gs h => (openingZero_rec (hu.2 _ _ _ _ h)).2.2.2.2.1) _ z a τ x hx b1
    (b2.trans hbase) (hholds z a ha hm) (htie d₁ d₂ he hk hds nm c' hu z a τ x ha hm hx) hS t ht
  have h2 := shown_at_new H c' _ a τ x hx t ht
  rw [hheld, hshown, hnoColl]
  exact ⟨h1.1, h2, h1.2⟩

/-- **hNewW at the wider meaning over the composed one.** -/
theorem hNewW_at9 {Z : ProofFile.Pub} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} {aN : ℕ} {R₁ R₂ R₃ : Rounds} {all : List LeftT} {X₁ X₂ Xi Tok : Type}
    {rows cols : ℕ}
    {T : ThreeAt (ckP .two) (dataOf aN R₁ R₂ R₃) all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Wit (CellsQ rows cols) Tok MsgT)}
    {nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X) (dk : K12Data)
    (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))
    (msgW : Array OracleNotice) (radW : ℕ → ℕ)
    (HP : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Z msgW) → d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 356)).take 2 = [d₁, d₂] →
      PlanAt (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) Dm.cs Dm.G Dm.ms
        (parWZ Z msgW) radW (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ [Dm.N.w])
    (hbase : Dm.N.treesAt psF[356]? = (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))))
    (hholds : ∀ (z : ProofFile.InstPub)
      (a : S × (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str),
      onQ Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) Sound.linksFull psF (fun s : S => (z, s)) 356 a → a.1.failed = none →
      BookHolds a.1.book)
    (htie : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Z msgW) → d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 356)).take 2 = [d₁, d₂] →
      ∀ c' : Block S Cl, c'.UnderR (atM4 (whereOf Z) (sendAtS (parWZ Z msgW))) →
      ∀ (z : ProofFile.InstPub) a τ x,
      onQ Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) Sound.linksFull psF (fun s : S => (z, s)) 356 a → a.1.failed = none →
      (sendPiece (W := (Wit (CellsQ rows cols) Tok MsgT))
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ (parWZ Z msgW).coordinates
        (errPort (parWZ Z msgW) radW)).ior.red.out a τ = some x →
      ∀ j : Fin (shapesOf (parWZ Z msgW)).length, ∀ m ∈ Dm.ms,
        SitsAt m (seatOfMsg (parWZ Z msgW) (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) j.val).1
          (seatOfMsg (parWZ Z msgW) (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) j.val).2 →
        SmpTie Dm.cs Dm.smp (z, x.1) m x.1.st
          (x.1.st.oracles.size - (shapesOf (parWZ Z msgW)).length + j.val)) :
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
      onQ Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) Sound.linksFull psF (fun s : S => (z, s)) 356 a → a.1.failed = none →
      (sendPiece (W := Wit (CellsQ rows cols) Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ (parWZ Z msgW).coordinates
        (errPort (parWZ Z msgW) radW)).ior.red.out a τ = some x →
      (∀ j, sampledAt (parWZ Z msgW) j →
        Sealed (parWZ Z msgW).codes (shapeAt (parWZ Z msgW) j) (radW j.val) (fOf x.2 j) x.1.st
          (x.1.st.oracles.size - (shapesOf (parWZ Z msgW)).length + j.val)) →
      (wSitsItem ∈ (First.pubSets (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more Sound.linksFull psF)[356 + 1]?.getD [] →
        wSitsB (parWZ Z msgW).codes (whereOf Z) x.1 = true ∧
          x.1.book.place[x.1.st.oracles.size - (shapesOf (parWZ Z msgW)).length]? = some Dm.N.w) →
      (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).held Dm.N.w.1 Dm.N.w.2 (z, x.1) = true ∧
        (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).noColl Dm.N.w.1 Dm.N.w.2 (z, x.1)
          (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2) :=
  hNewW_of Dm.cs Dm.G Dm.smp Dm.ms Dm.N _ rfl rfl rfl msgW radW HP hbase hholds htie

/-- **hshownW there.** -/
theorem hshownW_at9 {Z : ProofFile.Pub} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} {aN : ℕ} {R₁ R₂ R₃ : Rounds} {all : List LeftT} {X₁ X₂ Xi Tok : Type}
    {rows cols : ℕ}
    {T : ThreeAt (ckP .two) (dataOf aN R₁ R₂ R₃) all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Wit (CellsQ rows cols) Tok MsgT)}
    {nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X) (dk : K12Data)
    (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))
    (msgW : Array OracleNotice) (radW : ℕ → ℕ)
    (HP : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Z msgW) → d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 356)).take 2 = [d₁, d₂] →
      PlanAt (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) Dm.cs Dm.G Dm.ms
        (parWZ Z msgW) radW (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ [Dm.N.w]) :
    ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Z msgW) → d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 356)).take 2 = [d₁, d₂] →
      ∀ c' : Block S Cl, c'.UnderR (atM4 (whereOf Z) (sendAtS (parWZ Z msgW))) →
      ∀ (z : ProofFile.InstPub) a τ x,
      onQ Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) Sound.linksFull psF (fun s : S => (z, s)) 356 a → a.1.failed = none →
      (sendPiece (W := Wit (CellsQ rows cols) Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ (parWZ Z msgW).coordinates
        (errPort (parWZ Z msgW) radW)).ior.red.out a τ = some x →
      (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).shown Dm.N.w.1 Dm.N.w.2
        (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2) :=
  hshownW_of Dm.cs Dm.G Dm.smp Dm.ms Dm.N _ rfl msgW radW HP

/-- **hNew0 there.** -/
theorem hNew0_at9 {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} {aN : ℕ} {R₁ R₂ R₃ : Rounds} {all : List LeftT} {X₁ X₂ Xi Tok : Type}
    {rows cols : ℕ}
    {T : ThreeAt (ckP .two) (dataOf aN R₁ R₂ R₃) all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Wit (CellsQ rows cols) Tok MsgT)}
    {nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X) (dk : K12Data)
    (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))
    (X0 : LayPar)
    (HP : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (firstPar Bs.G₀.first (gpOf Z)) →
      d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 2)).take 2 = [d₁, d₂] →
      PlanAt (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) Dm.cs Dm.G Dm.ms
        (firstPar Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar Bs.G₀.first (gpOf Z)))
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))) d₁ d₂
        (First.sampledIn Dm.N (openAt Sound.linksFull psF (2 + 1))))
    (hbase : Dm.N.treesAt psF[2]? = (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))))
    (hholds : ∀ (z : ProofFile.InstPub)
      (a : S × (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str),
      onQ Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) Sound.linksFull psF (fun s : S => (z, s)) 2 a → a.1.failed = none →
      BookHolds a.1.book)
    (htie : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (firstPar Bs.G₀.first (gpOf Z)) →
      d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 2)).take 2 = [d₁, d₂] →
      ∀ (nm : String) (c' : Block S Cl), c'.UnderR (openingZero Bs.G₀.first (gpOf Z) nm X0
        (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol) →
      ∀ (z : ProofFile.InstPub) a τ x,
      onQ Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) Sound.linksFull psF (fun s : S => (z, s)) 2 a → a.1.failed = none →
      (sendPiece (W := (Wit (CellsQ rows cols) Tok MsgT))
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))) d₁ d₂
        (firstPar Bs.G₀.first (gpOf Z)).coordinates
        (errPort (firstPar Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar Bs.G₀.first (gpOf Z))))).ior.red.out a τ = some x →
      ∀ j : Fin (shapesOf (firstPar Bs.G₀.first (gpOf Z))).length, ∀ m ∈ Dm.ms,
        SitsAt m (seatOfMsg (firstPar Bs.G₀.first (gpOf Z)) (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))) j.val).1
          (seatOfMsg (firstPar Bs.G₀.first (gpOf Z)) (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))) j.val).2 →
        SmpTie Dm.cs Dm.smp (z, x.1) m x.1.st
          (x.1.st.oracles.size - (shapesOf (firstPar Bs.G₀.first (gpOf Z))).length + j.val)) :
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
      onQ Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) Sound.linksFull psF (fun s : S => (z, s)) 2 a → a.1.failed = none →
      (sendPiece (W := Wit (CellsQ rows cols) Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))) d₁ d₂
        (firstPar Bs.G₀.first (gpOf Z)).coordinates
        (errPort (firstPar Bs.G₀.first (gpOf Z)) (radRec 0 (firstPar Bs.G₀.first (gpOf Z))))).ior.red.out a τ = some x →
      (∀ j, sampledAt (firstPar Bs.G₀.first (gpOf Z)) j →
        Sealed (firstPar Bs.G₀.first (gpOf Z)).codes
          (shapeAt (firstPar Bs.G₀.first (gpOf Z)) j) ((radRec 0 (firstPar Bs.G₀.first (gpOf Z))) j.val) (fOf x.2 j) x.1.st
          (x.1.st.oracles.size - (shapesOf (firstPar Bs.G₀.first (gpOf Z))).length + j.val)) →
      ∀ t ∈ First.sampledIn Dm.N (openAt Sound.linksFull psF (2 + 1)),
        (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).held t.1 t.2 (z, x.1) = true ∧
          (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).shown t.1 t.2
            (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2) ∧
          (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).noColl t.1 t.2 (z, x.1)
            (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2) :=
  hNew0_of Dm.cs Dm.G Dm.smp Dm.ms Dm.N _ rfl rfl rfl X0 HP hbase hholds htie

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hNewW_of
#print axioms VerifiableInference.Desc.K1.hshownW_of
#print axioms VerifiableInference.Desc.K1.hNew0_of
#print axioms VerifiableInference.Desc.K1.hNewW_at9
#print axioms VerifiableInference.Desc.K1.hshownW_at9
#print axioms VerifiableInference.Desc.K1.hNew0_at9
