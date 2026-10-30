-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/NewAtW9.lean: THE PAYER OF THE PREMISE hNew OF THE TIE AT W's COMMITMENT
(number 356), IN A FORM THAT CAN BE MET THERE. Statements with their proofs: calls. WHY.
`hNewW_paid` (Johnson/Desc/K1/Law/NewAtTwoPaid.lean) asks hsam: EVERY message of the place has an
OOD sample. W's sending has two messages, and by the kernel's word
(`w_own_sampled` [not in this library]) the second, the mask, HAS NONE: so at the release's own
list of rounds that
premise is false and the payer says nothing. What it calls (`htie_at`,
Johnson/Desc/K1/Law/HtieAt.lean) asks less. `hNewW_weak`: the same statement with hsam IN THAT
  WEAKER FORM: a message at whose seat a member of ms sits has an OOD sample. Made by program out
  of `hNewW_paid`'s own text: one binder and one argument turn. `bookFits_open9`,
  `bookFits_openW`: "the book fits" is open in front of number 356 at the wider door over the
  composed filling's closed door: by the kernel. So hopen falls at `plus13 D d (mgAll 𝔇 mgBase)`.
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

/-- **hNewW, with what its payers ask and no more.** -/
theorem hNewW_weak {Z : ProofFile.Pub} {c : Chain S Cl} {A : ProofFile.SharedSeat}
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
    (hsam : ∀ j : Fin (shapesOf (parWZ Z msgW)).length, ∀ m' ∈ ms,
      SitsAt m'
        (seatOfMsg (parWZ Z msgW) (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) j.val).1
        (seatOfMsg (parWZ Z msgW) (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) j.val).2
            →
      sampledAt (parWZ Z msgW) j)
    (hCond : condPort (parWZ Z msgW) radW = true) (hNd : seats.Nodup)
    (hpl : ∀ j : Fin (shapesOf (parWZ Z msgW)).length,
      seats[N.msgsAt psF[356]? + j.val]? =
        some (seatOfMsg (parWZ Z msgW) (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356)))
            j.val)) :
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
      exact htie_at cs seats ms N Mg _ _ 356 (parWZ Z msgW) radW radW _ d₁ d₂ (HP d₁ d₂ he hk
          hds).mems
        hsam hCond hNd hpl
        (atM4 (whereOf Z) (sendAtS (parWZ Z msgW)) : Block S Unit) rfl
        (fun s s' r₁ r₂ gs h => atM4_booked h) c' hu _ z)

set_option maxRecDepth 1000000 in
/-- "The book fits" is open in front of number 356 at the wider door. -/
theorem bookFits_open9 : K13.Law.bookFitsItem ∈ K13.Law.qAt9 356 := by
  decide +kernel

/-- So at the wider filling over the composed one over its closed base. -/
theorem bookFits_openW {Xi Pp Tok : Type} {rows cols nD nR : ℕ} {XV : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi Pp Tok rows cols nD XV)
    (D : K13.Law.DataK13 Pp (Wit (CellsQ rows cols) Tok MsgT) nR) (d : K12.Door.K12Data) :
    K13.Law.bookFitsItem ∈ (First.pubSets (K13.Law.plus13 D d (mgAll 𝔇 mgBase)).more
      Sound.linksFull psF)[356]?.getD [] := by
  rw [K13.Law.plus13_moreW, mgAll_more_base]
  exact bookFits_open9

end VerifiableInference.Desc.K1
