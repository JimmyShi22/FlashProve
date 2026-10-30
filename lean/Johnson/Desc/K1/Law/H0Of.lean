-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/H0Of.lean, SECOND FORM: K01_law's OPEN PLACE H0 (number 2: the first chain's opening
sending, "G0:1") AS A CALL: the binder H0 of k01_law (Johnson/Desc/K1/Law/K01Law.lean),
TO THE LETTER: at the file's data dataOf aN R₁ R₂ R₃, at the table's own extractor extQAt, AT THE
ERROR BOUNDS THAT THE CUT ITSELF GIVES THE PIECE. One theorem: a joining: nothing is typed anew.

Why a second form: as in HWOf.lean. That the sub-protocol number 2 of the IOP as written in
Lean is under the wrappers of the law's is the premise hU: the statement of IM.first_under
(Johnson/IMR/FirstUnder.lean), sign for sign but for three names written short: hU :=
IM.first_under hS hR O is one line. In this file hU stays a premise.

OBJECT   the piece number 2 of the first chain, of the IOP as written in Lean, in scope.
USER     k01_law's binder H0.
FIELD    K01_law (ProofSound).

  H0_of   **the binder.** THE CALLS: letters_at_flat · tiedAt_of_seatTie · below_underR ·
          first_tied_seat (in its form with the letter mk) · tiedAt_err · sendErr_le_cap_port ·
          extQAt_two. LEFT: hU · hC · hWr · hCap (the cut's rest at 2 bears the cap) · hX (the
          public parameters give X) · hCond · h1 · hpow · hRow · hF (at every name nm: hU gives
          the name as "there is one") · hgroups · hown (first_tied_seat's own) · hNew: its two
          that name the piece, AT ALL d₁ d₂ with the seeds' tags, at every nm, every c' under the
          wrappers, every value z; fOf | fIn are given with them.
What is not claimed. NONE OF THESE PREMISES IS SHOWN HERE. Nothing on soundness.
Every premise and binder that names d₁ d₂ has an antecedent
behind the two tags: d₁ d₂ are the two rounds that the written data hold at the place. Why: asked
at every d₁ d₂ with the two tags a premise could not be met (planAt_all_false [not in this library]:
at a d₁ without a tree PlanAt's field tree is false): the laws above would be true and empty.

-/
import Johnson.Desc.K1.Law.HWOf
import Johnson.Desc.K13.Law.AtTableFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Flat KObj Iop Run
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More start flatPlacesOf)
open OnBytes.Params (Rounds)
open ProofFile (Cl)
open IM (Open)
open VerifiableInference.Desc.K13.Law (RowG FillG openAt first_tied_seat tiedAt_of_seatTie
  below_underR)
open Johnson.Desc.First.Walk (LayPar)

/-- **K01_law's binder H0, as a call.** -/
theorem H0_of {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {aN : ℕ} {R₁ R₂ R₃ : Rounds}
    {e₁ : List (List ByteArray × ByteArray)} {all : List LeftT} {X₁ X₂ Xi Cells Tok : Type}
    {T : ThreeAt (ckP .two) (dataOf aN R₁ R₂ R₃) all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Wit Cells Tok MsgT)}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) (hT : OfDesc _ T)
    (N : Numbers) (Mg : Meaning ProofFile.InstPub (Wit Cells Tok MsgT)) (cs : Codes)
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : ProofFile.InstPub × S → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × S → Option Cells)
    (c₀ : Cells) (tokOf : ProofFile.InstPub × S → Tok)
    {b₁ : Block (ProofFile.InstPub × S) Cl} {l₁ : List (Block (ProofFile.InstPub × S) Cl)}
    {rest₁ : (i : ℕ) → (ds : List RDT) →
      Sound.Rest (ckP .two) (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)
        (ProofFile.InstPub × S) (Wit Cells Tok MsgT) ds}
    {r : Fmt.RoundView} (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 (dataOf aN R₁ R₂ R₃).ds₁ b₁ l₁)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁)
    (hU : ∃ (e : Block S Cl) (nm : String) (X : LayPar), c.blocksInOrder[2]? = some e ∧
      Johnson.Desc.First.Walk.Seat.zeroAt Z.p.built.links Z.p.X = some X ∧
      e.UnderR (openingZero Bs.G₀.first (gpOf Z) nm X
        (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol : Block S Cl))
    (hCap : ∀ d₁ d₂ : RDT, (rest₁ 2 [d₁, d₂]).err = Err.cap 128 (uLT (ckP .two) [d₁, d₂]))
    (X : LayPar) (hX : Johnson.Desc.First.Walk.Seat.zeroAt Z.p.built.links Z.p.X = some X)
    (mk : List Pub) (rad : ℕ → ℕ) (hCond : condPort (firstPar Bs.G₀.first (gpOf Z)) rad = true)
    (h1 : (firstPar Bs.G₀.first (gpOf Z)).seeds = 1)
    (hpow : powB (firstPar Bs.G₀.first (gpOf Z)) rad 128 = true)
    (hRow : RowG N Mg.more Sound.linksFull psF 2 (layOf (firstPar Bs.G₀.first (gpOf Z))).shapes.size
      (firstPar Bs.G₀.first (gpOf Z)).sent.size mk)
    (hF : ∀ nm : String, FillG Cl Bs.G₀.first (gpOf Z) nm X
      (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol N Mg
      ((First.pubSets Mg.more Sound.linksFull psF)[2]?.getD []) psF[2]? mk)
    (hgroups : ∀ x, Mg.pub .noneSent x = true → N.groupAt 0 = x.2.st.groups.size)
    (hown : ∀ x, Mg.inOrder x = true → First.bookAt N psF[2]? x.2 = true →
      ownSeatsB N (openAt Sound.linksFull psF (2 + 1)) (firstPar Bs.G₀.first (gpOf Z))
        (x.2.check.frame.atMoment 0).length x.2.book.trees.size = true)
    (hNew : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (firstPar Bs.G₀.first (gpOf Z)) →
      d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 2)).take 2 = [d₁, d₂] →
      ∃ (fOf : (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str →
          ∀ j, (portOmZ (firstPar Bs.G₀.first (gpOf Z)).codes
            (shapeAt (firstPar Bs.G₀.first (gpOf Z)) j) (rad j.val)).Str)
        (fIn : (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str →
          (wT d₁).Msg →
          ∀ j, (portOmZ (firstPar Bs.G₀.first (gpOf Z)).codes
            (shapeAt (firstPar Bs.G₀.first (gpOf Z)) j) (rad j.val)).Str),
      ∀ (nm : String) (c' : Block S Cl), c'.UnderR (openingZero Bs.G₀.first (gpOf Z) nm X
        (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol) →
      (∀ y τ, fOf ((sendPiece (W := Wit Cells Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))) d₁ d₂
        (firstPar Bs.G₀.first (gpOf Z)).coordinates
        (errPort (firstPar Bs.G₀.first (gpOf Z)) rad)).ior.imp y τ) = fIn y τ.1) ∧
      ∀ (z : ProofFile.InstPub) a τ x,
      onQ N Mg Sound.linksFull psF (fun s : S => (z, s)) 2 a → a.1.failed = none →
      (sendPiece (W := Wit Cells Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 2))) d₁ d₂
        (firstPar Bs.G₀.first (gpOf Z)).coordinates
        (errPort (firstPar Bs.G₀.first (gpOf Z)) rad)).ior.red.out a τ = some x →
      (∀ j, sampledAt (firstPar Bs.G₀.first (gpOf Z)) j →
        Sealed (firstPar Bs.G₀.first (gpOf Z)).codes
          (shapeAt (firstPar Bs.G₀.first (gpOf Z)) j) (rad j.val) (fOf x.2 j) x.1.st
          (x.1.st.oracles.size - (shapesOf (firstPar Bs.G₀.first (gpOf Z))).length + j.val)) →
      ∀ t ∈ First.sampledIn N (openAt Sound.linksFull psF (2 + 1)),
        Mg.held t.1 t.2 (z, x.1) = true ∧
          Mg.shown t.1 t.2
            (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2) ∧
          Mg.noColl t.1 t.2 (z, x.1)
            (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2)) :
    ∀ q, (T.p₁ :: T.l₁)[2]? = some q →
      TiedAt N Mg Sound.linksFull (flatPlacesOf Sound.linksFull true) (fun a => a) 2
        (q.withMap ((fun k => extQAt cs G arr smp ms decT c₀ tokOf N Sound.linksFull
          (flatPlacesOf Sound.linksFull true) (fun a => a) k) 2)) := by
  intro q hq
  obtain ⟨e, nm, X', hflat, hX', hu⟩ := hU
  obtain rfl : X' = X := Option.some.inj (hX'.symm.trans hX)
  obtain ⟨d₁, d₂, he₁, hk₁, hds, hL⟩ :=
    letters_at_flat' hS hR O hT hC hWr 2 (by omega) e hflat (firstPar Bs.G₀.first (gpOf Z))
      (hu.1.trans (by first | rfl | (unfold openingZero; simp; done)))
  obtain ⟨fOf, fIn, hN⟩ := hNew d₁ d₂ he₁ hk₁ hds
  have hb := below_underR hu
  refine tiedAt_of_seatTie hT hflat hq Sound.linksFull _ N Mg _
    (fun x y w => extQAt_two cs G arr smp ms decT c₀ tokOf N (fun a => a) x y w) _ (hL q hq) ?_
  intro z
  refine tiedAt_err N Mg _ _ _ _ _ _ ?_
    (first_tied_seat N Mg _ _ z 2 Bs.G₀.first (gpOf Z) nm _ _ _ mk rad hCond _ hb _ d₁ d₂ he₁ hk₁ _
      (Nat.le_refl _) fOf fIn (hN nm _ hb).1 hRow (hF nm) hgroups hown ((hN nm _ hb).2 z))
  rw [hCap d₁ d₂]
  exact sendErr_le_cap_port (firstPar Bs.G₀.first (gpOf Z)) h1 rad hpow d₁ d₂ he₁ hk₁

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.H0_of
