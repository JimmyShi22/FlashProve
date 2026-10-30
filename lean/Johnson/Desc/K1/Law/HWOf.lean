-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/HWOf.lean, SECOND FORM: K01_law's OPEN PLACE HW (number 356: W's sending, "M:4") AS A CALL:
the binder HW of k01_law (Johnson/Desc/K1/Law/K01Law.lean), TO THE LETTER: at the
file's data dataOf aN R₁ R₂ R₃, at the table's own extractor extQAt, AT THE ERROR BOUNDS THAT THE
CUT ITSELF GIVES THE PIECE. One abbreviation beside the first form's, one theorem: a joining:
nothing is typed anew.

Why a second form. The first asked HasSendLetters: an equation of the piece's error bounds to the
kind's own: false where the cut's rests bear the cap 2^-128; and it had the extractor's map as a
letter E with "E is the identity". Here, as at the kind's fifty later places: the piece's letters
come out of the cut (letters_at_flat, LettersAtFifty.lean); the tie goes up in the error
bounds (tiedAt_err) from the kind's own to the cap (sendErr_le_cap_port, SendErrCap.lean);
the map is extQAt, which is the identity at this place (extQAt_w, CallsE2.lean: the table's
row lays nothing there: by the kernel).

OBJECT   the piece number 356 of the first chain, of the IOP as written in Lean, in scope.
USER     k01_law's binder HW.
FIELD    K01_law (ProofSound).

  HW_of   **the binder.** THE CALLS: k13_sits_flat · letters_at_flat · tiedAt_of_seatTie ·
          below_underR · w_tied_seat · tiedAt_err · sendErr_le_cap_port · extQAt_w. LEFT: hC · hWr
          (the framework's two, shared by every kind) · hCap (the cut's rest at 356 bears the cap)
          · hm (the public parameters have W's message) · hCond · h1 · hpow (three tests on the
          sending's parameters) · hRow · hF · hPl · hbase (w_tied_seat's own) · hNew · hshown:
          w_tied_seat's three that name the piece, AT ALL d₁ d₂ with the seeds' tags, at every
          sub-protocol c' under the wrappers of the law's, at every value z of the public part;
          fOf | fIn are given with them ("there are").
What is not claimed. NONE OF THESE PREMISES IS SHOWN HERE. Nothing on soundness.
Every premise and binder that names d₁ d₂ has an antecedent
behind the two tags: d₁ d₂ are the two rounds that the written data hold at the place. Why: asked
at every d₁ d₂ with the two tags a premise could not be met (planAt_all_false [not in this library]:
at a d₁ without a tree PlanAt's field tree is false): the laws above would be true and empty.

-/
import Johnson.Desc.K1.Law.LettersAtFifty
import Johnson.Desc.K1.Law.CallsE2
import Johnson.Desc.K1.Law.SendErrCap
import Johnson.Desc.K13.Law.AtTableW
import Johnson.Desc.Sound.MsgSig

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
open VerifiableInference.Desc.K13 (whereOf atM4)
open VerifiableInference.Desc.K13.Law (RowM4 FillM4 wSitsItem wSitsB planSitsB planSeatB
  w_tied_seat tiedAt_of_seatTie below_underR k13_sits_flat)

/-- The sending's parameters at "M:4", as the IOP as written in Lean lays them. -/
abbrev parWZ (Z : ProofFile.Pub) (msg : Array OracleNotice) : Par :=
  parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg

/-- The first chain's written places at the full size: Sound.linksFull's places (flatPlacesOf). -/
abbrev psF : List Place := flatPlacesOf Sound.linksFull true

/-- **K01_law's binder HW, as a call.** -/
theorem HW_of {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
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
    (hCap : ∀ d₁ d₂ : RDT, (rest₁ 356 [d₁, d₂]).err = Err.cap 128 (uLT (ckP .two) [d₁, d₂]))
    (msg : Array OracleNotice) (hm : linMessageW Z.first.lin = some msg) (rad : ℕ → ℕ)
    (hCond : condPort (parWZ Z msg) rad = true) (h1 : (parWZ Z msg).seeds = 1)
    (hpow : powB (parWZ Z msg) rad 128 = true)
    (hRow : RowM4 N Mg.more Sound.linksFull psF 356 (layOf (parWZ Z msg)).shapes.size
      (parWZ Z msg).sent.size)
    (hF : FillM4 Cl (whereOf Z) (parWZ Z msg) N Mg
      ((First.pubSets Mg.more Sound.linksFull psF)[356]?.getD []) psF[356]?)
    (hPl : wSitsItem ∈ (First.pubSets Mg.more Sound.linksFull psF)[356 + 1]?.getD [] →
      planSitsB (whereOf Z) (parWZ Z msg) = true ∧ planSeatB N psF[356]? (parWZ Z msg) = true)
    (hbase : N.index.1 < nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356)))
    (hNew : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Z msg) → d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 356)).take 2 = [d₁, d₂] →
      ∃ (fOf : (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str →
          ∀ j, (portOmZ (parWZ Z msg).codes (shapeAt (parWZ Z msg) j) (rad j.val)).Str)
        (fIn : (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁).E.Str →
          (wT d₁).Msg →
          ∀ j, (portOmZ (parWZ Z msg).codes (shapeAt (parWZ Z msg) j) (rad j.val)).Str),
      ∀ c' : Block S Cl, c'.UnderR (atM4 (whereOf Z) (sendAtS (parWZ Z msg))) →
      (∀ y τ, fOf ((sendPiece (W := Wit Cells Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ (parWZ Z msg).coordinates
        (errPort (parWZ Z msg) rad)).ior.imp y τ) = fIn y τ.1) ∧
      ∀ (z : ProofFile.InstPub) a τ x,
      onQ N Mg Sound.linksFull psF (fun s : S => (z, s)) 356 a → a.1.failed = none →
      (sendPiece (W := Wit Cells Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ (parWZ Z msg).coordinates
        (errPort (parWZ Z msg) rad)).ior.red.out a τ = some x →
      (∀ j, sampledAt (parWZ Z msg) j →
        Sealed (parWZ Z msg).codes (shapeAt (parWZ Z msg) j) (rad j.val) (fOf x.2 j) x.1.st
          (x.1.st.oracles.size - (shapesOf (parWZ Z msg)).length + j.val)) →
      (wSitsItem ∈ (First.pubSets Mg.more Sound.linksFull psF)[356 + 1]?.getD [] →
        wSitsB (parWZ Z msg).codes (whereOf Z) x.1 = true ∧
          x.1.book.place[x.1.st.oracles.size - (shapesOf (parWZ Z msg)).length]? = some N.w) →
      Mg.held N.w.1 N.w.2 (z, x.1) = true ∧
        Mg.noColl N.w.1 N.w.2 (z, x.1)
          (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2))
    (hshown : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Z msg) → d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c 356)).take 2 = [d₁, d₂] →
      ∀ c' : Block S Cl, c'.UnderR (atM4 (whereOf Z) (sendAtS (parWZ Z msg))) →
      ∀ (z : ProofFile.InstPub) a τ x,
      onQ N Mg Sound.linksFull psF (fun s : S => (z, s)) 356 a → a.1.failed = none →
      (sendPiece (W := Wit Cells Tok MsgT)
        (F := (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁)) c'
        (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c 356))) d₁ d₂ (parWZ Z msg).coordinates
        (errPort (parWZ Z msg) rad)).ior.red.out a τ = some x →
      Mg.shown N.w.1 N.w.2
        (strsOf (Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁) x.2)) :
    ∀ q, (T.p₁ :: T.l₁)[356]? = some q →
      TiedAt N Mg Sound.linksFull (flatPlacesOf Sound.linksFull true) (fun a => a) 356
        (q.withMap ((fun k => extQAt cs G arr smp ms decT c₀ tokOf N Sound.linksFull
          (flatPlacesOf Sound.linksFull true) (fun a => a) k) 356)) := by
  intro q hq
  obtain ⟨_, e, msg', hflat, _, hm', hu⟩ := k13_sits_flat hS hR O
  obtain rfl : msg' = msg := Option.some.inj (hm'.symm.trans hm)
  obtain ⟨d₁, d₂, he₁, hk₁, hds, hL⟩ :=
    letters_at_flat' hS hR O hT hC hWr 356 (by omega) e hflat (parWZ Z msg') hu.1
  obtain ⟨fOf, fIn, hN⟩ := hNew d₁ d₂ he₁ hk₁ hds
  have hb := below_underR hu
  refine tiedAt_of_seatTie hT hflat hq Sound.linksFull _ N Mg _
    (fun x y w => extQAt_w cs G arr smp ms decT c₀ tokOf N (fun a => a) x y w) _ (hL q hq) ?_
  intro z
  refine tiedAt_err N Mg _ _ _ _ _ _ ?_
    (w_tied_seat N Mg _ _ z 356 (whereOf Z) _ rad hCond _ hb _ d₁ d₂ he₁ hk₁ _ (Nat.le_refl _) fOf
      fIn (hN _ hb).1 hRow hF hPl hbase ((hN _ hb).2 z) (hshown d₁ d₂ he₁ hk₁ hds _ hb z))
  rw [hCap d₁ d₂]
  exact sendErr_le_cap_port (parWZ Z msg') h1 rad hpow d₁ d₂ he₁ hk₁

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.HW_of
