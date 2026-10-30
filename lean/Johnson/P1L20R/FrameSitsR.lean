-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FrameSitsR.lean:
the ties of the link's frame's 51 sub-protocols (the chain's front, 25 "laid", 25 "cleared") IN THE
FORM WITH A CONDITION Rch BESIDE THE PROMISE (TiedAtR, Johnson/Desc/Sound/ChainOfPromisesR.lean).

Why. FrameSits.lean ends in the first form of a tie, which is asked at every statement that meets
the table's promise. At the frame's borders that promise says little of the verifier's state (of its
book of trees: three sizes). A sentence that reads the strings through the state's own book, as the
one on the carried word does, cannot be shown to go back under that promise alone: it needs a fact
that holds at every reached state. The second form hands Rch k to each tie.

  In            a family of letters: In k a y: WHAT IS KNOWN IN FRONT of sub-protocol number k of a
                statement a that bears no mark, with strings y
  ClearOwesR, FrameOwesR   ClearOwes and FrameOwes (FrameSits.lean) with In k for the promise
  front_tiedR, laid_tiedR, cleared_tiedR   the three sorts of tie, from these
  frame_tiedR_ours   at every place of the kind "frame" of the written list: TiedAtR, from
                FrameOwesR, "the promise in front and Rch k give In k where no mark is borne", and
                the two shares of other files (the 25 behind the batching; the seal) in that form

Limits. A form with its debts counted: no field of FrameOwesR is shown at a filling, and GivesIn at
no Rch: it is where every fact on reached states is spent. Where In k never holds FrameOwesR's
fields on LettersRide hold trivially and the debt moves whole to GivesIn. ClearOwesR's "Hold goes
back" and PileGivesWo (FrameTied.lean) are asked at marked statements too. That Rch is handed on by
the 51 steps is not said here (Johnson/Top/H0/Walk/ReachHands.lean). FrameSits.lean's own ends
(FrameOwes, frame_kindTied_ours) stay true, but at a sentence on the carried word that reads the
strings through the state's book FrameOwes cannot be met: call this file's. No soundness statement.

-/
import Johnson.P1L20R.FrameSits

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start openSets pubSets flatPlacesOf)
open Johnson.Desc.First.Walk (layFront clearWith LinkPub)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {C : CK} {D : WholeD} {all : List LeftT}
  {X₁ X₂ W : Type}
  {T : ThreeAt C D all
    (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
    X₁ X₂ W}

/-- LettersRide at sub-protocol number k of the written list, at what is known in front. -/
abbrev RideAt (N : Numbers) (Mg : Meaning ProofFile.InstPub W) (f : S → Except String S) (base k : ℕ)
    (In : ProofFile.InstPub × S → Strs → Prop) : Prop :=
  LettersRide N Mg (Yes f) base In
    ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[k + 1]?.getD [])
    ((pubSets Mg.more linksFull (flatPlacesOf linksFull true))[k + 1]?.getD [])
    (openAfter (insQ linksFull (flatPlacesOf linksFull true))
      (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ start linksFull) (k + 1))

/-- **What "link l: cleared" owes**, with In for the promise in front. -/
def ClearOwesR (N : Numbers) (Mg : Meaning ProofFile.InstPub W) (Z : ProofFile.Pub)
    (f : Johnson.Desc.First.Walk.Seat.LinkFrame) (l base : ℕ)
    (Hold : ProofFile.InstPub × S → W → OnBytes.TensorRow → Prop)
    (In : ProofFile.InstPub × S → Strs → Prop) : Prop :=
  RideAt N Mg f.clear base (clearIx l) In ∧
  ∀ X', Z.p.built.links[l]? = some X' → X'.fv = true →
    (∀ a y w, (∀ r, Johnson.Desc.First.Walk.Law.rowAt Z.p.X.layers.wsLay X'.NCL Z.first.lin
      a.2 = some r → Hold a w r) → Mg.wo l a y w) ∧
    ∀ p s t y w r, f.clear s = .ok t → In (p, s) y → Hold (p, t) w r → Hold (p, s) w r

/-- What the promise in front and Rch k give, where no mark is borne. -/
abbrev GivesIn (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (Rch : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → Prop)
    (In : ℕ → ProofFile.InstPub × S → Strs → Prop) (k : ℕ) : Prop :=
  ∀ a, onQ N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) k a → Rch k a →
    a.1.2.failed = none → In k (a.1.1, a.1.2) (strsOf (frameAt D all D.key₁ T.ft₁) a.2)

variable {Rch : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → Prop}
  {In : ℕ → ProofFile.InstPub × S → Strs → Prop}

/-- **The front.** -/
theorem front_tiedR (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hT : OfDesc _ T) {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W}
    (hq : (T.p₁ :: T.l₁)[0]? = some q) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E a b w = w) (hn : NoneBetween N (flatPlacesOf linksFull true) 0)
    (hL : RideAt N Mg .ok q.base 0 (In 0)) (hI : GivesIn (T := T) N Mg Rch In 0) :
    TiedAtR N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) Rch 0 (q.withMap E) := by
  obtain ⟨b, h0, -, -, -, -, hy⟩ := IM.front_of O
  exact tied_of_ridesR (step_front front_places_full.1 front_places_full.2 hn
    (sits_lift q b (OfDesc.pieceAt hT hq h0) E .ok fun s rs gs t h => by
      rw [(hy s rs gs t).1 h])
    (laysNothing_withMap q E hE) hL) hI

/-- **"link l: laid".** -/
theorem laid_tiedR (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hT : OfDesc _ T) (l : ℕ)
    (hl : l < 25) {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W}
    (hq : (T.p₁ :: T.l₁)[14 * l + 1]? = some q) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E a b w = w) (hn : NoneBetween N (flatPlacesOf linksFull true) (14 * l + 1))
    (hL : RideAt N Mg (layFront l) q.base (14 * l + 1) (In (14 * l + 1)))
    (hI : GivesIn (T := T) N Mg Rch In (14 * l + 1)) :
    TiedAtR N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) Rch (14 * l + 1)
      (q.withMap E) := by
  obtain ⟨h1, ⟨p', h2, h3, h4⟩, -⟩ := places_full hl
  obtain ⟨-, fs, -, h⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, f, bL, -, -, -, -, -, -, hlay, yL, -, iL, -, dL, -⟩ := h l hl
  rw [hlay] at yL
  exact tied_of_ridesR (step_laid h1 h2 h3 h4 hn
    (sits_lift q bL (OfDesc.pieceAt hT hq iL) E (layFront l) fun s rs gs t e => by
      rw [dL] at e
      exact ((yL s t).1 e).1)
    (laysNothing_withMap q E hE) hL) hI

/-- **"link l: cleared"**, whichever the segment's sort. -/
theorem cleared_tiedR (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hT : OfDesc _ T)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (l : ℕ) (hl : l < 25) (N : Numbers)
    (Mg : Meaning ProofFile.InstPub W)
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E a b w = w) (Hold : ProofFile.InstPub × S → W → OnBytes.TensorRow → Prop)
    (hpile : ∀ a y w, a.2.atBetween = true → Mg.pile a y w →
      ∀ r ∈ a.2.out.pending, Hold a w r)
    (hI : GivesIn (T := T) N Mg Rch In (clearIx l)) :
    ∃ fs, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
      ∃ f, fs[l]? = some f ∧
        ∀ (q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W),
        (T.p₁ :: T.l₁)[clearIx l]? = some q →
        NoneBetween N (flatPlacesOf linksFull true) (clearIx l) →
        ClearOwesR N Mg Z f l q.base Hold (In (clearIx l)) →
        TiedAtR N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) Rch (clearIx l)
          (q.withMap E) := by
  obtain ⟨-, -, h3, h4, h5, p', h6, h7⟩ := places_full hl
  obtain ⟨-, fs, hfs, h⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, f, -, -, bC, -, hlen, hf, -, -, -, yC, -, -, -, -, -, -, iC, -, dC⟩ := h l hl
  rw [hlen] at iC
  refine ⟨fs, hfs, f, hf, fun q hq hn hO => ?_⟩
  have hSit : Sits (fun a => a) (q.withMap E) f.clear :=
    sits_lift q bC (OfDesc.pieceAt hT hq iC) E f.clear fun s rs gs t e => by
      rw [dC] at e
      exact ((yC s t).1 e).1
  obtain ⟨X, counts, left, X', e, hX', hkk, hNCL, hfv, hflag⟩ :=
    clear_with_flag hfs hf (plans_hold hS hR O hp hfs hl hf)
  have hrec : ∀ s t, f.clear s = .ok t →
      ClearedRec X left Z.p.X.layers.wsLay Z.first.lin s t := fun s t h => by
    rw [e] at h
    exact clearedGives X counts left _ _ s t h
  by_cases ha : IM.subAt l = ModelPart.attention
  · have e4 : clearPlace l = ⟨1, some l, 13, KindName.frame⟩ := by
      unfold clearPlace
      rw [ha]
      rfl
    rw [e4] at h4 h5
    rw [ha] at h3
    exact tied_of_ridesR (step_clearedAtt h3 h4 h5 h6 h7 hn hSit hrec
      (laysNothing_withMap q E hE) hO.1) hI
  · rcases hflag with ⟨h1, -⟩ | ⟨-, hv, hleft⟩
    · exact absurd (hkk ▸ h1) (kind_not_att hS hR O hl ha hX')
    · obtain ⟨hwo, hback⟩ := hO.2 X' hX' (hfv ▸ hv)
      exact tied_of_ridesR (step_clearedRow h3 ha h4 h5 h6 h7 hn hSit hrec
        (laysNothing_withMap q E hE) hO.1
        (pileGivesWo_of Mg l f.clear X left _ _ q.base _ Hold hrec hv hleft (hNCL ▸ hwo) hpile
          hback)) hI

/-- **What the 51 places owe**, with In k for the promise in front. -/
structure FrameOwesR (N : Numbers) (Mg : Meaning ProofFile.InstPub W) (Z : ProofFile.Pub)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (Hold : ProofFile.InstPub × S → W → OnBytes.TensorRow → Prop)
    (In : ℕ → ProofFile.InstPub × S → Strs → Prop) : Prop where
  /-- the table's extractor lays nothing at the 51 numbers -/
  eFront : ∀ a b w, E 0 a b w = w
  eLaid : ∀ l, l < 25 → ∀ a b w, E (14 * l + 1) a b w = w
  eClear : ∀ l, l < 25 → ∀ a b w, E (clearIx l) a b w = w
  /-- the plan's numbers of trees and messages do not move across them -/
  nFront : NoneBetween N (flatPlacesOf linksFull true) 0
  nLaid : ∀ l, l < 25 → NoneBetween N (flatPlacesOf linksFull true) (14 * l + 1)
  nClear : ∀ l, l < 25 → NoneBetween N (flatPlacesOf linksFull true) (clearIx l)
  rFront : ∀ q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W,
    (T.p₁ :: T.l₁)[0]? = some q → RideAt N Mg .ok q.base 0 (In 0)
  rLaid : ∀ l, l < 25 → ∀ q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W,
    (T.p₁ :: T.l₁)[14 * l + 1]? = some q →
    RideAt N Mg (layFront l) q.base (14 * l + 1) (In (14 * l + 1))
  rClear : ∀ l, l < 25 → ∀ fs f, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first
      Z.p.X = .ok fs → fs[l]? = some f →
    ∀ q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W,
    (T.p₁ :: T.l₁)[clearIx l]? = some q → ClearOwesR N Mg Z f l q.base Hold (In (clearIx l))
  /-- "pile" gives Hold of every pending row, where the chain stands between two links -/
  pile : ∀ a y w, a.2.atBetween = true → Mg.pile a y w → ∀ r ∈ a.2.out.pending, Hold a w r

/-- **THE KIND "frame" AT ITS 77 PLACES OF THE WRITTEN LIST, IN THE FORM WITH Rch**: 51 from
FrameOwesR and GivesIn; the other 26 are the two premises hSeal and hBehind. -/
theorem frame_tiedR_ours (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hT : OfDesc _ T)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (Hold : ProofFile.InstPub × S → W → OnBytes.TensorRow → Prop)
    (H : FrameOwesR (T := T) N Mg Z E Hold In) (hI : ∀ k, GivesIn (T := T) N Mg Rch In k)
    (hSeal : ∀ q, (T.p₁ :: T.l₁)[357]? = some q →
      TiedAtR N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) Rch 357
        (q.withMap (E 357)))
    (hBehind : ∀ l, l < 25 → ∀ q, (T.p₁ :: T.l₁)[behindIx l]? = some q →
      TiedAtR N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) Rch (behindIx l)
        (q.withMap (E (behindIx l)))) :
    ∀ i q a, (T.p₁ :: T.l₁)[i]? = some q → (flatPlacesOf linksFull true)[i]? = some a →
      a.kind = KindName.frame →
      TiedAtR N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) Rch i
        (q.withMap (E i)) := by
  intro i q a hq ha hk
  rcases frame_places_full i a ha hk with rfl | rfl | ⟨l, hl, rfl | rfl | rfl⟩
  · exact front_tiedR O hT hq N Mg (E 0) H.eFront H.nFront (H.rFront q hq) (hI 0)
  · exact hSeal q hq
  · exact laid_tiedR hS hR O hT l hl hq N Mg (E _) (H.eLaid l hl) (H.nLaid l hl)
      (H.rLaid l hl q hq) (hI _)
  · exact hBehind l hl q hq
  · obtain ⟨fs, hfs, f, hf, h⟩ :=
      cleared_tiedR hS hR O hT hp l hl N Mg (E _) (H.eClear l hl) Hold H.pile (hI _)
    exact h q hq (H.nClear l hl) (H.rClear l hl fs f hfs hf q hq)

end

end P1L20

#print axioms P1L20.front_tiedR
#print axioms P1L20.laid_tiedR
#print axioms P1L20.cleared_tiedR
#print axioms P1L20.frame_tiedR_ours
