-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/TieThreeSmpAt.lean: code switching: THE PREMISE hσ OF THE THIRD TIE AT A PLACE
(k02_t3R, Tw/K2C/TieThreeR.lean), AT THE CLOSED CONSTANT's READER
OF OOD SAMPLES smp := smpNamed r.cs seats (Johnson/Desc/Sound/SmpNamed.lean), BEHIND THE WAY OUT. A
JOINING: every step is a call. NO SUB-PROTOCOL IMPORTS THIS FILE.
  seated_joint      where the seated sub-protocol accepts: ALL that seated_both
                    (K2Caller/SeatText.lean) hands on, AND a joint OOD seed, typed, that is what
                    round 1 drew (JointIs, by jointIs_at, K2Caller/BehindPaid.lean): the road of
                    seated_text and of seated_atYes (K2Caller/SeatYes.lean), with two more of
                    outT_inv's clauses kept: the fullest of the four forms
  hσ_at_place_list  hσ, from the two facts on the list seats APART: seats.Nodup (one fact for all 25
                    code switches) · seats[n0 + i]? = some (seatN i): by forms_at_yes
                    | smpLike_of_list (Tw/K2C/SmpLikeNew.lean) at the state that the decision made,
                    carried over the way out by formsAt_kept (K2Caller/DoorKeeps.lean)
  hσ_at_place       the same from the test newSeatsB seats seatN n0 = true (Tw/K2C/SmpForms.lean)
LEFT, BY NAME: the tie's own w2 · hr · hs · the two facts on seats, or the test (closed) · hK :
KeepsOut leave · hnd h0f hcs hpub and hT1, which hAt_at_place takes too (there at rows := 0: lay 0).
n0 IS NO FREE LETTER: hT1 gives fx.st.oracles.size = n0, and the table of joints' promise
(bookAt's third clause) a.1.st.oracles.size = N.msgsAt ps[k]?: so hT1 and the facts on seats are met
together at a state ONLY AT n0 = N.msgsAt ps[k]? (where the way in and the front leave the count).
Whoever pays the test at a written number owes that equation: it is shown by nothing here.
AT seatN := seatNew N m r: lay it for the letter seatN. newSeatsB DOES NOT FOLLOW FROM sentPlaceB
(Tw/K2C/SentByPlace.lean), AT THE CLOSED CONSTANT's OWN seats EITHER: sentPlaceB counts TREES
(N.treesAt) and never MESSAGES: turn n0 into n0 + 1: sentPlaceB does not move, and newSeatsB rejects
(no repeats; r.l not empty). It reads neither the letter seats (the seats of ALL messages, in the
order of sending, off the list of rounds) nor n0.
LIMITS. Both readers' OOD seeds are by choice (SmpLikeNew.lean's limit). That r.cs is the closed
constant's codes is the assembler's. No premise is shown met here. No soundness is claimed. On
hiding nothing.
-/
import Johnson.Top.H0.Tw.K2C.TieThreeAt
import Johnson.Top.H0.Tw.K2C.SmpLikeNew

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim FileDescription Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers)
open VerifiableInference.Desc.First.K2Hands
open _root_.Run (ckP)
open _root_.Tw.K2 (switchNotices)

section
variable {F : Frame} {W W' Cl Cl₀ : Type}
variable {r : SwRow} {H : r.OK} (X : Letters r H)
  (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  (d₁ d₂ : RDT) (ρ : WordsOf (selZ X iJ iQ) d₁) (p : K2.P2) (base : ℕ)
  (ext : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W → W)

/-- **What an acceptance of the seated sub-protocol is made of, with the joint OOD seed.** -/
theorem seated_joint (w : K2Wr r d₁ d₂) (B : Block Rec Cl) (enter : Rec → Except String Rec)
    (leave : Rec → Rec → Except String Rec) (hr : B.rounds = (K2.codeSwitchKind (Cl := Cl₀) p).rounds)
    (hs : SeatStep B (K2.codeSwitchKind (Cl := Cl₀) p) enter leave)
    (ext' : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W' → W')
    (strs : Rec × F.E.Str → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).Ex.Str)
    (inX : Rec → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).X)
    (a b : Rec × F.E.Str) (τ : Tr (uLT (ckP .two) [d₁, d₂]))
    (ho : (seatedAt (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext) B ext').ior.red.out a τ =
      some b) :
    ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok b.1 ∧
      (vN d₂ τ.2.2.1 τ.2.2.2.1).drawn.poss.length = baseCount r.set .request r.g ∧
      K2.decideWith _root_.Tw.K2.sendByL8 p t [vN d₁ τ.1 τ.2.1, vN d₂ τ.2.2.1 τ.2.2.2.1]
        (shownP X iJ iQ d₁ d₂ ρ p base ext (t, a.2) τ) = .ok t' ∧
      (∃ sd, JointIs r.cs r.l (vN d₁ τ.1 τ.2.1) sd) ∧
      ∃ x y S3 Y rows G c, K2.AtYes p t t' (vN d₁ τ.1 τ.2.1) (vN d₂ τ.2.2.1 τ.2.2.2.1)
        (shownP X iJ iQ d₁ d₂ ρ p base ext (t, a.2) τ) x y S3 Y rows G c := by
  have hs' : SeatStep B (K2.codeSwitchKind (Cl := Claim) p) enter leave := hs
  obtain ⟨t, t', e1, e2, e3⟩ := seated_out (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext)
    (K2.codeSwitchKind (Cl := Claim) p) rfl rfl B enter leave hr hs' ext' a b τ ho
  obtain ⟨b₂, hl⟩ := piece_is_lawOut X iJ iQ d₁ d₂ ρ p base ext strs inX w (t, a.2) (t', b.2) τ e2
  obtain ⟨q1, -, ht, sd, -, hsd, -, -⟩ := outT_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl
  exact ⟨t, t', e1, e3, len_at d₁ d₂ w _ _, ht,
    ⟨sd, jointIs_at X iJ iQ d₁ d₂ ρ w τ.1 τ.2.1 q1 sd hsd⟩, K2.yes_whole p t _ _ _ t' ht⟩

end

set_option maxHeartbeats 4000000 in
/-- **hσ OF THE THIRD TIE AT A PLACE**, at smp := smpNamed r.cs seats, from the two facts on the
list seats apart. -/
theorem hσ_at_place_list {F : Frame} {P Cells Tok Cl Cl₀ Xi : Type} {r : SwRow} (h : r.ok = true)
    (iJ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
        h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J →
      (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
        h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q →
      (sigOf r.cs r.l).Ent)
    (G : FileDescription Xi) (seatN : Fin r.l.length → ℕ × ℕ) (base : ℕ) (d₁ d₂ : RDT)
    (w2 : K2Wr r d₁ d₂) (p : K2.P2)
    (strs : Rec × F.E.Str →
      (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).Ex.Str)
    (inX : Rec → (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).X)
    (B : Block Rec Cl) (enter : Rec → Except String Rec) (leave : Rec → Rec → Except String Rec)
    (hr : B.rounds = (K2.codeSwitchKind (Cl := Cl₀) p).rounds)
    (hs : SeatStep B (K2.codeSwitchKind (Cl := Cl₀) p) enter leave)
    (ext' : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → Wit Cells Tok MsgT →
      Wit Cells Tok MsgT)
    (N : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place) (z : P) (Rch : ℕ → Rec × F.E.Str → Prop)
    (k n0 grp rows : ℕ) (hK : KeepsOut leave)
    (f₀ : _root_.Tw.K2.Front) (W : SwitchFrame) (olds : List ℕ)
    (hnd : olds.Nodup) (h0f : K2.frameAt f₀ = some W) (hcs : f₀.st.codes = r.cs)
    (hpub : frontPubB r.l.length f₀ = true)
    (hT1 : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        frontB2 f₀ W grp rows n0 olds fx = true ∧ Tied r.l (switchNotices fx.T fx.others))
    (seats : List (ℕ × ℕ)) (hNd : seats.Nodup)
    (hSt : ∀ i : Fin r.l.length, seats[n0 + i.val]? = some (seatN i)) :
    ∀ a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G
          seatN base d₁ F) p base
        idExt) B ext').ior.red.out a τ = some b →
      K2.SmpLike r.cs (smpNamed (P := P) r.cs seats) (z, b.1) ⟨r.l, seatN⟩
        (fun o => newSmp n0 b.1 o) := by
  intro a τ b ha hrc hm hout
  obtain ⟨t, t', et, el, -, -, ⟨sd, J⟩, x, y, S3, Y, rws, Gg, c, A⟩ :=
    seated_joint (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G seatN base d₁ F) p
      base idExt w2 B enter leave hr hs ext' strs inX a b τ hout
  obtain ⟨hB2, hTd⟩ := hT1 a ha hrc hm t et x A.front
  have P12 : Pub12 (r := r) (placeFrame W n0 olds) x := pub12_of_twelve h0f hcs hpub hnd hTd hB2
  obtain ⟨e1, -, -⟩ := nums_of_twelve (r := r) h0f hcs hpub hnd hTd hB2
  have K := hK a.1 t' b.1 el
  refine smpLike_of_list seats seatN n0 z b.1 hNd hSt fun i => ?_
  obtain ⟨ρ', hρ⟩ := forms_at_yes A n0 P12.codes e1 hTd sd J i
  exact ⟨ρ', by rw [formsAt_kept r.cs _ K.1]; exact hρ⟩

/-- **hσ OF THE THIRD TIE AT A PLACE**, from the test newSeatsB. -/
theorem hσ_at_place {F : Frame} {P Cells Tok Cl Cl₀ Xi : Type} {r : SwRow} (h : r.ok = true)
    (iJ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
        h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J →
      (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
        h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q →
      (sigOf r.cs r.l).Ent)
    (G : FileDescription Xi) (seatN : Fin r.l.length → ℕ × ℕ) (base : ℕ) (d₁ d₂ : RDT)
    (w2 : K2Wr r d₁ d₂) (p : K2.P2)
    (strs : Rec × F.E.Str →
      (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).Ex.Str)
    (inX : Rec → (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).X)
    (B : Block Rec Cl) (enter : Rec → Except String Rec) (leave : Rec → Rec → Except String Rec)
    (hr : B.rounds = (K2.codeSwitchKind (Cl := Cl₀) p).rounds)
    (hs : SeatStep B (K2.codeSwitchKind (Cl := Cl₀) p) enter leave)
    (ext' : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → Wit Cells Tok MsgT →
      Wit Cells Tok MsgT)
    (N : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place) (z : P) (Rch : ℕ → Rec × F.E.Str → Prop)
    (k n0 grp rows : ℕ) (hK : KeepsOut leave)
    (f₀ : _root_.Tw.K2.Front) (W : SwitchFrame) (olds : List ℕ)
    (hnd : olds.Nodup) (h0f : K2.frameAt f₀ = some W) (hcs : f₀.st.codes = r.cs)
    (hpub : frontPubB r.l.length f₀ = true)
    (hT1 : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        frontB2 f₀ W grp rows n0 olds fx = true ∧ Tied r.l (switchNotices fx.T fx.others))
    (seats : List (ℕ × ℕ)) (hN : K2.newSeatsB seats seatN n0 = true) :
    ∀ a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G
          seatN base d₁ F) p base
        idExt) B ext').ior.red.out a τ = some b →
      K2.SmpLike r.cs (smpNamed (P := P) r.cs seats) (z, b.1) ⟨r.l, seatN⟩
        (fun o => newSmp n0 b.1 o) :=
  hσ_at_place_list h iJ iQ G seatN base d₁ d₂ w2 p strs inX B enter leave hr hs ext' N Mg links ps z
    Rch k n0 grp rows hK f₀ W olds hnd h0f hcs hpub hT1 seats
    (K2.newSeats_of_test seats seatN n0 hN).1 (K2.newSeats_of_test seats seatN n0 hN).2

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.seated_joint
#print axioms VerifiableInference.Desc.First.K2Caller.hσ_at_place_list
#print axioms VerifiableInference.Desc.First.K2Caller.hσ_at_place
