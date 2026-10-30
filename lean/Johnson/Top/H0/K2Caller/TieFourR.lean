-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/TieFourR.lean: THE FOURTH TIE OF THE CODE SWITCH AT A PLACE, WITH «REACHED»:
one theorem: the join of `t4R_front` (TiesFrontR.lean), `carry_of_R` (CarryOfR.lean), `pins_of_R`
(PinsOfR.lean), `hall_at` (HallAt.lean), `seated_atYes` (SeatYes.lean), `pub12_of_twelve`
(PubOfTwelve.lean) and three lemmas at an acceptance (Johnson/Top/H0/K2Hears/CheckSkel.lean,
ThereAtYes.lean).

Main names:
  `k02_t4R`: where the seated piece accepts, under the table of joints' promise in front and Rch, at
    a state without a mark: the relation in front of `k02_place` (PlaceLaw.lean), at what the
    piece's extractor lays, gives all that the table's row closes in front: the sentence on the
    carried claim and the pin of every kept tenant.
  THE PREMISES, AND WHO PAYS EACH. On the typed structure and the written rounds: r.ok · `K2Wr` · 0
    < the count of positions: closed at the written entries. The seated sub-protocol and its door
    (hr, hs): the row on where the kind sits. The table's row (hins, hctx): closed facts on the
    written list. hcar, hpin: the composed meaning's two fields, by unfolding at its filling, where
    the frame's list of trees and keys are the sentence's own and the typed structure's codes are
    the filling's. hdoor: the sentence's way in is the door: asked under the promise and Rch alone
    (`doorZ_at_switch`, CarryClosed.lean: at a state inside a link the two part). hext: the piece's
    extractor is the table's. hE: `msgsOf_ext` (ExtMade.lean), on a closed fact that is still to be
    held. Six closed facts at a written front and its frame. C, FtF: `caller_fam` (OnTopFacts.lean)
    and the like for `Fit`. hT1: the first tie's content: the test `frontB2` at the place's numbers
    of the kept old messages, the notices, two invariants' fruits, and that the state's and the
    front's statements hold the same oracle messages. hSF (at the kept members alone), hB, ho, hal,
    hN, hNd, hAl: facts on the plan (tests with code: `keptSeatsB`; KeptAlign.lean's test that both
    copies have one number; that the table's members at a kept tenant are the typed kept members,
    shape and radius). hBook: three tests on the state's book, from «reached». hOld: the book has a
        place for each kept old message: asked behind the front: from the promise and the test
        `storedB`. horc: the file's columns are read by the tree's
    number. hsh: every leaf is shown: from the promise.
Limits. A SENTENCE WITH MANY PREMISES; NONE IS SHOWN MET HERE; no member. The numbers of the kept
old messages are ONE list (olds), not «there are». It is no soundness of the protocol. On hiding
nothing.

-/
import Johnson.Top.H0.K2Caller.HallAt
import Johnson.Top.H0.K2Caller.PinsOfR
import Johnson.Top.H0.K2Caller.CarryOfR
import Johnson.Top.H0.K2Caller.TiesFrontR
import Johnson.Top.H0.K2Caller.SeatYes
import Johnson.Top.H0.K2Hears.CheckSkel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb IOR
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim FileDescription Strs Wit Place)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers)
open VerifiableInference.Desc.First.K2Hands
open Johnson.G (smpTop keptBitsB keptShapeB storedB)
open _root_.Run (ckP)
open _root_.Tw.K2 (switchNotices)

variable {F : Frame}

set_option maxHeartbeats 8000000 in
/-- **THE FOURTH TIE OF THE CODE SWITCH AT A PLACE, WITH «REACHED»**: where the seated piece
    accepts,
under the table of joints' promise in front and Rch, at a state without a mark: the law's relation
    in
front (`k02_place`, PlaceLaw.lean) at what the piece's extractor lays gives what the table's row
closes in front: the sentence on the carried claim and the kept members' pins. Every premise is
named; who pays which stands in the head. -/
theorem k02_t4R {P Cells Tok Cl Cl₀ Xi : Type} {r : SwRow} (h : r.ok = true)
    (iJ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
        h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
        h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (G : FileDescription Xi) (seat : Fin r.lo.length → ℕ × ℕ) (seatN : Fin r.l.length → ℕ × ℕ)
    (base : ℕ) (d₁ d₂ : RDT) (w2 : K2Wr r d₁ d₂) (arr : ℕ → ℕ → ℕ) (seats : List (ℕ × ℕ))
    (decT : (ℕ → Option (ℕ × List UInt64)) → P × VerifiableInference.Desc.First.S → Option Cells)
    (c₀ : Cells)
    (d₀ : (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).X ×
      (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).Ex.Str) (y₀ : F.E.Str)
    (rowAt : ℕ → Option SwRow) (pAt : ℕ → K2.P2) (door : ℕ → First.S → Option First.S) (m : ℕ)
    (hrow : rowAt m = some r) (B : Block Rec Cl) (enter : Rec → Except String Rec)
    (leave : Rec → Rec → Except String Rec) (hr : B.rounds = (K2.codeSwitchKind (Cl := Cl₀) (pAt m)).rounds)
    (hs : SeatStep B (K2.codeSwitchKind (Cl := Cl₀) (pAt m)) enter leave)
    (ext' : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (N : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place) (z : P)
    (Rch : ℕ → Rec × F.E.Str → Prop) (k : ℕ)
    (hins : (rowQ links ps k).ins = [.carry m, .pinKept m]) (hctx : (rowQ links ps k).ctx = [])
    (hcar : ∀ s y w, carryK2 rowAt pAt door (K2.orcY F.all F.key) (fun r H => smpK2 r H) m (z, s) y
      w → Mg.carry m (z, s) y w)
    (ms minePad : List Mem)
    (hpin : ∀ (q : ℕ × ℕ) s y w, pinJT r.cs G arr (smpNamed r.cs seats) ms q.1 q.2 (z, s) y w →
      Mg.pin q.1 q.2 (z, s) y w)
    (hdoor : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → door m a.1 = some t)
    (hext : ∀ a τ w, ext' a τ w = extAt r.cs G arr (smpNamed r.cs seats) decT c₀ [] minePad false
      none (z, a.1) (strsOf F a.2) w)
    (hE : ∀ a τ w, msgsOf r.cs r.l seatN arr (ext' a τ w) = msgsOf r.cs r.l seatN arr w)
    (f₀ : _root_.Tw.K2.Front) (W : SwitchFrame) (n0 grp rows : ℕ) (olds : List ℕ)
    (hnd : olds.Nodup) (h0f : K2.frameAt f₀ = some W) (hcs : f₀.st.codes = r.cs)
    (hpub : frontPubB r.l.length f₀ = true) (hkA : r.keptAt W = true)
    (hbB : keptBitsB r W = true) (hsB : keptShapeB r = true)
    (C : ∀ W₀, Renumbered W W₀ → CallerAt (selR (Letters.plain r (r.ok_says h))) r.cs r.l iJ iQ memK
        rowK (plK W₀) W₀)
    (FtF : ∀ W₀, Renumbered W W₀ → Fit r.cs r.l (plainR r (r.ok_says h)).s W₀
      (memK (r := r) (H := (r.ok_says h))) rowK (plK W₀))
    (hpos : 0 < baseCount r.set .request r.g)
    (hT1 : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt (pAt m) t = some fx →
        frontB2 f₀ W grp rows n0 olds fx = true ∧ Tied r.l (switchNotices fx.T fx.others) ∧
        K2.SampleGoodS fx.st ∧ storedB r (placeFrame W n0 olds) fx = true ∧ a.1.st.oracles =
            fx.st.oracles)
    (L : Laid) (trees : ℕ) (news : List (ℕ × ℕ)) (hSF : ∀ κ : {a // (plainHd r (r.ok_says h)).cl a},
        SeatFitAt G r.cs r.lo seat κ.1.1)
    (hB : keptSeatsB G r.cs L seats trees r.lo seat r.kept olds = true)
    (ho : ∀ κ : {a // (plainHd r (r.ok_says h)).cl a},
      olds[r.kept.idxOf κ.1.1.val]? = some (keptK2 r (r.ok_says h) (placeFrame W n0 olds) κ).old)
    (hBook : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t →
        VerifiableInference.Desc.K12.Door.atFirstBook (K2.par9 (pAt m)).firstTree t = true ∧
        VerifiableInference.Desc.K12.Door.atFirstSeats L t = true ∧
        VerifiableInference.Desc.K12.Door.atFirstFits t = true)
    (hOld : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt (pAt m) t = some fx →
        ∀ κ : {a // (plainHd r (r.ok_says h)).cl a},
          (keptK2 r (r.ok_says h) (placeFrame W n0 olds) κ).old < t.book.place.size)
    (horc : ∀ y j, j < trees → ∀ x, K2.orcY F.all F.key y j x = y.col j x)
    (hal : ∀ κ : {a // (plainHd r (r.ok_says h)).cl a}, ∃ v, news[1 + r.kept.idxOf κ.1.1.val]? =
        some v ∧
      arr (seat κ.1.1).1 (seat κ.1.1).2 = arr v.1 v.2)
    (hN : ∀ (n : ℕ) (ho : 1 + n < r.l.length), news[1 + n]? = some (seatN ⟨_, ho⟩))
    (hNd : (minePad.map seatOf).Nodup)
    (hsh : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      ∀ q ∈ N.keptOf m, shownJT r.cs G ms q.1 q.2 (strsOf F a.2))
    (hAl : ∀ q ∈ N.keptOf m, (∃ x ∈ ms, SitsAt x q.1 q.2) ∧ ∀ x ∈ ms, SitsAt x q.1 q.2 →
      x ∈ minePad ∧ ∃ κ : {a // (plainHd r (r.ok_says h)).cl a},
          VerifiableInference.Desc.Sound.Alike x ⟨⟨r.lo, seat⟩, κ.1.1⟩) :
    ∀ a τ b w, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G
          seatN base d₁ F) (pAt m) base idExt) B ext').ior.red.out a τ = some b →
      (∀ t, enter a.1 = .ok t → ((Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ
          iQ).sw).S.over (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ
          iQ).sw).A).relR (lawFa (Letters.plain r (r.ok_says h)) iJ iQ (strsTop iJ iQ (pAt m) (fun y
          => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) (smpTop r (r.ok_says h)
          iJ iQ (baseCount r.set .request r.g) (smp₀ r (r.ok_says h))) d₀) (inXTop iJ iQ (pAt m)
          (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) (smpTop r
          (r.ok_says h) iJ iQ (baseCount r.set .request r.g) (smp₀ r (r.ok_says h))) d₀ y₀) (t,
          a.2)) (selBk (Letters.plain r (r.ok_says h)) iJ iQ (wtMade iJ iQ seatN arr (ext' a τ w))))
          →
      relAt (meansQ N Mg (fun s => (z, s))) (insQ links ps k) a (ext' a τ w) := by
  intro a τ b w ha hrc hm hout hR
  obtain ⟨t, t', et, -, hlen, x, y', S3, Y, rws, Gg, c, A⟩ := seated_atYes (Letters.plain r
      (r.ok_says h)) iJ iQ d₁ d₂
    (wordsMade iJ iQ G seatN base d₁ F) (pAt m) base idExt w2 B enter leave hr hs ext'
    (strsTop iJ iQ (pAt m) (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y)
        (smpTop r (r.ok_says h) iJ iQ (baseCount r.set .request r.g) (smp₀ r (r.ok_says h))) d₀)
        (inXTop iJ iQ (pAt m) (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂])
        y) (smpTop r (r.ok_says h) iJ iQ (baseCount r.set .request r.g) (smp₀ r (r.ok_says h))) d₀
        y₀) a b τ hout
  obtain ⟨hB2, hTd, hG, hSt, hor⟩ := hT1 a ha hrc hm t et x A.front
  have P12 : Pub12 (r := r) (placeFrame W n0 olds) x := pub12_of_twelve h0f hcs hpub hnd hTd hB2
  have hRn : Renumbered W (placeFrame W n0 olds) := ⟨_, _, _, rfl⟩
  have hne : (vN d₂ τ.2.2.1 τ.2.2.2.1).drawn.poss ≠ [] := by
    intro e
    rw [e] at hlen
    exact absurd hlen.symm (Nat.ne_of_gt hpos)
  have h0 : (K2.longFront (pAt m) t x (K2.orcY F.all F.key (strsOf F a.2)) 0).isSome = true :=
    K2.there_of_atYes A (K2.listed_of_drawn _ _ hne) _ 0
  obtain ⟨b1, b2, b3⟩ := hBook a ha hrc hm t et
  have b4 := hOld a ha hrc hm t et x A.front
  refine t4R_front N Mg links ps (fun s => (z, s)) Rch k m hins hctx
    (fun a' w' => a' = a ∧ w' = ext' a τ w) (fun _ _ => True) ?_ ?_ a _ ha hrc hm ⟨rfl, rfl⟩ trivial
  · rintro a' w' - - - ⟨rfl, rfl⟩
    exact hcar _ _ _ (carry_of_R h iJ iQ base d₁ d₂ d₀ y₀ rowAt pAt door m hrow z a'.1 t a'.2 _
      (hdoor a' ha hrc hm t et) x (placeFrame W n0 olds) A.front P12.frameIs _ (hR t et))
  · rintro a' w' - - - ⟨rfl, rfl⟩ - q hq
    apply hpin
    rw [hext a' τ w]
    exact pins_of_R iJ iQ G seat seatN (pAt m) base d₁ d₂ arr seats decT c₀ d₀ y₀ (z, a'.1) t a'.2 x
      (placeFrame W n0 olds) A.front P12 (Johnson.Top.H.check_facts A.check).1 (C _ hRn) (FtF _ hRn)
          0 h0 w
      (ext' a' τ w) (hE a' τ w) (hR t et) ms minePad hNd q (hAl q hq).1
      (hall_at G seat seatN (pAt m) (K2.orcY F.all F.key) arr seats L trees (z, a'.1) t x
          (placeFrame W n0 olds)
        (strsOf F a'.2) P12 (K2.check_skel_atYes A P12.keptPos) hG
        ((keptAt_renumber r W _ _ _).trans hkA) ((keptBits_renumber r W _ _ _).trans hbB) hsB hSt
        (FtF _ hRn) hor hSF olds hB ho b1 b2 b3 0 h0 b4 (horc _) news hal hN ms minePad q
        (hsh a' ha hm q hq) (hAl q hq).2)

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.k02_t4R
