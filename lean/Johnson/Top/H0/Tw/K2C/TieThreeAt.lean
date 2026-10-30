-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/TieThreeAt.lean: code switching: THE PREMISE hAt OF THE THIRD TIE AT A PLACE
(k02_t3R, Tw/K2C/TieThreeR.lean), WHOLE, AS ONE JOIN. A JOINING:
every step is a call. NO SUB-PROTOCOL IMPORTS THIS FILE.
  frontLight_of_pub   the twelve public clauses at a front (Pub12, K2Caller/TopAt.lean) are
                      FrontLight (Tw/K2C/OnlyAtLight.lean), field by field
  fresh_of_nums       where the front's statement has, at the code switch's group, a group without
                      a row, the group G of an acceptance (K2.AtYes) has none
  seats_of_yes        T3At.seats: by K2.seat_by_new (Tw/K2C/WordsAtNew.lean), where the way out
                      leaves the book and seatN is the layout's seat by place
  hAt_at_place        hAt
WHAT hAt ASKS, AND WHENCE EACH PART COMES HERE.
  «the way out keeps the tables and the group's rows»  hK : KeepsOut leave (K2Caller/DoorKeeps.lean)
  T3At.keptPos · count · groupNo · fresh                the first tie's content hT1: the test
      frontB2 AT rows := 0 and Tied, by pub12_of_twelve | nums_of_twelve (K2Caller/PubOfTwelve.lean)
  T3At.groupIs                                          hgrp : N.groupAt m = grp, with groupNo
  T3At.carried · position                               hD, asked at the front WITH THE LAYOUT OF
      ITS NOTICES IN HAND (the form in which what is owed on the numbers comes; an acceptance has a
      layout: K2.seat_by_new), at a letter d with hd : d = baseCount r.set .request r.g
  T3At.seats                                            seats_of_yes: hKb (the way out leaves the
      book: KeepsOut DOES NOT SAY IT) and hS, asked at the front
  T3At.typed, first clause (OnlyAt) and third (SlotsAll)  typed_of_yes
      (K2Caller/TypedAtT3.lean) at W₀ := placeFrame W n0 olds, from C (caller_fam,
      K2Caller/OnTopFacts.lean), FrontLight (above), Held, the acceptance and p.logN ≤ 32
  Held                                                  held_of_yes (Tw/K2C/HeldNamesAt.lean), at
      the law's own aOfK r H and fun _ _ => 0: from r.keptAt W and hone, asked at the front
  T3At.typed, second clause (ZeroAsks)                  zeroAsks_of_yes | shapesAt_of_yes
      (Tw/K2C/ZeroAsksAtYes.lean): from the same, Tied, hK and the test on the codes' lengths
LEFT, BY NAME. Closed, on public data: h32 · hL · hkA · hnd h0f hcs hpub (as in the fourth tie) ·
C (caller_fam concludes it at its own iJ | iQ alone) · hgrp · hd. On the way out: hK · hKb. Asked at
the front, under the table of joints' promise, Rch and «no mark»: hT1 (FoldSideR.lean's foldSideR_*
conclude it at rows := 0) · hD · hone (TieThreeOneRow.lean) · hS (TieThreeSeatsAt.lean;
base_is_roots, Johnson/IMR/BaseIsRoots.lean). NOTHING IS ASKED AT AN ACCEPTANCE.
THE PRICE: these four are asked at every such front, also where the decision rejects.
LIMITS. A SENTENCE WITH MANY PREMISES; NONE IS SHOWN MET HERE. IT FORCES rows := 0 in the first
tie's test. m IS THE NEW SEGMENT's NUMBER (pin m 0 · N.sent m 0), one more than the first and the
fourth tie's m. olds IS ONE LIST for all states, where the law at a place has «there are». THREE
COUNTS MEET AT THE SPENDER: hS seats the new members BY PLACE from the tree's NUMBER p.firstTree +
t.roots on; what is owed on the numbers (K2.LinkDebts.sent | K2.SwitchDebts.sent) seats N.sent m 0,
AS A SET, from the tree's PLACE IN THE BOOK, the book's count of trees; and the tie's own premise M
(K2.MembersLike) holds seatN against N.sent m 0, into and onto. SO hS, THE DEBTS AND M HOLD TOGETHER
ONLY WHERE t.book.trees.size = p.firstTree + t.roots AND seatN's VALUES ARE JUST THE SEATS THAT THE
DEBTS COUNT: OWED, SHOWN BY NOBODY HERE; elsewhere the tie over this join is empty. THE EQUATION HAS
TWO HALVES WITH DIFFERENT PAYERS: (i) t.book.trees.size = t.roots (as many roots as trees: an
invariant of the verifier's state; the fourth tie's hBook asks a test of that name at the same
front) · (ii) p.firstTree = 0 (a fact on the seated sub-protocol's parameters): with (i), the
equation is false wherever p.firstTree ≠ 0. «Link» is here the chain's segment, not a proof that two
committed tables encode the same weights. It is no soundness of the protocol. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.TypedAtT3
import Johnson.Top.H0.K2Caller.PubOfTwelve
import Johnson.Top.H0.K2Caller.DoorKeeps
import Johnson.Top.H0.K2Caller.OnTopFacts
import Johnson.Top.H0.Tw.K2C.ZeroAsksAtYes
import Johnson.Top.H0.Tw.K2C.HeldNamesAt
import Johnson.Top.H0.Tw.K2C.HeldAtYes
import Johnson.Top.H0.Tw.K2C.WordsAtNew

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim FileDescription Strs Wit Place)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers)
open VerifiableInference.Desc.First.K2Hands
open _root_.Run (ckP)
open _root_.Tw.K2 (switchNotices)
open Johnson.G (aOfK)

variable {F : Frame}

/-- The twelve public clauses at a front are FrontLight, field by field. -/
theorem frontLight_of_pub {r : SwRow} {W₀ : SwitchFrame} {x : _root_.Tw.K2.Front}
    (P : Pub12 (r := r) W₀ x) : FrontLight r.cs r.l W₀ x :=
  ⟨P.frameIs, P.z32, P.twoOld, P.codes, P.keptPos, P.keptRows, P.ell, P.first, P.next, P.mainVars,
    P.d0, P.d1⟩

/-- Where the front's statement has no row yet at the code switch's group, the group of an
acceptance has none. -/
theorem fresh_of_nums {p : K2.P2} {t t' : Rec} {r₁ r₂ : Fmt.RoundView} {gs : Gs}
    {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : Statement} {Y : Array E}
    {rows : List OnBytes.Row} {Gg : Group} {c : Code}
    (A : K2.AtYes p t t' r₁ r₂ gs x y S3 Y rows Gg c) {grp : ℕ} (e : x.f.group = grp)
    (h : ∃ G, x.st.groups[grp]? = some G ∧ G.rows.size = 0) : Gg.rows = #[] := by
  obtain ⟨G, hG, h0⟩ := h
  have hb := A.before
  rw [e, hG] at hb
  have e1 : G.rows = Gg.rows := Option.some.inj hb
  rw [← e1]
  exact Array.eq_empty_of_size_eq_zero h0

/-- **The new members' seats in the book behind**, where the way out leaves the book and seatN is
the layout's seat by place. -/
theorem seats_of_yes {l : List (OracleShape × ℕ)} {p : K2.P2} {t t' u : Rec} {r₁ r₂ : Fmt.RoundView}
    {gs : Gs} {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : Statement} {Y : Array E}
    {rows : List OnBytes.Row} {Gg : Group} {c : Code}
    (ht : K2.decideWith _root_.Tw.K2.sendByL8 p t [r₁, r₂] gs = .ok t')
    (A : K2.AtYes p t t' r₁ r₂ gs x y S3 Y rows Gg c)
    (hT : Tied l (switchNotices x.T x.others)) (hb : u.book = t'.book)
    (seatN : Fin l.length → ℕ × ℕ)
    (hS : ∀ lay, layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      ∀ i : Fin l.length,
        seatN i = (p.firstTree + (t.roots + lay.tree.getD i.val 0), lay.part.getD i.val 0)) :
    ∀ i : Fin l.length, seatBy noFirst u.book (x.st.oracles.size + i.val) = some (seatN i) := by
  obtain ⟨x', lay, hx', hl, hs⟩ := K2.seat_by_new ht
  obtain rfl : x' = x := Option.some.inj ((K2.frontAt_of hx').symm.trans A.front)
  intro i
  obtain ⟨n, hn, -⟩ := hT i
  rw [hb, hs i.val (Array.getElem?_eq_some_iff.1 hn).1, hS lay hl i]

set_option maxHeartbeats 4000000 in
/-- **hAt OF THE THIRD TIE AT A PLACE.** Every premise is named; whence each part of hAt comes
stands in the head. -/
theorem hAt_at_place {P Cells Tok Cl Xi : Type} {r : SwRow} (h : r.ok = true)
    (iJ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
        h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J →
      (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
        h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q →
      (sigOf r.cs r.l).Ent)
    (G : FileDescription Xi) (seatN : Fin r.l.length → ℕ × ℕ) (base : ℕ) (d₁ d₂ : RDT) (p : K2.P2)
    (B : Block Rec Cl) (enter : Rec → Except String Rec) (leave : Rec → Rec → Except String Rec)
    (ext' : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → Wit Cells Tok MsgT →
      Wit Cells Tok MsgT)
    (N : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place) (z : P) (Rch : ℕ → Rec × F.E.Str → Prop)
    (k m n0 grp : ℕ)
    (hK : KeepsOut leave) (hKb : ∀ s t' s', leave s t' = .ok s' → s'.book = t'.book)
    (h32 : p.logN ≤ 32) (hL : r.cs.lengthsOk = true)
    (f₀ : _root_.Tw.K2.Front) (W : SwitchFrame) (olds : List ℕ)
    (hnd : olds.Nodup) (h0f : K2.frameAt f₀ = some W) (hcs : f₀.st.codes = r.cs)
    (hpub : frontPubB r.l.length f₀ = true) (hkA : r.keptAt W = true)
    (C : ∀ W₀, Renumbered W W₀ → CallerAt (selR (Letters.plain r (r.ok_says h))) r.cs r.l iJ iQ memK
        rowK (plK W₀) W₀)
    (hT1 : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        frontB2 f₀ W grp 0 n0 olds fx = true ∧ Tied r.l (switchNotices fx.T fx.others))
    (hgrp : N.groupAt m = grp)
    (d : ℕ) (hd : d = baseCount r.set .request r.g)
    (hD : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        ∀ lay, layTrees fx.st.codes (switchNotices fx.T fx.others) = some lay →
          ∀ W₀, K2.frameAt fx = some W₀ →
            N.rowsAt m .carried = (0, 1 + K2.keptSamples fx W₀) ∧
            N.rowsAt m .position = (1 + K2.keptSamples fx W₀,
              d * (1 + K2.targetRows fx.T + 2)))
    (hone : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        ∀ κ ∈ (placeFrame W n0 olds).kept,
          (fx.st.oracles.getD κ.old default).sampleRows.size = 1)
    (hS : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        ∀ lay, layTrees fx.st.codes (switchNotices fx.T fx.others) = some lay →
          ∀ i : Fin r.l.length,
            seatN i = (p.firstTree + (t.roots + lay.tree.getD i.val 0), lay.part.getD i.val 0)) :
    ∀ a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G
          seatN base d₁ F) p base
        idExt) B ext').ior.red.out a τ = some b →
      ∀ t t' x y S3 Y rws Gg c, enter a.1 = .ok t → leave a.1 t' = .ok b.1 →
        (vN d₂ τ.2.2.1 τ.2.2.2.1).drawn.poss.length = baseCount r.set .request r.g →
        K2.decideWith _root_.Tw.K2.sendByL8 p t [vN d₁ τ.1 τ.2.1, vN d₂ τ.2.2.1 τ.2.2.2.1]
          (shownP (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G seatN base d₁ F) p
              base idExt (t, a.2) τ) = .ok t' →
        K2.AtYes p t t' (vN d₁ τ.1 τ.2.1) (vN d₂ τ.2.2.1 τ.2.2.2.1)
          (shownP (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G seatN base d₁ F) p
              base idExt (t, a.2) τ) x y S3 Y rws Gg c →
        K2.SameTables t'.st b.1.st ∧
        (b.1.st.groups[x.f.group]?).map (·.rows) = (t'.st.groups[x.f.group]?).map (·.rows) ∧
        T3At (r.ok_says h) iJ iQ seatN N m n0 grp b.1 x rws (vN d₂ τ.2.2.1 τ.2.2.2.1) Gg := by
  intro a τ b ha hrc hm _ t t' x y S3 Y rws Gg c et el hlen ht A
  have K := hK a.1 t' b.1 el
  obtain ⟨hB2, hTd⟩ := hT1 a ha hrc hm t et x A.front
  have P12 : Pub12 (r := r) (placeFrame W n0 olds) x := pub12_of_twelve h0f hcs hpub hnd hTd hB2
  obtain ⟨e1, e2, hG⟩ := nums_of_twelve (r := r) h0f hcs hpub hnd hTd hB2
  obtain ⟨lay, hlay⟩ : ∃ lay, layTrees x.st.codes (switchNotices x.T x.others) = some lay := by
    obtain ⟨x', lay, hx', hl, -⟩ := K2.seat_by_new ht
    obtain rfl : x' = x := Option.some.inj ((K2.frontAt_of hx').symm.trans A.front)
    exact ⟨lay, hl⟩
  have PL := frontLight_of_pub P12
  have hC := C (placeFrame W n0 olds) ⟨_, _, _, rfl⟩
  have hH := held_of_yes (r.ok_says h) iJ iQ A ((keptAt_renumber r W _ _ _).trans hkA) PL
    (hone a ha hrc hm t et x A.front)
  have hZ := zeroAsks_of_yes (selR (Letters.plain r (r.ok_says h))) r.cs r.l iJ iQ h32 A hC PL hL
    (shapesAt_of_yes A hTd P12.codes K.1)
  exact ⟨K.1, K.2 _, t3At_of (r.ok_says h) iJ iQ seatN N m n0 grp h32 ht A hC PL hH hlen hZ
    P12.keptPos (fresh_of_nums A e2 hG) (hgrp.trans e2.symm)
    (fun W₀ hW => (hD a ha hrc hm t et x A.front lay hlay W₀ hW).1)
    (fun W₀ hW => by rw [hlen, ← hd]; exact (hD a ha hrc hm t et x A.front lay hlay W₀ hW).2)
    (seats_of_yes ht A hTd (hKb a.1 t' b.1 el) seatN (hS a ha hrc hm t et x A.front)) e1 e2⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.frontLight_of_pub
#print axioms VerifiableInference.Desc.First.K2Caller.fresh_of_nums
#print axioms VerifiableInference.Desc.First.K2Caller.seats_of_yes
#print axioms VerifiableInference.Desc.First.K2Caller.hAt_at_place
