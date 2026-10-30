-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/Shorter.lean: WHAT IS OWED AT A PLACE OF THE CODE SWITCH (`K2AllOwes`,
    Johnson/Top/H0/K2Ties/Assembly.lean), WITH THE PLACE's PARAMETERS LAID AT THE STRUCTURE's OWN,
    AND NINETEEN FIELDS DISCHARGED FROM SEVEN NEW ONES AND FROM OTHER FIELDS: A SHORTER LIST (62 FOR
    74), BY LEAN, EACH FIELD MARKED WITH ITS PART. One definition, one structure of Prop, three
        theorems. A law file:
    no sub-protocol imports it. MADE BY PROGRAM out of `K2AllOwes`' own text.

Why. What is left of a list of debts should be a list that Lean holds, not one that a reader keeps.

What is said.
  THE LAYINGS: the description G := D.G · the numbering arr := D.arr · the members ms := D.ms · the
      decoder decT := D.decT · the base Mg₀ := `mgBase` · the reader of OOD samples smp := the named
      one at the typed structure's codes and a list of tenants · the members whose pads are laid :=
      the table's own at the place · the two free types of claims := the one-point type · the
      piece's extractor ext := `extW`: the table's, written out at D's parameters.
  `K2Short`: 62 fields, each with what is known of its payer, EACH MARKED IN ITS DOCSTRING: (a) 37:
      a named test or a closed fact on the list of rounds, the three public files, the table or a
      parameter's text, with a payer by name · (b) 9: along "reached": a fact on reached states, a
      clause of the promise, or a clause at an accept, with a payer by name · (c) 12: NO PAYER KNOWN
      BY NAME TO WHOEVER TYPED THIS, OR A PAYER NAMED ONLY IN ANOTHER FILE's HEAD · (s) 4: where the
      kind sits, and the fifth tie's own list (`K2Owes`: fourteen fields of its own). "With a payer
      by name" does not say "paid": most are NOT JOINED, and some payers are known by
      reports alone: each docstring says which.
  `k2AllOwes_of_short`: `K2Short` gives `K2AllOwes` at these layings. DISCHARGED: hr · hs · hpin ·
      hpin3 · hext · hextD · hrowM · hshown · hnc · hheld · hin · hout · hPP · hSI · hBy · hpos ·
      FtF · ho · hE. NEW: cs · named · said · fit · oldsLen · newOff · leftDoor.
  `extAt_of_cs`, `smp_of_cs`: two carriages along the equation cs.

Limits. THE NOTES ON PAYERS IN THE FIELDS' DOCSTRINGS, AND THE MARKS (a) (b) (c), ARE NOT
    THE LAST WORD: every field has a payer at the closed constant:
    Johnson/P1K2R/LastLine.lean calls them. NO MEMBER OF `K2Short` IS SHOWN. The maps of names iJ,
    iQ stay parameters. No soundness is
    claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Top.H0.K2Ties.Assembly
import Johnson.Top.H0.K2Ties.MeaningJoins
import Johnson.Top.H0.K2Ties.PubBehind
import Johnson.P1K2R.SitsLeft
import Johnson.Top.H0.K2Caller.TieFourPays
import Johnson.Top.H0.K2Caller.ExtMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb IOR
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim FileDescription Strs Wit smpHeld)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers sampledIn sameMembers)
open VerifiableInference.Desc.First.K2Hands
open VerifiableInference.Desc.First.K2 (ownPiece MembersLike SmpLike SeedReads)
open VerifiableInference.Desc.First.K2Ties (Wq K2Owes DecBlind Left saidBehindB pubP_behind
    hheld_paid hrowM_paid hshown_of_cs hpin_of_cs hpin3_of_cs hnc_of_cs)
open H2K.JointK (Sits)
open ProofFile (Cl)
open IM (HandsR openAt)
open P1K2 (EQ pubAt LeftDoor)
open Johnson.G (smpTop aOfK keptBitsB keptShapeB storedB)
open _root_.Run (ckP)
open _root_.Tw.K2 (switchNotices)

variable {F : Frame}

section
variable {Xi P Tok : Type} {rws cls nR : ℕ} {X : OnBytes.Model.Verify.Public} (D : MgData Xi P Tok
    rws cls nR X)

/-- The table's extractor written out, carried along "the codes are D's". -/
theorem extAt_of_cs {c : OnBytes.Codes} (e : c = D.cs) (seats : List (ℕ × ℕ)) (hD : D.smp = smpNamed
    D.cs seats) (c₀ : CellsQ rws cls) (mp : List Mem) (a : P × First.S) (y : Strs) (w : Wq rws cls
    Tok) : extAt D.cs D.G D.arr D.smp D.decT c₀ [] mp false none a y w = extAt c D.G D.arr (smpNamed
    c seats) D.decT c₀ [] mp false none a y w := by
  subst e
  rw [hD]

/-- "The reader's value stays", carried along "the codes are D's". -/
theorem smp_of_cs {c : OnBytes.Codes} (e : c = D.cs) (seats : List (ℕ × ℕ)) (hD : D.smp = smpNamed
    D.cs seats) {a b : P × First.S} {x : Mem} (h : D.smp b x.1 x.2 = D.smp a x.1 x.2) : smpNamed c
    seats b x.1 x.2 = smpNamed c seats a x.1 x.2 := by
  subst e
  rw [← hD]
  exact h

/-- The piece's extractor: the table's, written out at D's own parameters. -/
noncomputable def extW (d₁ d₂ : RDT) (c₀ : CellsQ rws cls) (links : List ModelPart) (pl :
          VerifiableInference.Desc.Place) : P → Rec
    × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → Wq rws cls Tok → Wq rws cls Tok :=
  fun z a _ w => extAt D.cs D.G D.arr D.smp D.decT c₀ [] (minePadAt D.ms D.N links pl) false none
      (z, a.1) (strsOf F a.2) w

end

section
variable {P Tok XiD : Type} {rws cls nR : ℕ} {X : OnBytes.Model.Verify.Public} {r : SwRow} (D :
    MgData XiD P Tok rws cls nR X) (Rch : ℕ → (P × First.S) × F.E.Str → Prop) (h : r.ok = true) (iJ
    : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says h)).oM
    (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent) (iQ : ((rowsAt r
    (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says h)).oM
    (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent) (seat : Fin
    r.lo.length → ℕ × ℕ) (seatN : Fin r.l.length → ℕ × ℕ) (base : ℕ) (d₁ : RDT) (d₂ : RDT) (seats :
    List (ℕ × ℕ)) (c₀ : (CellsQ rws cls)) (d₀ : (Cb.Pv.SendLoc.stage (selZ (Letters.plain r
    (r.ok_says h)) iJ iQ).sw).X × (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ
    iQ).sw).Ex.Str) (y₀ : F.E.Str) (rowAt : ℕ → Option SwRow) (pAt : ℕ → K2.P2) (door : ℕ → First.S
    → Option First.S) (m : ℕ) (B : Block Rec Cl) (enter : Rec → Except String Rec) (leave : Rec →
    Rec → Except String Rec) (links : List ModelPart) (ps : List VerifiableInference.Desc.Place) (k : ℕ)
    (f₀ : _root_.Tw.K2.Front) (W : SwitchFrame) (n0 : ℕ) (grp : ℕ) (rows : ℕ) (olds : List ℕ) (L :
    Laid) (trees : ℕ) (news : List (ℕ × ℕ)) (b₀ : TB (Letters.plain r (r.ok_says h)) iJ iQ) (bq :
    Block (P × First.S) Cl) (extq : (P × First.S) × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → Wq rws
    cls Tok → Wq rws cls Tok) (pl : VerifiableInference.Desc.Place) (MO : List OracleShape) (LO :
    Laid) (Fk : P → ℕ → Rec → Prop)

/-- **THE SHORTER LIST.** -/
structure K2Short : Prop where
  /-- (a) A TIE TO THE WRITTEN VALUES: the typed structure's codes are the structure of parameters':
      K2's files', under the test madePinnedAt (entry test 9 asks its row): written_in_scope
          (K2Hands/WrittenInScope.lean), BY REPORT, NOT OPENED HERE; NOT JOINED
          (Where this and lean/THEOREM.md differ, the
          page holds.) -/
  cs : r.cs = D.cs
  /-- (a) WHOEVER CLOSES smp: it is the named reader at D's own codes and the list of tenants: so by
      the constant's own text -/
  named : D.smp = smpNamed D.cs seats
  /-- (a) A TEST WITH CODE ON THE TABLE: by the kernel at all 25 numbers (`said_full`,
      PubBehind.lean) -/
  said : saidBehindB links ps k = true
  /-- (a) A TEST WITH CODE ON THE TYPED STRUCTURE AND THE WRITTEN FRAME; in FtF's place (`fit_fam`,
      K2Caller/TieFourPays.lean) -/
  fit : fitAt r W = true
  /-- (a) THE PLAN's NUMBERS: as many numbers of kept old messages as kept members (evaluated once
      at the full size: so at all 25); in ho's place (`olds_at_frame`) -/
  oldsLen : olds.length = r.kept.length
  /-- (a) THE PLAN's NUMBERS: no new member's tenant is one whose pad is laid; in hE's place
      (`msgsOf_ext`, K2Caller/ExtMade.lean). BY REPORT, NOT OPENED:
      no_new_is_kept (declared nowhere in this library) -/
  newOff : ∀ i, seatN i ∉ (minePadAt D.ms D.N links pl).map seatOf
  /-- (a) THE TWO WRITTEN ROUNDS fit the typed structure: closed at the written entries -/
  w2 : K2Wr r d₁ d₂
  /-- (a) THE TABLE OF TYPED STRUCTURES: its entry m is r: closed at the written entries -/
  hrow : rowAt m = some r
  /-- (a) A TEST WITH CODE ON THE TYPED STRUCTURE: closed at the written entries -/
  hW : r.writtenOK = true
  /-- (a) as hW -/
  hz : r.sizedB = true
  /-- (a) A CLOSED FACT ON THE TYPED STRUCTURE: the target is 128 bits -/
  ht : r.set.target = 128
  /-- (c) K2's FILES' TO SHOW: the place's numbers are the typed structure's (`P2At`) -/
  hp : P2At r (pAt m)
  /-- (a) THE KIND's TEST ON THE LIST OF ROUNDS accepts -/
  hpl : (K2.codeSwitchKind (Cl := Unit) (pAt m)).planOk = true
  /-- (a) THE TWO WRITTEN ROUNDS have the declared entries -/
  he : [d₁, d₂].map (·.entry) = (K2.rounds (pAt m)).map (·.entry)
  /-- (a) and the declared kinds -/
  hk : ∀ d ∈ [d₁, d₂], Fmt.kindOf d.entry.name = some d.kind
  /-- (c) THE PLAN's NUMBERS: each new member's tree is one that the first written round sends -/
  hseat : ∀ i, base ≤ (seatN i).1 ∧ (seatN i).1 - base < d₁.trees.length
  /-- (c) THE PLAN's NUMBERS: no number of a kept old message stands twice (evaluated once at the
      full size: they rise) -/
  hnd : olds.Nodup
  /-- (a) A CLOSED FACT AT THE WRITTEN FRONT AND ITS FRAME (one of six) -/
  h0f : K2.frameAt f₀ = some W
  /-- (a) as h0f -/
  hcs : f₀.st.codes = r.cs
  /-- (a) as h0f -/
  hpub : frontPubB r.l.length f₀ = true
  /-- (a) as h0f -/
  hkA : r.keptAt W = true
  /-- (a) as h0f -/
  hbB : keptBitsB r W = true
  /-- (a) as h0f -/
  hsB : keptShapeB r = true
  /-- (a) A CLOSED FACT ON THE WRITTEN LIST: what the table's row closes. BY
      REPORT, NOT OPENED: SwitchRows (no declaration bears this name; several files do): by the
      kernel at the 25 numbers, with negative tests -/
  hins : (rowQ links ps k).ins = [.carry m, .pinKept m]
  /-- (a) A CLOSED FACT ON THE WRITTEN LIST: the row reads nothing: as hins -/
  hctx : (rowQ links ps k).ctx = []
  /-- (a) A CLOSED FACT ON THE WRITTEN LIST: the row opens the new sending's pin: as hins -/
  hoP : Item.pin (m + 1) 0 ∈ (rowQ links ps k).outs
  /-- (a) as hoP: the carried rows -/
  hoC : Item.row (m + 1) .carried ∈ (rowQ links ps k).outs
  /-- (a) as hoP: the rows on positions -/
  hoR : Item.row (m + 1) .position ∈ (rowQ links ps k).outs
  /-- (c) A CLOSED FACT ON THE WRITTEN LIST: the sampled tenants that are open behind are the index
      masks' and the new sending's; no payer known by name -/
  hsam : sampledIn D.N (openAt links ps (k + 1)) = D.N.index :: D.N.sent (m + 1) 0
  /-- (c) A CLOSED FACT ON THE WRITTEN LIST: the index masks' tenant is open in front (kin of
      `pinOpen_full`, FenceOf.lean) -/
  hidx : D.N.index ∈ sampledIn D.N (openAt links ps k)
  /-- (a) BY REPORT, NOT OPENED: seats_full (K2Caller/SeatFitsFull.lean):
      by the kernel at the full size, under one field of the constant's head (PlanOk.fit) -/
  hSF : ∀ κ : {a // (plainHd r (r.ok_says h)).cl a}, SeatFitAt D.G r.cs r.lo seat κ.1.1
  /-- (a) A TEST WITH CODE ON THE LIST OF ROUNDS (`keptSeatsB`): EVALUATED ONCE at the stored
      full-size public files: accepts at 24 switches with members, idly at the 25th; three negative
      tests reject -/
  hB : keptSeatsB D.G r.cs L seats trees r.lo seat r.kept olds = true
  /-- (a) THE TEST `keptAlignB` (P5T/KeptAlign.lean): both copies of a kept message have one number:
      EVALUATED ONCE: true at 24 and at 25; a negative test rejects -/
  hal : ∀ κ : {a // (plainHd r (r.ok_says h)).cl a}, ∃ v, news[1 + r.kept.idxOf κ.1.1.val]? = some v
      ∧ D.arr (seat κ.1.1).1 (seat κ.1.1).2 = D.arr v.1 v.2
  /-- (a) THE PLAN's NUMBERS: the new members' tenants are the listed ones. BY
      REPORT, NOT OPENED: by the kernel at the written values (K2Caller/ClosedAt25.lean) -/
  hN : ∀ (n : ℕ) (ho : 1 + n < r.l.length), news[1 + n]? = some (seatN ⟨_, ho⟩)
  /-- (a) THE PLAN's NUMBERS: no tenant whose pad is laid stands twice: as hAl -/
  hNd : ((minePadAt D.ms D.N links pl).map seatOf).Nodup
  /-- (a) THE PLAN's MEMBERS: the table's members at a kept tenant are the typed kept members, shape
      and radius. BY REPORT, NOT OPENED: held_at_plan
      (K2Caller/MembersAtHeld.lean) -/
  hAl : ∀ q ∈ D.N.keptOf m, (∃ x ∈ D.ms, SitsAt x q.1 q.2) ∧ ∀ x ∈ D.ms, SitsAt x q.1 q.2 → x ∈
      (minePadAt D.ms D.N links pl) ∧ ∃ κ : {a // (plainHd r (r.ok_says h)).cl a},
      VerifiableInference.Desc.Sound.Alike x ⟨⟨r.lo, seat⟩, κ.1.1⟩
  /-- (a) THE PLAN's MEMBERS, the other way round: each typed kept member has a member of the
      table's list that is alike it -/
  hAl_t1 : ∀ κ : {a // (plainHd r (r.ok_says h)).cl a}, ∃ q ∈ D.N.keptOf m, ∃ x ∈ D.ms, SitsAt x q.1
      q.2 ∧ VerifiableInference.Desc.Sound.Alike x ⟨⟨r.lo, seat⟩, κ.1.1⟩
  /-- (a) FOUR CLOSED CLAUSES ON LISTS (`K2.MembersLike`). BY REPORT, NOT
      OPENED: to follow from new_at_plan (K2Caller/MembersAtPlan.lean); NOT JOINED -/
  M : K2.MembersLike D.ms ⟨r.l, seatN⟩ (D.N.sent (m + 1) 0)
  /-- (a) K2's FILES': `caller_fam` (OnTopFacts.lean), at the maps of names off the written frame -/
  C : ∀ W₀, Renumbered W W₀ → CallerAt (selR (Letters.plain r (r.ok_says h))) r.cs r.l iJ iQ memK
      rowK (plK W₀) W₀
  /-- (a) K2's FILES': `keysFit_in_scope` -/
  hkeys : KeysFit (F := F) (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ
      D.G seatN base d₁ F) (pAt m) base idExt
  /-- (a) K2's FILES': `orcY_in_scope` (K2Hears/OrcAtFrame.lean): the file's columns are
      read by the tree's number, at the description's own list of trees and keys; NOT JOINED -/
  horc : ∀ y j, j < trees → ∀ x, K2.orcY F.all F.key y j x = y.col j x
  /-- (c) A FACT ON THE TEXT THAT READS A SEED (`K2.SeedReads`); its payer stands in
      Johnson/Top/H0/Tw/K2C/HeldAtPlace.lean's head -/
  hSR : SeedReads
  /-- (a) WHOEVER CLOSES decT: PAID AT THE CONSTANT (`decBlind_at`, AtConstant.lean) -/
  hd : DecBlind D.decT
  /-- (c) WHOEVER NAMES Rch: a reached state is one of the fold's family -/
  hFk : ∀ z (a : Rec × F.E.Str), Rch k ((z, a.1), a.2) → Fk z k a.1
  /-- (b) THE TABLE's TESTS ALONG THE FOLD, at this sub-protocol (`IM.HandsR`): three shares at
      the 25 places (Johnson/P1K2R/HandsShares.lean), at other files' key -/
  hHands : ∀ z, HandsR (Fk z) D.N links ps (EQ (mgAll D mgBase) links ps z) F.ft k B
  /-- (b) THE FOLD's SIDE, UNDER "REACHED": the first tie's content at the front that the text makes
      behind the way in: the test `frontB2`, the notices, two invariants' fruits, the same oracle
      messages: K2's FILES': foldSideR_one, _link, _head, _fin (P1K2R/FoldSideR.lean),
      in scope at all 25, under the written ties, the
      counts at written cuts and the listed shapes; NOT JOINED -/
  hT1 : ∀ z, ∀ a, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → (rchAtZ Rch z) k a → ¬
      a.1.failed ≠ none → ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt (pAt m) t = some fx → frontB2 f₀
      W grp rows n0 olds fx = true ∧ Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st
      ∧ storedB r (placeFrame W n0 olds) fx = true ∧ a.1.st.oracles = fx.st.oracles
  /-- (b) THREE FACTS ON REACHED STATES, BY NAME: bookInOrder (at the place's first tree),
      seatsCarried, bookFits, at the state behind the way in. BY REPORT, NOT
      OPENED: hBook3_of_fold (K2Caller/KeptMembersInBookAtFront.lean) -/
  hBook : ∀ z, ∀ a, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → (rchAtZ Rch z) k a → ¬
      a.1.failed ≠ none → ∀ t, enter a.1 = .ok t → VerifiableInference.Desc.K12.Door.atFirstBook
      (K2.par9 (pAt m)).firstTree t = true ∧ VerifiableInference.Desc.K12.Door.atFirstSeats L t =
      true ∧ VerifiableInference.Desc.K12.Door.atFirstFits t = true
  /-- (b) THE BOOK HAS A PLACE FOR EACH KEPT OLD MESSAGE, at the state behind the way in. BY
      REPORT, NOT OPENED: hOld_of_front (K2Caller/KeptMembersInBookAtFront.lean) -/
  hOld : ∀ z, ∀ a, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → (rchAtZ Rch z) k a → ¬
      a.1.failed ≠ none → ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt (pAt m) t = some fx → ∀ κ : {a
      // (plainHd r (r.ok_says h)).cl a}, (keptK2 r (r.ok_says h) (placeFrame W n0 olds) κ).old <
      t.book.place.size
  /-- (c) A FACT ON REACHED STATES, BY NAME: bookFits, in front AND behind: the second wants
      "reached" behind: it leans on the hand-on -/
  hBF : ∀ z a τ b, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (ownPiece (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq base d₁ d₂
      extq) B ((extW (F := F) D d₁ d₂ c₀ links pl) z) (k2ErrAt (F := F) h iJ iQ D.G seatN base d₁ d₂
      pAt m)).ior.red.out a τ = some b → BookFits a.1.book ∧ BookFits b.1.book
  /-- (b) K2's FILES': the carried claim's way in is the door: `doorZ_at_switch`
      (Johnson/Top/H0/K2Caller/CarryClosed.lean) -/
  hdoor : ∀ z, ∀ a, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → (rchAtZ Rch z) k a → ¬
      a.1.failed ≠ none → ∀ t, enter a.1 = .ok t → door m a.1 = some t
  /-- (b) THE PROMISE's OWN CLAUSE: every leaf of a kept tenant's tree is shown. BY
      REPORT, NOT OPENED: hsh_mgAll (K2Caller/KeptShownAt.lean) -/
  hsh : ∀ z, ∀ a, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none → ∀
      q ∈ D.N.keptOf m, shownJT r.cs D.G D.ms q.1 q.2 (strsOf F a.2)
  /-- (b) THE PROMISE's TWO CLAUSES at each kept tenant: every leaf is shown; no collision. BY
      REPORT, NOT OPENED: hsn_mgAll (K2Caller/KeptShownAt.lean) -/
  hsn : ∀ z, ∀ a, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none → ∀
      q ∈ D.N.keptOf m, shownJT r.cs D.G D.ms q.1 q.2 (strsOf F a.2) ∧ noCollJT r.cs D.G (smpNamed
      r.cs seats) D.ms q.1 q.2 (z, a.1) (strsOf F a.2)
  /-- (b) THE TABLE's READER OF OOD SAMPLES gives, at the new members behind, the typed sample up to
      the seed's values (`K2.SmpLike`). BY REPORT, NOT OPENED:
      smpLike_at_yes (Tw/K2C/SmpLikeNew.lean) under a test that ran true at 25 of 25 -/
  hσ : ∀ z, ∀ a τ b, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → (rchAtZ Rch z) k a →
      ¬ a.1.failed ≠ none → (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁
      d₂ (wordsMade iJ iQ D.G seatN base d₁ F) (pAt m) base idExt) B ((extW (F := F) D d₁ d₂ c₀
      links pl) z)).ior.red.out a τ = some b → K2.SmpLike r.cs (smpNamed (P := P) r.cs seats) (z,
      b.1) ⟨r.l, seatN⟩ (fun o => newSmp n0 b.1 o)
  /-- (c) AT EVERY ACCEPT: every leaf of the new members' trees is shown behind; its payer stands in
      Johnson/P1K2R/TieTwoR.lean's head -/
  hshN : ∀ z a τ b, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2)
      → ¬ a.1.failed ≠ none → (ownPiece (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq base d₁ d₂
      extq) B ((extW (F := F) D d₁ d₂ c₀ links pl) z) (k2ErrAt (F := F) h iJ iQ D.G seatN base d₁ d₂
      pAt m)).ior.red.out a τ = some b → ∀ i, ShownAt D.G r.cs r.l seatN (strsOf F b.2) i
  /-- (c) AT EVERY ACCEPT: the front's notices lay the new sending's tenants, each with an answer
      and a row; its payer stands in HeldAtPlace.lean's head -/
  hnew : ∀ z a τ b, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2)
      → ¬ a.1.failed ≠ none → (ownPiece (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq base d₁ d₂
      extq) B ((extW (F := F) D d₁ d₂ c₀ links pl) z) (k2ErrAt (F := F) h iJ iQ D.G seatN base d₁ d₂
      pAt m)).ior.red.out a τ = some b → ∀ t, enter a.1 = .ok t → ∃ (x : _root_.Tw.K2.Front) (lay :
      TreeLay) (n : Nat), K2.frontAt (pAt m) t = some x ∧ layTrees x.st.codes (switchNotices x.T
      x.others) = some lay ∧ sameMembers ((List.range n).map fun i => (t.book.trees.size +
      lay.tree.getD i 0, lay.part.getD i 0)) (D.N.sent (m + 1) 0) = true ∧ ∀ i, i < n → ∃ nt,
      (switchNotices x.T x.others)[i]? = some nt ∧ nt.shape.answers ≠ 0 ∧ 0 < nt.shape.mainRows +
      nt.shape.maskRows
  /-- (b) AT EVERY ACCEPT: the way out leaves the tables and the group's rows (`opened_keeps`,
      Johnson/Top/H0/Walk/FrameOpened.lean · `headOpenQ_kept` · `finishBehindQ_kept`,
      Johnson/Top/H0/K2Caller/DoorKeeps.lean), and `T3At`: its named fields, each with its payer in
      Johnson/Top/H0/Tw/K2C/TieThreeR.lean's head. Its field on where the new members sit speaks of
      the book BEHIND. It is bound at the piece's own views and shown columns, with the decision's
      own accept in hand -/
  hAt : ∀ z, ∀ a τ b, onQ D.N (mgAll D mgBase) links ps (fun s => (z, s)) k a → (rchAtZ Rch z) k a →
      ¬ a.1.failed ≠ none → (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁
      d₂ (wordsMade iJ iQ D.G seatN base d₁ F) (pAt m) base idExt) B ((extW (F := F) D d₁ d₂ c₀
      links pl) z)).ior.red.out a τ = some b → ∀ t t' x y S3 Y rws Gg c, enter a.1 = .ok t → leave
      a.1 t' = .ok b.1 → (vN d₂ τ.2.2.1 τ.2.2.2.1).drawn.poss.length = baseCount r.set .request r.g
      → K2.decideWith _root_.Tw.K2.sendByL8 (pAt m) t [vN d₁ τ.1 τ.2.1, vN d₂ τ.2.2.1 τ.2.2.2.1]
      (shownP (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ D.G seatN base d₁ F) (pAt
      m) base idExt (t, a.2) τ) = .ok t' → K2.AtYes (pAt m) t t' (vN d₁ τ.1 τ.2.1) (vN d₂ τ.2.2.1
      τ.2.2.2.1) (shownP (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ D.G seatN base
      d₁ F) (pAt m) base idExt (t, a.2) τ) x y S3 Y rws Gg c → K2.SameTables t'.st b.1.st ∧
      (b.1.st.groups[x.f.group]?).map (·.rows) = (t'.st.groups[x.f.group]?).map (·.rows) ∧ T3At
      (r.ok_says h) iJ iQ seatN D.N (m + 1) n0 grp b.1 x rws (vN d₂ τ.2.2.1 τ.2.2.2.1) Gg
  /-- (c) THE COMPOSED MEANING's FIELD carry, by unfolding at its filling (`mgAll_carry`); NOT
      JOINED -/
  hcar : ∀ z, ∀ s y w, carryK2 rowAt pAt door (K2.orcY F.all F.key) (fun r H => smpK2 r H) m (z, s)
      y w → (mgAll D mgBase).carry m (z, s) y w
  /-- (s) THE ROW ON WHERE THE KIND SITS: `Sits`, whole, over claims of the one-point type:
      `k02_sits_file` (Johnson/P1K2R/SitsDoor.lean) -/
  hS : Sits B (K2.codeSwitchKind (pAt m) : Block Rec Unit) enter leave
  /-- (s) K2's FILES': at all 25 places of the proof file's description (`k02_left_file`,
      Johnson/P1K2R/SitsLeft.lean); that a closed constant's chain is that description's: NOT JOINED
      -/
  leftDoor : LeftDoor enter leave
  /-- (s) THE ROW ON WHERE THE KIND SITS: the way out keeps what the law reads (`KeepsOut` at each
      door) -/
  hD : DoorKeeps (F := F) (Letters.plain r (r.ok_says h)) iJ iQ (pAt m) leave (fbOf (Letters.plain r
      (r.ok_says h)) iJ iQ n0 b₀ (fun _ i => isEmptyElim i) (strMadeB iJ iQ D.G seatN) (fun _ =>
      ((), ())))
  /-- (c) THE WAY IN LEAVES THE BOOK: by each door's text; no payer known by name -/
  hbk : ∀ s t, enter s = .ok t → t.book = s.book
  /-- (s) THE FIFTH TIE's DEBTS: `K2Owes` (T5.lean), each field with its payer there; at the closed
      constant: AtConstant.lean, FenceOf.lean, KeptOff.lean, Table.lean, Johnson/P1K2R/SitsLeft.lean
      -/
  O : ∀ z, K2Owes D mgBase links ps k z (ownPiece (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq
      base d₁ d₂ extq) B ((extW (F := F) D d₁ d₂ c₀ links pl) z) (k2ErrAt (F := F) h iJ iQ D.G seatN
      base d₁ d₂ pAt m)) (rchAtZ Rch z k) pl (m + 1) MO LO

variable {D Rch h iJ iQ seat seatN base d₁ d₂ seats c₀ d₀ y₀ rowAt pAt door m B enter leave links ps
    k f₀ W n0 grp rows olds L trees news b₀ bq extq pl MO LO Fk}

set_option maxHeartbeats 4000000 in
/-- **The shorter list gives the whole.** -/
theorem k2AllOwes_of_short (S : K2Short D Rch h iJ iQ seat seatN base d₁ d₂ seats c₀ rowAt pAt door
    m B enter leave links ps k f₀ W n0 grp rows olds L trees news b₀ bq extq pl MO LO Fk) :
    K2AllOwes Unit Unit D mgBase Rch h iJ iQ D.G seat seatN base d₁ d₂ (extW (F := F) D d₁ d₂ c₀
        links pl) D.arr seats D.decT c₀ rowAt pAt door m B enter leave links ps k D.ms (minePadAt
        D.ms D.N links pl) f₀ W n0 grp rows olds L trees news b₀ (smpNamed (P := P) r.cs seats) bq
        extq pl MO LO Fk :=
  {
    w2 := S.w2
    hrow := S.hrow
    hr := S.hS.rounds
    hs := S.hS.step
    hins := S.hins
    hctx := S.hctx
    hcar := S.hcar
    hpin := fun z q s y w => hpin_of_cs D mgBase S.cs seats S.named q (z, s) y w
    hdoor := S.hdoor
    hext := fun z a _ w => extAt_of_cs D S.cs seats S.named c₀ _ (z, a.1) (strsOf F a.2) w
    hE := fun z a _ w => (congrArg (msgsOf r.cs r.l seatN D.arr) (extAt_of_cs D S.cs seats S.named
        c₀ _ (z, a.1) (strsOf F a.2) w)).trans (msgsOf_ext r.cs D.G D.arr (smpNamed r.cs seats)
        D.decT c₀ r.l seatN _ none (z, a.1) (strsOf F a.2) w S.newOff)
    hnd := S.hnd
    h0f := S.h0f
    hcs := S.hcs
    hpub := S.hpub
    hkA := S.hkA
    hbB := S.hbB
    hsB := S.hsB
    C := S.C
    FtF := fun W₀ hW => fit_fam (r.ok_says h) S.hkA S.fit W₀ hW
    hpos := positions_pos S.hp S.hpl
    hT1 := S.hT1
    hSF := S.hSF
    hB := S.hB
    ho := olds_at_frame (r.ok_says h) S.hkA S.oldsLen
    hBook := S.hBook
    hOld := S.hOld
    horc := S.horc
    hal := S.hal
    hN := S.hN
    hNd := S.hNd
    hsh := S.hsh
    hAl := S.hAl
    hsn := S.hsn
    hAl_t1 := S.hAl_t1
    hW := S.hW
    hz := S.hz
    hp := S.hp
    he := S.he
    hk := S.hk
    hpl := S.hpl
    hseat := S.hseat
    hkeys := S.hkeys
    hD := S.hD
    hoP := S.hoP
    hoC := S.hoC
    hoR := S.hoR
    hpin3 := fun z q s y w => hpin3_of_cs D mgBase S.cs seats S.named q (z, s) y w
    hrowM := fun z c s y w => hrowM_paid D mgBase (m + 1) c (z, s) y w
    M := S.M
    hBy := smpNamed_bySeat r.cs seats
    hσ := S.hσ
    hAt := S.hAt
    ht := S.ht
    hextD := fun _ _ _ _ => rfl
    O := S.O
    hd := S.hd
    hHands := S.hHands
    hFk := S.hFk
    hsam := S.hsam
    hidx := S.hidx
    hshown := hshown_of_cs D mgBase S.cs
    hnc := hnc_of_cs D mgBase S.cs seats S.named
    hheld := hheld_paid D mgBase
    hSI := fun z a τ b ha hR hm hb x hx hs => smp_of_cs D S.cs seats S.named ((S.O z).smp a b.1 ⟨ha,
        hR, Classical.byContradiction hm⟩ ((S.O z).left a τ b hb) x hx hs)
    hshN := S.hshN
    hS := S.hS
    hin := S.leftDoor.1
    hout := S.leftDoor.2
    hbk := S.hbk
    hSR := S.hSR
    hBF := S.hBF
    hnew := S.hnew
    hPP := fun z _ _ b _ _ _ _ _ _ => pubP_behind D links ps k S.said (z, b.1) }

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.extAt_of_cs
#print axioms VerifiableInference.Desc.First.K2Caller.smp_of_cs
#print axioms VerifiableInference.Desc.First.K2Caller.k2AllOwes_of_short
