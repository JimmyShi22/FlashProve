-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/Assembly.lean: THE CODE SWITCH's THEOREMS AT A PLACE MEET IN ONE MEMBER OF THE
    STRUCTURE OF TIES WITH "REACHED" (`TiesAtR`, Johnson/Top/H0/Tw/K2C/TiedFormR.lean): EVERY FIELD
    IS A CALL. Seven definitions, one structure of Prop, two theorems. A law file: no sub-protocol
    imports it.

Why. Each field of `TiesAtR` has a theorem of its own. The structure asks
    that the condition in front, the promise behind and the two relations be THE SAME FOUR TERMS in
    all of them. Here Lean holds it.

What is said.
  `k2On`, `k2OnB`, `k2Rel`, `k2RelB`: the four terms, taken BY PROGRAM out of the statement of the
      law at a place (`k02_place2`, Johnson/Top/H0/K2Caller/PlaceLaw2.lean), at the closed held OOD
      samples.
  `k2Q`: a description's piece at a place of the kind, written out: two rounds, nothing behind, the
      error 2^-128 a round, the bits of proof of work counted in (how many:
      K2Caller/WrittenMeets.lean's head). `k2ErrAt`: the typed law's own error. `rchAtZ`: "reached",
      read at the state alone with the public part z laid back in.
  `K2AllOwes`: ALL THAT IS STILL OWED AT ONE PLACE, one field a debt, each with its payer. MADE BY
      PROGRAM: the binders of the five statements, merged by name. «K2's:»: the payer is K2's files.
  `k02_tiesAtR`: THE MEMBER. good := `k02_place2` · errLe := `k2_err_cap` (CapAt.lean) · lays :=
      `lays_of_ext` (Lays.lean) · t1 := `k02_t1R` (TieOneR.lean) · t2 := `k02_t2S`
      (Johnson/P1K2R/TieTwoS.lean) · t3 := `k02_t3R` (Johnson/Top/H0/Tw/K2C/TieThreeR.lean) · t4 :=
      `k02_t4R` (TieFourR.lean) · t5 := `k02_t5R_table` (T5.lean) · dec := `k02_dec`
      (DecAtMgAll.lean).
  `k02_tiedAtR`: so `TiedAtR` (Johnson/Desc/Sound/ChainOfPromisesR.lean) at that piece with the
      table's extractor, by `tiedAtR_of_ties`.
  THE NUMBERS: m is the carried claim's segment (the group in front); the segment that the switch
      opens is m + 1: so the second and the third tie are called at m + 1, and `K2Owes` at m + 1.
  The claims are the proof file's own type (`ProofFile.Cl`): the second tie stands there.

Limits. A SENTENCE WITH MANY PREMISES; NONE IS SHOWN MET HERE; NO MEMBER OF `K2AllOwes` IS SHOWN:
    nothing says that its fields can be met together. At Rch := never all is free. No soundness is
    claimed. «NOT OPENED» at a field: what is said of the file named is not from its text.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Top.H0.K2Caller.PlaceLaw2
import Johnson.Top.H0.K2Caller.TieOneR
import Johnson.Top.H0.K2Caller.TieFourR
import Johnson.Top.H0.K2Caller.CapAt
import Johnson.Top.H0.Tw.K2C.TieThreeR
import Johnson.Top.H0.Tw.K2C.TiedFormR
import Johnson.Top.H0.K2Ties.T5
import Johnson.Top.H0.K2Ties.DecAtMgAll
import Johnson.Top.H0.K2Ties.Lays
import Johnson.P1K2R.TieTwoS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb IOR
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim FileDescription Strs Wit Place smpHeld)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers sampledIn sameMembers)
open VerifiableInference.Desc.First.K2Hands
open VerifiableInference.Desc.First.K2 (ownPiece TiesAtR tiedAtR_of_ties MembersLike SmpLike
    SeedReads)
open VerifiableInference.Desc.First.K2Ties (Wq K2Owes DecBlind k02_t5R_table k02_dec Left
    lays_of_ext)
open H2K.JointK (Sits)
open ProofFile (Cl)
open IM (HandsR openAt)
open P1K2 (EQ pubAt)
open Johnson.G (smpTop aOfK keptBitsB keptShapeB storedB)
open _root_.Run (ckP)
open _root_.Tw.K2 (switchNotices)

variable {F : Frame}

/-- "Reached", read at the state alone with the public part z laid back in. -/
abbrev rchAtZ {P : Type} (Rch : ℕ → (P × First.S) × F.E.Str → Prop) (z : P) :
    ℕ → First.S × F.E.Str → Prop := fun k a => Rch k ((z, a.1), a.2)

/-- A description's piece at a place of the kind, written out. -/
noncomputable abbrev k2Q {P Cl W : Type} (bq : Block (P × First.S) Cl) (base : ℕ) (d₁ d₂ : RDT)
    (extq : (P × First.S) × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W → W) :
    Piece (ckP .two) F (P × First.S) Cl W :=
  ⟨bq, base, [d₁, d₂], [], extq, Err.cap 128 (uLT (ckP .two) [d₁, d₂])⟩

/-- The typed law's own error. -/
noncomputable abbrev k2ErrAt {Xi : Type} {r : SwRow} (h : r.ok = true) (iJ : ((rowsAt r (r.ok_says
    h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says h)).oM (Letters.plain r
    (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent) (iQ : ((rowsAt r (r.ok_says h)
    (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says h)).oM (Letters.plain r
    (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent) (G : FileDescription Xi) (seatN : Fin
           r.l.length → ℕ × ℕ) (base : ℕ) (d₁ d₂ : RDT) (pAt : ℕ → K2.P2) (m : ℕ) : Err (uLT (ckP .two)
           [d₁, d₂]) :=
  (k2Piece (F := F) (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G seatN
      base d₁ F) (pAt m) base idExt).err

/-- The condition in front. -/
def k2On {r : SwRow} (h : r.ok = true) (iJ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says
    h)).t₀ (Letters.plain r (r.ok_says h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J
    → (sigOf r.cs r.l).Ent) (iQ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀
    (Letters.plain r (r.ok_says h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q →
    (sigOf r.cs r.l).Ent) (base : ℕ) (d₁ : RDT) (d₂ : RDT) (d₀ : (Cb.Pv.SendLoc.stage (selZ
    (Letters.plain r (r.ok_says h)) iJ iQ).sw).X × (Cb.Pv.SendLoc.stage (selZ (Letters.plain r
    (r.ok_says h)) iJ iQ).sw).Ex.Str) (y₀ : F.E.Str) (pAt : ℕ → K2.P2) (m : ℕ) (enter : Rec → Except
    String Rec) (f₀ : _root_.Tw.K2.Front) (W : SwitchFrame) (n0 : ℕ) (grp : ℕ) (rows : ℕ) : Rec ×
    F.E.Str → Prop :=
  fun a => ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt (pAt m) t = some fx → (∃ olds : List ℕ,
      olds.Nodup ∧ frontB2 f₀ W grp rows n0 olds fx = true ∧ Tied r.l (switchNotices fx.T fx.others)
      ∧ K2.SampleGoodS fx.st ∧ storedB r (placeFrame W n0 olds) fx = true) ∧ ((K2.longFront (pAt m)
      t fx (K2.orcY F.all F.key (strsOf F a.2)) 0).isSome = true → switchTargetCheck fx.st fx.f.rows
      fx.T = true → KeptFree iJ iQ (strsTop iJ iQ (pAt m) (fun y => K2.orcS
      (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) (smpTop r (r.ok_says h) iJ iQ
      (baseCount r.set .request r.g) (smp₀ r (r.ok_says h))) d₀) (inXTop iJ iQ (pAt m) (fun y =>
      K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) (smpTop r (r.ok_says h) iJ iQ
      (baseCount r.set .request r.g) (smp₀ r (r.ok_says h))) d₀ y₀) (t, a.2))

/-- The promise behind. -/
def k2OnB {r : SwRow} (h : r.ok = true) (iJ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says
    h)).t₀ (Letters.plain r (r.ok_says h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J
    → (sigOf r.cs r.l).Ent) (iQ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀
    (Letters.plain r (r.ok_says h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q →
    (sigOf r.cs r.l).Ent) {Xi : Type} (G : FileDescription Xi) (seatN : Fin r.l.length → ℕ × ℕ) (n0 : ℕ)
    (b₀ : TB (Letters.plain r (r.ok_says h)) iJ iQ) : Rec × F.E.Str → Prop :=
  fun b => lawPb (Letters.plain r (r.ok_says h)) iJ iQ (fbOf (Letters.plain r (r.ok_says h)) iJ iQ
      n0 b₀ (fun _ i => isEmptyElim i) (strMadeB iJ iQ G seatN) (fun _ => ((), ())) b)

/-- The relation in front. -/
def k2Rel {Cells Tok : Type} {r : SwRow} (h : r.ok = true) (iJ : ((rowsAt r (r.ok_says h)
    (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says h)).oM (Letters.plain r
    (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent) (iQ : ((rowsAt r (r.ok_says h)
    (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says h)).oM (Letters.plain r
    (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent) (seatN : Fin r.l.length → ℕ × ℕ)
    (base : ℕ) (d₁ : RDT) (d₂ : RDT) (arr : ℕ → ℕ → ℕ) (d₀ : (Cb.Pv.SendLoc.stage (selZ
    (Letters.plain r (r.ok_says h)) iJ iQ).sw).X × (Cb.Pv.SendLoc.stage (selZ (Letters.plain r
    (r.ok_says h)) iJ iQ).sw).Ex.Str) (y₀ : F.E.Str) (pAt : ℕ → K2.P2) (m : ℕ) (enter : Rec → Except
    String Rec) : Rec × F.E.Str → Wit Cells Tok MsgT → Prop :=
  fun a w => ∀ t, enter a.1 = .ok t → ((Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ
      iQ).sw).S.over (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).A).relR
      (lawFa (Letters.plain r (r.ok_says h)) iJ iQ (strsTop iJ iQ (pAt m) (fun y => K2.orcS
      (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) (smpTop r (r.ok_says h) iJ iQ
      (baseCount r.set .request r.g) (smp₀ r (r.ok_says h))) d₀) (inXTop iJ iQ (pAt m) (fun y =>
      K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) (smpTop r (r.ok_says h) iJ iQ
      (baseCount r.set .request r.g) (smp₀ r (r.ok_says h))) d₀ y₀) (t, a.2)) (selBk (Letters.plain
      r (r.ok_says h)) iJ iQ (wtMade iJ iQ seatN arr w))

/-- The relation behind. -/
def k2RelB {Cells Tok : Type} {r : SwRow} (h : r.ok = true) (iJ : ((rowsAt r (r.ok_says h)
    (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says h)).oM (Letters.plain r
    (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent) (iQ : ((rowsAt r (r.ok_says h)
    (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says h)).oM (Letters.plain r
    (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent) {Xi : Type} (G : FileDescription Xi)
    (seatN : Fin r.l.length → ℕ × ℕ) (base : ℕ) (d₁ : RDT) (d₂ : RDT) (arr : ℕ → ℕ → ℕ) (d₀ :
    (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).X × (Cb.Pv.SendLoc.stage
    (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).Ex.Str) (y₀ : F.E.Str) (pAt : ℕ → K2.P2) (m :
    ℕ) (W : SwitchFrame) (n0 : ℕ) (grp : ℕ) (rows : ℕ) (b₀ : TB (Letters.plain r (r.ok_says h)) iJ
    iQ) : Rec × F.E.Str → Wit Cells Tok MsgT → Prop :=
  fun b w => ∀ W₀ : {V // Renumbered W V}, ∀ a, OnTop iJ iQ (pAt m) (fun y => K2.orcS
      (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) (smpTop r (r.ok_says h) iJ iQ
      (baseCount r.set .request r.g) (smp₀ r (r.ok_says h))) d₀ y₀ W₀.1 n0 grp rows (aOfK r
      (r.ok_says h)) (fun _ _ => 0) a → lawRb (Letters.plain r (r.ok_says h)) iJ iQ (pAt m) F.E.Str
      a (b.1, fbOf (Letters.plain r (r.ok_says h)) iJ iQ n0 b₀ (fun _ i => isEmptyElim i) (strMadeB
      iJ iQ G seatN) (fun _ => ((), ())) b) (wtMade iJ iQ seatN arr w)

section
variable {P Tok Xi XiD : Type} (Cl₀ Cl₁ : Type) {rws cls nR : ℕ} {X : OnBytes.Model.Verify.Public}
    {r : SwRow} (D : MgData XiD P Tok rws cls nR X) (Mg₀ : Meaning P (Wq rws cls Tok)) (Rch : ℕ → (P
    × First.S) × F.E.Str → Prop) (h : r.ok = true) (iJ : ((rowsAt r (r.ok_says h) (Letters.plain r
    (r.ok_says h)).t₀ (Letters.plain r (r.ok_says h)).oM (Letters.plain r (r.ok_says h)).oZ).keep
    r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent) (iQ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says
    h)).t₀ (Letters.plain r (r.ok_says h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q
    → (sigOf r.cs r.l).Ent) (G : FileDescription Xi) (seat : Fin r.lo.length → ℕ × ℕ) (seatN : Fin
           r.l.length → ℕ × ℕ) (base : ℕ) (d₁ : RDT) (d₂ : RDT) (ext : P → Rec × F.E.Str → Tr (uLT (ckP
           .two) [d₁, d₂]) → Wq rws cls Tok → Wq rws cls Tok) (arr : ℕ → ℕ → ℕ) (seats : List (ℕ × ℕ))
    (decT : (ℕ → Option (ℕ × List UInt64)) → P × VerifiableInference.Desc.First.S → Option (CellsQ
    rws cls)) (c₀ : (CellsQ rws cls)) (d₀ : (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says
    h)) iJ iQ).sw).X × (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).Ex.Str)
    (y₀ : F.E.Str) (rowAt : ℕ → Option SwRow) (pAt : ℕ → K2.P2) (door : ℕ → First.S → Option
    First.S) (m : ℕ) (B : Block Rec Cl) (enter : Rec → Except String Rec) (leave : Rec → Rec →
    Except String Rec) (links : List ModelPart) (ps : List Place) (k : ℕ) (ms : List Mem) (minePad : List
          Mem) (f₀ : _root_.Tw.K2.Front) (W : SwitchFrame) (n0 : ℕ) (grp : ℕ) (rows : ℕ) (olds : List ℕ)
    (L : Laid) (trees : ℕ) (news : List (ℕ × ℕ)) (b₀ : TB (Letters.plain r (r.ok_says h)) iJ iQ)
    (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf r.cs s.l).om i).Smp)
    (bq : Block (P × First.S) Cl) (extq : (P × First.S) × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) →
    Wq rws cls Tok → Wq rws cls Tok) (tokOf : P × First.S → Tok) (pl : Place) (MO : List
    OracleShape) (LO : Laid) (Fk : P → ℕ → Rec → Prop)

/-- **ALL THAT IS STILL OWED AT ONE PLACE OF THE CODE SWITCH, ONE FIELD A DEBT**, each with its
    payer. -/
structure K2AllOwes : Prop where
  /-- THE TWO WRITTEN ROUNDS fit the typed structure: closed at the written entries -/
  w2 : K2Wr r d₁ d₂
  /-- THE TABLE OF TYPED STRUCTURES: its entry m is r: closed at the written entries -/
  hrow : rowAt m = some r
  /-- THE ROW ON WHERE THE KIND SITS (K02_sits): the seated sub-protocol declares the kind's rounds
      -/
  hr : B.rounds = (K2.codeSwitchKind (Cl := Cl₀) (pAt m)).rounds
  /-- THE ROW ON WHERE THE KIND SITS: it sits on the kind's behind the door: the field step of
      `Sits` -/
  hs : SeatStep B (K2.codeSwitchKind (Cl := Cl₀) (pAt m)) enter leave
  /-- A CLOSED FACT ON THE WRITTEN LIST: what the table's row closes. AS REPORTED, NOT CHECKED HERE:
      SwitchRows of the shared chain: by the kernel at the 25 numbers, with negative tests -/
  hins : (rowQ links ps k).ins = [.carry m, .pinKept m]
  /-- A CLOSED FACT ON THE WRITTEN LIST: the row reads nothing: as hins -/
  hctx : (rowQ links ps k).ctx = []
  /-- THE COMPOSED MEANING's FIELD carry, by unfolding at its filling (`mgAll_carry`); NOT JOINED -/
  hcar : ∀ z, ∀ s y w, carryK2 rowAt pAt door (K2.orcY F.all F.key) (fun r H => smpK2 r H) m (z, s)
      y w → (mgAll D Mg₀).carry m (z, s) y w
  /-- THE COMPOSED MEANING's FIELD pin, by unfolding at its filling (`mgAll_pin`), where G, arr, ms
      and the reader of OOD samples are the filling's; NOT JOINED -/
  hpin : ∀ z, ∀ (q : ℕ × ℕ) s y w, pinJT r.cs G arr (smpNamed r.cs seats) ms q.1 q.2 (z, s) y w →
      (mgAll D Mg₀).pin q.1 q.2 (z, s) y w
  /-- K2's: the carried claim's way in is the door: `doorZ_at_switch`
      (Johnson/Top/H0/K2Caller/CarryClosed.lean) -/
  hdoor : ∀ z, ∀ a, onQ D.N (mgAll D Mg₀) links ps (fun s => (z, s)) k a → (rchAtZ Rch z) k a → ¬
      a.1.failed ≠ none → ∀ t, enter a.1 = .ok t → door m a.1 = some t
  /-- K2's: the piece's extractor is the table's, written out; with hlays -/
  hext : ∀ z, ∀ a τ w, (ext z) a τ w = extAt r.cs G arr (smpNamed r.cs seats) decT c₀ [] minePad
      false none (z, a.1) (strsOf F a.2) w
  /-- K2's: the extractor leaves the new members' messages: `msgsOf_ext` (ExtMade.lean), over "no
      new tenant is a kept one" (BY WORD ALONE, NOT OPENED: no_new_is_kept, not in this library) -/
  hE : ∀ z, ∀ a τ w, msgsOf r.cs r.l seatN arr ((ext z) a τ w) = msgsOf r.cs r.l seatN arr w
  /-- THE PLAN's NUMBERS: no number of a kept old message stands twice (evaluated once at the full
      size: they rise) -/
  hnd : olds.Nodup
  /-- A CLOSED FACT AT THE WRITTEN FRONT AND ITS FRAME (one of six) -/
  h0f : K2.frameAt f₀ = some W
  /-- as h0f -/
  hcs : f₀.st.codes = r.cs
  /-- as h0f -/
  hpub : frontPubB r.l.length f₀ = true
  /-- as h0f -/
  hkA : r.keptAt W = true
  /-- as h0f -/
  hbB : keptBitsB r W = true
  /-- as h0f -/
  hsB : keptShapeB r = true
  /-- K2's: `caller_fam` (OnTopFacts.lean), at the maps of names made off the written frame -/
  C : ∀ W₀, Renumbered W W₀ → CallerAt (selR (Letters.plain r (r.ok_says h))) r.cs r.l iJ iQ memK
      rowK (plK W₀) W₀
  /-- K2's: `fit_fam` (Johnson/Top/H0/K2Caller/TieFourPays.lean) -/
  FtF : ∀ W₀, Renumbered W W₀ → Fit r.cs r.l (plainR r (r.ok_says h)).s W₀ (memK (r := r) (H :=
      (r.ok_says h))) rowK (plK W₀)
  /-- K2's: `positions_pos` (TieFourPays.lean): the typed structure counts at least one position -/
  hpos : 0 < baseCount r.set .request r.g
  /-- THE FOLD's SIDE, UNDER "REACHED": the first tie's content at the front that the text makes
      behind the way in: the test `frontB2`, the notices, two invariants' fruits, the same oracle
      messages: K2's: foldSideR_one, _link, _head, _fin (Johnson/P1K2R/FoldSideR.lean),
      in scope at all 25, under the written ties, the
      counts at written cuts and the listed shapes; NOT JOINED -/
  hT1 : ∀ z, ∀ a, onQ D.N (mgAll D Mg₀) links ps (fun s => (z, s)) k a → (rchAtZ Rch z) k a → ¬
      a.1.failed ≠ none → ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt (pAt m) t = some fx → frontB2 f₀
      W grp rows n0 olds fx = true ∧ Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st
      ∧ storedB r (placeFrame W n0 olds) fx = true ∧ a.1.st.oracles = fx.st.oracles
  /-- BY REPORT, NOT OPENED: seats_full (K2Caller/SeatFitsFull.lean): by
      the kernel at the full size, under one field of the constant's head (PlanOk.fit) -/
  hSF : ∀ κ : {a // (plainHd r (r.ok_says h)).cl a}, SeatFitAt G r.cs r.lo seat κ.1.1
  /-- A TEST WITH CODE ON THE LIST OF ROUNDS (`keptSeatsB`): EVALUATED ONCE at the stored full-size
      public files: accepts at 24 switches with members, idly at the 25th; three negative tests
      reject -/
  hB : keptSeatsB G r.cs L seats trees r.lo seat r.kept olds = true
  /-- K2's: `olds_at_frame` (TieFourPays.lean) -/
  ho : ∀ κ : {a // (plainHd r (r.ok_says h)).cl a}, olds[r.kept.idxOf κ.1.1.val]? = some (keptK2 r
      (r.ok_says h) (placeFrame W n0 olds) κ).old
  /-- THREE FACTS ON REACHED STATES, BY NAME: bookInOrder (at the place's first tree), seatsCarried,
      bookFits, at the state behind the way in. BY REPORT, NOT OPENED:
      hBook3_of_fold (K2Caller/KeptMembersInBookAtFront.lean) -/
  hBook : ∀ z, ∀ a, onQ D.N (mgAll D Mg₀) links ps (fun s => (z, s)) k a → (rchAtZ Rch z) k a → ¬
      a.1.failed ≠ none → ∀ t, enter a.1 = .ok t → VerifiableInference.Desc.K12.Door.atFirstBook
      (K2.par9 (pAt m)).firstTree t = true ∧ VerifiableInference.Desc.K12.Door.atFirstSeats L t =
      true ∧ VerifiableInference.Desc.K12.Door.atFirstFits t = true
  /-- THE BOOK HAS A PLACE FOR EACH KEPT OLD MESSAGE, at the state behind the way in. BY
      REPORT, NOT OPENED: hOld_of_front (K2Caller/KeptMembersInBookAtFront.lean) -/
  hOld : ∀ z, ∀ a, onQ D.N (mgAll D Mg₀) links ps (fun s => (z, s)) k a → (rchAtZ Rch z) k a → ¬
      a.1.failed ≠ none → ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt (pAt m) t = some fx → ∀ κ : {a
      // (plainHd r (r.ok_says h)).cl a}, (keptK2 r (r.ok_says h) (placeFrame W n0 olds) κ).old <
      t.book.place.size
  /-- K2's: `orcY_in_scope` (Johnson/Top/H0/K2Hears/OrcAtFrame.lean): the file's columns are read by
      the tree's number, at the description's own list of trees and keys; NOT JOINED -/
  horc : ∀ y j, j < trees → ∀ x, K2.orcY F.all F.key y j x = y.col j x
  /-- THE TEST `keptAlignB` (KeptAlign.lean): both copies of a kept message have one number:
      EVALUATED ONCE: true at 24 and at 25; a negative test rejects -/
  hal : ∀ κ : {a // (plainHd r (r.ok_says h)).cl a}, ∃ v, news[1 + r.kept.idxOf κ.1.1.val]? = some v
      ∧ arr (seat κ.1.1).1 (seat κ.1.1).2 = arr v.1 v.2
  /-- THE PLAN's NUMBERS: the new members' tenants are the listed ones. BY WORD ALONE, NOT
      OPENED: by the kernel at the written values (K2Caller/ClosedAt25.lean) -/
  hN : ∀ (n : ℕ) (ho : 1 + n < r.l.length), news[1 + n]? = some (seatN ⟨_, ho⟩)
  /-- THE PLAN's NUMBERS: no tenant whose pad is laid stands twice: as hAl -/
  hNd : (minePad.map seatOf).Nodup
  /-- THE PROMISE's OWN CLAUSE: every leaf of a kept tenant's tree is shown. BY REPORT,
      NOT OPENED: hsh_mgAll (K2Caller/KeptShownAt.lean) -/
  hsh : ∀ z, ∀ a, onQ D.N (mgAll D Mg₀) links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none → ∀ q ∈
      D.N.keptOf m, shownJT r.cs G ms q.1 q.2 (strsOf F a.2)
  /-- THE PLAN's MEMBERS: the table's members at a kept tenant are the typed kept members, shape and
      radius. BY REPORT, NOT OPENED: held_at_plan
      (K2Caller/MembersAtHeld.lean) -/
  hAl : ∀ q ∈ D.N.keptOf m, (∃ x ∈ ms, SitsAt x q.1 q.2) ∧ ∀ x ∈ ms, SitsAt x q.1 q.2 → x ∈ minePad
      ∧ ∃ κ : {a // (plainHd r (r.ok_says h)).cl a}, VerifiableInference.Desc.Sound.Alike x ⟨⟨r.lo,
      seat⟩, κ.1.1⟩
  /-- THE PROMISE's TWO CLAUSES at each kept tenant: every leaf is shown; no collision. BY
      REPORT, NOT OPENED: hsn_mgAll (K2Caller/KeptShownAt.lean) -/
  hsn : ∀ z, ∀ a, onQ D.N (mgAll D Mg₀) links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none → ∀ q ∈
      D.N.keptOf m, shownJT r.cs G ms q.1 q.2 (strsOf F a.2) ∧ noCollJT r.cs G (smpNamed r.cs seats)
      ms q.1 q.2 (z, a.1) (strsOf F a.2)
  /-- THE PLAN's MEMBERS, the other way round: each typed kept member has a member of the table's
      list that is alike it -/
  hAl_t1 : ∀ κ : {a // (plainHd r (r.ok_says h)).cl a}, ∃ q ∈ D.N.keptOf m, ∃ x ∈ ms, SitsAt x q.1
      q.2 ∧ VerifiableInference.Desc.Sound.Alike x ⟨⟨r.lo, seat⟩, κ.1.1⟩
  /-- A TEST WITH CODE ON THE TYPED STRUCTURE: closed at the written entries -/
  hW : r.writtenOK = true
  /-- as hW -/
  hz : r.sizedB = true
  /-- K2's: the place's numbers are the typed structure's (`P2At`) -/
  hp : P2At r (pAt m)
  /-- THE TWO WRITTEN ROUNDS have the declared entries -/
  he : [d₁, d₂].map (·.entry) = (K2.rounds (pAt m)).map (·.entry)
  /-- and the declared kinds -/
  hk : ∀ d ∈ [d₁, d₂], Fmt.kindOf d.entry.name = some d.kind
  /-- THE KIND's TEST ON THE LIST OF ROUNDS accepts -/
  hpl : (K2.codeSwitchKind (Cl := Cl₁) (pAt m)).planOk = true
  /-- THE PLAN's NUMBERS: each new member's tree is one that the first written round sends -/
  hseat : ∀ i, base ≤ (seatN i).1 ∧ (seatN i).1 - base < d₁.trees.length
  /-- K2's: `keysFit_in_scope` -/
  hkeys : KeysFit (F := F) (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ
      G seatN base d₁ F) (pAt m) base idExt
  /-- THE ROW ON WHERE THE KIND SITS: the way out keeps what the law reads (`KeepsOut` at each door)
      -/
  hD : DoorKeeps (F := F) (Letters.plain r (r.ok_says h)) iJ iQ (pAt m) leave (fbOf (Letters.plain r
      (r.ok_says h)) iJ iQ n0 b₀ (fun _ i => isEmptyElim i) (strMadeB iJ iQ G seatN) (fun _ => ((),
      ())))
  /-- A CLOSED FACT ON THE WRITTEN LIST: the row opens the new sending's pin: as hins -/
  hoP : Item.pin (m + 1) 0 ∈ (rowQ links ps k).outs
  /-- as hoP: the carried rows -/
  hoC : Item.row (m + 1) .carried ∈ (rowQ links ps k).outs
  /-- as hoP: the rows on positions -/
  hoR : Item.row (m + 1) .position ∈ (rowQ links ps k).outs
  /-- THE COMPOSED MEANING's FIELD pin, the other way round (`mgAll_pin`); NOT JOINED -/
  hpin3 : ∀ z, ∀ (q : ℕ × ℕ) s y w, (mgAll D Mg₀).pin q.1 q.2 (z, s) y w → pinJT r.cs G arr smp ms
      q.1 q.2 (z, s) y w
  /-- THE COMPOSED MEANING's FIELD row (`mgAll_row`); NOT JOINED -/
  hrowM : ∀ z, ∀ c s y w, (mgAll D Mg₀).row (m + 1) c (z, s) y w → rowSays D.N (wordsAtFirst (P :=
      P) arr) (m + 1) c (z, s) y w
  /-- FOUR CLOSED CLAUSES ON LISTS (`K2.MembersLike`). BY WORD ALONE, NOT OPENED: to follow from
      new_at_plan (K2Caller/MembersAtPlan.lean); NOT JOINED -/
  M : K2.MembersLike ms ⟨r.l, seatN⟩ (D.N.sent (m + 1) 0)
  /-- `smpNamed_bySeat` (Johnson/Desc/Sound/SmpNamed.lean) -/
  hBy : SmpBySeat r.cs smp
  /-- THE TABLE's READER OF OOD SAMPLES gives, at the new members behind, the typed sample up to the
      seed's values (`K2.SmpLike`). BY REPORT, NOT OPENED: smpLike_at_yes
      (Tw/K2C/SmpLikeNew.lean) under a test that ran true at 25 of 25 -/
  hσ : ∀ z, ∀ a τ b, onQ D.N (mgAll D Mg₀) links ps (fun s => (z, s)) k a → (rchAtZ Rch z) k a → ¬
      a.1.failed ≠ none → (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂
      (wordsMade iJ iQ G seatN base d₁ F) (pAt m) base idExt) B (ext z)).ior.red.out a τ = some b →
      K2.SmpLike r.cs smp (z, b.1) ⟨r.l, seatN⟩ (fun o => newSmp n0 b.1 o)
  /-- AT EVERY ACCEPT: the way out leaves the tables and the group's rows (`opened_keeps`,
      Johnson/Top/H0/Walk/FrameOpened.lean · `headOpenQ_kept` · `finishBehindQ_kept`,
      Johnson/Top/H0/K2Caller/DoorKeeps.lean), and `T3At`: its named fields, each with its payer in
      Johnson/Top/H0/Tw/K2C/TieThreeR.lean's head. Its field on where the new members sit speaks of
      the book BEHIND. It is bound at the piece's own views and shown columns, with the decision's
      own accept in hand -/
  hAt : ∀ z, ∀ a τ b, onQ D.N (mgAll D Mg₀) links ps (fun s => (z, s)) k a → (rchAtZ Rch z) k a → ¬
      a.1.failed ≠ none → (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂
      (wordsMade iJ iQ G seatN base d₁ F) (pAt m) base idExt) B (ext z)).ior.red.out a τ = some b →
      ∀ t t' x y S3 Y rws Gg c, enter a.1 = .ok t → leave a.1 t' = .ok b.1 → (vN d₂ τ.2.2.1
      τ.2.2.2.1).drawn.poss.length = baseCount r.set .request r.g → K2.decideWith
      _root_.Tw.K2.sendByL8 (pAt m) t [vN d₁ τ.1 τ.2.1, vN d₂ τ.2.2.1 τ.2.2.2.1] (shownP
      (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G seatN base d₁ F) (pAt m) base
      idExt (t, a.2) τ) = .ok t' → K2.AtYes (pAt m) t t' (vN d₁ τ.1 τ.2.1) (vN d₂ τ.2.2.1 τ.2.2.2.1)
      (shownP (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G seatN base d₁ F) (pAt
      m) base idExt (t, a.2) τ) x y S3 Y rws Gg c → K2.SameTables t'.st b.1.st ∧
      (b.1.st.groups[x.f.group]?).map (·.rows) = (t'.st.groups[x.f.group]?).map (·.rows) ∧ T3At
      (r.ok_says h) iJ iQ seatN D.N (m + 1) n0 grp b.1 x rws (vN d₂ τ.2.2.1 τ.2.2.2.1) Gg
  /-- A CLOSED FACT ON THE TYPED STRUCTURE: the target is 128 bits -/
  ht : r.set.target = 128
  /-- K2's: the piece's extractor is the table's, written out at the structure's own parameters: no
      member's message, the members whose pads are laid, no cells, no token; with hext: the two say
      one thing where the place's parameters are the structure's. From it the field lays
      (`lays_of_ext`, Lays.lean) -/
  hextD : ∀ z a τ w, ext z a τ w = extAt D.cs D.G D.arr D.smp D.decT c₀ [] (minePadAt D.ms D.N links
      pl) false none (z, a.1) (strsOf F a.2) w
  /-- THE FIFTH TIE's DEBTS: `K2Owes` (T5.lean), each field with its payer there; at the closed
      constant: AtConstant.lean, FenceOf.lean, KeptOff.lean, Table.lean, Johnson/P1K2R/SitsLeft.lean
      -/
  O : ∀ z, K2Owes D Mg₀ links ps k z (ownPiece (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq
      base d₁ d₂ extq) B (ext z) (k2ErrAt (F := F) h iJ iQ G seatN base d₁ d₂ pAt m)) (rchAtZ Rch z
      k) pl (m + 1) MO LO
  /-- WHOEVER CLOSES decT: PAID AT THE CONSTANT (`decBlind_at`, AtConstant.lean) -/
  hd : DecBlind D.decT
  /-- THE TABLE's TESTS ALONG THE FOLD, at this sub-protocol (`IM.HandsR`): K2's three shares at the
      25 places (Johnson/P1K2R/HandsShares.lean), at a key of other files -/
  hHands : ∀ z, HandsR (Fk z) D.N links ps (EQ (mgAll D Mg₀) links ps z) F.ft k B
  /-- WHOEVER NAMES Rch: a reached state is one of the fold's family -/
  hFk : ∀ z (a : Rec × F.E.Str), Rch k ((z, a.1), a.2) → Fk z k a.1
  /-- A CLOSED FACT ON THE WRITTEN LIST: the sampled tenants that are open behind are the index
      masks' and the new sending's; no payer's name is known -/
  hsam : sampledIn D.N (openAt links ps (k + 1)) = D.N.index :: D.N.sent (m + 1) 0
  /-- A CLOSED FACT ON THE WRITTEN LIST: the index masks' tenant is open in front (kin of
      `pinOpen_full`, FenceOf.lean) -/
  hidx : D.N.index ∈ sampledIn D.N (openAt links ps k)
  /-- THE COMPOSED MEANING's FIELD shown, by unfolding at its filling; NOT JOINED -/
  hshown : ∀ j t y, (mgAll D Mg₀).shown j t y ↔ shownJT r.cs G ms j t y
  /-- THE COMPOSED MEANING's FIELD noColl, as hshown -/
  hnc : ∀ j t a y, (mgAll D Mg₀).noColl j t a y ↔ noCollJT r.cs G smp ms j t a y
  /-- THE COMPOSED MEANING's FIELD held, as hshown -/
  hheld : ∀ j t (a : P × Rec), (mgAll D Mg₀).held j t a = smpHeld a.2.st a.2.book j t
  /-- K2's: the field smp of `K2Owes` with `left`, where the reader and the members are the
      structure's own (`smp_of_named`, SmpLeft.lean); NOT JOINED -/
  hSI : ∀ z a τ b, onQ D.N (mgAll D Mg₀) links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) → ¬
      a.1.failed ≠ none → (ownPiece (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq base d₁ d₂
      extq) B (ext z) (k2ErrAt (F := F) h iJ iQ G seatN base d₁ d₂ pAt m)).ior.red.out a τ = some b
      → ∀ x ∈ ms, SitsAt x D.N.index.1 D.N.index.2 → smp (z, b.1) x.1 x.2 = smp (z, a.1) x.1 x.2
  /-- AT EVERY ACCEPT: every leaf of the new members' trees is shown behind; its payer stands in
      Johnson/P1K2R/TieTwoR.lean's head -/
  hshN : ∀ z a τ b, onQ D.N (mgAll D Mg₀) links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) → ¬
      a.1.failed ≠ none → (ownPiece (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq base d₁ d₂
      extq) B (ext z) (k2ErrAt (F := F) h iJ iQ G seatN base d₁ d₂ pAt m)).ior.red.out a τ = some b
      → ∀ i, ShownAt G r.cs r.l seatN (strsOf F b.2) i
  /-- THE ROW ON WHERE THE KIND SITS: `Sits`, whole, over claims of the one-point type:
      `k02_sits_file` (Johnson/P1K2R/SitsDoor.lean) -/
  hS : Sits B (K2.codeSwitchKind (pAt m) : Block Rec Unit) enter leave
  /-- K2's: PAID at all 25 places: `k02_left_file` (Johnson/P1K2R/SitsLeft.lean): the way in gives
      `Left` -/
  hin : ∀ s t, enter s = .ok t → Left s t
  /-- as hin: the way out -/
  hout : ∀ s t s', leave s t = .ok s' → Left t s'
  /-- THE WAY IN LEAVES THE BOOK: by each door's text; no payer's name is known -/
  hbk : ∀ s t, enter s = .ok t → t.book = s.book
  /-- A FACT ON THE TEXT THAT READS A SEED (`K2.SeedReads`); its payer stands in
      Johnson/Top/H0/Tw/K2C/HeldAtPlace.lean's head -/
  hSR : SeedReads
  /-- A FACT ON REACHED STATES, BY NAME: bookFits, in front AND behind: the second wants "reached"
      behind: it leans on the hand-on -/
  hBF : ∀ z a τ b, onQ D.N (mgAll D Mg₀) links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) → ¬
      a.1.failed ≠ none → (ownPiece (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq base d₁ d₂
      extq) B (ext z) (k2ErrAt (F := F) h iJ iQ G seatN base d₁ d₂ pAt m)).ior.red.out a τ = some b
      → BookFits a.1.book ∧ BookFits b.1.book
  /-- AT EVERY ACCEPT: the front's notices lay the new sending's tenants, each with an answer and a
      row; its payer stands in HeldAtPlace.lean's head -/
  hnew : ∀ z a τ b, onQ D.N (mgAll D Mg₀) links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) → ¬
      a.1.failed ≠ none → (ownPiece (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq base d₁ d₂
      extq) B (ext z) (k2ErrAt (F := F) h iJ iQ G seatN base d₁ d₂ pAt m)).ior.red.out a τ = some b
      → ∀ t, enter a.1 = .ok t → ∃ (x : _root_.Tw.K2.Front) (lay : TreeLay) (n : Nat), K2.frontAt
      (pAt m) t = some x ∧ layTrees x.st.codes (switchNotices x.T x.others) = some lay ∧ sameMembers
      ((List.range n).map fun i => (t.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0))
      (D.N.sent (m + 1) 0) = true ∧ ∀ i, i < n → ∃ nt, (switchNotices x.T x.others)[i]? = some nt ∧
      nt.shape.answers ≠ 0 ∧ 0 < nt.shape.mainRows + nt.shape.maskRows
  /-- K2's: PAID over the closed base: `pubP_behind` with `said_full` (PubBehind.lean): by the
      kernel at all 25 -/
  hPP : ∀ z a τ b, onQ D.N (mgAll D Mg₀) links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) → ¬
      a.1.failed ≠ none → (ownPiece (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq base d₁ d₂
      extq) B (ext z) (k2ErrAt (F := F) h iJ iQ G seatN base d₁ d₂ pAt m)).ior.red.out a τ = some b
      → (fun _ => k2OnB h iJ iQ G seatN n0 b₀) z b → b.1.failed = none → ∀ x ∈ pubAt (mgAll D Mg₀)
      links ps (k + 1), (mgAll D Mg₀).pubP x (z, b.1)

variable {Cl₀ Cl₁ D Mg₀ Rch h iJ iQ G seat seatN base d₁ d₂ ext arr seats decT c₀ d₀ y₀ rowAt pAt
    door m B enter leave links ps k ms minePad f₀ W n0 grp rows olds L trees news b₀ smp bq extq
    tokOf pl MO LO Fk}

/-- The field lays. -/
theorem K2AllOwes.hlays (A : K2AllOwes Cl₀ Cl₁ D Mg₀ Rch h iJ iQ G seat seatN base d₁ d₂ ext arr
    seats decT c₀ rowAt pAt door m B enter leave links ps k ms minePad f₀ W n0 grp rows olds L trees
    news b₀ smp bq extq pl MO LO Fk) : ∀ z a τ b w, (ownPiece (k2Q (P := P) (Cl := Cl) (W := Wq rws
    cls Tok) bq base d₁ d₂ extq) B (ext z) (k2ErrAt (F := F) h iJ iQ G seatN base d₁ d₂ pAt
    m)).ior.red.out a τ = some b → ext z a τ w = atPub (extQAt D.cs D.G D.arr D.smp D.ms D.decT c₀
    tokOf D.N links ps (fun x => x) k) z a b w :=
  fun z a τ b w hb => lays_of_ext D.cs D.G D.arr D.smp D.ms D.decT c₀ tokOf D.N links ps k pl (A.O
      z).place (A.O z).kind (fun z => (ownPiece (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq
      base d₁ d₂ extq) B (ext z) (k2ErrAt (F := F) h iJ iQ G seatN base d₁ d₂ pAt m))) A.hextD z a τ
      b w hb

set_option maxHeartbeats 8000000 in
/-- **They meet.** -/
theorem k02_tiesAtR (A : K2AllOwes Cl₀ Cl₁ D Mg₀ Rch h iJ iQ G seat seatN base d₁ d₂ ext arr seats
    decT c₀ rowAt pAt door m B enter leave links ps k ms minePad f₀ W n0 grp rows olds L trees news
    b₀ smp bq extq pl MO LO Fk) :
    TiesAtR D.N (mgAll D Mg₀) links ps Rch k (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq base
        d₁ d₂ extq) B (extQAt D.cs D.G D.arr D.smp D.ms D.decT c₀ tokOf D.N links ps (fun x => x) k)
        ext (k2ErrAt (F := F) h iJ iQ G seatN base d₁ d₂ pAt m) (fun _ => k2On h iJ iQ base d₁ d₂ d₀
        y₀ pAt m enter f₀ W n0 grp rows) (fun _ => k2OnB h iJ iQ G seatN n0 b₀) (fun _ => k2Rel h iJ
        iQ seatN base d₁ d₂ arr d₀ y₀ pAt m enter) (fun _ => k2RelB h iJ iQ G seatN base d₁ d₂ arr
        d₀ y₀ pAt m W n0 grp rows b₀) :=
  ⟨fun z => k02_place2 h A.hW A.hz iJ iQ G seatN base d₁ d₂ (pAt m) A.hp A.he A.hk A.hpl A.hseat
      (smp₀ r (r.ok_says h)) d₀ y₀ f₀ W n0 grp rows A.h0f A.hcs A.hpub A.hkA A.hbB A.hsB A.C A.hkeys
      b₀ B enter leave A.hr A.hs A.hD (ext z) arr (A.hE z) A.hpos,
    k2_err_cap h A.hW A.ht (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G seatN base
        d₁ F) A.w2 (pAt m) base idExt,
    A.hlays,
    fun z a ha hR hm => k02_t1R h iJ iQ G seat seatN base d₁ d₂ arr seats d₀ y₀ pAt m enter D.N
        (mgAll D Mg₀) links ps z (rchAtZ Rch z) k ms f₀ W n0 grp rows olds A.hnd A.h0f A.hcs A.hpub
        A.hkA A.hbB A.hsB A.FtF (A.hT1 z) L trees news A.hSF A.hB A.ho (A.hBook z) (A.hOld z) A.horc
        A.hal A.hN (A.hsn z) A.hAl_t1 a ha hR hm,
    k02_t2S A.hHands A.hFk (k02_dec D Mg₀ A.hd (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq
        base d₁ d₂ extq) B ext (k2ErrAt (F := F) h iJ iQ G seatN base d₁ d₂ pAt m)) A.hsam A.hidx iJ
        iQ G seatN n0 b₀ smp A.hshown A.hnc A.hheld A.M A.hBy (fun _ _ hb => hb) (fun z => (A.O
        z).base) A.hSI A.hσ A.hshN A.hS A.hin A.hout A.hbk A.hSR A.hBF A.hnew A.hPP,
    fun z a τ b w ha hR hm hb _ hw => k02_t3R h iJ iQ G seatN base d₁ d₂ A.w2 arr (pAt m) (fun y =>
        K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) (smpTop r (r.ok_says h) iJ
        iQ (baseCount r.set .request r.g) (smp₀ r (r.ok_says h))) d₀ y₀ (aOfK r (r.ok_says h)) (fun
        _ _ => 0) B enter leave A.hr A.hs (ext z) D.N (mgAll D Mg₀) links ps z (rchAtZ Rch z) k (m +
        1) A.hoP A.hoC A.hoR smp ms (A.hpin3 z) (A.hrowM z) A.M A.hBy n0 grp rows b₀ (Renumbered W)
        (A.hσ z) (A.hAt z) a τ b w ha hR hm hb hw,
    fun z a τ b w ha hR hm hb _ _ hRel => by
      have e := A.hlays (tokOf := tokOf) z a τ b w hb
      rw [← e] at hRel ⊢
      exact k02_t4R h iJ iQ G seat seatN base d₁ d₂ A.w2 arr seats decT c₀ d₀ y₀ rowAt pAt door m
          A.hrow B enter leave A.hr A.hs (ext z) D.N (mgAll D Mg₀) links ps z (rchAtZ Rch z) k
          A.hins A.hctx (A.hcar z) ms minePad (A.hpin z) (A.hdoor z) (A.hext z) (A.hE z) f₀ W n0 grp
          rows olds A.hnd A.h0f A.hcs A.hpub A.hkA A.hbB A.hsB A.C A.FtF A.hpos (A.hT1 z) L trees
          news A.hSF A.hB A.ho (A.hBook z) (A.hOld z) A.horc A.hal A.hN A.hNd (A.hsh z) A.hAl a τ b
          w ha hR hm hb hRel,
    fun z a τ b w i ha hR hm hb hon hall hi hin => k02_t5R_table (A.O z) c₀ tokOf a τ b w i ha hR hm
        hb hon hall hi hin,
    k02_dec D Mg₀ A.hd (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq base d₁ d₂ extq) B ext
        (k2ErrAt (F := F) h iJ iQ G seatN base d₁ d₂ pAt m)⟩

include d₀ y₀ in
/-- **So the description's piece is tied at the table of joints, with "reached".** hq: the piece
    holds the strict reading of B, lifted over the public part; hM: no accept at a marked state. -/
theorem k02_tiedAtR (A : K2AllOwes Cl₀ Cl₁ D Mg₀ Rch h iJ iQ G seat seatN base d₁ d₂ ext arr seats
    decT c₀ rowAt pAt door m B enter leave links ps k ms minePad f₀ W n0 grp rows olds L trees news
    b₀ smp bq extq pl MO LO Fk) (hq : bq = (below B).lift Prod.snd fun t s => (t.1, s)) (hM : ∀ a τ
    b, (ownPiece (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq base d₁ d₂ extq) B (fun _ _ w =>
    w) (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq base d₁ d₂ extq).err).ior.red.out a τ =
    some b → a.1.failed = none) :
    TiedAtR D.N (mgAll D Mg₀) links ps (fun a => a) Rch k ((k2Q (P := P) (Cl := Cl) (W := Wq rws cls
        Tok) bq base d₁ d₂ extq).withMap (extQAt D.cs D.G D.arr D.smp D.ms D.decT c₀ tokOf D.N links
        ps (fun x => x) k)) :=
  tiedAtR_of_ties D.N (mgAll D Mg₀) links ps Rch k (k2Q (P := P) (Cl := Cl) (W := Wq rws cls Tok) bq
      base d₁ d₂ extq) B hq (extQAt D.cs D.G D.arr D.smp D.ms D.decT c₀ tokOf D.N links ps (fun x =>
      x) k) ext (k2ErrAt (F := F) h iJ iQ G seatN base d₁ d₂ pAt m) _ _ _ _ hM (k02_tiesAtR (d₀ :=
      d₀) (y₀ := y₀) A)

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.K2AllOwes.hlays
#print axioms VerifiableInference.Desc.First.K2Caller.k02_tiesAtR
#print axioms VerifiableInference.Desc.First.K2Caller.k02_tiedAtR
