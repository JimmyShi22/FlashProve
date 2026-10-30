-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/RowTwoCand.lean: THE LAST CHAIN, BLOCK 2 (the proximity test on the request's own group): "THE ONE ROW THAT IS OWED" (TestGivesCand, Johnson/Desc/Sound/WordsLaw.lean) AT THE PIECE WHOSE BLOCK IS THE KIND K12's BLOCK AT A SEAT,
FROM THE KIND's LAW IN THE PLAIN FORM WITH A LETTER FOR WHAT IS CONCLUDED (k12_lawN, Johnson/Desc/K12/Coin/LawN.lean: the counted set asks that the round's test of work passes) AND NAMED PREMISES. A joining of two proved ends.

The piece. pieceTwo: the kind's piece at its own record T12 (pieceT) · seated in the chain's record S₃ by Block.inside (seated, Coin/Inside.lean) · with the test "below the prime" in front (Piece.under, Plain/LiftBelow.lean) · laid at the pair
(what the earlier chains left, S₃) by Piece.lift Prod.snd (LiftRule.lean): so its block is a member of the list that the rule of composition asks at a description: (F.second.blocksInOrder.map below).map (Block.lift Prod.snd …).
  pieceTwo_b: its block, to the letter. pieceTwo_out: WHERE IT PUTS OUT b: enter returned t; the kind's piece put out t' from t at the same oracles and transcript and left b's oracles; leave returned b's part; the first part is as it was.
  batAtN_mono: the batching's converse (BatAtN) is monotone in what is concluded, under Fixes.

The trick of the joining. k12_lawN holds AT EVERY LETTER N, and a plain law speaks statement by statement: so N may be chosen AT EACH OUTER STATEMENT a: candN a: "there is one tuple of candidates of mine at a, of which ins holds however it is laid":
the table's own tongue.

THE NAMED PREMISES. The theorems take structure RowTwoOwes: place · opens · NH (what the batching's converse in K12's files concludes: ONE letter) · bat (BatAtN at NH) · seam (NH under Fixes gives candN at the outer statement) · behind.
Structure RowTwoDebt is the elder form, with NH and seam split by a tuple θ in letters; RowTwoDebt.owes carries it over. Its fields, each with the files that are to pay it:
  place    AtPlace: the plan's side of the kind's law: K12's files.
  opens    FirstOpens at what enter returns, inside the promise: the files on FirstOpens.
  Θ, toC, SaysH, CandH: LETTERS for the either-arm of K12's files: a tuple θ (one message a member) of which "all rows say so of the tuple's tables" (SaysH) and "each is a candidate of the member's word as sent at its sample" (CandH); toC θ: the tuple in the
           library's types.
  bat      BatAtN at N := "there is such a θ": THE BATCHING's CONVERSE: K12's files (tuple_on_or_few, Johnson/Desc/K12/Law/TupleOn.lean, with the second arm priced at "BAT"'s round).
  cand     SEAM (s3): the candidate of K12's files is the table's CandAt (one notion of the word as sent: W0 F no D.book y against wordsOf G cs … y): K12's files with other files.
  rows     SEAMS (s4) | (s5): what the tuple's tables say of the rows at "begun" is ins of every witness in which the tuple is laid: items_iff_begun (Johnson/Desc/Means/ItemsBegun.lean) · the files on the term "words".
  behind   (s6) the promise behind the block, wherever the piece says yes: the table's files.
  **rowTwo_cand**: RowTwoOwes ⇒ TestGivesCand at pieceTwo. rowTwo_words: so WordsAreCommitted, where no two of mine have one number (by words_of_cand).
  pieceTwoX x: the piece with an extractor x; rowTwoX_cand: the row holds of it too. **rowTwo_goodIn**: at the row's own extractor (extAt … mine [] …): Piece.GoodIn: what the rule of composition asks of a block (by goodIn_of_words).
  ReadsMine, rows_of_one: the clause "rows" is asked at every witness in which the tuple is laid: where ins reads of a witness nothing but mine's messages and pads, one such witness is enough.

Silly members. mine := []: cand is for nothing; the row says "on' b, and ins a w' at every w' that agrees with w". SaysH := CandH := fun … => False: bat then asks that few challenges give a batched row with a near witness: the law's own silly letter.
A seat whose enter never returns: the piece never puts out: the row holds for nothing. ins := fun _ _ => True: rows is for nothing.
Every "there is", walked. candN: the tuple c: it is toC θ of the θ of K12's files. pieceTwo_out: t, t': what enter returns and what the kind's piece puts out: both are values of functions at a, τ.
Limits. A JOINING: NOTHING OF THE DEBT IS PAID HERE, and bat | seam (in the elder form: bat | cand | rows) hold the semantic weight. In RowTwoDebt Θ, SaysH, CandH are letters. pieceTwo's
extractor is the identity; pieceTwoX takes any. Nothing on soundness of its own; nothing on hiding.
(RowTwoOwes: the debt with the either-arm as one letter NH and one seam; the theorems take it; RowTwoDebt.owes carries the split form over.)
(pieceTwoX, rowTwoX_cand and rowTwo_goodIn stand AT ANY TYPE Cl OF CLAIMS: at a real description the pieces stand at the description's own Cl, not at Unit. The kind's law and pieceTwo stay at Unit: what a piece puts out does not read Cl: k12_alike · chainAt_alike (AnyClaims.lean) · pieceTwoX_out.)
(The piece is called pieceTwo | pieceTwoX: «rowTwo» is a theorem of RowTwoOwn.lean in this very namespace: the two could not be imported together.)

-/
import Johnson.Desc.Sound.WordsLaw
import Johnson.Desc.K12.Coin.LawN
import Johnson.Desc.Plain.LiftBelow
import Johnson.Flat.Last.AnyClaims

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles.Last
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Fo.Peel Cb Johnson.Pack
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open H2K.JointK H2K.Pub
open H2K.First (gpL Plain)

/-! ## 1 The batching's converse is monotone in what is concluded -/

theorem batAtN_mono {F : Frame} {π : P12} {no : ℕ → ℕ} {rad : Sg → ℕ} {rd : ℕ → ℕ} {dB : RDT} {e₀ : ℕ} {N₁ N₂ : ConclK F}
    {x : T12 × F.E.Str}
    (hm : ∀ a rest G0 Ly D, Fixes π x.1 a rest G0 Ly D → N₁ x a rest G0 Ly D → N₂ x a rest G0 Ly D)
    (h : BatAtN F π no rad rd dB e₀ N₁ x) : BatAtN F π no rad rd dB e₀ N₂ x := by
  intro a rest G0 Ly D row₀ hok hfix m
  refine le_trans (cnt_mono ?_) (h a rest G0 Ly D row₀ hok hfix m)
  rintro c ⟨hp, row, w, h1, h2, hn⟩
  exact ⟨hp, row, w, h1, h2, fun k => hn (hm a rest G0 Ly D hfix k)⟩

/-! ## 2 The piece -/

section
variable {Pp S₃ W : Type} (Fr : Frame) (π : P12) (base : ℕ) (dB : RDT) (dt : List RDT) (e₀ : ℕ)
  (εt : Err (uLT (ckP .two) dt)) (enter : S₃ → Except String T12) (leave : S₃ → T12 → Except String S₃)

/-- **Block 2's piece**: the kind's piece, seated, with the test "below the prime" in front, laid at the pair. -/
def pieceTwo : Piece (ckP .two) Fr (Pp × S₃) Unit W :=
  ((seated (pieceT Fr W π base dB dt e₀ εt) enter leave).under).lift Prod.snd fun t s => (t.1, s)

/-- Its block, to the letter: a member of the list that the rule of composition asks at a description. -/
theorem pieceTwo_b : (pieceTwo (Pp := Pp) (W := W) Fr π base dB dt e₀ εt enter leave).b =
    (below ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave)).lift Prod.snd fun t s => (t.1, s) := rfl

/-- The same piece AT ANY TYPE Cl OF CLAIMS (the kind's block makes no claim: its text is typed at a letter) and with an extractor x in the identity's place. What it puts out, its stretch, its base and its errors are pieceTwo's (pieceTwoX_out). -/
def pieceTwoX {Cl : Type} (x : (Pp × S₃) × Fr.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) : Piece (ckP .two) Fr (Pp × S₃) Cl W :=
  ⟨(below ((proximityTestKind guardedProximityTestParts π : Block T12 Cl).inside enter leave)).lift Prod.snd fun t s => (t.1, s), base, dB :: dt, [], x, (e₀, εt)⟩

theorem pieceTwoX_out {Cl : Type} (x : (Pp × S₃) × Fr.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) :
    (pieceTwoX (Cl := Cl) Fr π base dB dt e₀ εt enter leave x).ior.red.out = (pieceTwo (Pp := Pp) (W := W) Fr π base dB dt e₀ εt enter leave).ior.red.out := by
  have hrun : (pieceTwoX (Cl := Cl) Fr π base dB dt e₀ εt enter leave x).run = (pieceTwo (Pp := Pp) (W := W) Fr π base dB dt e₀ εt enter leave).run := by
    funext s v
    show (chainAt _ Fr.ft [(pieceTwoX (Cl := Cl) Fr π base dB dt e₀ εt enter leave x).b] s ⟨v.rounds ++ [], v.opened⟩).toOption =
      (chainAt _ Fr.ft [(pieceTwo (Pp := Pp) (W := W) Fr π base dB dt e₀ εt enter leave).b] s ⟨v.rounds ++ [], v.opened⟩).toOption
    have hA : (pieceTwoX (Cl := Cl) Fr π base dB dt e₀ εt enter leave x).b.Alike (pieceTwo (Pp := Pp) (W := W) Fr π base dB dt e₀ εt enter leave).b :=
      alike_lift _ _ (alike_below (alike_inside enter leave (k12_alike guardedProximityTestParts π)))
    rw [hA.1]
    exact congrArg Except.toOption (chainAt_alike hA _ Fr.ft s ⟨v.rounds ++ [], v.opened⟩)
  funext a τ
  show ((if sTests (ckP .two) (pieceTwo (Pp := Pp) (W := W) Fr π base dB dt e₀ εt enter leave).stage a.2 τ then
      (pieceTwoX (Cl := Cl) Fr π base dB dt e₀ εt enter leave x).run a.1
        (sView (ckP .two) (pieceTwo (Pp := Pp) (W := W) Fr π base dB dt e₀ εt enter leave).stage a.2 τ) else none).map
      fun xo => (xo, (pieceTwo (Pp := Pp) (W := W) Fr π base dB dt e₀ εt enter leave).ior.imp a.2 τ)) = _
  rw [hrun]

/-- **Where it puts out.** -/
theorem pieceTwo_out (a : (Pp × S₃) × Fr.E.Str) (τ : Iop.Tr (uLT (ckP .two) (dB :: dt))) (b : (Pp × S₃) × Fr.E.Str)
    (h : (pieceTwo (W := W) Fr π base dB dt e₀ εt enter leave).ior.red.out a τ = some b) :
    ∃ t t', enter a.1.2 = .ok t ∧ (pieceT Fr W π base dB dt e₀ εt).ior.red.out (t, a.2) τ = some (t', b.2) ∧
      leave a.1.2 t' = .ok b.1.2 ∧ b.1.1 = a.1.1 := by
  have e := liftOut (Pp × S₃) S₃ Unit W (ckP .two) Fr Prod.snd (fun t s => (t.1, s))
    (seated (pieceT Fr W π base dB dt e₀ εt) enter leave).under (fun _ _ => rfl) (fun _ _ _ => rfl) a τ
  obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 (e.symm.trans h)
  have h1 := under_out (seated (pieceT Fr W π base dB dt e₀ εt) enter leave) rfl (atPart Prod.snd a) τ b₀ hb₀
  obtain ⟨t, t', e1, e2, e3⟩ := seated_out (pieceT Fr W π base dB dt e₀ εt) enter leave (atPart Prod.snd a) τ b₀ h1
  exact ⟨t, t', e1, e2, e3, rfl⟩
end

/-! ## 3 The debt, and the row -/

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {Pp S₃ Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smp : (Pp × S₃) → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (Fr : Frame) (π : P12) (base : ℕ) (dB : RDT) (dt : List RDT) (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
  (enter : S₃ → Except String T12) (leave : S₃ → T12 → Except String S₃) (mine : List Mem)
  (on on' : (Pp × S₃) × Fr.E.Str → Prop) (ins : (Pp × S₃) × Fr.E.Str → Wit Cells Tok MsgT → Prop)

/-- What is concluded, chosen at the outer statement a: one tuple of candidates of which ins holds however it is laid. -/
def candN (a : (Pp × S₃) × Fr.E.Str) : Prop :=
  ∃ c : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg,
    (∀ x ∈ mine, CandAt cs G smp x a.1 (strsOf Fr a.2) (c x)) ∧ ∀ w w', LaidBy cs arr mine c w w' → ins a w'

/-- **The named premises.** -/
structure RowTwoDebt (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) where
  place : AtPlace Fr π num L mC mS mW rad base dB dt εt
  opens : ∀ a t, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) → enter a.1.2 = .ok t → FirstOpens π num no base t
  /-- the tuples of K12's files' either-arm: a letter -/
  Θ : Type
  /-- the tuple in the library's types -/
  toC : Θ → (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg
  /-- "all rows say so of the tuple's tables": a letter -/
  SaysH : T12 × Fr.E.Str → Fmt.M1.Stage → List Fmt.M1.Stage → Group → GroupLayout → Plain → Θ → Prop
  /-- "each is a candidate of the member's word as sent at its sample": a letter -/
  CandH : T12 × Fr.E.Str → Fmt.M1.Stage → List Fmt.M1.Stage → Group → GroupLayout → Plain → Θ → Prop
  bat : ∀ a t, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) → enter a.1.2 = .ok t →
    BatAtN Fr π no rad rd dB e₀ (fun x st rest G0 Ly D => ∃ θ, SaysH x st rest G0 Ly D θ ∧ CandH x st rest G0 Ly D θ) (t, a.2)
  cand : ∀ a t st rest G0 Ly D θ, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) → enter a.1.2 = .ok t →
    Fixes π t st rest G0 Ly D → CandH (t, a.2) st rest G0 Ly D θ → ∀ x ∈ mine, CandAt cs G smp x a.1 (strsOf Fr a.2) (toC θ x)
  rows : ∀ a t st rest G0 Ly D θ, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) → enter a.1.2 = .ok t →
    Fixes π t st rest G0 Ly D → SaysH (t, a.2) st rest G0 Ly D θ → ∀ w w', LaidBy cs arr mine (toC θ) w w' → ins a w'
  behind : ∀ a τ b, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) →
    (pieceTwo (W := Wit Cells Tok MsgT) Fr π base dB dt e₀ εt enter leave).ior.red.out a τ = some b → on' b

/-- **The same debt with the either-arm as ONE letter**: NH: what the batching's converse in K12's files concludes; seam: under Fixes it gives the table's own conclusion at the outer statement. (RowTwoDebt splits NH and seam by a tuple θ: RowTwoDebt.owes.) -/
structure RowTwoOwes (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) where
  place : AtPlace Fr π num L mC mS mW rad base dB dt εt
  opens : ∀ a t, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) → enter a.1.2 = .ok t → FirstOpens π num no base t
  NH : ConclK Fr
  bat : ∀ a t, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) → enter a.1.2 = .ok t → BatAtN Fr π no rad rd dB e₀ NH (t, a.2)
  seam : ∀ a t st rest G0 Ly D, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) → enter a.1.2 = .ok t →
    Fixes π t st rest G0 Ly D → NH (t, a.2) st rest G0 Ly D → candN cs G arr smp Fr mine ins a
  behind : ∀ a τ b, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) →
    (pieceTwo (W := Wit Cells Tok MsgT) Fr π base dB dt e₀ εt enter leave).ior.red.out a τ = some b → on' b

variable {cs G arr smp Fr π base dB dt e₀ εt enter leave mine on on' ins}

/-- The debt split by a tuple gives the debt with one letter. -/
def RowTwoDebt.owes {num : Fmt.TreeSource → ℕ} {no : ℕ → ℕ} {L mC mS mW : Sg → ℕ → ℕ} {rad : Sg → ℕ} {rd : ℕ → ℕ}
    (H : RowTwoDebt cs G arr smp Fr π base dB dt e₀ εt enter leave mine on on' ins num no L mC mS mW rad rd) :
    RowTwoOwes cs G arr smp Fr π base dB dt e₀ εt enter leave mine on on' ins num no L mC mS mW rad rd where
  place := H.place
  opens := H.opens
  NH := fun x st rest G0 Ly D => ∃ θ, H.SaysH x st rest G0 Ly D θ ∧ H.CandH x st rest G0 Ly D θ
  bat := H.bat
  seam := fun a t st rest G0 Ly D hon hpr he hfix ⟨θ, hs, hc⟩ =>
    ⟨H.toC θ, H.cand a t st rest G0 Ly D θ hon hpr he hfix hc, H.rows a t st rest G0 Ly D θ hon hpr he hfix hs⟩
  behind := H.behind

/-- **THE ONE ROW THAT IS OWED, AT BLOCK 2 OF THE LAST CHAIN.** -/
theorem rowTwo_cand {num : Fmt.TreeSource → ℕ} {no : ℕ → ℕ} {L mC mS mW : Sg → ℕ → ℕ} {rad : Sg → ℕ} {rd : ℕ → ℕ}
    (H : RowTwoOwes cs G arr smp Fr π base dB dt e₀ εt enter leave mine on on' ins num no L mC mS mW rad rd)
    (outs : (Pp × S₃) × Fr.E.Str → Wit Cells Tok MsgT → Prop) :
    TestGivesCand cs G arr smp (pieceTwo (W := Wit Cells Tok MsgT) Fr π base dB dt e₀ εt enter leave) mine on on' ins outs := by
  intro _ _ a hon hpr
  cases he : enter a.1.2 with
  | error e =>
    refine Doomed.of_forall _ _ fun τ b hb => ?_
    obtain ⟨t, _, h1, _⟩ := pieceTwo_out Fr π base dB dt e₀ εt enter leave a τ b hb
    rw [he] at h1
    cases h1
  | ok t =>
    have hB : BatAtN Fr π no rad rd dB e₀ (fun _ _ _ _ _ _ => candN cs G arr smp Fr mine ins a) (t, a.2) :=
      batAtN_mono (fun st rest G0 Ly D hfix hN => H.seam a t st rest G0 Ly D hon hpr he hfix hN) (H.bat a t hon hpr he)
    have hL := k12_lawN Fr (Wit Cells Tok MsgT) π num no L mC mS mW rad rd base dB dt e₀ εt
      (fun _ _ _ _ _ _ => candN cs G arr smp Fr mine ins a) H.place (t, a.2) ⟨H.opens a t hon hpr he, hB⟩
    refine Doomed.mono _ _ ?_ hL
    intro τ hτ b hb
    obtain ⟨t₁, t', h1, h2, _, _⟩ := pieceTwo_out Fr π base dB dt e₀ εt enter leave a τ b hb
    rw [he] at h1
    cases h1
    obtain ⟨_, _, _, _, _, _, c, hc, hi⟩ := hτ _ h2
    exact ⟨H.behind a τ b hon hpr hb, fun w _ => ⟨c, hc, fun w' hw' => hi w w' hw'⟩⟩

/-- So words are committed, where no two of mine have one number. -/
theorem rowTwo_words {num : Fmt.TreeSource → ℕ} {no : ℕ → ℕ} {L mC mS mW : Sg → ℕ → ℕ} {rad : Sg → ℕ} {rd : ℕ → ℕ}
    (H : RowTwoOwes cs G arr smp Fr π base dB dt e₀ εt enter leave mine on on' ins num no L mC mS mW rad rd)
    (decT : (ℕ → Option (ℕ × List UInt64)) → (Pp × S₃) → Option Cells) (c₀ : Cells)
    (outs : (Pp × S₃) × Fr.E.Str → Wit Cells Tok MsgT → Prop) (hN : (mine.map (numOf arr)).Nodup) :
    WordsAreCommitted cs G arr smp decT c₀ (pieceTwo (W := Wit Cells Tok MsgT) Fr π base dB dt e₀ εt enter leave) mine on on' ins outs :=
  words_of_cand cs G arr smp decT c₀ _ mine on on' ins outs hN (rowTwo_cand H outs)

/-- The row at the piece with any extractor: no clause of TestGivesCand reads the extractor. -/
theorem rowTwoX_cand {Cl : Type} {num : Fmt.TreeSource → ℕ} {no : ℕ → ℕ} {L mC mS mW : Sg → ℕ → ℕ} {rad : Sg → ℕ} {rd : ℕ → ℕ}
    (H : RowTwoOwes cs G arr smp Fr π base dB dt e₀ εt enter leave mine on on' ins num no L mC mS mW rad rd)
    (x : (Pp × S₃) × Fr.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (outs : (Pp × S₃) × Fr.E.Str → Wit Cells Tok MsgT → Prop) :
    TestGivesCand cs G arr smp (pieceTwoX (Cl := Cl) Fr π base dB dt e₀ εt enter leave x) mine on on' ins outs := by
  intro hS hF a hon hpr
  refine Doomed.mono _ _ ?_ (rowTwo_cand H outs hS hF a hon hpr)
  intro τ hτ b hb
  exact hτ b ((congrFun (congrFun (pieceTwoX_out (Cl := Cl) Fr π base dB dt e₀ εt enter leave x) a) τ).symm.trans hb)

/-- **WHAT THE RULE OF COMPOSITION ASKS OF BLOCK 2** (Piece.GoodIn), at the piece with the row's own extractor: between (on with the promise) and on', and between (the pins with ins) and outs. -/
theorem rowTwo_goodIn {Cl : Type} {num : Fmt.TreeSource → ℕ} {no : ℕ → ℕ} {L mC mS mW : Sg → ℕ → ℕ} {rad : Sg → ℕ} {rd : ℕ → ℕ}
    (H : RowTwoOwes cs G arr smp Fr π base dB dt e₀ εt enter leave mine on on' ins num no L mC mS mW rad rd)
    (decT : (ℕ → Option (ℕ × List UInt64)) → (Pp × S₃) → Option Cells) (c₀ : Cells)
    (outs : (Pp × S₃) × Fr.E.Str → Wit Cells Tok MsgT → Prop) (hN : (mine.map (numOf arr)).Nodup)
    (hS : SeatsFit cs G mine) (hF : Fenced base mine) :
    (pieceTwoX (Cl := Cl) Fr π base dB dt e₀ εt enter leave
        fun a _ w => extAt cs G arr smp decT c₀ mine [] false none a.1 (strsOf Fr a.2) w).GoodIn
      (fun a => on a ∧ Promised cs G smp mine a.1 (strsOf Fr a.2)) on'
      (fun a w => Pinned cs G arr smp mine a.1 (strsOf Fr a.2) w ∧ ins a w) outs :=
  goodIn_of_words cs G arr smp decT c₀ _ mine on on' ins outs hS hF (fun _ _ _ _ _ => rfl)
    (words_of_cand cs G arr smp decT c₀ _ mine on on' ins outs hN (rowTwoX_cand H _ outs))

/-- ins reads of a witness nothing but mine's messages and pads. -/
def ReadsMine (arr : ℕ → ℕ → ℕ) (mine : List Mem) (ins : (Pp × S₃) × Fr.E.Str → Wit Cells Tok MsgT → Prop) : Prop :=
  ∀ a w₁ w₂, (∀ x ∈ mine, w₁.msg (numOf arr x) = w₂.msg (numOf arr x)) →
    (∀ x ∈ mine, w₁.pad (x.1.seat x.2).1 (x.1.seat x.2).2 = w₂.pad (x.1.seat x.2).1 (x.1.seat x.2).2) → ins a w₁ → ins a w₂

/-- **How the clause "rows" is paid**: it is asked at EVERY witness in which the tuple is laid: where ins reads mine's components alone, ONE such witness is enough. -/
theorem rows_of_one (hR : ReadsMine arr mine ins) (a : (Pp × S₃) × Fr.E.Str) (c : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg)
    (w₀ : Wit Cells Tok MsgT) (hm : ∀ x ∈ mine, w₀.msg (numOf arr x) = toMsgT cs x.1.l x.2 (c x))
    (hp : ∀ x ∈ mine, w₀.pad (x.1.seat x.2).1 (x.1.seat x.2).2 = toMsgT cs x.1.l x.2 (c x)) (h₀ : ins a w₀) :
    ∀ w w', LaidBy cs arr mine c w w' → ins a w' := by
  intro w w' hl
  obtain ⟨_, _, l3, _, l5, _⟩ := hl
  exact hR a w₀ w' (fun x hx => (hm x hx).trans (l3 x hx).symm) (fun x hx => (hp x hx).trans (l5 x hx).symm) h₀

end

end VerifiableInference.OnPublicFiles.Last

#print axioms VerifiableInference.OnPublicFiles.Last.batAtN_mono
#print axioms VerifiableInference.OnPublicFiles.Last.pieceTwo_out
#print axioms VerifiableInference.OnPublicFiles.Last.rowTwo_cand
#print axioms VerifiableInference.OnPublicFiles.Last.rowTwo_words
#print axioms VerifiableInference.OnPublicFiles.Last.rowTwoX_cand
#print axioms VerifiableInference.OnPublicFiles.Last.rowTwo_goodIn
#print axioms VerifiableInference.OnPublicFiles.Last.rows_of_one
