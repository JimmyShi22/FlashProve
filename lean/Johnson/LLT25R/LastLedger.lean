-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastLedger.lean. A LAYER Y ON THE LAST CHAIN's OWN STATE
STANDS BESIDE THE BOOK-KEEPING (`besideS`, PlmCode.lean): e₃ concludes at `besideS (fillAt
… hand ended) Y`; the field seam may spend Y's yes at border 2; row0 is asked at the layer;
`LastRest` asks of Y three things (y12: one test at borders 1 and 2; y3, y4: yes of every state at 3
and 4). So a fact on that state which row 0's accepting run lays, and row 2 spends, need not be
asked of every statement inside the promise.

THE TWO LATER TABLES' OWN CONDITION Oc IS A LETTER: the
tables' files count them at `ocEnd … ∧ Rc`; `LastRest` asks of the letter two things:
ocIs (it gives `ocEnd …`) and ocBelow (it reads the strings below the last chain's first tree:
`OcReadsBelow`); every field's promise stands at Oc, so a payer has more in hand, not less.
`LastPlan` is cut into `LastPlan8` and K12's files' four tests · the twelve
tests stand in a structure of their own, `LastPlan`, which `LastRest` extends · the field seam
stands under a yes of the seated block · the law yesLays is no field of the structure: it is proved:
`ownYesLays`, LastYesLays.lean · the structure is cut in two, `LastRest` and `LastLeft`, which adds
row 0's · two lists of members, ms₁ the first table's and ms₂ the shared table's. THE LEDGER
OF THE LAST CHAIN's FIELD: ALL THAT IS STILL OWED FOR e₃ (the premise `EachLeads Pl.on₃ Pl.Q₃ 0 (p₃
:: l₃)` of the plain form's rule for a file, which gives the field `leads3_last_chains_table` of the
proof file's one structure of premises) AT THE PROOF FILE's OWN DESCRIPTION AND AT THE FILLINGS THAT
LIE, AS ONE STRUCTURE: one field a debt, with its payer in the field's own comment. The letters that
are laid. The description: FL (LastSeat.lean). The table's six: the numbers `tiedNumbers N₁
Ns`; the meaning `tiedMeaning get (meaningSig …) (meaningSigS …)`; the promise's meaning `promSigS
…`; (the table's files' fillings by signature); the slot's own condition Oc IS A LETTER, of which
ocIs and ocBelow are asked; the book-keeping `fillAt (p14At Z) (c2 N).rounds hand ended`;
ML is free. The pieces: the maker's cut of FL's own last chain at the extractors
`extsLast` and the cap's errors.
  `LastPlan8` with `LastPlan` (the twelve tests), `LastRest` (with six more: eighteen fields),
    `LastLeft` (row 0's beside): NINETEEN FIELDS. TWO ON THE LETTER Oc: ocIs, ocBelow. TWELVE TESTS,
    each a Bool, a comparison of numbers or a condition on the plan's finite lists: sampled, wIn,
    iIn, omega, nodup, seats, fence, placeB, joh, batOne, count, errs. TWO CONDITIONS OF MAKE, which
    no run can evaluate (each says "for every"): sits (paid from five tests at a closed smp and
    mine: LastMine.lean) and numbering (from one comparison at the numbering `numAt`:
    LastNum.lean). THREE LAWS: row0, opens, seam.
  `e3_of_left`: **e₃ from `LastLeft`, the flat list's equation and hds** (which `hds_of_planOk`,
    LastStretch.lean, pays from the data's yes and the tests on the plan).
What is spent: row 1: `rowOne_pure`; row 3: `rowThree_pure` (LastQuiet.lean); their two
conditions on the letters: `promReadsBelow_of`, `pinsReadBelow_of` (LastReads.lean) at ocBelow and
the table's
files' `readsTree_sig`, `pin₁_col_sig`; row 2: `rowTwo_own_of_cand`
(LastRowTwoOwn.lean) at `rowTwo_cand_gameY` (Desc/K12/Coin/CandYes.lean), `prom_sig`, `pins_sig`
(LastRowTwo.lean), `behind_fill` (LastBehind.lean) at `ownYesLays`; the table's files'
`leadsThreeAt`.
Limits. NO MEMBER OF `LastLeft` IS SHOWN: whether all its fields can be had together is not known.
hand, ended, get, the samples' readers and the numbers are letters: nothing says here that they are
the seated ones. First arm of the proximity test (the first fold's mask has come from outside).
Nothing on soundness.
-/
import Johnson.LLT25R.LastRowTwoOwn
import Johnson.LLT25R.LastRowTwo
import Johnson.LLT25R.LastQuiet
import Johnson.LLT25R.LastReads
import Johnson.LLT25R.LastBehind
import Johnson.LLT25R.LastYesLays
import Johnson.LLT25R.LastLayerS
import Johnson.Desc.K12.Coin.CandYes
import Johnson.Desc.Sound.ReadsBelowAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace LLT25
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Fo.Peel Cb
    Johnson.Pack
open Iop Prob _root_.Run
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn onOwn)
open VerifiableInference.Desc.Third (SharedOut)
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers openSets sampledIn start)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At)
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0)
open H2K.First (batOneOk)

/-- Agreement below a greater bound is agreement below a lesser. -/
theorem promReadsBelow_mono {S₂ P₁ : Type} (Nn : NumbersS) (Pm : PromMeaning S₂)
    (Oc : P₁ → Strs → Prop) {lo lo' : ℕ} (h : PromReadsBelow Nn Pm Oc lo) (hl : lo ≤ lo') :
    PromReadsBelow Nn Pm Oc lo' :=
  fun y y' hc hb => h y y' hc fun j x hj => hb j x (Nat.lt_of_lt_of_le hj hl)

/-- The like for the three pins. -/
theorem pinsReadBelow_mono {P S₁ S₂ S₃ Wt : Type} (Nn : NumbersS) (Mg : MeaningS S₂ (P × S₁) Wt)
    (ML : MeaningL S₃ Wt) {lo lo' : ℕ} (h : PinsReadBelow (S₃ := S₃) Nn Mg ML lo) (hl : lo ≤ lo') :
    PinsReadBelow (S₃ := S₃) Nn Mg ML lo' :=
  fun i hi p e s y y' w hc hb => h i hi p e s y y' w hc fun j x hj => hb j x (Nat.lt_of_lt_of_le hj
      hl)

/-- The last table's promise is monotone in the letter Oc. -/
theorem onQ₃_mono {P S₁ S₂ S₃' Wt : Type} {Fr : Frame} {Nn : NumbersS}
    {Mg : MeaningS S₂ (P × S₁) Wt} {Pm : PromMeaning S₂} {PL : PromMeaningL S₂ S₃' (P × S₁)}
    {Oc Oc' : P × S₁ → Strs → Prop} (h : ∀ q y, Oc q y → Oc' q y) {k : ℕ}
    {a : ((P × S₁ × S₂) × S₃') × Fr.E.Str} (ha : onQ₃ Nn Mg Pm PL Oc k a) :
    onQ₃ Nn Mg Pm PL Oc' k a :=
  ⟨h _ _ ha.1, ha.2⟩

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (A : SharedSeat) (N : H2U.Places4)
  (c : Chain S Cl) {Cells Tok P₀ : Type} (D : WholeD)
  (cs : OnBytes.Codes) {Xi' : Type} (G : FileDescription Xi') (arr : ℕ → ℕ → ℕ)
  (smp : (((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) × (FL o mk Z A N
      c).S₃) → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → (((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o
      mk Z A N c).S₂) × (FL o mk Z A N c).S₃) → Option Cells)
  (c₀' : Cells) (dB : RDT) (dt : List RDT) (mine : List Mem)
  (get : (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ → P₀ × First.S)
  (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (smp₂ : (FL o mk Z A N c).S₂ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om
      i).Smp)
  (ms₁ ms₂ : List Mem) (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ × First.S → Option Cells)
  (decT₂ : (ℕ → Option (ℕ × List UInt64)) → (FL o mk Z A N c).S₂ → Option Cells)
  (M₁ : Meaning P₀ (Wit Cells Tok MsgT)) (MS : MeaningS (FL o mk Z A N c).S₂ ((FL o mk Z A N
      c).XiPub × (FL o mk Z A N c).S₁) (Wit Cells Tok MsgT))
  (ML : MeaningL (FL o mk Z A N c).S₃ (Wit Cells Tok MsgT)) (stOf : (FL o mk Z A N c).S₂ →
      OnBytes.Statement)
  (bookOf : (FL o mk Z A N c).S₂ → OnBytes.TreeBook) (Pm₀ : PromMeaning (FL o mk Z A N c).S₂) (N₁ :
      Numbers) (Ns : NumbersS)
  (links : List ModelPart) (ps : List VerifiableInference.Desc.Place)
  (Oc : (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ → Strs → Prop)
  (Y : ℕ → (FL o mk Z A N c).S₃ → Bool)
  (hand : (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ → Option Handed) (ended : (FL o mk Z A N
      c).S₂ → Option SharedOut)
  (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rd : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ)

/-- **EIGHT TESTS** on the two tables' numbers, the lists of members and the place: each a Bool, a
comparison of numbers or a condition on the plan's finite lists. -/
structure LastPlan8 : Prop where
  /-- A TEST ON THE FIRST TABLE: every sampled seat that is open at its last border lies in a tree
  below the last chain's first. -/
  sampled : sampledBelow (D.t₁ + D.t₂) N₁ ((openSets links ps (start links))[ps.length]?.getD []) =
      true
  /-- A TEST ON THE FIRST TABLE: W's seat is among these. -/
  wIn : N₁.w ∈ sampledIn N₁ ((openSets links ps (start links))[ps.length]?.getD [])
  /-- A TEST ON THE FIRST TABLE: so is the index masks'. -/
  iIn : N₁.index ∈ sampledIn N₁ ((openSets links ps (start links))[ps.length]?.getD [])
  /-- A COMPARISON: Omega's tree lies below the last chain's first. -/
  omega : (Ns.tenant .oOmega).1 < D.t₁ + D.t₂
  /-- A TEST ON THE PLAN: no two of mine have one number. -/
  nodup : (mine.map (numOf arr)).Nodup
  /-- A TEST ON THE PLAN: the members' seats fit. -/
  seats : SeatsFit cs G mine
  /-- A TEST ON THE PLAN: they lie in trees sent in front of block 2. -/
  fence : Fenced (baseTwoAt (FL o mk Z A N c) D (c0 Z) (c1 N)) mine
  /-- A Bool: the tests on the place and on its stretch's data, together (`PlaceB`,
  Johnson/Desc/K12/Coin/BoolsTests.lean). PAYER of this and the next five: K12's files,
  by evaluation. -/
  placeB : PlaceB (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) (H2U.proximityTestParametersAt ⟨3, none, 2,
                                        .K12⟩ N.W) num (baseTwoAt (FL o mk Z A N c) D (c0 Z) (c1 N)) dB dt = true

/-- **THE TWELVE TESTS**: with K12's files' four on the place's codes and prices. -/
structure LastPlan : Prop extends LastPlan8 o mk Z A N c D cs G arr dB dt mine N₁ Ns links ps num
    where
  /-- A Bool: the test `johOk` on the place's stages at the radii r
  (Johnson/Desc/K12/Law/JohOk.lean). -/
  joh : johOk (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) r = true
  /-- A Bool: the place's first written round draws one element and no trits, at logN ≤ 64
  (`batOneOk`, Johnson/Desc/K12/Law/BatOneOk.lean). -/
  batOne : batOneOk (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) = true
  /-- A COMPARISON: `batV0` at the radii r, times the batching's round's w, is at most the cap's
  number for that round. -/
  count : batV0 (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) r * (bsRound .two dB.entry dB.kind).w ≤ capB dB
      dt
  /-- A COMPARISON, round by round: the errors behind the batching (`errJ`,
  Johnson/Desc/K12/Coin/GameJ.lean) are at most the cap's. -/
  errs : Err.le (errJ (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) r dt) (capT dB dt)

/-- **ALL THAT IS STILL OWED FOR e₃ AT THE PROOF FILE's OWN DESCRIPTION, BUT FOR ROW 0**: the twelve
tests, two conditions of make and two laws. -/
structure LastRest : Prop extends LastPlan o mk Z A N c D cs G arr dB dt mine N₁ Ns links ps num r
    where
  /-- ON THE LETTER Oc (the two later tables' own condition on what the first chain hands on): it
  gives
  the first chain's whole promise at its last border. -/
  ocIs : ∀ q y, Oc q y → ocEnd get N₁ (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) links ps q y
  /-- ON THE LETTER Oc: it reads the strings below the last chain's first tree. -/
  ocBelow : OcReadsBelow (D.t₁ + D.t₂) Oc
  /-- A CONDITION OF MAKE (LastRowTwo.lean): tests on the plan's members' seats, and three
  equations of samples at every state: the make of smp. PAYER: whoever lays smp: this folder's
  files, with the table's files. -/
  sits : MineSits cs smp smp₁ smp₂ ms₁ ms₂ mine get N₁ Ns
  /-- A CONDITION OF MAKE, at every n: the numbering of the block's own trees begins at its base:
  the make of num. -/
  numbering : ∀ n, num (.own ((H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.free + n)) = (baseTwoAt (FL o
                          mk Z A N c) D (c0 Z) (c1 N)) + n
  /-- A LAW. What the first switch's round opens, at what the seat's door returns, inside the
  promise. PAYER: the files on FirstOpens. -/
  opens : ∀ a t, (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber))
      (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G
      arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2
          N).rounds
      hand ended) Oc 2) a → Promised cs
      G smp mine a.1 (strsOf (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) a.2) →
      enterOwn a.1.2 = .ok t → FirstOpens (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) num no (baseTwoAt (FL o
                          mk Z A N c) D (c0 Z) (c1 N)) t
  /-- A LAW. THE SEAM: what the game concludes (one tuple near the group's word) gives the table's
  own conclusion at the outer statement, WHERE THE SEATED BLOCK SAYS YES AT SOME ROUNDS. It is cut
  to
  plain facts in LastSeamEnds.lean. -/
  seam : ∀ a t st rest G0 Ly D', (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z A N
      c).lastChainFirstTreeNumber)) (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁)
                    (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillAt
                    (p14At Z) (c2 N).rounds hand ended) Oc 2) a → Y 2 a.1.2 = true → Promised cs G smp mine a.1
          (strsOf (frameAt D
          (allOf D) D.key₃ (FL o mk Z A N
      c).lastChainFirstTreeNumber) a.2) → enterOwn a.1.2 = .ok t → Fixes (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) t st
      rest G0 Ly D' → NTuple (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) (H2U.proximityTestParametersAt
                    ⟨3, none, 2, .K12⟩ N.W) no (fun s => r s.st) rd (t, a.2) st rest G0 Ly D' → (∃ rs gs s',
                    (onOwn (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 Cl)).decide a.1.2 rs gs =
                    .ok s') → candN cs G arr smp (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) mine
      (fun a w => ML.rows a.1.2 w) a
  /-- ON THE LAYER Y: at borders 1 and 2 it is one test. -/
  y12 : ∀ s, Y 2 s = Y 1 s
  /-- ON THE LAYER Y: at border 3 it says yes of every state. -/
  y3 : ∀ s, Y 3 s = true
  /-- ON THE LAYER Y: at border 4 too. -/
  y4 : ∀ s, Y 4 s = true

/-- **ALL THAT IS STILL OWED FOR e₃ AT THE PROOF FILE's OWN DESCRIPTION.** -/
structure LastLeft : Prop extends LastRest o mk Z A N c D cs G arr smp dB dt mine get smp₁
    smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS ML stOf bookOf Pm₀ N₁ Ns links ps Oc Y hand ended num no rd r
        where
  /-- A LAW. ROW 0 (K14's second part): its own law between {rows} and {ev, dot}, and what rides is
  kept. PAYER: row 0's files. -/
  row0 : RowZeroOwed (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁)
      (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (besideS
          (fillAt (p14At Z) (c2 N).rounds hand ended) Y) Oc (pieceZeroAt (FL o mk Z A N c) D (c0 Z)
          (restCap
          (extsLast (Tok := Tok) (FL o mk Z A N c)
      D cs G arr smp decT c₀' mine)))

variable (a₁ : Block (FL o mk Z A N c).S₁ (FL o mk Z A N c).Cl) (k₁ : List (Block (FL o mk Z A N
    c).S₁ (FL o mk Z A N c).Cl))
  (a₂ : Block (FL o mk Z A N c).S₂ (FL o mk Z A N c).Cl) (k₂ : List (Block (FL o mk Z A N c).S₂ (FL
      o mk Z A N c).Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) ((FL o mk Z A
      N c).XiPub × (FL o mk Z A N c).S₁) (Wit Cells Tok MsgT) ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0) (((FL o mk Z A
      N c).XiPub × (FL o mk Z A N c).S₁) × (FL o mk Z A N c).S₂) (Wit Cells Tok MsgT) ds)
  (d wEnd : Wit Cells Tok MsgT)

variable {o mk Z A N c D cs G arr smp decT c₀' dB dt mine get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS ML
    stOf
    bookOf Pm₀ N₁ Ns links ps Oc Y hand ended num no rd r}

/-- The promise's two parts that read the strings read them below the last chain's first tree. -/
theorem LastRest.promReads (L : LastRest o mk Z A N c D cs G arr smp dB dt mine get smp₁
    smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS ML stOf bookOf Pm₀ N₁ Ns links ps Oc Y hand ended num no rd r) :
    PromReadsBelow (tiedNumbers N₁ Ns) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) Oc (D.t₁ + D.t₂) :=
  promReadsBelow_of (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁)
      (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) Oc
    L.ocBelow
    (readsTree_sig cs G arr smp₂ ms₂ decT₂ stOf bookOf MS Pm₀) L.omega

/-- The three pins read them below it too. -/
theorem LastRest.pinsRead (L : LastRest o mk Z A N c D cs G arr smp dB dt mine get smp₁
    smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS ML stOf bookOf Pm₀ N₁ Ns links ps Oc Y hand ended num no rd r) :
    PinsReadBelow (S₃ := (FL o mk Z A N c).S₃) (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G
        arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML (D.t₁ + D.t₂) :=
  pinsReadBelow_of (tiedNumbers N₁ Ns) ML (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (tiedMeaning get
      (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G arr smp₂ ms₂ decT₂ MS))
    (readsTree_sig cs G arr smp₂ ms₂ decT₂ stOf bookOf MS Pm₀)
    (fun j t q y y' w hc hp => pin₁_col_sig cs G arr smp₁ ms₁ decT₁ M₁ get _ j t q y y' w hc hp)
    (of_decide_eq_true (List.all_eq_true.1 L.sampled _ L.wIn))
    (of_decide_eq_true (List.all_eq_true.1 L.sampled _ L.iIn)) L.omega

/-- **THE LAST CHAIN's FIELD IN THE TABLES' FILES' OWN FORM (`EachOwn`), FROM THE LEDGER.** -/
theorem own3_of_left (L : LastLeft o mk Z A N c D cs G arr smp decT c₀' dB dt mine get smp₁ smp₂ ms₁
    ms₂ decT₁ decT₂ M₁ MS ML stOf bookOf Pm₀ N₁ Ns links ps Oc Y hand ended num no rd r) (b₀ : Block
    (FL o mk Z A N c).S₃ (FL o mk Z A N c).Cl) (l : List (Block (FL o mk Z A N c).S₃ (FL o mk Z A N
    c).Cl)) (hflat : (FL o mk Z A N c).second.blocksInOrder = b₀ :: l) (hds : ds₂ D.ds₃ (held (P := (FL o mk
             Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) (c0 Z)) (held (P := (FL o mk Z A N
             c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) (c1 N)) (held (P := (FL o mk Z A N
             c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) (c2 N)) = dB :: dt) : EachOwn (onQ₃ (Fr
             := frameAt D (allOf D) D.key₃ (atDesc (FL o mk Z A N c) (piecesAt (ckP .two) (FL o mk Z A N c) D
             a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z A N c) D cs G arr smp
             decT c₀' mine)) d wEnd)).ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁
             decT₁ M₁) (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀)
             (besideS (fillAt (p14At Z) (c2 N).rounds hand ended) Y) Oc) (meansQ₃ (tiedNumbers N₁ Ns)
             (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G arr smp₂ ms₂ decT₂
             MS)) ML) insQ₃ outsQ₃ (· ∈ startLast) 0 ((atDesc (FL o mk Z A N c) (piecesAt (ckP .two) (FL o mk
             Z A N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z A N c) D cs G
             arr smp decT c₀' mine)) d wEnd)).p₃ :: (atDesc (FL o mk Z A N c) (piecesAt (ckP .two) (FL o mk Z
             A N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z A N c) D cs G
             arr smp decT c₀' mine)) d wEnd)).l₃) := by
  have le₁ : D.t₁ + D.t₂ ≤ (pieceOneAt (FL o mk Z A N c) D (c0 Z) (c1 N) (restCap (extsLast (Tok :=
      Tok) (FL o mk Z A N c) D cs G arr smp decT c₀' mine))).base := Nat.le_add_right _ _
  have le₂ : D.t₁ + D.t₂ ≤ (baseTwoAt (FL o mk Z A N c) D (c0 Z) (c1 N)) := Nat.le_trans
      (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have le₃ : D.t₁ + D.t₂ ≤ (pieceThreeAt (FL o mk Z A N c) D (c0 Z) (c1 N) (c2 N) (c3 Z N) (restCap
      (extsLast (Tok := Tok) (FL o mk Z A N c) D cs G arr smp decT c₀' mine))).base :=
    Nat.le_trans le₂ (Nat.le_add_right _ _)
  have h₁ := rowOne_pure o mk Z A N c D cs G arr smp decT c₀' mine (tiedNumbers N₁ Ns) (tiedMeaning
      get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML
      (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) Oc (p14At Z) hand ended
    (promReadsBelow_mono _ _ _ L.toLastRest.promReads le₁) (pinsReadBelow_mono _ _ _
        L.toLastRest.pinsRead le₁)
  have h₃ := rowThree_pure o mk Z A N c D (restCap (extsLast (Tok := Tok) (FL o mk Z A N c) D cs G
      arr smp decT c₀' mine)) (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁
      decT₁ M₁) (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀)
      Oc (p14At Z) (c2 N).rounds hand
      ended
    (promReadsBelow_mono _ _ _ L.toLastRest.promReads le₃)
  have pr : ∀ k a, onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber))
      (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G
      arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (besideS (fillAt (p14At Z)
      (c2 N).rounds hand ended) Y) Oc k a → onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z A N
      c).lastChainFirstTreeNumber)) (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁)
                    (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillAt
                    (p14At Z) (c2 N).rounds hand ended) Oc k a ∧ Y k a.1.2 = true := fun k a => (onQ₃_besideS
                    (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G
                    arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2
                    N).rounds hand ended) Oc Y k a).1
  have hC := rowTwo_cand_gameY (Cl := (FL o mk Z A N c).Cl) cs G arr smp (frameAt D (allOf D) D.key₃
      (FL o mk Z A N c).lastChainFirstTreeNumber) (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) (baseTwoAt (FL o mk Z A N c)
                                        D (c0 Z) (c1 N)) dB dt (capB dB dt) (capT dB dt) enterOwn leaveOwn mine
    (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber)) (tiedNumbers N₁ Ns)
        (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G arr smp₂ ms₂
        decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (besideS (fillAt (p14At Z) (c2 N).rounds
        hand ended) Y) Oc 2) (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber))
        (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs
        G arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (besideS (fillAt (p14At
        Z) (c2 N).rounds hand ended) Y) Oc 3) (fun a w => ML.rows a.1.2 w) num no rd r
        (fun a _ w => extAt cs G arr smp decT c₀' mine [] false none a.1 (strsOf (frameAt D (allOf
            D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) a.2) w)
    L.placeB L.numbering L.joh L.batOne L.count L.errs (fun a t hon hP ht => L.opens a t (pr 2 a
        hon).1 hP ht)
    (fun a t st rest G0 Ly D' τ b hon hP ht hf hN hb =>
      L.seam a t st rest G0 Ly D' (pr 2 a hon).1 (pr 2 a hon).2 hP ht hf hN
        (let ⟨_, rs, gs, hd⟩ := held_yes _ _ rfl a τ b hb; ⟨rs, gs, _, hd⟩))
    (fun a τ e ha _ he => (onQ₃_besideS (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr
        smp₁ ms₁ decT₁ M₁) (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf
        bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds hand ended) Oc Y 3 e).2 ⟨behind_fill
        (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs
        G arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) Oc (p14At Z) (c2
        N).rounds
        hand ended (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) _ rfl
      (promReadsBelow_mono _ _ _ L.toLastRest.promReads le₂) (ownYesLays _ _ _) a τ e (pr 2 a ha).1
          he, L.y3 _⟩)
    (relAt (meansQ₃ (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁)
        (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML) (outsQ₃ 2))
  have own₂ := rowTwo_own_of_cand (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁
      decT₁ M₁) (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML (promSigS cs G smp₂ ms₂ stOf bookOf
      Pm₀)
      (besideS (fillAt (p14At Z) (c2 N).rounds hand ended) Y) Oc cs G arr smp decT c₀' (H2U.proximityTestParametersAt
          ⟨3, none, 2, .K12⟩ N.W) (baseTwoAt (FL o mk Z A
      N c) D (c0 Z) (c1 N)) dB dt (capB dB dt) (capT dB dt) enterOwn leaveOwn mine
    hC L.nodup L.seats L.fence
    (fun a ha => prom_sig G arr decT₁ decT₂ M₁ MS stOf bookOf Pm₀ (fillAt (p14At Z) (c2 N).rounds
        hand ended) links ps L.sits L.wIn L.iIn a (onQ₃_mono L.ocIs (pr 2 a ha).1))
    (fun a w _ hP => pins_sig G arr decT₁ decT₂ M₁ MS ML L.sits a w hP)
  exact eachOwn_of_own o mk Z A N c D a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd cs G arr smp decT c₀' dB dt
      mine
      (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G
          arr smp₂ ms₂ decT₂ MS)) ML (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (besideS (fillAt
          (p14At Z) (c2 N).rounds hand ended) Y) Oc b₀ l
      hflat hds L.row0 (rowOne_besideS _ _ _ _ _ _ Y _ L.y12 h₁) own₂ (rowThree_besideS _ _ _ _ _ Y
          _ L.y4 h₃)

/-- **e₃ AT THE PROOF FILE's OWN DESCRIPTION, FROM THE LEDGER**: the same in the form "each leads".
-/
theorem e3_of_left (L : LastLeft o mk Z A N c D cs G arr smp decT c₀' dB dt mine get smp₁ smp₂ ms₁
    ms₂ decT₁ decT₂ M₁ MS ML stOf bookOf Pm₀ N₁ Ns links ps Oc Y hand ended num no rd r) (b₀ : Block
    (FL o mk Z A N c).S₃ (FL o mk Z A N c).Cl) (l : List (Block (FL o mk Z A N c).S₃ (FL o mk Z A N
    c).Cl)) (hflat : (FL o mk Z A N c).second.blocksInOrder = b₀ :: l) (hds : ds₂ D.ds₃ (held (P := (FL o mk
             Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) (c0 Z)) (held (P := (FL o mk Z A N
             c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) (c1 N)) (held (P := (FL o mk Z A N
             c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) (c2 N)) = dB :: dt) : EachLeads (onQ₃
             (Fr := frameAt D (allOf D) D.key₃ (atDesc (FL o mk Z A N c) (piecesAt (ckP .two) (FL o mk Z A N
             c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z A N c) D cs G arr
             smp decT c₀' mine)) d wEnd)).ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁
             ms₁ decT₁ M₁) (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀)
             (besideS (fillAt (p14At Z) (c2 N).rounds hand ended) Y) Oc) (stepQ₃ (atDesc (FL o mk Z A N c)
             (piecesAt (ckP .two) (FL o mk Z A N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok :=
             Tok) (FL o mk Z A N c) D cs G arr smp decT c₀' mine)) d wEnd)) (tiedNumbers N₁ Ns) (tiedMeaning
             get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML
             (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (besideS (fillAt (p14At Z) (c2 N).rounds hand ended) Y)
             Oc) 0 ((atDesc (FL o mk Z A N c) (piecesAt (ckP .two) (FL o mk Z A N c) D a₁ k₁ a₂ k₂ b₀ l rest₁
             rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z A N c) D cs G arr smp decT c₀' mine)) d
             wEnd)).p₃ :: (atDesc (FL o mk Z A N c) (piecesAt (ckP .two) (FL o mk Z A N c) D a₁ k₁ a₂ k₂ b₀ l
             rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z A N c) D cs G arr smp decT c₀' mine)) d
             wEnd)).l₃) :=
  leadsThreeAt (atDesc (FL o mk Z A N c) (piecesAt (ckP .two) (FL o mk Z A N c) D a₁ k₁ a₂ k₂ b₀ l
      rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z A N c) D cs G arr smp decT c₀' mine)) d
      wEnd)) (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁)
      (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) ML (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (besideS
      (fillAt (p14At Z) (c2 N).rounds hand ended) Y) Oc (own3_of_left a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd
      L b₀ l hflat hds)

end LLT25

#print axioms LLT25.own3_of_left
#print axioms LLT25.e3_of_left
#print axioms LLT25.LastRest.promReads
#print axioms LLT25.LastRest.pinsRead
#print axioms LLT25.promReadsBelow_mono
