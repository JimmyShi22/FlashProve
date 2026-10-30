-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/K6Tied.lean: THE OUTPUT HEAD'S BLOCK (K6) IN THE CHAIN OF PROMISES: `TiedAt`
(Johnson/Desc/Sound/ChainOfPromises.lean) AT THE PIECE THAT HOLDS THE BLOCK AS A LOT SEATS IT OVER
Block.lean AND State.lean. A RULE: every premise
that is left is named. NO RESULT ON THE PROTOCOL.

THE OBJECT. The seated constant is `seatedClaims Wp l bef` (Johnson/Stored/HeadAddsAtS.lean): the
kind's block with its four runs typed at `Claim`, the lot's tests on the plan and its list "before".
K6's files' law (`Came.k6Own`, Johnson/Desc/Kinds/Law/K6Own.lean) speaks of `blockOf Wp l`,
at the unit type. `Seated`: what a seat and a description lay around the constant: B narrows it, B's
yes bears no mark, the piece holds `below B` lifted over the public part, no round is put behind.

  `Block.YesAcross.below`: the same rounds and the same yes, across two types of claims, pass the
    strict reading.
  `seated_across`, `seated_record`: where the seated constant is there, so is `blockOf`'s value,
    with the same rounds and the same yes; and a yes of the seated constant turns three fields of
    the head's own part (the ledger, what its rounds heard, the squares' level) AND NOTHING ELSE.
  `seated_of_term`: at the term `Block.guarded same but { markGuard bS with name := n }`
    (Johnson/Desc/Sound/SeatNarrows.lean) the two facts on B hold.
  `k6_behind`: so at a yes of the piece: no mark in front; the public part stays; the record behind
    is the record in front with these three fields turned.
  `k6_own_seated`: K6's files' law carried to the piece: across the types of claims
    (`goodIn_across`), name and guards, `below`, the lift, the table's extractor (`rowOfPart`). "The
    samples stay" and "the stored table's decoding stays" ARE PAID from `Blind`: the two readers do
    not read where the chain stands.
  `k6_t1`: **THE FIRST TIE, PROVED**, from: the test `pubFit` on the promise's table; the place's
    numbers; the two tests on the plan (`planB`); and `PubSays`: what four public items give at the
    filling: K6's files' own four Bools (Johnson/Desc/Kinds/Law/K6OnB.lean).
  `k6_tiedBy`: `TiedBy` (Johnson/Desc/Sound/TiedBy.lean: `TiedAt` with the kind's words named) at
    block number k; "a mark stays" is paid (a yes has no mark in front).

Over a version of the table (the row does not ask "request").
THE CARRIAGE AND THE TIE ARE GENERAL IN THE LAW (`k6_carry`, `k6_carry_left`,
`k6_tiedBy_of_law`): `k6_own_seated`, `k6_own_left` AND `k6_tiedBy` ARE THEIR INSTANCES AT THE
FORM OF K6's FILES' LAW (`Came.k6Own`), IN WHICH THE READING rd6 AND THE LIST ms ARE FREE
LETTERS: AT A CONSTANT rd6 THAT TIE HOLDS AND READS NOTHING OF THE WITNESS
: IT IS NOT THE ONE THAT SHOULD COUNT: the one that should is `k6_tiedBy_of_law` at K6's files'
law without letters for the reading. The tie's word in front is `K6Left`; "request"
is not spent. Over a version of the seat (the seated decision
asks the record's own test on the request):
`seated_across` goes through the kind's block with true claims, which the seated constant narrows;
`seated_start`: a yes has passed that test.

WHAT IS LEFT, BY NAME, AND WHOSE: the head of `k6_tiedBy`.

Limits. rd6, ms, smp, decT, Mg are letters. `PubSays` is met BY MAKE at a meaning whose four public
items are filled with K6's files' Bools: THAT THE BLOCKS IN FRONT MAKE AND KEEP THESE BOOLS IS THEIR
SECOND TIES': shown by nobody. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Kinds.Law.K6Own
import Johnson.Desc.Kinds.Law.K6OnB
import Johnson.Desc.Kinds.Law.SeatedBridge
import Johnson.Desc.Kinds.Law.AtBorder
import Johnson.Desc.Sound.GoodInRefuses
import Johnson.Desc.Sound.RowOfPart
import Johnson.Desc.Sound.SeatNarrows
import Johnson.Desc.Sound.MergeAcross
import Johnson.Desc.Sound.ExtQuiet
import Johnson.Desc.Sound.OnParts
import Johnson.Desc.Sound.TiedBy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

/-- The same rounds and the same yes pass the strict reading. -/
theorem Block.YesAcross.below {S Cl Cl' : Type} {b : Block S Cl} {b' : Block S Cl'}
    (h : b.YesAcross b') : (Sound.below b).YesAcross (Sound.below b') := by
  refine ⟨h.1, fun s rs gs s' => ?_⟩
  show (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide s rs gs
      else .error "a word is not below the prime") = .ok s' ↔
    (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b'.decide s rs gs
      else .error "a word is not below the prime") = .ok s'
  by_cases hk : viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ = true
  · rw [if_pos hk, if_pos hk]
    exact h.2 s rs gs s'
  · rw [if_neg hk, if_neg hk]

end VerifiableInference.Desc

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Model (Fork)
open VerifiableInference.Desc.First (S HeadOwn ModelPart Numbers Meaning Pub pubFit pubRowOf)
open VerifiableInference.Desc.Sound (Piece Frame relAt Sending Mem MsgT Fenced SmpStays ErrBears
  kitK kitFs rowOfPart yes_of_part onQ meansQ relQ insQ outsQ openAfter extQAt extQAt_quiet
  lays_nothing_K6 strsOf TiedAt TiedBy asked_of_on goodIn_across out_yes below_narrows out_behind)

namespace AtTable

/-- **Where the seated constant is there, so is the block of which K6's files' laws speak**: it has
the declared rounds and the yes of the kind's block with true claims, b0, WHICH THE SEATED CONSTANT
NARROWS (the seated decision asks the record's own test on the request first). -/
theorem seated_across {W : OnBytes.Model.Verify.Public} {l : Nat} {bef : List (Nat × Nat)}
    {bS : Block S Claim} (hS : seatedClaims W l bef = some bS) :
    ∃ (b6 : Block S Unit) (b0 : Block S Claim),
      blockOf W l = some b6 ∧ b6.YesAcross b0 ∧ bS.Narrows b0 := by
  obtain ⟨b0, h0, rfl⟩ := seatedClaims_some hS
  unfold blockClaims at h0
  obtain ⟨iU3, hU, hb0⟩ := Option.map_eq_some_iff.mp h0
  refine ⟨blockAt W.hS iU3 ((Params.settingOf W.P.frame).workOf .field .request) l, b0, ?_, ?_,
    ⟨rfl, fun s rs gs t e => ((tested_decide _ _ _ _ s t rs gs).1 e).1⟩⟩
  · unfold blockOf
    rw [hU]
    rfl
  · subst hb0
    exact ⟨rfl, fun _ _ _ _ => Iff.rfl⟩

/-- The record behind a yes of `blockOf`'s value, written out. -/
theorem record6 {W : OnBytes.Model.Verify.Public} {l : Nat} {b6 : Block S Unit}
    (h6 : blockOf W l = some b6) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : b6.decide s rs gs = .ok s') :
    ∃ (o : HeadOwn) (F1 : Fork) (X : OnBytes.Model.Head.Heard) (Q : OnBytes.Model.Psc),
      s.here = .head o ∧ o.opened = true ∧ s.failed = none ∧
      s' = { s with here := .head { o with F := F1, x := some X, squaresP := some Q } } := by
  unfold blockOf at h6
  cases hU : W.H.tl.ix.U.getD 2 none with
  | none =>
    rw [hU] at h6
    simp at h6
  | some i =>
    rw [hU] at h6
    simp only [Option.map_some, Option.some.injEq] at h6
    subst h6
    exact Came.decide_record W.hS i _ l hd

/-- **A yes of the seated constant turns three fields of the head's own part, and nothing else.** -/
theorem seated_record {W : OnBytes.Model.Verify.Public} {l : Nat} {bef : List (Nat × Nat)}
    {bS : Block S Claim} (hS : seatedClaims W l bef = some bS) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : bS.decide s rs gs = .ok s') :
    ∃ (o : HeadOwn) (F1 : Fork) (X : OnBytes.Model.Head.Heard) (Q : OnBytes.Model.Psc),
      s.here = .head o ∧ o.opened = true ∧ s.failed = none ∧
      s' = { s with here := .head { o with F := F1, x := some X, squaresP := some Q } } := by
  obtain ⟨b6, b0, h6, hY, hN⟩ := seated_across hS
  exact record6 h6 ((hY.2 s rs gs s').2 (hN.2 s rs gs s' hd))

/-- A yes of the seated constant has passed the record's own test on the request. -/
theorem seated_start {W : OnBytes.Model.Verify.Public} {l : Nat} {bef : List (Nat × Nat)}
    {bS : Block S Claim} (hS : seatedClaims W l bef = some bS) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : bS.decide s rs gs = .ok s') :
    startOk W s = true := by
  obtain ⟨b0, _, rfl⟩ := seatedClaims_some hS
  exact ((tested_decide _ _ _ _ s s' rs gs).1 hd).2

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells) (c₀ : Cells) (ms : List Mem)
  (rd6 : (Mem → MsgT) → Cells → Pinned) (Wp : OnBytes.Model.Verify.Public) (fld : Fmt.Fld)
  (Fr : Frame) (q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT)) (l : ℕ)
  (bef : List (ℕ × ℕ)) (B bS : Block S Claim)

/-- **What a seat and a description lay around the seated constant.** -/
structure Seated : Prop where
  /-- the lot's block -/
  lot : seatedClaims Wp l bef = some bS
  /-- the flat list's entry refuses more -/
  narrows : B.Narrows bS
  /-- and its yes bears no mark -/
  unmarked : ∀ s rs gs t, B.decide s rs gs = .ok t → t.failed = none
  /-- the piece holds that entry, under the strict reading, lifted over the public part -/
  piece : q.b = (Sound.below B).lift Prod.snd fun t s => (t.1, s)
  /-- no round is put behind this piece -/
  back : q.back = []

/-- At the term that the first chain's seat lays (typed after it in SeatNarrows.lean) the two facts
on B hold. -/
theorem seated_of_term (same : S → S → Bool) (but : Place → Bool) (n : String) :
    (Block.guarded same but { markGuard bS with name := n }).Narrows bS ∧
      ∀ s rs gs t, (Block.guarded same but { markGuard bS with name := n }).decide s rs gs = .ok t →
        t.failed = none :=
  ⟨seat_narrows same but bS n, fun s rs gs t h =>
    markGuard_unmarked bS s rs gs t ((guarded_narrows same but _).2 s rs gs t h)⟩

/-- The two readers of the record beside the table's own do not read where the chain stands. -/
structure Blind : Prop where
  smp : ∀ (z : P) (s : S) h, smp (z, { s with here := h }) = smp (z, s)
  dec : ∀ c (z : P) (s : S) h, decT c (z, { s with here := h }) = decT c (z, s)

variable {Wp fld Fr q l bef B bS}

/-- **At a yes of the piece.** -/
theorem k6_behind (H : Seated Wp fld Fr q l bef B bS) (a b : (P × S) × Fr.E.Str)
    (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds)) (h : q.ior.red.out a τ = some b) :
    ∃ (o : HeadOwn) (F1 : Fork) (X : OnBytes.Model.Head.Heard) (Q : OnBytes.Model.Psc),
      a.1.2.here = .head o ∧ o.opened = true ∧ a.1.2.failed = none ∧ b.1 = (a.1.1,
        { a.1.2 with here := .head { o with F := F1, x := some X, squaresP := some Q } }) := by
  obtain ⟨⟨rs, gs, hd⟩, e1⟩ := yes_of_part q B H.piece a b τ h
  obtain ⟨o, F1, X, Q, h1, h2, h3, h4⟩ := seated_record H.lot (H.narrows.2 _ _ _ _ hd)
  exact ⟨o, F1, X, Q, h1, h2, h3, Prod.ext e1 h4⟩

/-- A yes of the piece has no mark in front. -/
theorem k6_no_mark (H : Seated Wp fld Fr q l bef B bS) (a b : (P × S) × Fr.E.Str)
    (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds)) (h : q.ior.red.out a τ = some b) :
    a.1.2.failed = none := by
  obtain ⟨_, _, _, _, _, _, h3, _⟩ := k6_behind H a b τ h
  exact h3

variable (Wp fld Fr q l bef B bS)

/-- **THE CARRIAGE OF K6's LAW TO THE DESCRIPTION's PIECE, GENERAL IN THE LAW**:
`law`: K6's files' law in whichever of its forms: `Own` between `K6On` and `K6After` at a piece over
the carried record that holds `below b6`, b6 `blockOf`'s value, AT ANY MEANING `means` OF ANY ITEMS,
for every value z of the public part. Across the type of claims; narrowed to the block at the
driver's entry; lifted over the public part. NOTHING HERE READS WHAT THE LAW's RELATIONS SAY: a law
whose relations read nothing of the witness is carried as any other: WHAT THE TIE IS WORTH IS WHAT
`means` IS WORTH. -/
theorem k6_carry {ι : Type} (H : Seated Wp fld Fr q l bef B bS)
    (means : P → ι → S × Fr.E.Str → Wit Cells Tok MsgT → Prop) (In Out : ι → Prop)
    (law : ∀ (z : P) (b6 : Block S Unit), blockOf Wp l = some b6 →
      (⟨Sound.below b6, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (_root_.Run.ckP fld) Fr S Unit (Wit Cells Tok MsgT)).Own (fun a => K6On Wp a.1)
        (fun b => K6After Wp b.1) (means z) In Out)
    (E : (P × S) × Fr.E.Str → (P × S) × Fr.E.Str → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (hE : ∀ a b w, E a b w = w) :
    (q.withMap E).Own (fun a => K6On Wp a.1.2)
      (fun b => K6After Wp b.1.2 ∧ b.1.2.failed = none)
      (fun i a w => means a.1.1 i (a.1.2, a.2) w) In Out := by
  obtain ⟨b6, b0, h6, hY, hN0⟩ := seated_across H.lot
  refine rowOfPart q B b0 H.piece (H.narrows.trans hN0) (fun s => s.failed = none) H.unmarked E hE
    (fun _ a => K6On Wp a.1) (fun _ b => K6After Wp b.1) means In Out fun z => ?_
  exact goodIn_across (⟨Sound.below b6, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
    Piece (_root_.Run.ckP fld) Fr S Unit (Wit Cells Tok MsgT)) (Sound.below b0) hY.below _ _ _ _
    (law z b6 h6)

/-- **THE SAME UNDER WHAT IS LEFT OF THE LAW's CONDITION** (`K6Left`): the two clauses
on the plan: hplan; the clause on the request need be promised by nobody: where it fails the seated
block says yes at no transcript. -/
theorem k6_carry_left {ι : Type} (H : Seated Wp fld Fr q l bef B bS) (hplan : planB Wp = true)
    (means : P → ι → S × Fr.E.Str → Wit Cells Tok MsgT → Prop) (In Out : ι → Prop)
    (law : ∀ (z : P) (b6 : Block S Unit), blockOf Wp l = some b6 →
      (⟨Sound.below b6, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (_root_.Run.ckP fld) Fr S Unit (Wit Cells Tok MsgT)).Own (fun a => K6On Wp a.1)
        (fun b => K6After Wp b.1) (means z) In Out)
    (E : (P × S) × Fr.E.Str → (P × S) × Fr.E.Str → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (hE : ∀ a b w, E a b w = w) :
    (q.withMap E).Own (fun a => K6Left Wp a.1.2)
      (fun b => K6After Wp b.1.2 ∧ b.1.2.failed = none)
      (fun i a w => means a.1.1 i (a.1.2, a.2) w) In Out :=
  Sound.goodIn_or_refuses (q.withMap E) _ _ _ _ _
    (k6_carry Wp fld Fr q l bef B bS H means In Out law E hE)
    fun a hL => by
      by_cases hst : startB Wp a.1.2 = true
      · left
        show K6On Wp a.1.2
        rw [Came.k6On_iff]
        refine ⟨hplan, ?_⟩
        unfold K6OnB
        simp only [Bool.and_eq_true]
        exact ⟨⟨⟨(Came.wellLaidB_iff _).2 hL.1, hst⟩, (Came.tokenB_iff _ _).2 hL.2.1⟩,
          (Came.cEndB_iff _ _).2 hL.2.2⟩
      · right
        intro τ
        cases hb : (q.withMap E).ior.red.out a τ with
        | none => rfl
        | some b =>
          obtain ⟨⟨rs, gs, hd⟩, _⟩ := yes_of_part q B H.piece a b τ hb
          exact absurd (startB_yes H.lot (H.narrows.2 _ _ _ _ hd)) hst

include c₀ in
/-- **K6's FILES' LAW AT THE PIECE THAT HOLDS THE SEATED CONSTANT**, with a map E that lays nothing
as its extractor. (c₀: any cells: K6's files' law wants a value.) -/
theorem k6_own_seated (H : Seated Wp fld Fr q l bef B bS) (hBl : Blind cs smp decT)
    (hloc : ReadsPinned cs ms rd6) (hF : Fenced q.base ms)
    (hlog : ∀ d, d ∈ toRDs q.ds → d.entry.logN ≤ 64)
    (hErr : ErrBears (_root_.Run.ckP fld)
      (fun j => kitK (toRDs q.ds) j *
        (priceAt (parOf Wp.hS (workOf Wp)) j * kitFs fld (toRDs q.ds) j)) (toRDs q.ds) 0 q.err)
    (E : (P × S) × Fr.E.Str → (P × S) × Fr.E.Str → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (hE : ∀ a b w, E a b w = w) :
    (q.withMap E).Own (fun a => K6On Wp a.1.2)
      (fun b => K6After Wp b.1.2 ∧ b.1.2.failed = none)
      (fun i a w => meansK6 cs G arr (fun s => smp (a.1.1, s)) (fun c s => decT c (a.1.1, s)) ms
        rd6 Wp Fr i (a.1.2, a.2) w) InK6 OutK6 := by
  obtain ⟨b6, b0, h6, hY, hN0⟩ := seated_across H.lot
  have hrec : ∀ (a b : S × Fr.E.Str) τ,
      (⟨Sound.below b6, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (_root_.Run.ckP fld) Fr S Unit (Wit Cells Tok MsgT)).ior.red.out a τ = some b →
      ∃ h, b.1 = { a.1 with here := h } := by
    intro a b τ hb
    obtain ⟨rs, gs, hd⟩ := out_yes (⟨Sound.below b6, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (_root_.Run.ckP fld) Fr S Unit (Wit Cells Tok MsgT)) a b τ hb
    obtain ⟨o, F1, X, Q, _, _, _, e⟩ := record6 h6 ((below_narrows b6).2 _ _ _ _ hd)
    exact ⟨_, e⟩
  refine rowOfPart q B b0 H.piece (H.narrows.trans hN0) (fun s => s.failed = none) H.unmarked E hE
    (fun _ a => K6On Wp a.1) (fun _ b => K6After Wp b.1)
    (fun z => meansK6 cs G arr (fun s => smp (z, s)) (fun c s => decT c (z, s)) ms rd6 Wp Fr) InK6
    OutK6 fun z => ?_
  refine goodIn_across (⟨Sound.below b6, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
    Piece (_root_.Run.ckP fld) Fr S Unit (Wit Cells Tok MsgT)) (Sound.below b0) hY.below _ _ _ _
    (Came.k6Own cs G arr (fun s => smp (z, s)) (fun c s => decT c (z, s)) c₀ ms rd6 Wp fld Fr _ l b6
      h6 rfl H.back (fun _ _ _ => rfl) hloc hF ?_ ?_ hlog hErr)
  · intro a τ b hb x _
    obtain ⟨h, e⟩ := hrec a b τ hb
    show smp (z, b.1) x.1 x.2 = smp (z, a.1) x.1 x.2
    rw [e, hBl.smp]
  · intro a τ b hb
    obtain ⟨h, e⟩ := hrec a b τ hb
    have e2 := out_behind (⟨Sound.below b6, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (_root_.Run.ckP fld) Fr S Unit (Wit Cells Tok MsgT)) a b τ hb
    show decT (strsOf Fr b.2).cell (z, b.1) = decT (strsOf Fr a.2).cell (z, a.1)
    rw [e, hBl.dec, e2]
    rfl

end

section
variable {P W : Type} (Wp : OnBytes.Model.Verify.Public)

/-- **What three public items give at the filling**: three of K6's files' own tests with
code. (The item "request" is not spent: the seated block asks that test itself.)
-/
structure PubSays (Mg : Meaning P W) (m : ℕ) : Prop where
  ledger : ∀ a, Mg.pub (.ledger m) a = true →
    wellLaidB ((seatAt Wp.hS (readsOf Wp)).ledger a.2) = true
  token : ∀ a, Mg.pub .tokenSmall a = true → tokenB Wp a.2 = true
  look : ∀ a, Mg.pub (.look m) a = true → cEndB Wp a.2 = true

/-- What the promise's table asks in front of the caller's block of the head's segment. -/
theorem asks_K6 (links : List ModelPart) (p : Place) (m : ℕ) (hl : p.link = some m)
    (hs : links[m]? = some .head) (hpc : p.piece = 4) :
    (pubRowOf links p).asks =
      [.ledger m, .look m, .left m, .linkFresh m, .freeAbove m, .tokenSmall] := by
  simp [pubRowOf, hl, hs, hpc, First.shift]

/-- **THE FIRST TIE.** -/
theorem k6_t1 {Fr : Frame} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (ps : List Place)
    (k : ℕ) (p : Place) (m : ℕ) (hfit : pubFit Mg.more links ps = true) (hp : ps[k]? = some p)
    (hl : p.link = some m) (hs : links[m]? = some .head) (hpc : p.piece = 4)
    (hPub : PubSays Wp Mg m) (a : (P × S) × Fr.E.Str)
    (ha : onQ (Fr := Fr) N Mg links ps (fun a => a) k a) (hm : ¬ a.1.2.failed ≠ none) :
    K6Left Wp a.1.2 := by
  have hm' : a.1.2.failed = none := Classical.not_not.1 hm
  have ask : ∀ x, x ∈ (pubRowOf links p).asks → Mg.pub x a.1 = true := fun x hx =>
    asked_of_on N Mg links ps (fun a => a) hfit k p hp a ha hm' x hx
  rw [asks_K6 links p m hl hs hpc] at ask
  exact ⟨(Came.wellLaidB_iff _).1 (hPub.ledger _ (ask _ (by simp))),
    (Came.tokenB_iff _ _).1 (hPub.token _ (ask _ (by simp))),
    (Came.cEndB_iff _ _).1 (hPub.look _ (ask _ (by simp)))⟩

end

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells) (c₀ : Cells) (ms : List Mem)
  (rd6 : (Mem → MsgT) → Cells → Pinned) (Wp : OnBytes.Model.Verify.Public) (fld : Fmt.Fld)
  (Fr : Frame) (q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT)) (l : ℕ)
  (bef : List (ℕ × ℕ)) (B bS : Block S Claim)

include c₀ in
/-- **THE LAW UNDER WHAT IS LEFT OF ITS CONDITION**: `K6Left` (the ledger well laid, the
token small, the lookup's last claim filled). The two clauses on the plan: hplan. THE CLAUSE ON THE
REQUEST NEED BE PROMISED BY NOBODY: where it fails the seated block says yes at no transcript
(`goodIn_or_refuses`, Johnson/Desc/Sound/GoodInRefuses.lean; `startB_yes`). -/
theorem k6_own_left (H : Seated Wp fld Fr q l bef B bS) (hplan : planB Wp = true)
    (hBl : Blind cs smp decT) (hloc : ReadsPinned cs ms rd6) (hF : Fenced q.base ms)
    (hlog : ∀ d, d ∈ toRDs q.ds → d.entry.logN ≤ 64)
    (hErr : ErrBears (_root_.Run.ckP fld)
      (fun j => kitK (toRDs q.ds) j *
        (priceAt (parOf Wp.hS (workOf Wp)) j * kitFs fld (toRDs q.ds) j)) (toRDs q.ds) 0 q.err)
    (E : (P × S) × Fr.E.Str → (P × S) × Fr.E.Str → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (hE : ∀ a b w, E a b w = w) :
    (q.withMap E).Own (fun a => K6Left Wp a.1.2)
      (fun b => K6After Wp b.1.2 ∧ b.1.2.failed = none)
      (fun i a w => meansK6 cs G arr (fun s => smp (a.1.1, s)) (fun c s => decT c (a.1.1, s)) ms
        rd6 Wp Fr i (a.1.2, a.2) w) InK6 OutK6 :=
  Sound.goodIn_or_refuses (q.withMap E) _ _ _ _ _
    (k6_own_seated cs G arr smp decT c₀ ms rd6 Wp fld Fr q l bef B bS H hBl hloc hF hlog hErr E hE)
    fun a hL => by
      by_cases hst : startB Wp a.1.2 = true
      · left
        show K6On Wp a.1.2
        rw [Came.k6On_iff]
        refine ⟨hplan, ?_⟩
        unfold K6OnB
        simp only [Bool.and_eq_true]
        exact ⟨⟨⟨(Came.wellLaidB_iff _).2 hL.1, hst⟩, (Came.tokenB_iff _ _).2 hL.2.1⟩,
          (Came.cEndB_iff _ _).2 hL.2.2⟩
      · right
        intro τ
        cases hb : (q.withMap E).ior.red.out a τ with
        | none => rfl
        | some b =>
          obtain ⟨⟨rs, gs, hd⟩, _⟩ := yes_of_part q B H.piece a b τ hb
          exact absurd (startB_yes H.lot (H.narrows.2 _ _ _ _ hd)) hst

/-- **K6 IN THE CHAIN OF PROMISES, GENERAL IN THE LAW**. `law`, `means`, In, Out: as
in
`k6_carry`. t3, t4: the exchange between the table's items and the law's own relations, AT THAT
MEANING. LEFT, BY NAME: ON THE TABLE: hfit hp hk hl hs hpc · ON THE SEAT's TEXT: H · ON THE PLAN:
hplan · ON THE FILLINGS: hPub hDec · THE LAW · THE TIES: t2 t3 t4 t5. -/
theorem k6_tiedBy_of_law {ι : Type} (msT : List Mem) (tokOf : P × S → Tok) (N : Numbers)
    (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place) (k : ℕ) (p : Place)
    (m : ℕ) (hfit : pubFit Mg.more links ps = true) (hp : ps[k]? = some p) (hk : p.kind = .K6)
    (hl : p.link = some m) (hs : links[m]? = some .head) (hpc : p.piece = 4)
    (H : Seated Wp fld Fr q l bef B bS) (hplan : planB Wp = true) (hPub : PubSays Wp Mg m)
    (means : P → ι → S × Fr.E.Str → Wit Cells Tok MsgT → Prop) (In Out : ι → Prop)
    (law : ∀ (z : P) (b6 : Block S Unit), blockOf Wp l = some b6 →
      (⟨Sound.below b6, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (_root_.Run.ckP fld) Fr S Unit (Wit Cells Tok MsgT)).Own (fun a => K6On Wp a.1)
        (fun b => K6After Wp b.1) (means z) In Out)
    (t2 : ∀ a τ b, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      onQ (Fr := Fr) N Mg links ps (fun a => a) (k + 1) b)
    (t3 : ∀ a τ b w, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      relAt (meansQ (Fr := Fr) N Mg fun a => a) (outsQ links ps k) b w →
      relAt (means b.1.1) Out (b.1.2, b.2) w)
    (t4 : ∀ a τ b w, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      relAt (meansQ (Fr := Fr) N Mg fun a => a) (outsQ links ps k) b w →
      relAt (means a.1.1) In (a.1.2, a.2) w → relAt (meansQ (Fr := Fr) N Mg fun a => a) (insQ links
    ps k) a w) (t5 : ∀ a τ b w i, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → a.1.2.failed =
      none → q.ior.red.out a τ = some b → onQ (Fr := Fr) N Mg links ps (fun a => a) (k + 1) b →
      relQ (Fr := Fr) N Mg links ps (fun a => a) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k i → ¬ insQ links ps k i →
      meansQ (Fr := Fr) N Mg (fun a => a) i a w)
    (hDec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes a.1 (strsOf Fr a.2) →
      Mg.decodes b.1 (strsOf Fr b.2)) :
    TiedBy N Mg links ps (fun a => a) k
      (q.withMap (extQAt cs G arr smp msT decT c₀ tokOf N links ps (fun a => a) k))
      (fun a => K6Left Wp a.1.2) (fun b => K6After Wp b.1.2 ∧ b.1.2.failed = none)
      (relAt (fun i a w => means a.1.1 i (a.1.2, a.2) w) In)
      (relAt (fun i a w => means a.1.1 i (a.1.2, a.2) w) Out) := by
  have hE := extQAt_quiet (Fr := Fr) cs G arr smp msT decT c₀ tokOf N links ps (fun a => a) k p hp
    (lays_nothing_K6 N links p hk).1 (lays_nothing_K6 N links p hk).2.1
    (lays_nothing_K6 N links p hk).2.2
  have hid := Sound.withMap_id q
    (extQAt cs G arr smp msT decT c₀ tokOf N links ps (fun a => a) k) hE
  refine ⟨
    k6_carry_left Wp fld Fr q l bef B bS H hplan means In Out law _ hE,
    fun a ha hm => k6_t1 Wp N Mg links ps k p m hfit hp hl hs hpc hPub a ha hm,
    fun a τ b ha hm hb h' => t2 a τ b ha (Classical.not_not.1 hm) hb h'.1,
    fun a τ b w ha hm hb h' hw => t3 a τ b w ha (Classical.not_not.1 hm) hb h'.1 hw,
    fun a τ b w ha hm hb h' hw hi => ?_,
    fun a τ b w i ha hm hb hon hall hi hin => ?_,
    fun a τ b hb hm => absurd (k6_no_mark H a b τ hb) hm,
    hDec⟩
  · rw [hid] at hi ⊢
    exact t4 a τ b w ha (Classical.not_not.1 hm) hb h'.1 hw hi
  · rw [hid]
    exact t5 a τ b w i ha (Classical.not_not.1 hm) hb hon hall hi hin


/-- **K6 IN THE CHAIN OF PROMISES.** LEFT, BY NAME: ON THE TABLE: hfit hp hk hl hs hpc · ON THE
SEAT's TEXT: H (five fields) · ON THE PLAN: hplan hF hlog · ON THE FILLINGS: hBl hloc hPub hDec ·
THE BITS: hErr · THE TIES: t2 t3 t4 t5. -/
theorem k6_tiedBy (msT : List Mem) (tokOf : P × S → Tok) (N : Numbers)
    (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place) (k : ℕ) (p : Place)
    (m : ℕ) (hfit : pubFit Mg.more links ps = true) (hp : ps[k]? = some p) (hk : p.kind = .K6)
    (hl : p.link = some m) (hs : links[m]? = some .head) (hpc : p.piece = 4)
    (H : Seated Wp fld Fr q l bef B bS) (hplan : planB Wp = true) (hF : Fenced q.base ms)
    (hlog : ∀ d, d ∈ toRDs q.ds → d.entry.logN ≤ 64) (hBl : Blind cs smp decT)
    (hloc : ReadsPinned cs ms rd6) (hPub : PubSays Wp Mg m)
    (hErr : ErrBears (_root_.Run.ckP fld)
      (fun j => kitK (toRDs q.ds) j *
        (priceAt (parOf Wp.hS (workOf Wp)) j * kitFs fld (toRDs q.ds) j)) (toRDs q.ds) 0 q.err)
    (t2 : ∀ a τ b, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      onQ (Fr := Fr) N Mg links ps (fun a => a) (k + 1) b)
    (t3 : ∀ a τ b w, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      relAt (meansQ (Fr := Fr) N Mg fun a => a) (outsQ links ps k) b w →
      relAt (meansK6 cs G arr (fun s => smp (b.1.1, s)) (fun c s => decT c (b.1.1, s)) ms rd6 Wp
        Fr) OutK6 (b.1.2, b.2) w)
    (t4 : ∀ a τ b w, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      relAt (meansQ (Fr := Fr) N Mg fun a => a) (outsQ links ps k) b w →
      relAt (meansK6 cs G arr (fun s => smp (a.1.1, s)) (fun c s => decT c (a.1.1, s)) ms rd6 Wp
        Fr) InK6 (a.1.2, a.2) w → relAt (meansQ (Fr := Fr) N Mg fun a => a) (insQ links ps k) a w)
    (t5 : ∀ a τ b w i, onQ (Fr := Fr) N Mg links ps (fun a => a) k a → a.1.2.failed = none →
      q.ior.red.out a τ = some b → onQ (Fr := Fr) N Mg links ps (fun a => a) (k + 1) b →
      relQ (Fr := Fr) N Mg links ps (fun a => a) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k i → ¬ insQ links ps k i →
      meansQ (Fr := Fr) N Mg (fun a => a) i a w)
    (hDec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes a.1 (strsOf Fr a.2) →
      Mg.decodes b.1 (strsOf Fr b.2)) :
    TiedBy N Mg links ps (fun a => a) k
      (q.withMap (extQAt cs G arr smp msT decT c₀ tokOf N links ps (fun a => a) k))
      (fun a => K6Left Wp a.1.2) (fun b => K6After Wp b.1.2 ∧ b.1.2.failed = none)
      (relAt (fun i a w => meansK6 cs G arr (fun s => smp (a.1.1, s))
        (fun c s => decT c (a.1.1, s)) ms rd6 Wp Fr i (a.1.2, a.2) w) InK6)
      (relAt (fun i a w => meansK6 cs G arr (fun s => smp (a.1.1, s))
        (fun c s => decT c (a.1.1, s)) ms rd6 Wp Fr i (a.1.2, a.2) w) OutK6) := by
  have hE := extQAt_quiet (Fr := Fr) cs G arr smp msT decT c₀ tokOf N links ps (fun a => a) k p hp
    (lays_nothing_K6 N links p hk).1 (lays_nothing_K6 N links p hk).2.1
    (lays_nothing_K6 N links p hk).2.2
  have hid := Sound.withMap_id q
    (extQAt cs G arr smp msT decT c₀ tokOf N links ps (fun a => a) k) hE
  refine ⟨
    k6_own_left cs G arr smp decT c₀ ms rd6 Wp fld Fr q l bef B bS H hplan hBl hloc hF hlog hErr _
      hE,
    fun a ha hm => k6_t1 Wp N Mg links ps k p m hfit hp hl hs hpc hPub a ha hm,
    fun a τ b ha hm hb h' => t2 a τ b ha (Classical.not_not.1 hm) hb h'.1,
    fun a τ b w ha hm hb h' hw => t3 a τ b w ha (Classical.not_not.1 hm) hb h'.1 hw,
    fun a τ b w ha hm hb h' hw hi => ?_,
    fun a τ b w i ha hm hb hon hall hi hin => ?_,
    fun a τ b hb hm => absurd (k6_no_mark H a b τ hb) hm,
    hDec⟩
  · rw [hid] at hi ⊢
    exact t4 a τ b w ha (Classical.not_not.1 hm) hb h'.1 hw hi
  · rw [hid]
    exact t5 a τ b w i ha (Classical.not_not.1 hm) hb hon hall hi hin

end

end AtTable

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Block.YesAcross.below
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.seated_across
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.seated_record
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.seated_of_term
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_behind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_own_seated
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.asks_K6
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_t1
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_carry
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_carry_left
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_own_left
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_tiedBy_of_law
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_tiedBy
