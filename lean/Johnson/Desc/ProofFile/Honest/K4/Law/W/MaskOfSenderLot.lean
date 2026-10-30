-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MaskOfSenderLot.lean: CONDITIONAL. Four statements with their
proofs.

What is here. THE LEMMA ON THE SENDER's LOT, FOR THE MASK ROW OF THE SEGMENT OF THE MEMBER OF THE
FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4). The message with that mask row is sent by another
member; `k4MaskLotG` (Lot/MaskLotG.lean) is not laid: it is the text, number and fence of this
lemma. (1) `k4MaskOwn_of_senderLot`: WHERE A SCRIPT MEETS `OwnMsgs` (Honest/Thread/ScriptLots.lean,
of other writers) AT THE SENDER's LOT, WRITTEN AS ITS THREE LETTERS (the number nS, the fence fS,
the text tS), IT MEETS `OwnMsgs` AT THE THREE FIELDS OF `k4MaskLotG` TOO. The library's hypothesis h
on the public files, a thread and a list of lots do not stand in it; hP, hn and the lock's first
place are hypotheses on the public part Zp. Its hypotheses: hP (`k4PubG Zp g` returns Qp); K, the
lock `K4MaskLock` (Law/W/MaskLock.lean), a public test on the book; hn (nS is K4's number); hA (the
sender's text answers at the entries that K4's text reads, AT THE INPUTS THAT Vq NAMES: a sender's
text may answer only where a public test on the input passes, so hA is asked no wider than OS; AND
AT THE LISTS OF CHALLENGES AT WHICH IT IS SPENT: hd.take fS with N ≤ hd.length); hE (THE SENDER's
SENTENCE: where its text answers y' at entry ν of the mask row 0, below L, y' is the owner o's
element number base + ν); hL (K4's entries lie below L); OS. (2) `k4MaskTie_of_senderLot`: THE KEY
TURNED: with h, the library's hypothesis `P5J.AtMgA` on the public files, `LaidK4`, hQ and the
thread's stand: the end of `k4MaskTie_coinsG` (Law/W/MaskLotGPub.lean), to the letter. (3)
`k4MaskEntry_is_msg`: THE VERIFIER's SIDE: under h, `LaidK4`, hQ and the thread's stand, the entry
of the mask row at the ledger's next slot plus j, as the reader has it, IS THE SCRIPT's MESSAGE's
ENTRY NUMBER e + j OF THE MASK ROW 0, at every j with j + 1 below `k4Takes`: no test on the book and
no lot stand in it, and no element of a run's coins is named. (4) `k4MaskEntry_is_owners`: THE
SENDER's SENTENCE MEETS THE VERIFIER's READER: o's element number base + e + j is that entry, at the
stand's own coins. NO LOCK STANDS IN (4): o and base are hE's letters, and it holds whatever the
book lends K4: SO IT IS NO TEST THAT LOCK AND KEY FIT. What bears the lock: `k4Lock_member`
(Law/W/MaskLock.lean) and (1) and (2).

How. (1): where K4's text answers y, the entry lies inside the fences and y is a member of
`rowSpentGl` … (`k4MaskTextG_val`, Law/W/MaskTxtGIs.lean; `k4MaskTextG_coin`,
Law/W/MaskTxtGPub.lean); by the lock that member is o's element number base + ν (`k4Lock_member`,
`k4Cnt_of_lock`); by hA and hE the sender's text answers the same element; OS says that the Script's
message holds it. (2): one call each of (1), `k4PubG_of` (Law/W/PubGOf.lean) and `k4MaskTie_coinsG`,
whose named hypothesis on the book is the lock's field last.lends. (3): the first steps of the proof
of `k4MaskTie_of_own` (Law/W/MaskOfOwn.lean), with the room by `takes_room_head`
(Law/W/MaskBelowHead.lean), `slotsSharp_head` and `maskRow_ell_is` (Law/W/MaskEllHead.lean) in the
place of a lending. (4): (3), hA, hE and OS.

Not shown here. THAT ANY BOOK OF THE FULL SIZE PASSES THE LOCK: Law/W/MaskLock.lean's head. hA AND
hE ARE SENTENCES ON ANOTHER MEMBER's TEXT, and must be had at the very text tS at which OS is had:
they are shown, as far as we know, of no text that is laid, at any of K4's twelve segments. THAT ANY
SCRIPT MEETS OS: `ofLots_ownMsgs` (Honest/Thread/ScriptLots.lean) has it at a list of lots that
holds the sender's lot and agrees with it; no sender's lot for these messages is known to us. hn: an
equation of two public numbers. hL: a public inequality; it is concluded by no statement here. Near
it: `takes_room_head` (Law/W/MaskBelowHead.lean, under h and `LaidK4`: the lookup's entries and
`k4Takes` are within the plan's number of entries) and `slotsSharp_head` (Law/W/MaskEllHead.lean,
under h, at a group below 12 and its plan: that number and one more is at most 8192), beside
`k4Cnt_of_lock` (cnt + 1 is `k4Takes`). ONE L SERVES hL AND hE: a sender's sentence is given below
its mask code's length: so a call wants that K4's entries lie below that length at each of the
twelve messages: a public inequality, shown nowhere here. ONE Vq SERVES THREE: hA wants it narrow
(the inputs at which the sender's text answers), OS has it at its giver's letter, hV wants it wide
(the input at a stand of the thread): SO (2) AND (4) WANT THAT AT A STAND OF THE THREAD THE INPUT
PASSES THE SENDER's PUBLIC TEST: shown, as far as we know, by nobody. THE ONE EQUATION THAT JOINS
LOCK AND KEY: THE STRETCH BEGINS AT base + e WITH THE SENDER's OWN base: the lock's field stretch
has the book's start for K4's row as base + e, and the sender's sentence hE has its mask row's entry
number ν at its coin number base + ν: that the maker's start and the place where the sender's mask
row begins among its coins are one number plus e is shown nowhere here; AND THAT THE STRETCH's OWNER
o IS THE SENDER's OWN ADDRESS IS AS UNSHOWN AS THE START: it is what makes the coins the sender's.
THE LOCK's FIELD last.lends STANDS AT THE FIRST CHAIN AND READS THE BOOK's FIRST TABLE ALONE
(`lookDue`, Honest/Small/LendsRow.lean): at a book that keeps the row of the stretch's owner, or of
the last entry's, in another table it is false, and (1) and (2) are empty; (3) and (4) take no lock.
OTHER KINDS' PARTS SPEND OF THE SAME MASK ROW: that the book's entries hand out each coin of the
owner's once is a matter of all its entries together: nothing on it here; the frame's writers' law
on it: `ProverCoinCounts.spentApart_parts` (Honest/BookApart.lean). THAT THE THREAD HOLDS AT ANY RUN: hT is a
hypothesis of (2), (3) and (4): where the thread stands nowhere they are empty; so they are where
the state has no part of the segment. Of the hypotheses of (2) together, and of those of (4), no
example is known to us. That h can hold: the side library AtFullSide proves, with no hypothesis,
that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). THE FULL SIZE ALONE,
and the format's second hash function alone, in (2), (3) and (4). A program's walk from import to
import, which reads import lines alone and stops unopened at Johnson/Goal/, ThirdParty/, Johnson/D/,
Johnson/Bridge/ and Cb/Bridge*, stopped at 70 modules under Johnson/Goal/, at 7 under
Johnson/Bridge/ and at 1 that begins Cb.Bridge: floors. A LAW, NOT A PART: no file that defines a
part of the proof file's description may import this one. Nothing on soundness, on completeness or
on any other property. No property is claimed.

  `k4MaskOwn_of_senderLot`   **the lemma: `OwnMsgs` at the sender's lot gives `OwnMsgs` at K4's
      text**
  `k4MaskTie_of_senderLot`   the key turned: the entries are members of `rowSpentGl`
  `k4MaskEntry_is_msg`   the verifier's side: the reader's entry is the Script's message's
  `k4MaskEntry_is_owners`   the sender's sentence meets the verifier's reader; no lock in it
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskLock
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskLotGPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no standing table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open Johnson.Pack (pMask)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Rt (k4Takes)
open OnBytes.Road.K4 (parOf)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block Wit)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgT Mem seatTab memTab seatOf numOf dataQ)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead OwnMsgs)
open ProofFile.Honest.K4.SeatedHead (LaidK4 pub_of)
open ProofFile.Honest.K4.Lot (k4MaskLotG k4MaskNum k4PubG)

/-- CONDITIONAL on hP, K, hn, hA, hE, hL and OS. **THE LEMMA ON THE SENDER's LOT**: where the Script
meets `OwnMsgs` at the sender's number nS, fence fS and text tS, it meets `OwnMsgs` at K4's too. -/
theorem k4MaskOwn_of_senderLot {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Cl' Tok : Type} {cells : Tr → Cells}
    {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Zp : ProofFile.Pub} {g : ℕ} {Qp : K4Pub}
    (hP : k4PubG Zp g = some Qp) {es₁ : List Ahead} {eL : Ahead} {o : Addr} {base cnt : ℕ}
    (K : K4MaskLock Bk Qp (Forest.elems (P5J.At.X Zp).y.fo) es₁ eL o base cnt)
    (Q : Script Bk (Local W₀ Rc Xi Tr) Cl' Tok MsgT) (nS fS : ℕ)
    (tS : Coins Bk → Local W₀ Rc Xi Tr → List Fmt.Drawn → Bool → ℕ → ℕ → Option Cb.Gl.E)
    (hn : nS = k4MaskNum Zp (2 * g)) {Vq : Local W₀ Rc Xi Tr → Prop} {N : ℕ}
    (hA : ∀ k w (hd : List Fmt.Drawn) ν, Vq w → N ≤ hd.length →
      Forest.elems (P5J.At.X Zp).y.fo ≤ ν → ν < Forest.elems (P5J.At.X Zp).y.fo + cnt →
      (tS k w (hd.take fS) true 0 ν).isSome = true)
    {L : ℕ}
    (hE : ∀ k w hd ν y', ν < L → tS k w hd true 0 ν = some y' →
      (k.look 0 o).2.eAt (base + ν) = .ok y')
    (hL : Forest.elems (P5J.At.X Zp).y.fo + cnt ≤ L) (OS : OwnMsgs Q Vq N nS fS tS) :
    OwnMsgs Q Vq N (k4MaskLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g).n
      (k4MaskLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g).fx
      (k4MaskLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g).txt := by
  intro k w hd hV hN mask row place y hy
  have hy1 : ((k4PubG Zp g).bind fun Qp => Lot.k4MaskTextG X cells weights tokens look Qp
      (Forest.elems (P5J.At.X Zp).y.fo) k w (hd.take 0) mask row place) = some y := hy
  rw [hP] at hy1
  have hy' : Lot.k4MaskTextG X cells weights tokens look Qp (Forest.elems (P5J.At.X Zp).y.fo) k w
      (hd.take 0) mask row place = some y := hy1
  obtain ⟨hm, hr0, f1, f2⟩ := (k4MaskTextG_val cells weights tokens look Qp hy').1
  subst hm
  subst hr0
  have c0 := k4MaskTextG_coin cells weights tokens look Qp hy'
  have hc := k4Cnt_of_lock K
  have hj : place - Forest.elems (P5J.At.X Zp).y.fo < cnt := by omega
  obtain ⟨y1, m1, a1⟩ := k4Lock_member K k hj
  rw [c0] at m1
  have e1 : y = y1 := Option.some.inj m1
  have hpl : base + Forest.elems (P5J.At.X Zp).y.fo + (place - Forest.elems (P5J.At.X Zp).y.fo) =
      base + place := by omega
  rw [hpl, ← e1] at a1
  obtain ⟨y', hs⟩ := Option.isSome_iff_exists.1 (hA k w hd place hV hN f1 (by omega))
  have a2 := hE k w (hd.take fS) place y' (by omega) hs
  rw [a1] at a2
  have e2 : y = y' := Except.ok.inj a2
  have q := OS k w hd hV hN true 0 place y' hs
  show Q.msg (k4MaskNum Zp (2 * g)) k w (hd.take (Q.fixedMsg (k4MaskNum Zp (2 * g)))) true 0
    place = y
  rw [← hn, q]
  exact e2.symm

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL on h, Lh, hQ, K, hn, hA, hE, hL, OS, hT, hV and hN. **THE KEY TURNED**: the end of
`k4MaskTie_coinsG`, from `OwnMsgs` at the sender's lot. -/
theorem k4MaskTie_of_senderLot {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) {es₁ : List Ahead} {eL : Ahead} {o : Addr} {base cnt : ℕ}
    (K : K4MaskLock Bk Qp (Forest.elems (P5J.At.X Zp).y.fo) es₁ eL o base cnt)
    (nS fS : ℕ)
    (tS : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Bool → ℕ → ℕ → Option Cb.Gl.E)
    (hn : nS = k4MaskNum Zp (2 * g)) {Vq : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    (hA : ∀ k w (hd : List Fmt.Drawn) ν, Vq w → N ≤ hd.length →
      Forest.elems (P5J.At.X Zp).y.fo ≤ ν → ν < Forest.elems (P5J.At.X Zp).y.fo + cnt →
      (tS k w (hd.take fS) true 0 ν).isSome = true)
    {L : ℕ}
    (hE : ∀ k w hd ν y', ν < L → tS k w hd true 0 ν = some y' →
      (k.look 0 o).2.eAt (base + ν) = .ok y')
    (hL : Forest.elems (P5J.At.X Zp).y.fo + cnt ≤ L) (OS : OwnMsgs Q Vq N nS fS tS)
    {c : Coins Bk} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (hV : Vq mm.st.input) (hN : N ≤ mm.st.heard.length) :
    ∀ a, segAt? s = some a → ∀ ds j, j + 1 < k4Takes Qp.P Qp.hp Qp.g →
      (rowSpentGl Bk (c.look 0) (k4Place Qp) (k4RowIn Qp).length 0)[j]? =
        some ((dataQ (h.𝔇.N.sent m 0) a (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms
          ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.wit c mm.st.input
            (mm.st.heard ++ ds)))).mask (a.F.next + j)) :=
  k4MaskTie_coinsG h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh (cells := cells)
    (weights := weights) (tokens := tokens) (look := look) hQ K.last.lends
    (k4MaskOwn_of_senderLot (k4PubG_of Lh hQ) K Q nS fS tS hn hA hE hL OS) hT hV hN

/-- CONDITIONAL on h, Lh, hQ and hT. **THE VERIFIER's SIDE**: the entry of the mask row at the
ledger's next slot plus j, as the reader has it, is the Script's message's entry number e + j of the
mask row 0. No test on the book and no lot stand in it; no element of a run's coins is named. -/
theorem k4MaskEntry_is_msg {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {Qp : K4Pub} (hQ : k4PubOf Zp x.2 = some Qp)
    {c : Coins Bk} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E) :
    ∀ a, segAt? s = some a → ∀ ds j, j + 1 < k4Takes Qp.P Qp.hp Qp.g →
      (dataQ (h.𝔇.N.sent m 0) a (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.wit c mm.st.input
          (mm.st.heard ++ ds)))).mask (a.F.next + j) =
        Q.msg (maskNumAt Zp m) c mm.st.input
          ((mm.st.heard ++ ds).take (Q.fixedMsg (maskNumAt Zp m))) true 0
          (Forest.elems (P5J.At.X Zp).y.fo + j) := by
  intro a ha ds j hj
  obtain ⟨xl, o, u, _, hl, _, P, _, hnum, _, _⟩ := maskRow_laid h Lh
  obtain ⟨f1, f2, f3⟩ :=
    maskRow_front_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT P a ha
  obtain ⟨en, _⟩ := ledger_front_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT a ha
  obtain ⟨⟨eP, eh, eg, -, -⟩, -, -, -⟩ := pub_of Lh hQ
  rw [← eP, ← eh, ← eg] at hj
  have r1 := takes_room_head h Lh
  have s1 : (parOf x).hp.ns + 1 ≤ 8192 := slotsSharp_head h Lh.lt Lh.hp
  have rm : a.F.next + j + 3 ≤ (pMask h.𝔇.cs (u.1.l.get u.2).1).ell := by
    rw [maskRow_ell_is h Lh P hl]
    omega
  rw [mask_at_seat f1 f2 f3]
  have R2 : ∀ w : WtF, seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms w (seatOf u) =
      memTab h.𝔇.cs h.𝔇.arr w u := by
    intro w
    unfold seatTab
    rw [maskRow_find P]
  rw [R2]
  show Wit.tab _ h.𝔇.cs (u.1.l.get u.2).1 (numOf h.𝔇.arr u) (u.1.seat u.2).1 (u.1.seat u.2).2 true 0
    (a.F.next + j) = _
  rw [tab_off_pad _ _ _ _ _ _ _ _ (by omega), hnum, en]
  rfl

/-- CONDITIONAL on h, Lh, hQ, hn, hA, hE, hL, OS, hT, hV and hN. **THE SENDER's SENTENCE MEETS THE
VERIFIER's READER**: o's element number base + e + j is the entry of the mask row at the ledger's
next slot plus j, at the stand's own coins. NO LOCK STANDS IN IT: o and base are hE's letters. -/
theorem k4MaskEntry_is_owners {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {Qp : K4Pub} (hQ : k4PubOf Zp x.2 = some Qp) (nS fS : ℕ)
    (tS : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Bool → ℕ → ℕ → Option Cb.Gl.E)
    (hn : nS = k4MaskNum Zp (2 * g)) {Vq : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    (hA : ∀ k w (hd : List Fmt.Drawn) ν, Vq w → N ≤ hd.length →
      Forest.elems (P5J.At.X Zp).y.fo ≤ ν →
      ν + 1 < Forest.elems (P5J.At.X Zp).y.fo + k4Takes Qp.P Qp.hp Qp.g →
      (tS k w (hd.take fS) true 0 ν).isSome = true)
    {o : Addr} {base L : ℕ}
    (hE : ∀ k w hd ν y', ν < L → tS k w hd true 0 ν = some y' →
      (k.look 0 o).2.eAt (base + ν) = .ok y')
    (hL : Forest.elems (P5J.At.X Zp).y.fo + k4Takes Qp.P Qp.hp Qp.g ≤ L + 1)
    (OS : OwnMsgs Q Vq N nS fS tS)
    {c : Coins Bk} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (hV : Vq mm.st.input) (hN : N ≤ mm.st.heard.length) :
    ∀ a, segAt? s = some a → ∀ ds j, j + 1 < k4Takes Qp.P Qp.hp Qp.g →
      (c.look 0 o).2.eAt (base + Forest.elems (P5J.At.X Zp).y.fo + j) =
        .ok ((dataQ (h.𝔇.N.sent m 0) a (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms
          ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.wit c mm.st.input
            (mm.st.heard ++ ds)))).mask (a.F.next + j)) := by
  intro a ha ds j hj
  have v := k4MaskEntry_is_msg h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQ hT a ha ds j hj
  obtain rfl := Lh.seg
  have hlen : N ≤ (mm.st.heard ++ ds).length := by
    rw [List.length_append]
    omega
  obtain ⟨y', hs⟩ := Option.isSome_iff_exists.1 (hA c mm.st.input (mm.st.heard ++ ds)
    (Forest.elems (P5J.At.X Zp).y.fo + j) hV hlen (Nat.le_add_right _ _) (by omega))
  have a2 := hE c mm.st.input _ (Forest.elems (P5J.At.X Zp).y.fo + j) y' (by omega) hs
  have q := OS c mm.st.input (mm.st.heard ++ ds) hV hlen true 0 _ y' hs
  rw [hn] at q
  rw [v, Nat.add_assoc]
  exact a2.trans (congrArg Except.ok q.symm)

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4MaskOwn_of_senderLot
#print axioms ProofFile.Honest.K4.W.k4MaskTie_of_senderLot
#print axioms ProofFile.Honest.K4.W.k4MaskEntry_is_msg
#print axioms ProofFile.Honest.K4.W.k4MaskEntry_is_owners
