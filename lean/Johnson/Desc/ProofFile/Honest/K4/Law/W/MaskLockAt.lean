-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MaskLockAt.lean: CONDITIONAL but for the first statement. Two
definitions, one with code, and five statements with their proofs.

What is here. A NAME FOR THE ONE HYPOTHESIS THAT JOINS LOCK AND KEY, for the mask row of the segment
of the member of the feed-forward layers' own rounds (sub-protocol K4). In `k4MaskOwn_of_senderLot`
(Law/W/MaskOfSenderLot.lean) the lock `K4MaskLock` (Law/W/MaskLock.lean) and the sender's sentence
hE share two letters, the owner o and the number base: whoever calls must hand in both at one o and
one base. `K4MaskLockAt Bk Qp e o base`: THE LOCK AT THE SENDER's LETTERS: `K4MaskLock` holds, at
some entries es₁, eL and some count cnt, at o, base and the first place e. ITS LETTERS ARE THE BOOK,
K4's PUBLIC DATA, THE FIRST PLACE e, AND THE SENDER's TWO: a closed public fact. (4) and (5) take it
at e := the number of scalars that the prover sends in the lookup (`Forest.elems` at the public
part's own structure); e is a letter of the name so that a test at small made-up data, where no
public part is at hand, can evaluate the named test itself (Law/W/MaskJoinToy.lean). (1)
`k4MaskLockAtB_iff`: IT IS DECIDED AT A WRITTEN BOOK BY A TEST WITH CODE, `k4MaskLockAtB`: no
hypothesis; no test is typed anew: the test is made of calls of `lendsRow`
(Honest/Small/LendsRow.lean), `rowEntries` and `oneStretch` (Honest/BookStretch.lean, of other
writers). (2) `k4MaskLockAt_fixed`: THE BOOK FIXES THE SENDER's LETTERS: at one book, one Qp and one
e the name holds at one pair (o, base) (across two values of e, base and e are fixed in their sum
alone: Law/W/MaskLock.lean's `k4Lock_fixed`; e is no letter of the sender's: it is the verifier's
side's number, public): so where it holds at base it is false at base + 1 and at every other owner:
THE STATEMENT's FORM OF «THE START ONE OFF»; NO TOOTH AT THE JOIN: which pair the sender's sentence
has, only a sender's text can say (at a made-up sender's text, by evaluation:
Law/W/MaskJoinToy.lean). (3) `k4LockAt_member`: whose the members are, under the name. (4)
`k4MaskOwn_at`: the lemma on the sender's lot, under the name. (5) `k4MaskTie_at`: the key turned,
under the name: the end of `k4MaskTie_coinsG` (Law/W/MaskLotGPub.lean), to the letter. In (4) and
(5) the count cnt is gone from hA and hL: they have the shape that `k4MaskEntry_is_owners` has: one
hA, one hE and one hL serve the statements under the name and that one; `k4MaskOwn_of_senderLot` and
`k4MaskTie_of_senderLot` keep the form with cnt.

How. (1): the list's last member and the rest (`List.dropLast_append_getLast?`), and
`k4Cnt_of_lock`. (2): `k4Lock_fixed`. (3) to (5): one call each of `k4Lock_member`,
`k4MaskOwn_of_senderLot` and `k4MaskTie_of_senderLot`, with `k4Cnt_of_lock` for the fences.

Not shown here. THAT ANY BOOK OF THE FULL SIZE MEETS THE NAME AT ANY LETTERS. THAT THE LETTERS AT
WHICH A BOOK MEETS IT ARE A SENDER's: that o is the address of the part that sends the message with
the mask row, and base the number at which that part's text lays the row's first entry: three
writers' numbers meet in it (the book's makers', the sender's, and e, the verifier's side's), and no
file imports all three. IT IS FOR K4's WRITERS TO SHOW. NEVER TO BE SAID FROM THIS FILE: «K4's coins
are the sender's» as had · «lock and key fit» («as had»: as a thing that is shown). The limits of
Law/W/MaskLock.lean and Law/W/MaskOfSenderLot.lean hold here: the field last.lends stands at the
first chain and reads the book's first table alone; hA and hE are sentences on another member's
text; one Vq serves three; one L serves hL and hE; where the thread stands nowhere (5) is empty. Of
the hypotheses of (4) together, and of those of (5), no example is known to us. THE FULL SIZE ALONE,
and the format's second hash function alone, in (5). A program's walk from import to import, which
reads import lines alone and stops unopened at Johnson/Goal/, ThirdParty/, Johnson/D/,
Johnson/Bridge/ and Cb/Bridge*, stopped at 70 modules under Johnson/Goal/, at 7 under
Johnson/Bridge/ and at 1 that begins Cb.Bridge: floors. A LAW, NOT A PART: no file that defines a
part of the proof file's description may import this one. Nothing on soundness, on completeness or
on any other property. No property is claimed.

  `K4MaskLockAt`   **the lock at the sender's letters.** A definition: a hypothesis's form
  `k4MaskLockAtB`, `k4MaskLockAtB_iff`   a test with code decides it
  `k4MaskLockAt_fixed`   **the book fixes the sender's letters**
  `k4LockAt_member`, `k4MaskOwn_at`, `k4MaskTie_at`   the members, the lemma and the key, under the
      name
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskOfSenderLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no standing table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Rt (k4Takes)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgT seatTab dataQ)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead OwnMsgs)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open ProofFile.Honest.K4.Lot (k4MaskLotG k4MaskNum k4PubG)

/-- **THE LOCK AT THE SENDER's LETTERS.** o: the sender's address. base: the number at which its
mask row begins among its coins. e: the first place that K4 reads in that row. The entries and the
count are no letters of the name: the book fixes them. This defines the form of a hypothesis; the
definition claims nothing. -/
def K4MaskLockAt (Bk : ProverCoinCounts) (Qp : K4Pub) (e : ℕ) (o : Addr) (base : ℕ) : Prop :=
  ∃ es₁ eL cnt, K4MaskLock Bk Qp e es₁ eL o base cnt

/-- The same as a test with code: three calls of tests that lie elsewhere. -/
def k4MaskLockAtB (Bk : ProverCoinCounts) (Qp : K4Pub) (e : ℕ) (o : Addr) (base : ℕ) : Bool :=
  lendsRow Bk 0 (k4Place Qp) (k4RowIn Qp) &&
    decide (((rowEntries Bk (k4Place Qp) (k4RowIn Qp).length 0).getLast?.map
      fun f => f.count.e) = some 1) &&
    decide (oneStretch (rowEntries Bk (k4Place Qp) (k4RowIn Qp).length 0).dropLast =
      some (o, base + e, k4Takes Qp.P Qp.hp Qp.g - 1))

variable {Bk : ProverCoinCounts} {Qp : K4Pub} {e : ℕ} {o : Addr} {base : ℕ}

/-- No hypothesis. **THE TEST DECIDES THE NAME.** -/
theorem k4MaskLockAtB_iff :
    k4MaskLockAtB Bk Qp e o base = true ↔ K4MaskLockAt Bk Qp e o base := by
  unfold k4MaskLockAtB K4MaskLockAt
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    obtain ⟨eL, hl, hc⟩ := Option.map_eq_some_iff.1 h2
    exact ⟨_, eL, _, ⟨h1, (List.dropLast_append_getLast? eL hl).symm, hc⟩, h3⟩
  · rintro ⟨es₁, eL, cnt, K⟩
    have hc := k4Cnt_of_lock K
    have hc' : cnt = k4Takes Qp.P Qp.hp Qp.g - 1 := by omega
    refine ⟨⟨K.last.lends, ?_⟩, ?_⟩
    · rw [K.last.ents, List.getLast?_concat]
      exact congrArg some K.last.one
    · rw [K.last.ents, List.dropLast_concat, K.stretch, hc']

/-- CONDITIONAL on J and J'. **THE BOOK FIXES THE SENDER's LETTERS**: at one book, one Qp and one e
the name holds at one pair of letters. -/
theorem k4MaskLockAt_fixed {o' : Addr} {base' : ℕ} (J : K4MaskLockAt Bk Qp e o base)
    (J' : K4MaskLockAt Bk Qp e o' base') : o' = o ∧ base' = base := by
  obtain ⟨_, _, _, K⟩ := J
  obtain ⟨_, _, _, K'⟩ := J'
  obtain ⟨_, _, ho, hb, _⟩ := k4Lock_fixed K K'
  exact ⟨ho, by omega⟩

/-- CONDITIONAL on J. Whose the members are, under the name. -/
theorem k4LockAt_member (J : K4MaskLockAt Bk Qp e o base) (k : Coins Bk) {j : ℕ}
    (hj : j + 1 < k4Takes Qp.P Qp.hp Qp.g) :
    ∃ y, (rowSpentGl Bk (k.look 0) (k4Place Qp) (k4RowIn Qp).length 0)[j]? = some y ∧
      (k.look 0 o).2.eAt (base + e + j) = .ok y := by
  obtain ⟨_, _, _, K⟩ := J
  have hc := k4Cnt_of_lock K
  exact k4Lock_member K k (by omega)

/-- CONDITIONAL on hP, J, hn, hA, hE, hL and OS. **THE LEMMA ON THE SENDER's LOT, UNDER THE
NAME.** -/
theorem k4MaskOwn_at {W₀ Rc Xi Tr X Cl' Tok : Type} {cells : Tr → Cells}
    {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Zp : ProofFile.Pub} {g : ℕ}
    (hP : k4PubG Zp g = some Qp)
    (J : K4MaskLockAt Bk Qp (Forest.elems (P5J.At.X Zp).y.fo) o base)
    (Q : Script Bk (Local W₀ Rc Xi Tr) Cl' Tok MsgT) (nS fS : ℕ)
    (tS : Coins Bk → Local W₀ Rc Xi Tr → List Fmt.Drawn → Bool → ℕ → ℕ → Option Cb.Gl.E)
    (hn : nS = k4MaskNum Zp (2 * g)) {Vq : Local W₀ Rc Xi Tr → Prop} {N : ℕ}
    (hA : ∀ k w (hd : List Fmt.Drawn) ν, Vq w → N ≤ hd.length →
      Forest.elems (P5J.At.X Zp).y.fo ≤ ν →
      ν + 1 < Forest.elems (P5J.At.X Zp).y.fo + k4Takes Qp.P Qp.hp Qp.g →
      (tS k w (hd.take fS) true 0 ν).isSome = true)
    {L : ℕ}
    (hE : ∀ k w hd ν y', ν < L → tS k w hd true 0 ν = some y' →
      (k.look 0 o).2.eAt (base + ν) = .ok y')
    (hL : Forest.elems (P5J.At.X Zp).y.fo + k4Takes Qp.P Qp.hp Qp.g ≤ L + 1)
    (OS : OwnMsgs Q Vq N nS fS tS) :
    OwnMsgs Q Vq N (k4MaskLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g).n
      (k4MaskLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g).fx
      (k4MaskLotG (Bk := Bk) (Rc := Rc) X cells weights tokens look Zp g).txt := by
  obtain ⟨_, _, _, K⟩ := J
  have hc := k4Cnt_of_lock K
  exact k4MaskOwn_of_senderLot hP K Q nS fS tS hn
    (fun k w hd ν hv hN h1 h2 => hA k w hd ν hv hN h1 (by omega)) hE (by omega) OS

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

variable {W₀ Rc Ky Tr X₀ X' : Type}

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL on h, Lh, hQ, J, hn, hA, hE, hL, OS, hT, hV and hN. **THE KEY TURNED, UNDER THE
NAME**: the end of `k4MaskTie_coinsG`. cells, weights, tokens and look stand in no hypothesis and
not in the end: a caller names them. -/
theorem k4MaskTie_at {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard}
    (hQ : k4PubOf Zp x.2 = some Qp)
    (J : K4MaskLockAt Bk Qp (Forest.elems (P5J.At.X Zp).y.fo) o base) (nS fS : ℕ)
    (tS : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Bool → ℕ → ℕ → Option Cb.Gl.E)
    (hn : nS = k4MaskNum Zp (2 * g)) {Vq : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    (hA : ∀ k w (hd : List Fmt.Drawn) ν, Vq w → N ≤ hd.length →
      Forest.elems (P5J.At.X Zp).y.fo ≤ ν →
      ν + 1 < Forest.elems (P5J.At.X Zp).y.fo + k4Takes Qp.P Qp.hp Qp.g →
      (tS k w (hd.take fS) true 0 ν).isSome = true)
    {L : ℕ}
    (hE : ∀ k w hd ν y', ν < L → tS k w hd true 0 ν = some y' →
      (k.look 0 o).2.eAt (base + ν) = .ok y')
    (hL : Forest.elems (P5J.At.X Zp).y.fo + k4Takes Qp.P Qp.hp Qp.g ≤ L + 1)
    (OS : OwnMsgs Q Vq N nS fS tS)
    {c : Coins Bk} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (hV : Vq mm.st.input) (hN : N ≤ mm.st.heard.length) :
    ∀ a, segAt? s = some a → ∀ ds j, j + 1 < k4Takes Qp.P Qp.hp Qp.g →
      (rowSpentGl Bk (c.look 0) (k4Place Qp) (k4RowIn Qp).length 0)[j]? =
        some ((dataQ (h.𝔇.N.sent m 0) a (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms
          ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.wit c mm.st.input
            (mm.st.heard ++ ds)))).mask (a.F.next + j)) := by
  obtain ⟨_, _, _, K⟩ := J
  have hc := k4Cnt_of_lock K
  exact k4MaskTie_of_senderLot h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh (cells := cells)
    (weights := weights) (tokens := tokens) (look := look) hQ K nS fS tS hn
    (fun k w hd ν hv hN h1 h2 => hA k w hd ν hv hN h1 (by omega)) hE (by omega) OS hT hV hN

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4MaskLockAtB_iff
#print axioms ProofFile.Honest.K4.W.k4MaskLockAt_fixed
#print axioms ProofFile.Honest.K4.W.k4LockAt_member
#print axioms ProofFile.Honest.K4.W.k4MaskOwn_at
#print axioms ProofFile.Honest.K4.W.k4MaskTie_at
