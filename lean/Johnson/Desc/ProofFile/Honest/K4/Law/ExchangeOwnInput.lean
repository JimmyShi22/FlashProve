-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExchangeOwnInput.lean: CONDITIONAL.

What is here. The frame's authors mean to lay the parameter Vd of the first chain's thread as
`ReadyInput F H` (Honest/Thread/ReadyInput.lean): the instance passes the description's okStart, the
index is in range, the trace is the prover's own. Two of the three clauses «Vd w₁ → …» that the laws
on the own item of the feed-forward layers' own rounds (sub-protocol K4) ask are then had from its
first conjunct: hVd by `reqFine_of_okStart` (Law/W/MarkOfStart.lean), hW4 by `whole_of_okStart`
(Law/W/WholeAtStart.lean). With them `k4_exchange_own_widerPaid` (Law/ExchangeOwnWider.lean) is said
at that Vd. THE PARAMETER STANDS AMONG THE THREAD's LETTERS: so the thread in every hypothesis and
in the end is the thread at that Vd. Nothing new is shown: three calls.

  `hVd_of_readyInput`   `reqFine Zp w₁.x.pub = true`, from hv.
  `hW4_of_readyInput`   `w₁.x.pub.request.size % 4 = 0`, from hv.
  `k4_exchange_own_widerInput`   **`ExchangeAtS T Said k (Item.formsT m 3 "own")`** at A.H, w₁ a
      letter, T the thread at Vd := `ReadyInput (F0T OnBytes.secondHashFunction Zp Np cF) A.H`.

Not shown here. WHAT THE TOP LEAVES, BY NAME: h · hA · Lh · hRdIs · hb₀ · hKp · hMask · hQf · hb0 ·
hc0 · hI: Law/ExchangeOwnWider.lean's head says of each what it is. hI IS NOT HAD FROM `ReadyInput`:
it ties the script's cells at w₁ to the reader of the weights (`K4IndexIs`, Law/IndexIs.lean); of
the three conjuncts none reads the script. hv (the first two statements): THAT `ReadyInput` HOLDS OF
ANY INPUT: a hypothesis; by its own head it holds of no input at a request at which the prover's
trace is none, and nothing there puts it into a thread. THE TOP TAKES NO hv, AND THE LIMIT COMES
WITH ITS Vd ALL THE SAME: wherever the thread stands its own input is w₁ and Vd holds of it
(`input_head`, Law/IndexIs.lean): so at a w₁ at which `ReadyInput` fails (okStart refuses; the index
is out of range; the trace is not the prover's own at w₁'s index and instance; so at every w₁ if
that trace is none everywhere) no thread stands, hMask, hc0 and hI are idle, and the top says
nothing: w₁ is a letter: the law does not speak at every input. THAT THE FRAME LAYS Vd SO is its
authors' plan, not a fact of any file. WHAT THE TOP SPENDS OF THE PAIR ITSELF, WHICH IS NO NAMED
HYPOTHESIS: the sentences of the four items that are open in front and that the row shuts, and what
the public item `.left m` says beside its test (Law/ExchangeOwnWider.lean's head): THE LOOKUP's OWN
SENTENCE IS SO MOVED, NOT SHOWN. The side library AtFullSide proves, with no hypothesis, that h has
a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). Of h together with hA, hRdIs, Lh, hb₀, hKp, hMask, hQf, hb0, hc0
and hI no example is known to us; the first two statements take no h. NOT TESTED FOR EMPTINESS. No
test that can fail stands beside them. The top: THE FULL SIZE ALONE; all three: the format's second
hash function alone (`OnBytes.secondHashFunction`). Nothing on soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 81 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 89 is not counted: all the numbers are floors. They
come with h and with Law/ExchangeOwnWider.lean. This file imports files of the frame's authors, of
the authors of the kind "lookup" and of the authors of the filling. A LAW, NOT A PART: no file that
defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExchangeOwnWider
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MarkOfStart
import Johnson.Desc.ProofFile.Honest.K4.Law.W.WholeAtStart
import Johnson.Desc.ProofFile.Honest.Thread.ReadyInput

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT seatTab)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open OnBytes.Road.K4 (k4PlaceAt pinSeats)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

section
variable {W₀ Rc Ky Tr X₀ X' : Type} {H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X'}
  {w₁ : Local W₀ Rc ProofFile.Inst Tr}

/-- CONDITIONAL: on hv. **hVd AT THE FRAME's `ReadyInput`: THE REQUEST PASSES THE VERIFIER's TESTS
ON ITS WORDS THAT READ NO REPLY**: the definition's first clause is okStart. -/
theorem hVd_of_readyInput (hv : ReadyInput (F0T OnBytes.secondHashFunction Zp Np cF) H w₁) :
    reqFine Zp w₁.x.pub = true :=
  reqFine_of_okStart hv.1

/-- CONDITIONAL: on hv. **hW4 AT THE FRAME's `ReadyInput`: THE REQUEST FILE IS WHOLE WORDS.** -/
theorem hW4_of_readyInput (hv : ReadyInput (F0T OnBytes.secondHashFunction Zp Np cF) H w₁) :
    w₁.x.pub.request.size % 4 = 0 :=
  whole_of_okStart OnBytes.secondHashFunction Zp Np cF hv.1

end

variable {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts}
  (Q : Script Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat)
  (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)

/-- CONDITIONAL: on every hypothesis named; the head lists them. **THE EXCHANGE AT THE MEMBER's OWN
ITEM, AT THE FILLING `widerFillAt`, AT THE VALUE THAT THE FRAME's AUTHORS MEAN TO LAY FOR Vd**
(`ReadyInput`): the two clauses under Vd on the request are had; the one on the script's cells
stays. ν, st, Rr: the parameters of the frame's list `csHead`. born, nMsg: the parameters of the
frame's test on the script. -/
theorem k4_exchange_own_widerInput {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (ν : Nat) (st : Nat → TS → Prop) (Rr : Nat → Option Forest.Heard → Prop)
    (hRdIs : Rd = ridersOf (csHead ν st Rr))
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (hb₀ : b₀ ≠ k + 1) (hKp : ∀ s s', K4KeepsM s s' → Kp (k4PlaceAt g) s s')
    (hMask : ∀ c s mm E,
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀
        (ReadyInput (F0T OnBytes.secondHashFunction Zp Np cF) A.H) Rd Kp w₁).thread Said k c s mm E →
      K4MaskTieAt (lettersHead h A.H Q test carryX item n₁ n₂ b₀
        (ReadyInput (F0T OnBytes.secondHashFunction Zp Np cF) A.H) Rd Kp w₁).thread id
        (I.weights A.Z) k4Tokens k4LookAt (k4PubAt cF k x) (h.𝔇.N.sent m 0)
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm)
    {born : Nat → Nat} {nMsg : Nat}
    (hQf : Q.msgsFit (lettersHead h A.H Q test carryX item n₁ n₂ b₀
        (ReadyInput (F0T OnBytes.secondHashFunction Zp Np cF) A.H) Rd Kp w₁).thread.front
      (lettersHead h A.H Q test carryX item n₁ n₂ b₀
        (ReadyInput (F0T OnBytes.secondHashFunction Zp Np cF) A.H) Rd Kp w₁).thread.bs born nMsg = true)
    (hb0 : ∀ y ∈ pinSeats h.𝔇.N m,
      h.𝔇.arr y.1 y.2 < nMsg ∧ born (h.𝔇.arr y.1 y.2) ≤ k)
    (hc0 : ∀ c s mm E,
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀
        (ReadyInput (F0T OnBytes.secondHashFunction Zp Np cF) A.H) Rd Kp w₁).thread Said k c s mm E →
      CellIsList (k4PubAt cF k x)
        (k4Wit (k4PubAt cF k x) id (I.weights A.Z) k4Tokens (k4LookAt (k4PubAt cF k x))
          mm.st.input)
        ((h.𝔇.H.hid (Q.wit c mm.st.input mm.st.heard)).MG g) x.2.hp.tl)
    (hI : ReadyInput (F0T OnBytes.secondHashFunction Zp Np cF) A.H w₁ → K4IndexIs Q (I.weights A.Z) w₁) :
    ExchangeAtS (lettersHead h A.H Q test carryX item n₁ n₂ b₀
        (ReadyInput (F0T OnBytes.secondHashFunction Zp Np cF) A.H) Rd Kp w₁).thread Said k
      (Item.formsT m 3 "own") :=
  k4_exchange_own_widerPaid h Q test carryX item n₁ n₂ b₀ _ Rd Kp w₁ hA ν st Rr hRdIs Said Lh hb₀
    hKp hMask hQf hb0 hc0 hI hVd_of_readyInput hW4_of_readyInput

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.hVd_of_readyInput
#print axioms ProofFile.Honest.K4.W.hW4_of_readyInput
#print axioms ProofFile.Honest.K4.W.k4_exchange_own_widerInput
