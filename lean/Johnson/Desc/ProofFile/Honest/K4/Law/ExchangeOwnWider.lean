-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExchangeOwnWider.lean: CONDITIONAL.

What is here. The thread's debt `ExchangeAtS` at the own item of the member of the feed-forward
layers' own rounds (sub-protocol K4), at the thread with the library's own values (`lettersHead`,
Honest/Thread/FirstHead.lean), AT THE PROVER THAT THE FRAME's MAKER RETURNS AT THE FILLING
`widerFillAt I o S O`: there the prover's list holds K4's half at the member's place by
`half_widerAt` (Law/AtWiderPaid.lean), whose end is the hypothesis half of `k4_exchange_own_still`
(Law/ExchangeOwnStill.lean) to the letter at cells := id and weights := I.weights A.Z; the public
test fits is `fits_lookAt_tokens` (Law/ExchangeOwnBy.lean). So the three hypotheses on the filling's
lots that `k4_exchange_own_by` asks fall away. Nothing new is shown: one call.

  `k4_exchange_own_widerPaid`   **`ExchangeAtS T Said k (Item.formsT m 3 "own")`** at A.H, w₁ free.

Not shown here. WHAT IT LEAVES, BY NAME: h · hA · Lh · hRdIs · hb₀ · hKp · hMask · hQf · hb0 · hc0 ·
hI · hVd · hW4. hA: that the frame's maker returns at that filling. hRdIs: a laying, which a caller
pays by rfl. Lh (`LaidK4`, Law/SeatedHead.lean): `laid_at` (Law/LaidAtGroup.lean) has it under h at
each group. hb₀, hKp: on the thread's own parameters. hMask (`K4MaskTieAt`, Law/ScriptAt.lean), hc0
(`CellIsList`, Law/W/CellsTieOf.lean, at what was heard): on the script, the book and the trace,
wherever `ThrS` stands. hQf (`Script.msgsFit`, Honest/Thread/ScriptFit.lean) and hb0: on the script
and on that test's two parameters: Law/ExchangeOwnStill.lean's head says which two layings of these
would make the pair false, and that whether the pair can hold at an honest script is not shown. hI
(`K4IndexIs`, Law/IndexIs.lean), hVd, hW4: clauses under Vd of the thread's own input. WHAT IT
SPENDS OF THE PAIR ITSELF, WHICH IS NO NAMED HYPOTHESIS: the sentences of the four items that are
open in front and that the row shuts (`.constr m .idn`, `.worth m 2 "planes"`, `.worth m 2 "keys"`,
`.worth m 2 "rider"`: `asks_k4`, Law/W/OpenAtHead.lean) and what the public item `.left m` says
beside its test: they are debts of the members in front; THE LOOKUP's OWN SENTENCE IS SO MOVED, NOT
SHOWN: the conclusion speaks only where a thread stands that holds it already. The side library
AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Of h together with hA, hRdIs, Lh, hb₀, hKp, hMask, hQf, hb0, hc0, hI, hVd and hW4 no
example is known to us. NOT TESTED FOR EMPTINESS. No test that can fail stands beside it. THE FULL
SIZE ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`). Nothing on soundness, on
completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 81 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 89 is not counted: all the numbers are floors. They
come with h, with Law/ExchangeOwnStill.lean and with Law/AtWiderPaid.lean. This file imports files
of the frame's authors, of the authors of the kind "lookup" and of the authors of the filling. A
LAW, NOT A PART: no file that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExchangeOwnStill
import Johnson.Desc.ProofFile.Honest.K4.Law.AtWiderPaid

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
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open OnBytes.Road.K4 (k4PlaceAt pinSeats)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place} {W₀ : Type}
  {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts}
  (Q : Script Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
  (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)

/-- CONDITIONAL: on every hypothesis named; the head lists them. **THE EXCHANGE AT THE MEMBER's OWN
ITEM, AT THE PROVER THAT THE FRAME's MAKER RETURNS AT THE FILLING `widerFillAt`**: no hypothesis on
the prover's list is left; the thread's own input w₁ is free. ν, st, Rr: the parameters of the
frame's list `csHead`. born, nMsg: the parameters of the frame's test on the script. -/
theorem k4_exchange_own_widerPaid {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (ν : Nat) (st : Nat → TS → Prop) (Rr : Nat → Option Forest.Heard → Prop)
    (hRdIs : Rd = ridersOf (csHead ν st Rr))
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (hb₀ : b₀ ≠ k + 1) (hKp : ∀ s s', K4KeepsM s s' → Kp (k4PlaceAt g) s s')
    (hMask : ∀ c s mm E,
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      K4MaskTieAt (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread id
        (I.weights A.Z) k4Tokens k4LookAt (k4PubAt cF k x) (h.𝔇.N.sent m 0)
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm)
    {born : Nat → Nat} {nMsg : Nat}
    (hQf : Q.msgsFit (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.front
      (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs born nMsg = true)
    (hb0 : ∀ y ∈ pinSeats h.𝔇.N m,
      h.𝔇.arr y.1 y.2 < nMsg ∧ born (h.𝔇.arr y.1 y.2) ≤ k)
    (hc0 : ∀ c s mm E,
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      CellIsList (k4PubAt cF k x)
        (k4Wit (k4PubAt cF k x) id (I.weights A.Z) k4Tokens (k4LookAt (k4PubAt cF k x))
          mm.st.input)
        ((h.𝔇.H.hid (Q.wit c mm.st.input mm.st.heard)).MG g) x.2.hp.tl)
    (hI : Vd w₁ → K4IndexIs Q (I.weights A.Z) w₁)
    (hVd : Vd w₁ → reqFine Zp w₁.x.pub = true)
    (hW4 : Vd w₁ → w₁.x.pub.request.size % 4 = 0) :
    ExchangeAtS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k
      (Item.formsT m 3 "own") :=
  k4_exchange_own_still h Q test carryX item n₁ n₂ b₀ Vd Rd Kp A.H w₁ ν st Rr hRdIs Said Lh
    (half_widerAt h Lh hA) (fits_lookAt_tokens h Vd w₁ Lh hVd) hb₀ hKp hMask hQf hb0 hc0 hI hVd hW4

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4_exchange_own_widerPaid
