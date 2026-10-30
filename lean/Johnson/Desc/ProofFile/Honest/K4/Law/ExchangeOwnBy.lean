-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExchangeOwnBy.lean: CONDITIONAL: on the library's hypothesis h
on the public files and on every hypothesis named. THE FULL SIZE ALONE.

What is here. The thread's debt `ExchangeAtS` at the own item of the member of the feed-forward
layers' own rounds (sub-protocol K4), AT THE PROVER THAT THE FRAME's MAKER `onlineProverFromPublicFiles` RETURNS
(Honest/AtPure.lean), FOR A FILLING THAT NEED NOT HOLD K4's LOT ITSELF, BUT A LOT WITH THE SAME
HALVES: `k4_exchange_own_at` (Law/ExchangeOwnAt.lean) with its two hypotheses on the seat had from
statements of other files: half from `half_atPure_at` (Law/HalfAtPureBy.lean): hA: the maker
returns; hM: a lot M is a member of the filling's list; hE: at the maker's own public part and
ground M has the halves of `k4HLot cells weights (fun _ _ => k4LookAt)`; ho: no other lot of the
filling has a half at a place of the kind K4, or it has the same halves; and fits from
`fits_lookAt_tokens`, here: the public test `k4Fits` whole (`fits_member`, Law/FitsMember.lean) at
the test on what the lookup has sampled (`lookFits_lookAt`, Law/LookAtFill.lean) and the test on the
tokens (`tokensSeat_member`, Law/TokensSeat.lean). It is the like, for the own item, of
`k4_exchange_wo_at` (Law/TopsAt.lean). Nothing new is shown: calls.

  `fits_lookAt_tokens`   the hypothesis fits of the tops, at `k4LookAt` and `k4Tokens`, from hVd.
  `k4_exchange_own_by`   **`ExchangeAtS T Said k (Item.formsT m 3 "own")`** at the maker's prover.

Not shown here. b1, THE LOOKUP's OWN SENTENCE, WHICH HOLDS ALL THE CONTENT THAT IS LEFT OF THE
BATCHED SUMCHECK's OWN CLAIM, IS MOVED, NOT SHOWN (Law/ExchangeOfTies.lean's head says how): THE
CONCLUSION SPEAKS ONLY WHERE A THREAD STANDS THAT HOLDS IT ALREADY. WHAT STAYS, BY NAME. hA, hM, hE,
ho: on the filling: THAT ANY FILLING HAS SUCH A LOT M IS NOT SHOWN HERE: no filling is imported;
that hE holds at a wrapped lot by unfolding is not held by this file; that `onlineProverFromPublicFiles` returns at any
filling is not shown here. THREE CLAUSES UNDER Vd, on the thread's own input: hI (`K4IndexIs`,
Law/IndexIs.lean: it defines a hypothesis; its reader must answer with the index's own matrix, so
with 0 outside the table; the type of an input does not give that; it asks more than is spent) · hVd
(`reqFine`, Law/TokensSeat.lean: the verifier's tests on the request's words accept) · hW4 (the
request file is whole words: Law/W/WholeWords.lean and Law/W/WholeAtStart.lean name who has it).
hRdIs, Lh, hb₀, hKp, hMask, hc: as in Law/ExchangeOwnAt.lean; hc (`CellIsList`): the honest cells
against the list that the library's reader makes of the witness; Law/ExchangeOwnStill.lean asks it
at what was heard alone. WHETHER ALL THE HYPOTHESES CAN STAND TOGETHER AT AN HONEST SCRIPT HAS NOT
BEEN TESTED: of h together with Lh, hVd, hA, hRdIs, hM, hE, ho, hb₀, hKp, hMask, hc, hI and hW4 no
example is known to us, and nothing here was evaluated. THAT THE THREAD HOLDS AT ANY RUN, OR THAT
ANY STEP OF THE MEMBER ACCEPTS: the conclusion speaks only where `ThrS` stands and a step accepts;
where none does, it holds emptily. NOT COMPLETENESS. h: the library's hypothesis `P5J.AtMgA`
(Johnson/P5J/MgAtAll.lean). The side library AtFullSide proves, with no hypothesis, that h has a
member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). Every limit of the heads of Law/ExchangeOwnAt.lean,
Law/ExchangeOfTies.lean and Law/ExchangeTenth.lean holds here. Beneath `half_atPure_at`,
`fits_member` and `lookFits_lookAt` stand comparisons by Lean's own kernel that no independent
checker has replayed (Law/FitsMember.lean's head names them). No test that can fail stands beside
it. THE FULL SIZE ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`). Nothing on
soundness or on any other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 81 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 89 is not counted: all the numbers are floors. It
imports files of the frame's authors and of the authors of the kind "lookup". A LAW, NOT A PART: no
file that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExchangeOwnAt
import Johnson.Desc.ProofFile.Honest.K4.Law.HalfAtPureBy
import Johnson.Desc.ProofFile.Honest.K4.Law.LookAtFill
import Johnson.Desc.ProofFile.Honest.K4.Law.FitsMember
import Johnson.Desc.ProofFile.Honest.K4.Law.TokensSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block First.S)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT seatTab)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open OnBytes.Road.K4 (k4PlaceAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Tr X₀ X' : Type}
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

include h in
/-- CONDITIONAL: on h, Lh and hVd. **THE PUBLIC TEST `k4Fits`, WHOLE, AT THE TEXT `k4LookAt` AND THE
LOT's OWN READER OF THE TOKENS**, at every list of challenges, from one clause under Vd. -/
theorem fits_lookAt_tokens {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) (hVd : Vd w₁ → reqFine Zp w₁.x.pub = true) :
    ∀ fr, drawsFit (declsTo cF.blocksInOrder k) fr = true → Vd w₁ →
      k4Fits (k4PubAt cF k x) (k4LookAt (k4PubAt cF k x) fr) (k4Tokens w₁.x) = true :=
  fun fr _ hv =>
    fits_member h Lh (lookFits_lookAt h Lh fr) (tokensSeat_member h Lh w₁.x (hVd hv))

/-- CONDITIONAL: on every hypothesis named; the head lists them. **THE EXCHANGE AT THE MEMBER's OWN
ITEM, AT THE PROVER THAT THE FRAME's MAKER RETURNS**, for a filling with a lot that has the halves
of K4's lot at look := `k4LookAt`. ν, st, R: the parameters of the frame's list `csHead`. -/
theorem k4_exchange_own_by {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option Forest.Heard → Prop)
    (hRdIs : Rd = ridersOf (csHead ν st R))
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights (fun _ _ => k4LookAt)).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights (fun _ _ => k4LookAt)).halves A.Z A.G)
    (hb₀ : b₀ ≠ k + 1) (hKp : ∀ s s', K4KeepsM s s' → Kp (k4PlaceAt g) s s')
    (hMask : ∀ c s mm E,
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      K4MaskTieAt (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells weights
        k4Tokens k4LookAt (k4PubAt cF k x) (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm)
    (hc : ∀ c s mm E,
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      ∀ d, CellIsList (k4PubAt cF k x)
        (k4Wit (k4PubAt cF k x) cells weights k4Tokens (k4LookAt (k4PubAt cF k x)) mm.st.input)
        ((h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ d))).MG g) x.2.hp.tl)
    (hI : Vd w₁ → K4IndexIs Q weights w₁)
    (hVd : Vd w₁ → reqFine Zp w₁.x.pub = true)
    (hW4 : Vd w₁ → w₁.x.pub.request.size % 4 = 0) :
    ExchangeAtS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k
      (Item.formsT m 3 "own") :=
  k4_exchange_own_at h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ ν st R hRdIs Said Lh
    (half_atPure_at h Lh hA cells weights (fun _ _ => k4LookAt) hM hE ho)
    (fits_lookAt_tokens h Vd w₁ Lh hVd) hb₀ hKp hMask hc hI hVd hW4

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.fits_lookAt_tokens
#print axioms ProofFile.Honest.K4.W.k4_exchange_own_by
