-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExchangeOwnReady.lean: CONDITIONAL: on the library's hypothesis
h on the public files and on every hypothesis named. THE FULL SIZE ALONE.

What is here. The thread's debt `ExchangeAtS` at the own item of the member of the feed-forward
layers' own rounds (sub-protocol K4), AT THE PROVER THAT THE FRAME's MAKER `onlineProverFromPublicFiles` RETURNS AND AT
THE THREAD OF A RUN THAT IS READY: `k4_exchange_own_by` (Law/ExchangeOwnBy.lean) at the input R.own
of a return R of the frame's `ready` (Honest/Frame.lean), WITH TWO OF ITS THREE CLAUSES UNDER Vd HAD
FROM ONE PREMISE THAT THE FRAME's OWN STATEMENTS TAKE: hx: the seated description's test on the
instance accepts the run's instance. hVd (the verifier's tests on the request's words accept): by
`hVd_ready` (Law/TokensSeatReady.lean) from «the first chain's first state at the run's instance
bears no mark», which `hmark_of_okStart` (Law/W/MarkOfStart.lean) has from h and hx. hW4 (the
request file is whole words): by `hW4_ready` (here, over `whole_of_okStart`,
Law/W/WholeAtStart.lean, and `own_x_of_ready`, Law/TokensSeatReady.lean: the premise hx of
Honest/Thread/FileYes.lean and its like, at the description `P5J.F0T`). Nothing new is shown: calls.

  `hW4_ready`   the request file in a ready run's own input is whole words; at every Vd.
  `k4_exchange_own_ready`   **`ExchangeAtS T Said k (Item.formsT m 3 "own")`** at R.own's thread.

Not shown here. b1, THE LOOKUP's OWN SENTENCE, WHICH HOLDS ALL THE CONTENT THAT IS LEFT OF THE
BATCHED SUMCHECK's OWN CLAIM, IS MOVED, NOT SHOWN (Law/ExchangeOfTies.lean's head says how): THE
CONCLUSION SPEAKS ONLY WHERE A THREAD STANDS THAT HOLDS IT ALREADY. WHAT STAYS, BY NAME. hR: that a
run is ready; hx: hypotheses; no call of a statement of the frame's is made here: that its premises
are these is by reading. hA, hM, hE, ho: on the filling, as in Law/ExchangeOwnBy.lean: that any
filling has such a lot is not shown here. ONE CLAUSE UNDER Vd: hI (`K4IndexIs`, Law/IndexIs.lean: it
defines a hypothesis; its reader must answer with the index's own matrix, so with 0 outside the
table; the type of an input does not give that; it asks more than is spent). hRdIs, Lh, hb₀, hKp,
hMask, hc: as in Law/ExchangeOwnAt.lean. WHETHER ALL THE HYPOTHESES CAN STAND TOGETHER AT AN HONEST
SCRIPT HAS NOT BEEN TESTED: of h together with hA, hR, hx, hRdIs, Lh, hM, hE, ho, hb₀, hKp, hMask,
hc and hI no example is known to us, and nothing here was evaluated. THAT THE THREAD HOLDS AT ANY
RUN, OR THAT ANY STEP OF THE MEMBER ACCEPTS: the conclusion speaks only where `ThrS` stands and a
step accepts; where none does, it holds emptily. NOT COMPLETENESS. h: the library's hypothesis
`P5J.AtMgA` (Johnson/P5J/MgAtAll.lean). The side library AtFullSide proves, with no hypothesis, that
h has a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean,
whose own Limits say what it is worth). Every limit of the heads of Law/ExchangeOwnBy.lean,
Law/ExchangeOwnAt.lean, Law/ExchangeOfTies.lean and Law/ExchangeTenth.lean holds here. No test that
can fail stands beside it. THE FULL SIZE ALONE, and the format's second hash function alone
(`OnBytes.secondHashFunction`). Nothing on soundness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 81 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 89 is not counted: all the numbers are floors. It
imports files of the frame's authors and of the authors of the kind "lookup". A LAW, NOT A PART: no
file that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExchangeOwnBy
import Johnson.Desc.ProofFile.Honest.K4.Law.TokensSeatReady
import Johnson.Desc.ProofFile.Honest.K4.Law.W.WholeAtStart
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MarkOfStart

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
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open OnBytes.Road.K4 (k4PlaceAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  {w₀ : W₀} {rc : Rc} {ξ : ProofFile.Inst} {kc : Coins Bk}

/-- CONDITIONAL: on hR and hx. **THE REQUEST FILE IN A READY RUN's OWN INPUT IS WHOLE WORDS**, where
the seated description's test on the instance accepts the run's instance; at every Vd. -/
theorem hW4_ready {H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X'} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X'}
    (hR : ready (F0T OnBytes.secondHashFunction Zp Np cF) Bk H w₀ rc ξ kc = .ok R)
    (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true) :
    Vd R.own → R.own.x.pub.request.size % 4 = 0 := by
  intro _
  rw [own_x_of_ready hR]
  exact whole_of_okStart OnBytes.secondHashFunction Zp Np cF hx

/-- CONDITIONAL: on every hypothesis named; the head lists them. **THE EXCHANGE AT THE MEMBER's OWN
ITEM, AT THE MAKER's PROVER AND THE THREAD OF A READY RUN.** ν, st, Rr: the parameters of the
frame's list `csHead`. -/
theorem k4_exchange_own_ready {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {R : Ready W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X'}
    (hR : ready (F0T OnBytes.secondHashFunction Zp Np cF) Bk A.H w₀ rc ξ kc = .ok R)
    (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true)
    (ν : Nat) (st : Nat → TS → Prop) (Rr : Nat → Option Forest.Heard → Prop)
    (hRdIs : Rd = ridersOf (csHead ν st Rr))
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights (fun _ _ => k4LookAt)).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights (fun _ _ => k4LookAt)).halves A.Z A.G)
    (hb₀ : b₀ ≠ k + 1) (hKp : ∀ s s', K4KeepsM s s' → Kp (k4PlaceAt g) s s')
    (hMask : ∀ c s mm E,
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread Said k c s mm E →
      K4MaskTieAt (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread cells
        weights k4Tokens k4LookAt (k4PubAt cF k x) (h.𝔇.N.sent m 0)
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm)
    (hc : ∀ c s mm E,
      ThrS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread Said k c s mm E →
      ∀ d, CellIsList (k4PubAt cF k x)
        (k4Wit (k4PubAt cF k x) cells weights k4Tokens (k4LookAt (k4PubAt cF k x)) mm.st.input)
        ((h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ d))).MG g) x.2.hp.tl)
    (hI : Vd R.own → K4IndexIs Q weights R.own) :
    ExchangeAtS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread Said k
      (Item.formsT m 3 "own") :=
  k4_exchange_own_by h Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own hA ν st Rr hRdIs Said Lh cells
    weights hM hE ho hb₀ hKp hMask hc hI (hVd_ready Vd hR (hmark_of_okStart h hx))
    (hW4_ready Vd hR hx)

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.hW4_ready
#print axioms ProofFile.Honest.K4.W.k4_exchange_own_ready
