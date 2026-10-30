-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/SeatedAtBy.lean: CONDITIONAL.

What is here. SIX STATEMENTS OF THIS FOLDER AT THE HONEST PROVER THAT THE FRAME's MAKER `onlineProverFromPublicFiles`
RETURNS (Honest/AtPure.lean), IN A SECOND FORM: THEY NO LONGER ASK THAT K4's LOT ITSELF STANDS IN
THE FILLING's LIST OF LOTS. The elder forms ask hL: `k4HLot cells weights look` is a member of
P.lots. A filling may hold the lot inside a wrapper that picks the reader of the index by the public
part; then hL need hold at no one reader, and the first forms may not be callable. Here hL is
replaced by two hypotheses: hM: some lot M is a member of P.lots; hE: AT THE MAKER's PUBLIC PART AND
GROUND M has the halves of `k4HLot cells weights look`. ho, that no other lot has a half at a place
of the kind K4, keeps its letters: it names the lot's halves, never the lot. `k4Seated_at` and
`k4_accepted_free_at` are the statements from which their elders are made (`k4Seated_tokens`,
Law/TokensSeat.lean; `k4_accepted_last`, Law/LookJoinDear.lean), called at half := `half_atPure_at`
(Law/HalfAtPureBy.lean); the four others call one of this file's. They are: the seat `K4Seated` at a
free `look`; at look := `k4LookAt`; at a ready run typed at the library's description; at a ready
run of the maker's own description, book and prover; and `AcceptedS` at the member with the falls a
variable; at the falls by the member's number. The elder forms are the case M := the lot, hE := rfl.
Each proof is one call.

Not shown here. OF h TOGETHER WITH hA, hM, hE AND ho, AND WITH EACH STATEMENT's OWN (hLk, hVd, hR,
hmark, hf, hm), NO EXAMPLE IS KNOWN TO US (`LaidK4` asks nothing beyond h: `laid_head`,
Law/SeatedHead.lean, at the library's `atK4_full`). THAT ANY FILLING HAS SUCH AN M: no filling is
imported here; that hE holds at a wrapper by unfolding is not held by this file. hA, ho, hLk, hVd,
hR, hmark, hf, hm: hypotheses here, not discharged. THE LIMITS OF Law/FillTop.lean HOLD HERE TOO.
fall IS A FREE LETTER: where it always says something hf holds and `AcceptedS` says nothing.
THAT h CAN HOLD: the side library AtFullSide proves, with no
hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). `K4Seated` IS THE FORM
OF A HYPOTHESIS OF OTHER STATEMENTS; `AcceptedS` speaks only where the thread stands. NOT
COMPLETENESS. THE FULL SIZE ALONE, and at `OnBytes.secondHashFunction` alone. Beneath them stand comparisons by
Lean's own kernel, as the heads of Law/SeatedMember.lean, Law/HgAtPure.lean and
Law/LookAtFill.lean say of themselves; no independent checker has replayed them. It imports files of
the writers of the sub-protocol K3 (lookups) through Law/LookAtFill.lean and Law/LookJoinDear.lean.
A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one:
its imports reach modules under Johnson/Goal/, as those of Law/SeatedHead.lean do. Which modules it
imports in all has not been counted. No property is claimed.

  `k4Seated_at`   **`K4Seated` at the maker's prover**, `look` free; from hLk and hVd.
  `k4Seated_lookAt_at`   **the same at look := `k4LookAt`**: hLk is asked no more.
  `k4Seated_ready_at`   the same at a ready run, typed at the library's description.
  `k4Seated_run_at`   the same at a ready run of the maker's own description, book and prover.
  `k4_accepted_free_at`   **`AcceptedS` at the member**, at every fall under hf.
  `k4_accepted_filled_at`   the same at the falls by the member's number, from hm.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.HalfAtPureBy
import Johnson.Desc.ProofFile.Honest.K4.Law.TokensSeatReady
import Johnson.Desc.ProofFile.Honest.K4.Law.LookAtFill
import Johnson.Desc.ProofFile.Honest.K4.Law.LookJoinDear
import Johnson.Desc.ProofFile.Honest.K4.Law.DescAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X' : Type}

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts}
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)

/-- CONDITIONAL: on h, `LaidK4`, hA, hM, hE, ho, hLk and hVd. **`K4Seated` AT THE MAKER's
PROVER.** `K4Seated` says nothing on what any part sends. -/
theorem k4Seated_at (w : Local W₀ Rc ProofFile.Inst Tr) {P : OnlineProverParts W₀ Rc Tr X₀ X'}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    (hLk : ∀ fr, drawsFit (declsTo cF.blocksInOrder k) fr = true →
      k4LookFits (k4PubAt cF k x) (look Zp A.G (k4PubAt cF k x) fr) = true)
    (hVd : Vd w → reqFine Zp w.x.pub = true) :
    K4Seated (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k cells weights
      k4Tokens (look Zp A.G) (k4PubAt cF k x) { x.2 with k3Runs := true } blk :=
  k4Seated_tokens h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh
    (half_atPure_at h Lh hA cells weights look hM hE ho) hLk hVd

/-- CONDITIONAL: on h, `LaidK4`, hA, hM, hE, ho and hVd. **`K4Seated` AT THE MAKER's PROVER, AT
look := `k4LookAt`.** -/
theorem k4Seated_lookAt_at (w : Local W₀ Rc ProofFile.Inst Tr) {P : OnlineProverParts W₀ Rc Tr X₀ X'}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights (fun _ _ => k4LookAt)).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights (fun _ _ => k4LookAt)).halves A.Z A.G)
    (hVd : Vd w → reqFine Zp w.x.pub = true) :
    K4Seated (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k cells weights
      k4Tokens k4LookAt (k4PubAt cF k x) { x.2 with k3Runs := true } blk :=
  k4Seated_at h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hA Lh cells weights
    (fun _ _ => k4LookAt) hM hE ho (fun fr _ => W.lookFits_lookAt h Lh fr) hVd

/-- CONDITIONAL: on h, `LaidK4`, hA, hM, hE, ho, hR and hmark. **`K4Seated` AT THE THREAD OF A READY
RUN OF THE MAKER's PROVER, AT look := `k4LookAt`**; the run is typed at the library's description
and at any book. Where hmark fails: Law/TokensSeatReady.lean's head says it. -/
theorem k4Seated_ready_at {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights (fun _ _ => k4LookAt)).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights (fun _ _ => k4LookAt)).halves A.Z A.G)
    {w₀ : W₀} {rc : Rc} {ξ : ProofFile.Inst} {kc : Coins Bk}
    {R : Ready W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X'}
    (hR : ready (F0T OnBytes.secondHashFunction Zp Np cF) Bk A.H w₀ rc ξ kc = .ok R)
    (hmark : (ProofFile.startS Zp ξ.pub).failed = none) :
    K4Seated (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread k cells weights
      k4Tokens k4LookAt (k4PubAt cF k x) { x.2 with k3Runs := true } blk :=
  k4Seated_lookAt_at h Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own hA Lh cells weights hM hE ho
    (hVd_ready Vd hR hmark)

/-- CONDITIONAL: on h, `LaidK4`, hA, hM, hE, ho and hf. **`AcceptedS` AT THE MEMBER, AT THE MAKER's
PROVER, AT EVERY FALL UNDER hf.** -/
theorem k4_accepted_free_at (w : Local W₀ Rc ProofFile.Inst Tr) {P : OnlineProverParts W₀ Rc Tr X₀ X'}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    {fall : Nat → TS → List Fmt.Drawn → Option String}
    (hf : ∀ s ds, fall k s ds = none → k4CoinZero (k4PubAt cF k x) ds = none) :
    AcceptedS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall k :=
  k4_accepted_last h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said Lh
    (half_atPure_at h Lh hA cells weights look hM hE ho) hf

/-- CONDITIONAL: on h, `LaidK4`, hA, hM, hE, ho and hm. **The same at the falls by the member's
number** of a list that holds K4's own fall. -/
theorem k4_accepted_filled_at (w : Local W₀ Rc ProofFile.Inst Tr) {P : OnlineProverParts W₀ Rc Tr X₀ X'}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    {fs : List (Fall TS)} (hm : k4Fall (k4PubAt cF k x) ∈ fs) :
    AcceptedS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (fallsBy fs cF.blocksInOrder) k :=
  k4_accepted_free_at h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hA Said Lh cells weights look hM hE
    ho (hf_head Lh hm)

end

/-- CONDITIONAL: on h, `LaidK4`, hA, hM, hE, ho, hR and hmark. **`K4Seated` AT THE THREAD OF A READY
RUN OF THE MAKER's OWN DESCRIPTION, BOOK AND PROVER, AT look := `k4LookAt`.** The script is typed at
the maker's book, so hA stands in front of it. hR there holds every half's fit with that book. -/
theorem k4Seated_run_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (Q : Script A.B (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights (fun _ _ => k4LookAt)).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights (fun _ _ => k4LookAt)).halves A.Z A.G)
    {w₀ : W₀} {rc : Rc} {ξ : ProofFile.Inst} {kc : Coins A.B}
    {R : Ready W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X'}
    (hR : ready A.F A.B A.H w₀ rc ξ kc = .ok R)
    (hmark : (ProofFile.startS Zp ξ.pub).failed = none) :
    K4Seated (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread k cells weights
      k4Tokens k4LookAt (k4PubAt cF k x) { x.2 with k3Runs := true } blk :=
  k4Seated_ready_at h Q test carryX item n₁ n₂ b₀ Vd Rd Kp hA Lh cells weights hM hE ho
    (atPure_desc h hA ▸ hR) hmark

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4Seated_at
#print axioms ProofFile.Honest.K4.k4Seated_lookAt_at
#print axioms ProofFile.Honest.K4.k4Seated_ready_at
#print axioms ProofFile.Honest.K4.k4_accepted_free_at
#print axioms ProofFile.Honest.K4.k4_accepted_filled_at
#print axioms ProofFile.Honest.K4.k4Seated_run_at
