-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/ExchangeParts.lean: CONDITIONAL.

What is here. Three hypotheses of `k4_exchangeAtS_own_of_foot` (Law/W/ExchangeOfFoot.lean: the
thread's debt at the own item of the member of the feed-forward layers' own rounds, sub-protocol
K4), at the thread with the library's own values (`lettersHead`, Honest/Thread/FirstHead.lean):
`K4Table`, wholly; the seat at every member at that number, under four hypotheses; and `K4Front`
(Law/Kept.lean), of whose eight clauses three are paid: the two on the link's runs and the public
flag. Each proof is a call or two.

  `k4Table_head`   **`K4Table`** at own := the seats that the segment sends at its first moment and
      rdOf := the witness's tables at the seats: `k4Table_at` (Law/TableAt.lean) at the thread's
      values.
  `seated_all_head`   `K4Seated` at every member at the number k: there is one (`member_head`).
  `K4FrontFive`   the five clauses of `K4FrontAt` (Law/Kept.lean) that stay, each in its own text. A
      definition.
  `k4Front_of_five`   `K4Front` from them, the link's two runs and the flag. General in the thread.
  `k4Front_head`   **`K4Front` at the thread**, from the five alone.

Not shown here. h: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): a proposition on
the public files Z, the public part Zp and the first chain cF. In this file Q is the Script and Qp
the public data. THE FIVE CLAUSES OF `K4FrontFive`: hypotheses. For asks `keptAsks_own`
(Law/RunsAtStand.lean) has it at a stand from three smaller hypotheses, and a stand itself takes one
clause of asks; Law/FrontHead.lean has asks at the thread with no stand, so there is no circle; the
hypothesis hAsk of the pending row's share (Law/WoShare.lean) ends in this clause's own proposition:
one debt, not two. For test `test_head` (Law/W/TestHead.lean) has it from the thread's debt
`Behind`. For names and reads Law/FrontHead.lean has them at the thread; for stated
Law/StatedHead.lean, at one list of the arrays' names. hQ, half, front, fits: the four hypotheses of
`k4Seated_letters` (Law/SeatedHead.lean); `k4Fits_everywhere` (Law/MakersSkel.lean) has the test of
fits at every list of one skeleton from the test at one list; it is not called here. hl: the data
have a link at the segment (`K4Nine.runs`, Law/ElevenHead.lean, has one under h and `LaidK4`). The
side library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Of h together with Lh and hl (`k4Table_head`), with Lh, hQ, half, front and fits
(`seated_all_head`) or with Lh, hl and h5 (`k4Front_head`) no example is known to us;
`k4Front_of_five` takes no h: its hypotheses are st, hr and h5. `k4Front_of_five` is general in the
thread; the others: THE FULL SIZE ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`).
Nothing on soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 70 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 78 is not counted: all the numbers are floors. They
come with h and with Law/ElevenHead.lean. A LAW, NOT A PART: no file that defines a part of the
proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ElevenHead
import Johnson.Desc.ProofFile.Honest.K4.Law.TableAt
import Johnson.Desc.ProofFile.Honest.K4.Law.Kept

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Desc.First.K4.Total (KeptAsks)
open OnBytes.Road.K4 (StatedAt readsArrayB parOf)
open OnBytes.Road.K4.InT (StatesAt)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block Link Claim First.S)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.K9 (segAt? LinkHoles statesOfLink readersOfLink formsInT)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgT MsgQ Stated second dataQ seatTab)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4 member_head k4Seated_letters)

/-! ## 1 The five clauses that stay -/

/-- **The five clauses of `K4FrontAt` that stay**, each in its own text. This defines a hypothesis;
the definition claims nothing. -/
structure K4FrontFive {Wt : Type} (M : First.S → Bound GQ → Road.Mats GQ) (Hh : LinkHoles)
    (l : Link First.S Claim) (St : Stated) (own : List (Nat × Nat)) (rd : Wt → Nat × Nat → MsgQ)
    (tl : HTailF2) (p : Par) (s s' : First.S) (v : Wt) : Prop where
  /-- tests on the state in front, and the plan's public test -/
  asks : ∃ (P₀ : Layer.Pub) (o₀ : Own), KeptAsks p s s' P₀ o₀
  /-- the lookup's promise on the names of its pad -/
  names : ∀ a fo, s.here = .lay a → a.fo = some fo → _root_.Fo.Tp.PadNames fo a.F
  /-- the reads' array is there behind the step -/
  reads : readsArrayB p.hp s' = true
  /-- at the reads' array the stated function's cells are the true entries -/
  stated : ∀ A' o c, segAt? s' = some A' → s'.own? = some o → A'.L.arrayOf[o.v.iU3]? = some c →
    second s' c = true → StatedAt St M s' tl o c (p.hp.nU.getD 2 0) (dataQ own A' (rd v))
  /-- the table's public test at both runs -/
  test : ∀ q ∈ [(2, "front"), (2, "back")], formsInT (readersOfLink Hh l) own q.1 q.2 s' = true

/-- **`K4Front` from the five, the link's two runs and the flag.** CONDITIONAL: on st, hr and h5. -/
theorem k4Front_of_five {Bk : ProverCoinCounts} {V W X Pb : Type} {T : Thread Bk First.S Claim V W X Pb}
    {At : Coins Bk → First.S → Mid W X → Env → Prop} {b : Nat}
    {M : First.S → Bound GQ → Road.Mats GQ} {Hh : LinkHoles} {l : Link First.S Claim} {St : Stated}
    {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ} {tl : HTailF2} {p : Par}
    (st : ∀ u, StatesAt (statesOfLink l) 2 p "front" u ∧ StatesAt (statesOfLink l) 2 p "back" u)
    (hr : p.k3Runs = true)
    (h5 : ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', At k s m E →
      drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' → ∀ ds',
      K4FrontFive M Hh l St own rdOf tl p s s' (T.wit k y.2.st.input (y.2.st.heard ++ ds'))) :
    K4Front T At b M Hh l St own rdOf tl p := by
  intro blk hb k s m E ds y cols s' hA hd hS ds'
  have F := h5 blk hb k s m E ds y cols s' hA hd hS ds'
  exact ⟨F.asks, F.names, F.reads, (st s').1, (st s').2, hr, F.stated, F.test⟩

/-! ## 2 At the thread with the library's own values -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **`K4Table` AT THE THREAD.** l: the data's link at the segment. CONDITIONAL: on h, Lh and hl. -/
theorem k4Table_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {l : Link TS ProofFile.Cl} (hl : h.𝔇.lk m = some l) :
    K4Table (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k
      (Item.formsT m 3 "own") (Item.formsT m 2 "planes") (Item.formsT m 2 "join") (restK4 m)
      (holesK4 Zp m l) l h.𝔇.St (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) :=
  k4Table_at h _ Q _ _ test carryX item n₁ n₂ _ _ _ (atK4_of_laid Lh) hl

/-- **`K4Seated` AT EVERY MEMBER AT THE NUMBER k.** CONDITIONAL: on h, Lh, hQ, half, front and
fits. -/
theorem seated_all_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp)
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights tokens look Qp))
    (front : Qp.r0 = roundsTo cF.blocksInOrder k)
    (fits : ∀ fr, drawsFit (declsTo cF.blocksInOrder k) fr = true → Vd w₁ →
      k4Fits Qp (look Qp fr) (tokens w₁.x) = true) :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      K4Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k cells weights
        tokens look Qp (parOf x) blk := by
  intro blk hb
  obtain rfl : blk₀ = blk := Option.some.inj
    ((member_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh).symm.trans hb)
  exact k4Seated_letters h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQ half front fits

/-- **`K4Front` AT THE THREAD, FROM THE FIVE ALONE.** At: any hypothesis on where the run stands.
CONDITIONAL: on h, Lh, hl and h5. -/
theorem k4Front_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {l : Link TS ProofFile.Cl} (hl : h.𝔇.lk m = some l)
    {At : Coins Bk → TS → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Env → Prop}
    {M : TS → Bound GQ → Road.Mats GQ} {Hh : LinkHoles} {St : Stated} {own : List (ℕ × ℕ)}
    {rdOf : WtF → ℕ × ℕ → MsgQ} {tl : HTailF2}
    (h5 : ∀ blk,
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk →
      ∀ c s mm E ds y cols s', At c s mm E → drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
        cols s' → ∀ ds',
      K4FrontFive M Hh l St own rdOf tl (parOf x) s s'
        (Q.wit c y.2.st.input (y.2.st.heard ++ ds'))) :
    K4Front (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread At k M Hh l St own
      rdOf tl (parOf x) := by
  obtain ⟨l', _, _, hl', st, _⟩ := (nine_head h Lh).runs
  obtain rfl : l' = l := Option.some.inj (hl'.symm.trans hl)
  exact k4Front_of_five st rfl h5

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4Front_of_five
#print axioms ProofFile.Honest.K4.W.k4Table_head
#print axioms ProofFile.Honest.K4.W.seated_all_head
#print axioms ProofFile.Honest.K4.W.k4Front_head
