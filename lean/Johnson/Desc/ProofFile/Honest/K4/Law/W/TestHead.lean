-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/TestHead.lean: CONDITIONAL.

What is here. The clause test of `K4FrontAt` (Law/Kept.lean) and of `K4FrontFive`
(Law/W/ExchangeParts.lean): the table's public test at the two runs of the member of the
feed-forward layers' own rounds (sub-protocol K4), at the state behind the member's step: at the
thread with the library's own values (`lettersHead`, Honest/Thread/FirstHead.lean). The table ties a
public item to each open item (`pubOfItems`, Johnson/Desc/First/Borders.lean); behind K4's member
its own item is open, so the tied item `.formsInT m 3 "own"` is among those whose tests the thread's
form holds there; and that test is, by the library's `K4Means.formsInT`
(Johnson/Road/K4/K4Means.lean), `runs_own` (Law/TableAt.lean) and `readersAt_some`, the clause to
the letter.

  1  `k4TiedFitAt`, `k4_tied_full`, `k4_tied_front`, `tied_at`   a test on the table, decided by the
     kernel: behind every place of K4's the tied item is among the tied ones; a negative test: one
     border earlier the test says false (so at some place it is not among them in front).
  2  `form_tied`   general in the first chain's parameters: the thread's form holds the test of
     every public item that is tied to an open item. After `thr_pub` (Honest/Thread/FormLaw.lean),
     which has the open public items.
     `test_of_pub`   general in the meaning: the tied item's test is the test at the data's runs.
  3  `test_head`   **the clause test at the thread.**

Not shown here. THAT THE THREAD HOLDS AT ANY RUN, OR THAT ANY STEP OF THE MEMBER ACCEPTS: hT and hS
are hypotheses. hBh: the thread's debt `Behind` (Honest/Thread/Pays.lean) at the member: a
hypothesis here; `k4_behind_all` (Law/ElevenHead.lean) has it under h, `AtK4` and three hypotheses
on the thread's own parameters. hl: the data have a link at the segment. The side library AtFullSide
proves, with no hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). Of h together with
hBh, Lh, hl, hb, hT, hd and hS (`test_head`) no example is known to us; the others take no h: A
(`tied_at`), hF and hq (`form_tied`), ePub, hH and e (`test_of_pub`). Sections 1 and 3: THE FULL
SIZE's WRITTEN LISTS ALONE; section 3: the format's second hash function alone (`OnBytes.secondHashFunction`) besides.
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
import Johnson.Desc.ProofFile.Honest.K4.Law.W.ExchangeParts
import Johnson.Desc.ProofFile.Honest.Thread.FormLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.K4 (CellsK AtK4 k4Means_mgWide eAll)
open OnBytes.Road.K4.More (PS)
open OnBytes.Road.K4.Riders (atK4s atK4s_at)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block Link Wit)
open VerifiableInference.Desc.First (S Meaning onAt openSets pubSets pubHeld pubOfItems start pubAll
  pubWide_hand)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.Desc.K9 (readersOfLink readersAt_some formsInT)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.Sound (MsgT mgWide MgData WideData mgBase linksFull)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Letters Script WtF lettersHead noStrs)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-- The table's public items (`Pub` alone would name another type in this namespace). -/
local notation "PubI" => VerifiableInference.Desc.First.Pub

/-! ## 1 The tied item behind the member -/

/-- A TEST ON THE TABLE, at the full size's written lists: at every place of the sub-protocol, j
borders further on, the public item that is tied to K4's own item is among the tied ones. -/
def k4TiedFitAt (j : Nat) : Bool :=
  atK4s linksFull PS fun k m =>
    decide ((.formsInT m 3 "own" : PubI) ∈
      pubOfItems ((openSets linksFull PS (start linksFull))[k + j]?.getD []))

set_option maxRecDepth 1000000 in
theorem k4_tied_full : k4TiedFitAt 1 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: one border earlier the test says false: at some place of the sub-protocol the
item is not among the tied ones in front. -/
theorem k4_tied_front : k4TiedFitAt 0 = false := by decide +kernel

/-- CONDITIONAL: on A. -/
theorem tied_at {k m : Nat} {pl : Place} (A : AtK4 linksFull PS k m pl) :
    (.formsInT m 3 "own" : PubI) ∈
      pubOfItems ((openSets linksFull PS (start linksFull))[k + 1]?.getD []) := by
  have h0 := k4_tied_full
  unfold k4TiedFitAt at h0
  exact of_decide_eq_true (atK4s_at A h0)

/-! ## 2 The form holds the tied items' tests -/

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}

/-- **THE TEST OF EVERY PUBLIC ITEM THAT IS TIED TO AN OPEN ITEM HOLDS OF THE STATE**, wherever the
thread's form holds. CONDITIONAL: on hF and hq. -/
theorem form_tied (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M) {b : Nat} {k : Coins Bk} {s : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} (hF : L.thread.Form b k s m) {q : PubI}
    (hq : q ∈ pubOfItems (((openSets L.links L.ps (start L.links))[b]?).getD [])) :
    L.mgP.pub q (L.pubOf m.st.input.x, s) = true := by
  obtain ⟨hf, hP⟩ := hF
  have hf' : s.failed.isNone = true := hf
  have hP' : onAt L.N L.mgP L.links L.ps[b]?
      (((openSets L.links L.ps (start L.links))[b]?).getD [])
      (((pubSets L.mgP.more L.links L.ps)[b]?).getD []) (L.pubOf m.st.input.x, s) noStrs := hP
  obtain ⟨-, hP2⟩ := hP'
  rcases hP2 with hm | ⟨hB, -⟩
  · exfalso
    have hm' : s.failed ≠ none := hm
    cases hs : s.failed with
    | none => exact hm' hs
    | some e =>
      rw [hs] at hf'
      cases hf'
  · simp only [Bool.and_eq_true] at hB
    obtain ⟨⟨-, hpub⟩, -⟩ := hB
    unfold pubHeld at hpub
    exact List.all_eq_true.1 hpub q (List.mem_append_right _ hq)

end

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  {Dm : MgData Xi P Tok rows cols nR X}

/-- The closed base, at the witness's type. -/
local notation "Bm" => (mgBase (P := P) (W := Wit (CellsK rows cols) Tok MsgT))

/-- **The tied item's test is the table's test at the data's runs.** E₀: any value serves: the
library's lemma is stated at the wider meaning, which takes it; the conclusion does not read it.
CONDITIONAL: on ePub, hH and e. -/
theorem test_of_pub (E₀ : WideData P) {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)}
    (ePub : Mg.pub = pubAll Dm.pubD (Bm).pub) (hH : isLay Dm.links (headLink X) = false)
    {m k : ℕ} {rn : String} {z : P} {s : S} (e : Mg.pub (.formsInT m k rn) (z, s) = true) :
    ((Dm.runs m k rn).all fun p => formsInT (Dm.Rd m) (Dm.N.sent m 0) p.1 p.2 s) = true := by
  have Em := k4Means_mgWide Dm E₀ Bm hH (fun _ _ _ _ h => h) fun _ _ _ => rfl
  have hand : (mgWide Dm E₀ Bm).pub (.formsInT m k rn) (z, s) =
      Mg.pub (.formsInT m k rn) (z, s) := by
    rw [ePub]
    exact pubWide_hand E₀.d12 E₀.dP Dm.pubD (Bm).pub (.formsInT m k rn) rfl (z, s)
  rw [← hand, Em.formsInT] at e
  exact e

end

/-! ## 3 At the thread with the library's own values -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE CLAUSE test, BEHIND THE MEMBER's STEP.** l: the data's link at the segment. CONDITIONAL:
on h, hBh, Lh, hl, hb, hT, hd and hS. -/
theorem test_head
    {k m g : ℕ} (hBh : Behind (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k)
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {l : Link TS ProofFile.Cl} (hl : h.𝔇.lk m = some l) {blk : Block TS ProofFile.Cl}
    (hb : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk)
    {c : Coins Bk} {s s' : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (hd : drawsFit blk.rounds ds = true)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
      cols s') :
    ∀ q ∈ [(2, "front"), (2, "back")],
      formsInT (readersOfLink (holesK4 Zp m l) l) (h.𝔇.N.sent m 0) q.1 q.2 s' = true := by
  have A := atK4_of_laid Lh
  have F := (hBh blk hb c s mm E ds y cols s' hT hd hS).1
  have e := form_tied (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) F (tied_at A)
  have t := test_of_pub (Dm := h.𝔇) (eAll Zp cF VerifiableInference.Desc.K13.Law.LFull)
    (Mg := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP) rfl (nine_head h Lh).hH e
  have hsub : h.𝔇.links[m]? = some VerifiableInference.Desc.First.ModelPart.layers := A.sub
  have e2 : h.𝔇.Rd m = readersOfLink (holesK4 Zp m l) l := readersAt_some h.𝔇.lk _ _ m l hl
  rw [runs_own h hsub, e2] at t
  exact fun q hq => List.all_eq_true.1 t q hq

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4_tied_full
#print axioms ProofFile.Honest.K4.W.k4_tied_front
#print axioms ProofFile.Honest.K4.W.tied_at
#print axioms ProofFile.Honest.K4.W.form_tied
#print axioms ProofFile.Honest.K4.W.test_of_pub
#print axioms ProofFile.Honest.K4.W.test_head
