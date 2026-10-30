-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/StandsHead.lean: CONDITIONAL.

Not shown here. THAT THE THREAD HOLDS AT ANY RUN: hT : Thr is a hypothesis. THE CLAUSE OF hT THAT IS
SPENT is what the public item `.left m` says beside its test: it is owed behind the member of the
lookup on the calls, and no file of the honest side shows it there. hH (the head's segment is no
layers' segment in the data's list), A (`AtK4`) and Sx (`K4OnX`, Johnson/Road/K4/K4OnX.lean):
hypotheses on public lists and numbers. The side library AtFullSide proves, with no hypothesis, that
h has a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean,
whose own Limits say what it is worth). Of h together with hH, A, Sx, hT, hf and hh (`stands_head`)
no example is known to us; the two general statements take no h: their hypotheses are L, hf and hh
(`stands_of_left`) and ePP, eMore, hH, A, Sx and t (`left_of_promise`). SECTIONS 2 AND 3: THE FULL
SIZE's WRITTEN LISTS ALONE; section 3: the format's second hash function alone (`OnBytes.secondHashFunction`) besides.
Nothing on soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 17 modules under Johnson/Goal/ and at 4 under Johnson/Bridge/; it saw 46 modules whose
names hold RecCompile, none under Johnson/D/ or ThirdParty/, none that begins Cb.Bridge and none of
the three names. What lies behind the 21 is not counted: all the numbers are floors. They come with
h and with Law/PromiseAll.lean.

In front of the member of the feed-forward layers' own rounds (sub-protocol K4) there is a list of
rounds whose end values are what the state holds as heard by the lookup (`K3Stands`,
Johnson/Top/H/K3RowOut.lean): the hypothesis hS of Johnson/Road/K4/W/HotOfRider.lean; and its first
point has as many coordinates as the plan's trees are deep: the hypothesis hsx there. Both out of
the thread: the public item `.left m` is open at that border, and what it says beside its test is
the library's `K3LeftAt` (Johnson/Top/H/K3LeftStatement.lean), which names rounds.

  1  `stands_of_left`   `K3LeftAt` gives `K3Stands` and the size, at the ledger and the heard
     structure that the state holds.
  2  `left_of_promise`   general in the meaning: where every public item that is open in front of
     the member says what it says beside its test, `K3LeftAt` holds at the plan's own values. After
     the proof of `pubP_behind` (Law/PromiseAll.lean).
  3  `stands_head`   **at the thread with the library's own values laid in** (`lettersHead`,
     Honest/Thread/FirstHead.lean), by `thr_pubP` (Honest/Thread/FormLawP.lean).
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PromiseAll
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.FormLawP
import Johnson.Top.H.K3RowOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.K4 (CellsK AtK4 K4OnX k4Means_mgWide left_of_item)
open OnBytes.Road.K4.More (PS)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Wit)
open VerifiableInference.Desc.First (S Meaning pubSets)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.OnPublicFiles (headLink K3LeftAt K3Stands LeftQ)
open VerifiableInference.Desc.Sound (MsgT mgAll mgWide MgData WideData mgBase linksFull moreAll
  mgAll_more_base)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead thr_pubP)

/-! ## 1 From the library's promise behind the lookup -/

/-- **`K3LeftAt` names rounds for which the heard structure stands.** CONDITIONAL: on L, hf and hh.
-/
theorem stands_of_left {St : Type} {fork : St → Option Fork} {heard : St → Option Forest.Heard}
    {fs : Forest.Shape} {lm first : ℕ} {Qf : Fork → Prop} {s : St}
    (L : K3LeftAt fork heard fs lm first Qf s) {g : Forest.Heard} {F' : Fork}
    (hf : fork s = some F') (hh : heard s = some g) :
    K3Stands fs lm first Reading.gl g F' ∧ g.zx.size = fs.dT := by
  obtain ⟨F, F₁, g₁, rs, _, hn, K, hg, hF⟩ := L
  obtain rfl : g₁ = g := Option.some.inj (hg.symm.trans hh)
  obtain rfl : F₁ = F' := Option.some.inj (hF.symm.trans hf)
  have q := K.heardIs
  rw [hn] at q
  exact ⟨⟨rs, q⟩, K.zx⟩

/-! ## 2 Out of what the open public items say -/

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  {Dm : MgData Xi P Tok rows cols nR X}

/-- The closed base, at the witness's type. -/
local notation "Bm" => (mgBase (P := P) (W := Wit (CellsK rows cols) Tok MsgT))

/-- **`K3LeftAt` at the plan's own values, in front of K4's member.** E₀: any value serves: the
library's lemma is stated at the wider meaning, which takes it; the conclusion does not read it.
CONDITIONAL: on ePP, eMore, hH, A, Sx and t. -/
theorem left_of_promise (E₀ : WideData P) {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)}
    {k m : ℕ} {pl : Place} {par : Par} {pol KL : ByteArray} {layout : Option ByteArray}
    (ePP : Mg.pubP = (mgAll Dm Bm).pubP) (eMore : Mg.more = moreAll)
    (hH : isLay Dm.links (headLink X) = false) (A : AtK4 linksFull PS k m pl)
    (Sx : K4OnX X pol KL layout m par) {z : P} {s : S}
    (t : ∀ x ∈ (pubSets Mg.more linksFull PS)[k]?.getD [], Mg.pubP x (z, s)) :
    K3LeftAt S.fork? S.lookHeard? X.y.fo X.y.h.lmb 0 (LeftQ par.hp.ns) s := by
  obtain ⟨oQ, _, _, _⟩ := open_at A
  have Em := k4Means_mgWide Dm E₀ Bm hH (fun _ _ _ _ h => h) fun _ _ _ => rfl
  have eW : (mgWide Dm E₀ Bm).pubP = Mg.pubP := ePP.symm
  have hL : Mg.pubP (.left m) (z, s) := t _ (by rw [eMore, oQ]; simp [k4OpenQ])
  rw [← eW, Em.left] at hL
  exact left_of_item Sx.pubOf Sx.notHead Sx.step Sx.plan hL

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

/-- **WHEREVER THE THREAD STANDS IN FRONT OF K4's MEMBER, WHAT THE LOOKUP HAS HEARD STANDS FOR SOME
ROUNDS**, at the plan's shape of the trees, its number of mask bits and the first slot 0; and its
first point has the trees' depth. E₀: any value serves. CONDITIONAL: on h, hH, A, Sx, hT, hf and hh.
-/
theorem stands_head (E₀ : WideData ProofFile.InstPub) {k m : ℕ} {pl : Place} {par : Par}
    {pol KL : ByteArray} {layout : Option ByteArray}
    (hH : isLay h.𝔇.links (headLink (P5J.At.X Zp)) = false) (A : AtK4 linksFull PS k m pl)
    (Sx : K4OnX (P5J.At.X Zp) pol KL layout m par) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    {g : Forest.Heard} {F' : Fork} (hf : s.fork? = some F') (hh : s.lookHeard? = some g) :
    K3Stands (P5J.At.X Zp).y.fo (P5J.At.X Zp).y.h.lmb 0 Reading.gl g F' ∧
      g.zx.size = (P5J.At.X Zp).y.fo.dT :=
  stands_of_left
    (left_of_promise (Dm := h.𝔇) E₀
      (Mg := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP) rfl
      (mgAll_more_base h.𝔇) hH A Sx
      (fun _ hq => thr_pubP (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) hT hq)) hf hh

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.stands_of_left
#print axioms ProofFile.Honest.K4.W.left_of_promise
#print axioms ProofFile.Honest.K4.W.stands_head
