-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/LookPtsHead.lean: CONDITIONAL.

What is here. The hypothesis `K4LookPtsAt` (Law/W/LookTieHead.lean: the three equations that are
left of `K4LookTieAt`: the fields zx, zk and e of what the verifier's state holds of the lookup's
hearing are what the parameter `look` makes of the challenges heard), at the thread with the
library's own values (`lettersHead`, Honest/Thread/FirstHead.lean), in front of the member of the
feed-forward layers' own rounds (sub-protocol K4): BROUGHT DOWN TO A SENTENCE ON THE PARAMETER
`look` ALONE. The authors of the kind "lookup" have a text for what the lookup on the calls of a
layers' link returns, made of the public shape and the challenges alone (`lookOfK3`,
Honest/K3/Law/Thread/LayersTieHead.lean), and, under h, the law that the state which the first 28 g
+ 4 members make of any rounds agrees with that text in eleven fields (`layers_tie_head`, there).
The thread's clause `Made` (Honest/Thread/Thr.lean) says that the state in front of our member is
that fold over the rounds seen, and that these rounds' challenges are the challenges heard. So the
three equations hold wherever the thread stands, if `look` agrees with `lookOfK3` in the three
fields (`LookIsK3`). With `lookTie_head`: `K4LookTieAt` too. Each proof is a chain of calls.

  `LookIsK3`   THE SENTENCE ON `look`. A definition.
  `lookPts_head`   **`K4LookPtsAt look Qp s mm`**, from it.
  `lookTie_k3`   **`K4LookTieAt look Qp s mm`**, from it.

Not shown here. h: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): a proposition on
the public files Z, the public part Zp and the first chain cF. THAT THE THREAD HOLDS AT ANY RUN: hT
: Thr is a hypothesis. hL (`LookIsK3`): A HYPOTHESIS ON THE PARAMETER `look`, AT EVERY LIST OF
CHALLENGES: no state, no witness and no sent value stands in it: it is a matter of how whoever lays
the prover's halves fills `look`; that any half is laid over such a `look` is not shown here:
`k4LookAt_head` (Law/LookAtHead.lean) has the sentence at the text `k4LookAt` (Honest/K4/Look.lean).
`lookOfK3` lays eleven fields and leaves the structure's eight others blank; three of the eleven are
read here. By its authors' word it has been evaluated at no data. Lh (`LaidK4`,
Law/SeatedHead.lean): on public lists and numbers. The side library AtFullSide proves, with no
hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). Of h together with Lh,
hT and hL no example is known to us. THE FULL SIZE ALONE, and the format's second hash function alone
(`OnBytes.secondHashFunction`). Nothing on soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 80 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 88 is not counted: all the numbers are floors. IT
IMPORTS A FILE OF THE AUTHORS OF THE KIND "lookup" (Honest/K3/Law/Thread/LayersTieHead.lean). A LAW,
NOT A PART: no file that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.LookTieHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LayersTieHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Road.K4 (eAll)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block foldBlocks)
open VerifiableInference.Desc.First.FillK4 (lookLayB)
open VerifiableInference.Desc.Sound (MsgT mgAll_more_base)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead thr_pub)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open ProofFile.Honest.K3.Law.AtThr (lookOfK3 layers_tie_head)

/-- **THE SENTENCE ON `look`**: at every list of challenges it agrees with the text of the authors
of the kind "lookup" in the fields zx, zk and e. ξ: an instance; that text does not read it. This
defines a hypothesis; the definition claims nothing. -/
def LookIsK3 (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Q : K4Pub) (Zp : ProofFile.Pub)
    (cF : Chain TS ProofFile.Cl) (g : ℕ) (ξ : ProofFile.Inst) : Prop :=
  ∀ hd, (look Q hd).zx = (lookOfK3 Zp cF g ξ hd).zx ∧ (look Q hd).zk = (lookOfK3 Zp cF g ξ hd).zk ∧
    (look Q hd).e = (lookOfK3 Zp cF g ξ hd).e

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL: on h, Lh, hT and hL. **THE THREE EQUATIONS, WHERE THE THREAD STANDS.** -/
theorem lookPts_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hL : LookIsK3 look Qp Zp cF g mm.st.input.x) : K4LookPtsAt look Qp s mm := by
  intro g₁ hg1
  have N := nine_head h Lh
  obtain ⟨_, t2⟩ := two_tests (Dm := h.𝔇) (eAll Zp cF VerifiableInference.Desc.K13.Law.LFull)
    (Mg := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP) rfl
    (mgAll_more_base h.𝔇) N.hH (atK4_of_laid Lh) N.Sx N.Sd
    (fun q hq => thr_pub (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) hT hq)
  unfold lookLayB at t2
  split at t2
  · rename_i a ha
    rw [Bool.and_eq_true, decide_eq_true_eq] at t2
    obtain ⟨_, e⟩ := t2
    have h1 : a.lookHeard = some g₁ := by
      have q := hg1
      simp only [VerifiableInference.Desc.First.S.lookHeard?, ha] at q
      exact q
    have hfo : a.fo = some g₁ := e.trans h1
    obtain ⟨_, _, _, _, hM, _, _⟩ := hT
    obtain ⟨e1, _, _, _, s₀, cols, _, _, hf⟩ := hM
    have hf' : foldBlocks 0 (cF.blocksInOrder.take (28 * g + 4)) s₀ mm.seen cols = .ok (s, [], []) := by
      rw [← Lh.num]
      exact hf
    have W := layers_tie_head h g Lh.lt s₀ mm.st.input.x mm.seen cols s [] [] a g₁ hf' ha hfo
    obtain ⟨er, _⟩ := ProofFile.Honest.K3.Law.AtThr.fold_rest 0 _ _ _ _ _ _ _ hf'
    have et : mm.seen.take ((cF.blocksInOrder.take (28 * g + 4)).flatMap (·.rounds)).length = mm.seen :=
      List.take_of_length_le (List.drop_eq_nil_iff.1 er.symm)
    rw [et, e1] at W
    obtain ⟨b1, b2, b3⟩ := hL mm.st.heard
    exact ⟨b1.trans W.zx.symm, b2.trans W.zk.symm, b3.trans W.e.symm⟩
  · cases t2

/-- CONDITIONAL: on h, Lh, hT and hL. **`K4LookTieAt`, WHERE THE THREAD STANDS.** -/
theorem lookTie_k3 {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hL : LookIsK3 look Qp Zp cF g mm.st.input.x) : K4LookTieAt look Qp s mm :=
  lookTie_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT
    (lookPts_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT hL)

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.lookPts_head
#print axioms ProofFile.Honest.K4.W.lookTie_k3
