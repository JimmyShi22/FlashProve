-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ValuesAtThread.lean: AT THE FIRST CHAIN's THREAD AT THE FULL SIZE (lettersHead,
Johnson/Desc/ProofFile/Honest/Thread/FirstHead.lean): THE RULE FOR ACCEPTANCE's PREMISE ON VALUES
(ValuesJ, Honest/Thread/ShapeJV.lean) AT THE TABLE's OWN TESTS FALLS TO THE SAME PREMISE AT LIGHTER
TESTS: at the twelve members 28 g + 4 (the layers' own rounds) and at 342 (the head's reads). Under
the head P5J.AtMgA; at every "what is said", every family, every fall. A joining of laws; nothing is
evaluated.

How. The thread at a border gives that the state is reached there by the chain's own blocks
(thr_reach, Honest/Thread/ReachFacts.lean). From border 2 on the instance's request has passed the
start's test (Meaning.K2.reqOk_reached, Johnson/IMR/AtReach.lean). So what K4ValsOf.lean and
CoveredMid.lean show of reached states holds at the thread's state.

  `hq_reach`: from border 2 on the premise on the request of ReqReplyReach.lean's laws is paid.
  **`valuesJ_lighter`**: GENERAL IN THE TESTS: V' gives V at every state reached at border b: then
    ValuesJ at V' gives ValuesJ at V, at one table of steps. THE RAW FAMILY; every "what is said";
    RELATIVE.
  **`valuesJ_k4_head`** (g < 12): ValuesJ at 28 g + 4 at the table's own test, from ValuesJ at a
    test that asks there: every call's point ends as the lookup's own (mergedB), and the round
    behind the norms' rows draws no element that is 0 (coinB). THE REQUEST's TOKENS ARE ASKED NO
    MORE.
  **`valuesJ_342_head`**: ValuesJ at 342 at the table's own test, from ValuesJ at a test that asks
    there: the member's own commitment returns. THE COVERED POSITIONS ARE ASKED NO MORE.

Limits. THE LIGHTER PREMISES ARE NOT PAID HERE. mergedB is shown wherever the thread stands in front
of the member, on conditions (k4_merged_head,
Johnson/Desc/ProofFile/Honest/K4/Law/ValuesAtHead.lean). coinB hangs on the draws. That the
commitment returns is meant to follow from the step on shapes and the fit of the rounds: not called.
13 OF 358 MEMBERS. It is one premise
of the rule at these members. That the head has a member is shown in scope, where the reader returns
and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together,
at two named sets of public files, in a side library. At the format's second hash function. Nothing
on soundness, completeness or hiding.

-/
import Johnson.AtFull.Shape.K4ValsOf
import Johnson.AtFull.Shape.CoveredMid
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.ProofFile.Honest.Thread.ShapeJV

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Strs Place K1.commitAtS)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM)
open OnBytes.K.Kc (paired)
open OnBytes.Desc.First.K4 (entries)
open OnBytes.Desc.First.K4.Rt (coinB)
open ProofFile.Honest (ProverCoinCounts Prover Local Coins Mid ValuesJ)
open ProofFile.Honest.FirstThread (lettersHead thr_reach Script WtF)
open Johnson.Desc.First.Walk.Tied (Reach)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- From border 2 on the instance's request has passed the start's test. -/
theorem hq_reach (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : Nat} {a : ProofFile.InstPub × S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) (h2 : 2 ≤ k) :
    (Zp.s₀.withReq (Verify.words32 a.1.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact Meaning.K2.reqOk_reached h.scope h.reads O hr h2

section
variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → S → Option String) (carryX : Nat → ProofFile.InstPub × S → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → S → Prop) (Kp : Place → S → S → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr) (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
  (J : Nat → S → Prop) (fall : Nat → S → List Fmt.Drawn → Option String)

/-- **Where a lighter test gives the test at every state reached at the border, the premise on
values at the lighter test gives it at the test.** -/
theorem valuesJ_lighter (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {G : Nat → ShA → Except String ShA}
    {V V' : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool} {b : Nat}
    (hb : b ≤ 358)
    (hL : ∀ (a : ProofFile.InstPub × S) rs gs, Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b a →
      V' b a.2 rs gs = true → V b a.2 rs gs = true)
    (hV : ValuesJ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said J
      (firstZA G V') fall b) :
    ValuesJ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said J
      (firstZA G V) fall b := by
  intro blk hblk k s m E ds y cols hA hJ hd hst hf hMv
  exact hL (m.st.input.x.pub, s) _ _
    (thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by rw [flat_len h]; exact hb) hA.1)
    (hV blk hblk k s m E ds y cols hA hJ hd hst hf hMv)

/-- **The layers' own rounds: the request's tokens are asked no more.** -/
theorem valuesJ_k4_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (g : Nat) (hg : g < 12) :
    ∃ hp : Layer.HPlan2, Bs.G₀.W.G[g]? = some hp ∧
      ∀ V' : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool,
      (∀ s rs gs, V' (28 * g + 4) s rs gs = ((s.look?.all fun fo => mergedB Bs.G₀.W.layers fo) &&
        coinB Bs.G₀.W.layers g (paired rs (entries Bs.G₀.W.layers hp g)))) →
      ValuesJ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said J
        (firstZA (Tab.g Zp Bs.G₀) V') fall (28 * g + 4) →
      ValuesJ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said J
        (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) fall (28 * g + 4) := by
  obtain ⟨hp, e, hv⟩ := vals_k4_reach h hB g hg
  refine ⟨hp, e, fun V' hV' hJ' => valuesJ_lighter H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said J
    fall h (by omega) (fun a rs gs hr hl => ?_) hJ'⟩
  rw [hV', Bool.and_eq_true] at hl
  exact hv hr (hq_reach h hr (by omega)) rs gs hl.1 hl.2

/-- **The head's reads: the covered positions are asked no more.** -/
theorem valuesJ_342_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    ∃ rd : Option (List Nat), (Tab.nums Bs.G₀ 24).map (·.2.2.1) = some rd ∧
      ∀ V' : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool,
      (∀ s rs gs, V' 342 s rs gs =
        ((K1.commitAtS (Cl := Unit) (Tab.k1P Zp Bs.G₀ 24 5 1) 24 1 rd).decide s rs
          (gs.take (K1.commitAtS (Cl := Unit) (Tab.k1P Zp Bs.G₀ 24 5 1) 24 1
            rd).openings)).toOption.isSome) →
      ValuesJ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said J
        (firstZA (Tab.g Zp Bs.G₀) V') fall 342 →
      ValuesJ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said J
        (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) fall 342 := by
  obtain ⟨rd, erd, hv⟩ := vals_342_reach h hB
  refine ⟨rd, erd, fun V' hV' hJ' => valuesJ_lighter H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said J
    fall h (by omega) (fun a rs gs hr hl => ?_) hJ'⟩
  rw [hV'] at hl
  refine hv hr (hq_reach h hr (by omega)) rs gs ?_
  cases hc : (K1.commitAtS (Cl := Unit) (Tab.k1P Zp Bs.G₀ 24 5 1) 24 1 rd).decide a.2 rs
      (gs.take (K1.commitAtS (Cl := Unit) (Tab.k1P Zp Bs.G₀ 24 5 1) 24 1 rd).openings) with
  | ok m => exact ⟨m, rfl⟩
  | error e =>
    rw [hc] at hl
    cases hl

end

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.hq_reach
#print axioms Johnson.AtFull.Shape.valuesJ_lighter
#print axioms Johnson.AtFull.Shape.valuesJ_k4_head
#print axioms Johnson.AtFull.Shape.valuesJ_342_head
