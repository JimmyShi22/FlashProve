-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/ChainThreadAtHead.lean: THE SMALLNESS TEST, THE HONEST PROVER's
SIDE: THE NAMED PREMISE `ChainThread` (Johnson/Desc/ProofFile/Honest/K8/K8BehindTop.lean: six ties
of a thread to the first chain) HOLDS AT THE FRAME's OWN THREAD: THAT OF THE FIRST CHAIN's LETTERS
AT THE LIBRARY's HEAD (`lettersHead`, Johnson/Desc/ProofFile/Honest/Thread/FirstHead.lean), AT THE
TABLE's NUMBER OF EACH OF THE 25 BATCHINGS. SO A SENTENCE THAT TOOK IT STANDS THERE WITHOUT IT.
Calls and unfoldings; none of the library's goals.

  `batchAt_border` l < 25 ⊢ batchAt P5J.At.links P5J.At.ps l = 14 l + (if l = 24 then 11 else 9)
  **`chainThread_at_head`** the library's head h · the thread's letters, all free · l < 25 ⊢
                   ChainThread (lettersHead …).thread (batchAt P5J.At.links P5J.At.ps l) cF Zp l
  **`allFrontAtStand_at_head`** these, and nothing more ⊢ AllFrontAtStand Lk p (lettersHead
                   …).thread (batchAt … l), at all 25 segments, at every Lk and p
THE SIX FIELDS: ft and bs by unfolding (they are two of the five equations of `sits_head`,
FirstHead.lean) · border: `batchAt_border`, off the library's LPFK9.k10_border
(Johnson/LPFK9R/K10Border.lean) and P5J.batch_head_full (Johnson/P5J/K09Ahs1.lean); the library
states that number in four more forms (batchAt_full, batch_nAt, batchIsFront, batch_is), none of
them this one · len: the library's LPFK9.fields_at_constant (Johnson/LPFK9R/SitsAtConstant.lean)
shows a sub-protocol at that number · begun: by unfolding, at the input's public part · stored:
`storedWords_lt` (Johnson/Desc/ProofFile/Honest/Law/Run.lean), which holds of every prover.
KIN, AND FIRST: at `lettersHead` the two reaches that `ChainThread` exists to give lie in the
frame's own files: `thr_reach` (Honest/Thread/ReachFacts.lean: the chain's own blocks' reach, from
Thr) and `thrS_reach_below` (Honest/Thread/ReachAtHead.lean: the wrapped blocks' reach, from ThrS at
SaidOk), each under b ≤ cF.blocksInOrder.length alone; begun and stored are paid here as in their two proofs.
What this file adds: the structure itself, so that sentences stated at a general thread can be
called there; and the border.
By, beside these: `allFrontAtStand_of_chain` (AllFrontOfChain.lean).
ONE DEVICE STANDS IN IT: `attribute [-instance] Inst.Model.Scl.ref`. TACTICS THAT SEARCH: `omega` on
two lines, on numbers of segments and borders alone.
Limits. NO MEMBER: THAT THE THREAD HOLDS AT ANY RUN, OR THAT A STAND EXISTS, IS NOT SHOWN: where
there is no stand the sentence is idle. THE LIBRARY's HEAD IS A PREMISE. Lk and p are free: at a
link or numbers at which no stand exists the sentence is idle. `valid`, `rides` and `keeps`, which
lie wrapped at `lettersHead`, are not read. THE FULL SIZE ALONE, and the format's second hash function
alone. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.AllFrontOfChain
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Law.Run
import Johnson.LPFK9R.SitsAtConstant
import Johnson.LPFK9R.K10Border
import Johnson.P5J.K09Ahs1

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.LinkJoin (batchAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)

/-- The table's number of a segment's batching, in the form of the borders. -/
theorem batchAt_border {l : ℕ} (hl : l < 25) :
    batchAt P5J.At.links P5J.At.ps l = 14 * l + (if l = 24 then 11 else 9) := by
  show batchAt P5J.fullLinks P5J.At.ps l = _
  by_cases h24 : l = 24
  · subst h24
    rw [P5J.batch_head_full]
    rfl
  · have k := LPFK9.k10_border l (by omega)
    rw [if_neg h24]
    omega

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE SIX TIES OF THE THREAD TO THE CHAIN, AT THE FIRST CHAIN's LETTERS AT THE LIBRARY's HEAD,
AT EACH OF THE 25 BATCHINGS.** -/
theorem chainThread_at_head {l : ℕ} (hl : l < 25) :
    ChainThread (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps l) cF Zp l where
  ft := rfl
  bs := rfl
  border := batchAt_border hl
  len := by
    obtain ⟨L, p, Qc, -, -, -, e, -⟩ := LPFK9.fields_at_constant h l hl
    exact Nat.le_of_lt (List.getElem?_eq_some_iff.1 e).1
  begun := fun _ m => ⟨m.st.input.x.pub, fun _ h0 => h0⟩
  stored := fun v i p u hu => storedWords_lt H v.w₀ v.rc i p u hu

variable {Lk : Link S Claim} {p : Desc.K9.Where}

/-- **AllFrontAtStand THERE, AT ALL 25 SEGMENTS, UNDER THE LIBRARY's HEAD ALONE.** -/
theorem allFrontAtStand_at_head {l : ℕ} (hl : l < 25) :
    AllFrontAtStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps l) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact allFrontAtStand_of_chain h.scope h.reads O h.laid.planOk hl
    (chainThread_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl)

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.batchAt_border
#print axioms ProofFile.Honest.K8.chainThread_at_head
#print axioms ProofFile.Honest.K8.allFrontAtStand_at_head
