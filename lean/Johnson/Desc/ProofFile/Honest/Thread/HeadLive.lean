-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/HeadLive.lean: THE OPEN SEGMENT's OWN COPY OF THE FRAME,
WHEREVER THE THREAD HOLDS: A FACT AT REACHED STATES, NO RIDER. The library's laws
 on what a sending owes take as a premise that the open link's frame's group is the
numbers' `groupAt l`; asked at every state at which the six Bools hold, nobody can pay it; at one
state it can. The library has it, under the head, at every state that is reached without a mark at
a place of segment l: `K13.Law.live_reached` (Johnson/Desc/AtSeats/K01FactsAtAll.lean). The thread
gives that reach (`thr_reach`) and "no mark" (its form). One call.

  `head_live`

Limits. The full size and the format's second hash function alone: as the library's head, which is a
premise. None is one of the library's goals. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.AtSeats.K01FactsAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (flatPlacesOf)
open VerifiableInference.Desc.Sound (MsgT linksFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **AT A PLACE OF SEGMENT l, WHEREVER THE THREAD HOLDS**: every open link's own copy of the frame
has the numbers' group of l and the plan's shape. -/
theorem head_live (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hb : b ≤ cF.blocksInOrder.length)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E)
    {p : Place} {l : Nat} (hp : (flatPlacesOf linksFull true)[b]? = some p)
    (hl : p.link = some l) :
    ∀ L, s.link? = some L → L.check.frame.group = h.𝔇.N.groupAt l ∧
      L.check.frame.shape = (VerifiableInference.Desc.Sound.d13 h.𝔇).shape := by
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hF, -, -, -, -⟩ := hT'
  exact VerifiableInference.Desc.K13.Law.live_reached h b (m.st.input.x.pub, s)
    (thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT)
    (Option.isNone_iff_eq_none.1 hF.1) hp hl

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_live
