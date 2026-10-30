-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/SharedEnds.lean: the linear claim's shared rounds (kind K14): TWO
FACTS AT THE TWO ENDS OF THE SHARED CHAIN's THREAD AT THE PROOF FILE's OWN DESCRIPTION
(lettersShared, Honest/Thread/SharedHead.lean), for whoever joins the three chains.

  pinT_at_words       AT THE START. One item is open at the chain's start: the committed table's
                      pin. This kind's maker of the items' meaning (mgWords,
                      Honest/K14/Thread2.lean) leaves it as it finds it: by unfolding
  pinT_free           so where it is laid as "true" it holds at every state, string and witness.
                      THIS KIND's STATEMENTS AT THE MEMBERS 1 TO 8 SPEND NOTHING OF IT: K14Asks
                      (Honest/K14/Asks.lean) is general in that field; what they use of the
                      committed table comes from five implications from the letter valid
  omega_at_shared_end **AT THE END.** Under the library's hypothesis at the full size, wherever the
                      thread's invariant holds at the chain's last border, whatever the thread's
                      letters are: this kind's three tests on Omega, its pad and the three
                      messages' groups say yes (omegaEndB, omegaPadB, notedB,
                      Honest/K14/OmegaEnd.lean); Desc.K14.ended returns at that state, and what the
                      last chain takes of its value is oOf of the state. A call of omega_at_twelve
                      (Honest/K14/OmegaTwelve.lean)
  ended_at_shared_end its last clause alone

What is not claimed. That the invariant holds at any state. That the last chain's start returns:
ended's return is one of the things that it asks. Nothing on completeness, soundness or hiding.
Terms. letter, border: lean/GLOSSARY.md. A thread is the invariant along a chain with its parameters
(Honest/Thread/Thr.lean). A member is a sub-protocol of a chain's flat list, numbered from 0.
-/
import Johnson.Desc.ProofFile.Honest.K14.OmegaAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.Shared (NumbersS MeaningS ItemS)
open VerifiableInference.Desc.Third.Law (oOf)
open Desc.K14 (P14 St p14Of beforePointOf)

/-- This kind's maker of the items' meaning leaves the committed table's pin as it finds it. -/
theorem pinT_at_words {P₁ Wt : Type} (ℓ : WitLens Wt) (Q : P14) (N : NumbersS)
    (Mg₀ : MeaningS St P₁ Wt) (s : St) (y : Strs) (v : Wt) :
    ItemS.holdsSh N (mgWords ℓ Q N Mg₀) .pinT s y v ↔ Mg₀.pinT s y v := Iff.rfl

/-- Where it is laid as "true" it holds. -/
theorem pinT_free {P₁ Wt : Type} (ℓ : WitLens Wt) (Q : P14) (N : NumbersS)
    (Mg₀ : MeaningS St P₁ Wt) (h : ∀ s y v, Mg₀.pinT s y v) (s : St) (y : Strs) (v : Wt) :
    ItemS.holdsSh N (mgWords ℓ Q N Mg₀) .pinT s y v := h s y v

variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl) {Bk : ProverCoinCounts}
  {W₀ Rc Tr X₀ X P₁ Wt : Type} (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : NumbersS) (Mg : Common W₀ Rc OnBytes.TableKey → MeaningS St P₁ Wt)
  (shape : Nat → St → Bool) (nothingLeft : St → Bool) (order : St → Prop)
  (wit : Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    Place × Table)
  (fixed : Fmt.TreeSource → Nat) (n₁ n₂ : Nat) (Vd : Common W₀ Rc OnBytes.TableKey → Prop)
  (Rd : Nat → Common W₀ Rc OnBytes.TableKey → St → Prop) (Kp : Place → St → St → Prop)
  (w : Common W₀ Rc OnBytes.TableKey)

/-- **At the shared chain's last border**, wherever the thread's invariant holds there, under the
library's hypothesis at the full size, whatever the letters are: the three tests say yes, and
Desc.K14.ended returns. -/
theorem omega_at_shared_end {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {k : Coins Bk} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hA : Thr (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E) :
    omegaEndB (p14Of Zp.p.chains (beforePointOf Np)).S s₂ = true ∧
      omegaPadB (p14Of Zp.p.chains (beforePointOf Np)).S s₂ = true ∧ notedB s₂ = true ∧
      ∃ e, Desc.K14.ended s₂ = some e ∧
        VerifiableInference.Desc.Third.sharedOfEnd e = oOf s₂ := by
  obtain ⟨sentU, layO, hQ⟩ := plan2_at_head h
  obtain ⟨nO, hO⟩ := H2K.JointK.omega_some_in_scope h.scope Zp ProofFile.pureRoad.links Np cF
    h.laid.planOk (LPFD.asks_written h.laid.asks)
  obtain ⟨B⟩ := hQ.eight
  rw [shared_twelve Zp Np cF B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 nO hO B.made] at hA
  obtain ⟨h9, h10⟩ := plans_at_shared Zp Np cF nO hO h.laid.planOk
  exact (omega_at_twelve hQ
    (chainAt_shared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w)
    (tailAt_shared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w B.b1
      B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 nO hO B.made h9 h10) hA)

/-- **At the shared chain's last border Desc.K14.ended returns.** -/
theorem ended_at_shared_end {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {k : Coins Bk} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hA : Thr (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E) :
    ∃ e, Desc.K14.ended s₂ = some e ∧ VerifiableInference.Desc.Third.sharedOfEnd e = oOf s₂ :=
  (omega_at_shared_end Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w h
    hA).2.2.2

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.pinT_at_words
#print axioms ProofFile.Honest.K14.pinT_free
#print axioms ProofFile.Honest.K14.omega_at_shared_end
#print axioms ProofFile.Honest.K14.ended_at_shared_end
