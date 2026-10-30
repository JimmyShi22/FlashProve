-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/TiedAheadAtTerms.lean: the linear claim's second part ("K14, second part", the first
member of a proof file's last chain): THE TEST tiedAheadB
(Johnson/Desc/ProofFile/Honest/K14/TiedAhead.lean) AT THE RECORD THAT THE LAST CHAIN's START
RETURNS, FROM THE INVARIANTS OF THE TERMS firstThread AND sharedThread
(Honest/Thread/TheFirstThread.lean) AT THEIR LAST BORDERS. One theorem: tied_ahead_at_ends
(AtFullSide/K14/TiedAheadAtEnds.lean) at these two terms' letters. Its end is the sentence of the
clause tiedAheadRider: so it is what is owed of that clause where the last chain is entered.

It stands under the library's hypothesis at the full size (P5J.AtMgA), at the format's second hash
function:
that is the field head of h.

What is not claimed. That either invariant holds at any state, or that the start returns, or that
the premises can hold together: the two invariants are tied to each other by the states s₁ and s₂
alone. Nothing on completeness, soundness or hiding.
Terms. border: lean/GLOSSARY.md. A thread is the invariant along a chain with its parameters
(Honest/Thread/Thr.lean).
-/
import AtFullSide.K14.TiedAheadAtEnds
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders SharedThreadParts
  firstThread sharedThread)
open VerifiableInference.Desc.Third (S₃)
open P5J (TS)
open Desc.K14 (St)

variable {W₀ Rc Tr X₀ X : Type}

/-- **tiedAheadB at the record that the last chain's start returns**: from the first thread's
invariant at its last border at s₁, the shared thread's at its last border at s₂, and the start's
return s at s₁ and s₂. The two runs' inputs, coins, stands and tables are free of each other, and so
is x. -/
theorem tied_ahead_at_terms {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} {Wt : Type}
    (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
    (parts : SharedThreadParts A Wt) (w₁ : Local W₀ Rc ProofFile.Inst Tr)
    (w₂ : Common W₀ Rc OnBytes.TableKey)
    {k₁ : Coins A.B} {s₁ : TS} {mid₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E₁ : Env}
    (hT₁ : Thr (firstThread h first w₁) h.firstChain.blocksInOrder.length k₁ s₁ mid₁ E₁)
    {k : Coins A.B} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E' : Env}
    (hT₂ : Thr (sharedThread h reads parts w₂) h.description.shared.blocksInOrder.length k s₂ m E')
    (x : ProofFile.InstPub) (s : S₃) (hs : h.description.start₃ x s₁ s₂ = .ok s) :
    (tiedAheadRider (Local W₀ Rc ProofFile.Inst Tr) (LLT25.c2 h.places).rounds).prop 0 w₁ s :=
  tied_ahead_at_ends h.head A.H _ _ _ _ _ _ _ _ _ _ w₁ A.H _ _ _ _ _ _ _ _ _ _ _ _ _ w₂ hT₁ hT₂ x s
    hs

end AtFullSide.K14

#print axioms AtFullSide.K14.tied_ahead_at_terms
