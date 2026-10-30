-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/SharedDoorAtTerm.lean: the linear claim (kind K14): THE FIVE TESTS ON WHAT IS HANDED
OF THE SHARED CHAIN's END (sharedDoorB, Johnson/Desc/Last/ShapeDoor.lean) ALL SAY YES, FROM THE
INVARIANT OF THE TERM sharedThread (Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean) AT ITS
LAST BORDER. Two theorems, both calls of shared_door_ordered (AtFullSide/K14/SharedDoorAtEnd.lean)
at that term's letters. That theorem's one premise on the letters, "the letter order gives that the
statement is in order", holds at the term by unfolding: the term's order IS that sentence. So at the
term nothing is asked but the head and the invariant.

  shared_door_at_term   from the invariant (Thr)
  shared_door_saidS     from the invariant with a sentence Said beside it (ThrS), at every Said: the
                        form in which a door between chains hands a stand on

The parameters at which the tests are stated, ToldDesc.p14At A.Z, are the last chain's own.

It stands under the library's hypothesis at the full size (P5J.AtMgA), at the format's second hash
function:
that is the field head of h. What is not claimed. That the invariant holds at any state. That the
state of which a later chain's letters speak is the state of such a stand. Nothing on completeness,
soundness or hiding.
Terms. letter, border: lean/GLOSSARY.md. A thread is the invariant along a chain with its parameters
(Honest/Thread/Thr.lean).
-/
import AtFullSide.K14.SharedDoorAtEnd
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.FirstThread (HeadAtReturn IndexReaders SharedThreadParts sharedThread)
open VerifiableInference.Desc.Third (sharedOfEnd)
open VerifiableInference.Desc.Last (sharedDoorB)
open Desc.K14 (St)

variable {W₀ Rc Tr X₀ X : Type}

/-- **sharedDoorB at what is handed of the shared chain's end, from sharedThread's invariant at its
last border.** -/
theorem shared_door_at_term {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} {Wt : Type}
    (h : HeadAtReturn files A) (reads : IndexReaders W₀ Rc) (parts : SharedThreadParts A Wt)
    (w₂ : Common W₀ Rc OnBytes.TableKey)
    {k : Coins A.B} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hA : Thr (sharedThread h reads parts w₂) h.description.shared.blocksInOrder.length k s₂ m E) :
    ∀ e, Desc.K14.ended s₂ = some e →
      sharedDoorB (ToldDesc.p14At A.Z) (sharedOfEnd e) = true :=
  shared_door_ordered A.Z h.places h.firstChain A.H _ _ _ _ _ _ _ _ _ _ _ _ _ w₂ h.head
    (fun _ x => x) hA

/-- **The same from ThrS, at every Said.** -/
theorem shared_door_saidS {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} {Wt : Type}
    (h : HeadAtReturn files A) (reads : IndexReaders W₀ Rc) (parts : SharedThreadParts A Wt)
    (w₂ : Common W₀ Rc OnBytes.TableKey)
    (Said : Nat → Coins A.B → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Prop) :
    ∀ k s₂ m E, ThrS (sharedThread h reads parts w₂) Said h.description.shared.blocksInOrder.length k s₂ m
        E →
      ∀ e, Desc.K14.ended s₂ = some e →
        sharedDoorB (ToldDesc.p14At A.Z) (sharedOfEnd e) = true :=
  fun _ _ _ _ u => shared_door_at_term h reads parts w₂ u.1

end AtFullSide.K14

#print axioms AtFullSide.K14.shared_door_at_term
#print axioms AtFullSide.K14.shared_door_saidS
