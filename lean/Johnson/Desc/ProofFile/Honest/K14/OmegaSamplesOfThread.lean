-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K14/OmegaSamplesOfThread.lean: kind K14: where the shared chain's
honest thread (sharedThread, Honest/Thread/TheFirstThread.lean) stands at that chain's last border,
Omega's sample rows at that state say their claims of the words that the library's reading takes off
the SECOND chain's honest witness (lastWitness, the same file). Statements with their proofs; no
definition.

omega_samples (Honest/K14/OmegaSamplesAtLastWitness.lean) has that conclusion from six premises.
Two of them are read here off the thread's invariant: the statement is in order (the thread's clause
on its form), and the state holds Omega's sample rows, which hold of the shared chain's own witness
(Omega's pin, which is open at the last border, in this kind's meaning of a pin: mgWords,
Honest/K14/Thread2.lean).

  pin_open_at_end     Omega's pin is open at the border 12: by evaluation of the table of items
  order_of_thread     where the thread stands, at any border, the state's statement is in order
  smpOwn_of_thread    where it stands at a border at which Omega's pin is open: SmpOwn at the number
                      2, of the thread's own witness at every continuation of the challenges
  omega_samples_of_thread   **the conclusion of omega_samples from the thread at the border 12**

Premises of omega_samples_of_thread beside the thread u.
  hin     the input of the thread's run is ⟨w.w₀, w.rc, A.H.key w.x⟩: the shared chain's input made
          from w, the input of the second chain's run
  hd      the first challenge that the thread's run has heard is the first behind the first chain's
          in the list that lastWitness is handed
Both can be met at a run, by the frame's text (Honest/Frame.lean): ready lays the two inputs in just
this form, and Ready.start₃ hands the second chain the first chain's challenges followed by the
shared chain's; hd then needs that the first chain's run has heard as many challenges as that chain
declares rounds, and the shared chain's at least one.
  ho, hseat, hx   the state notes Omega as the message number 2; by its book that message sits at
          Omega's tenant; it has the plan's shape for Omega
NONE OF THE FIVE IS SHOWN HERE, NOR THAT THE THREAD STANDS AT ANY RUN. The coins k are the same on
both sides: one run's.

Limits. h : HeadAtReturn is a hypothesis (Honest/K14/WordsAtLastWitness.lean says what it holds).
Under the library's hypothesis at the full size the shared chain has twelve sub-protocols
(shared_twelve, Honest/K14/OmegaAtShared.lean), so the border 12 is its last. Omega alone.

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.K14.OmegaSamplesAtLastWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes.Slice (rdE)
open OnBytes.Means (SampleSays)
open VerifiableInference.Desc.Shared (ItemS Msg2)
open VerifiableInference.Desc.Sound (wordsShared seatBy noShared)
open VerifiableInference.Desc.Third (sharedOfEnd)
open VerifiableInference.Desc.K1 (qAt)
open Desc.K14 (St)
open Desc.K14.Honest (SmpOwn)
open ProofFile.Honest.FirstThread

/-- Omega's pin is open at the border 12. -/
theorem pin_open_at_end :
    ItemS.pin .oOmega ∈ fwdOpen SharedRows.start (SharedRows.rows true) 12 := by
  decide

variable {W₀ Rc Tr X₀ X Wt : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- Where the shared chain's thread stands, the state's statement is in order. -/
theorem order_of_thread (h : HeadAtReturn files A) (reads : IndexReaders W₀ Rc)
    (sh : SharedThreadParts A Wt) (w₂ : Common W₀ Rc OnBytes.TableKey) {b : Nat} {k : Coins A.B}
    {e₂ : St} {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u : Thr (sharedThread h reads sh w₂) b k e₂ m₂ E₂) : OnBytes.Means.InOrder e₂.st :=
  u.2.2.1.2

/-- **Where it stands at a border at which Omega's pin is open, the state holds Omega's sample rows,
and they hold of the thread's own witness**, at every continuation ds of the challenges. -/
theorem smpOwn_of_thread (h : HeadAtReturn files A) (reads : IndexReaders W₀ Rc)
    (sh : SharedThreadParts A Wt) (w₂ : Common W₀ Rc OnBytes.TableKey) {b : Nat} {k : Coins A.B}
    {e₂ : St} {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u : Thr (sharedThread h reads sh w₂) b k e₂ m₂ E₂)
    (hb : ItemS.pin .oOmega ∈ fwdOpen SharedRows.start (SharedRows.rows true) b)
    (ds : List Fmt.Drawn) :
    SmpOwn 2 e₂ (sh.lens.get (witL sh.lens (qAt A.Z h.places) (sentFirstOf A.Z h.places)
      (holds2 (qAt A.Z h.places) reads.weights reads.rand) sh.rest k m₂.st.input
      (m₂.st.heard ++ ds))) :=
  u.2.2.2.1 ds (.pin .oOmega) hb .oOmega rfl

/-- **FROM THE SHARED CHAIN's THREAD AT ITS LAST BORDER: OMEGA's SAMPLE ROWS SAY THEIR CLAIMS OF
lastWitness's WORDS.** -/
theorem omega_samples_of_thread (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (sh : SharedThreadParts A Wt)
    (w₂ : Common W₀ Rc OnBytes.TableKey) {k : Coins A.B} {e₂ : St}
    {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u : Thr (sharedThread h reads sh w₂) 12 k e₂ m₂ E₂) (w : Local W₀ Rc ProofFile.Inst Tr)
    (heard : List Fmt.Drawn) (hin : m₂.st.input = ⟨w.w₀, w.rc, A.H.key w.x⟩)
    (hd : firstRv m₂.st.heard = firstRv (heard.drop
      (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length))
    (t : Nat) (ho : e₂.loc.oOmega = 2)
    (hseat : seatBy (noShared t) e₂.book 2 = some (h.sharedNumbers.tenant .oOmega))
    (hx : (e₂.st.oracles[2]?).map (·.shape) = some (sharedShape A.Z h.places .oOmega)) :
    ∀ e, Desc.K14.ended e₂ = some e →
      SampleSays rdE (sharedOfEnd e).st (sharedOfEnd e).omega
        (wordsShared (P5J.At.arr A.Z) t (sharedOfEnd e).st (sharedOfEnd e).book
          (lastWitness h first reads k w heard)) := by
  have hS := smpOwn_of_thread h reads sh w₂ u pin_open_at_end []
  rw [List.append_nil, hin] at hS
  exact omega_samples h first reads sh k w heard m₂.st.heard hd t e₂
    (order_of_thread h reads sh w₂ u) ho hseat hx hS

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.pin_open_at_end
#print axioms ProofFile.Honest.K14.order_of_thread
#print axioms ProofFile.Honest.K14.smpOwn_of_thread
#print axioms ProofFile.Honest.K14.omega_samples_of_thread
