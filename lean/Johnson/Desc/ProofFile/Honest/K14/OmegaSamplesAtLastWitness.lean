-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K14/OmegaSamplesAtLastWitness.lean: kind K14: at the shared chain's
last state Omega's sample rows say their claims of the words that the library's reading takes off
the SECOND chain's honest witness (lastWitness, Honest/Thread/TheFirstThread.lean), where they say
them of the shared chain's own honest witness. Statements with their proofs; no definition.

What for. The second chain's proximity test takes Omega into its group, and its acceptance asks that
the sample rows of all members hold of the words of which that chain's thread speaks. For Omega that
is a sentence at the shared chain's end on lastWitness. The shared chain's thread ends with Omega's
pin open, which by this kind's meaning of a pin (mgWords, Honest/K14/Thread2.lean) is SmpOwn: the
state holds the message's sample rows, and they hold of the words of the shared chain's witness.
This file carries the one to the other.

  words2_beyond       beyond the real rows of Omega's tables the honest words (words2) are 0
  omega_words_last    **the words that wordsBy reads off lastWitness at the message number 2 of a
                      statement, where that message sits at Omega's seat and has Omega's shape, are
                      words2's at the number 2, AT EVERY INDEX**
  omega_words_shared  so they are the words that the shared chain's witness witL holds there, read
                      at any list of challenges with the same first member
  omega_samples       **Omega's sample rows at the shared chain's end say of lastWitness's words**:
                      the conclusion has the form that is asked in front of the second chain's
                      proximity test: at whatever Desc.K14.ended returns of the state e₂, at
                      sharedOfEnd's statement, book and number, through wordsShared

Premises of omega_samples, all on the state e₂ but the last; hS is on the state and on the shared
chain's witness.
  hI      its statement is in order (OnBytes.Means.InOrder)
  ho      it notes Omega as the message number 2
  hseat   by its book, read as the shared chain's book behind t trees, that message sits at the
          tenant that the table of numbers has for Omega
  hx      the message has the plan's shape for Omega
  hS      SmpOwn at the number 2 of the shared chain's witness, read at a list hd' of challenges
  hd      hd' has the same first member as the list that lastWitness hands on
NONE OF THE SIX IS SHOWN HERE. t is free: hseat ties it.

Limits.
  * h : HeadAtReturn is a hypothesis (Honest/K14/WordsAtLastWitness.lean says what it holds).
  * Omega alone. Nothing on o_u's or o_sp's sample rows.
  * Where Desc.K14.ended returns nothing, omega_samples says nothing.

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.K14.WordsAtLastWitness
import Johnson.Desc.Sound.WordsUsers
import Johnson.Desc.Means.ItemsLen
import Johnson.Desc.Third.Border
import Johnson.Prover.Send.Held

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (TableKey)
open OnBytes.Slice (rdE)
open OnBytes.Means (SampleSays)
open VerifiableInference.Desc.Shared (Msg2)
open VerifiableInference.Desc.Sound (wordsBy wordsShared seatBy noShared)
open VerifiableInference.Desc.Third (sharedOfEnd)
open VerifiableInference.Desc.K1 (qAt)
open Desc.K14 (St)
open Desc.K14.Honest (words2 SmpOwn)
open ProofFile.Honest.FirstThread

/-- **Beyond the real rows of Omega's tables the honest words are 0**: the words laid from the
chain's first state, which has no message, so that o_omega's sending begins at the number 2; at a
statement whose message number 2 has the shape of the first message that goes out with o_omega
(hsz: there is one). -/
theorem words2_beyond (Q : Desc.K14.P14) (sentU : Array OnBytes.OracleNotice) (key : TableKey)
    (r : Fmt.RoundView) (H : Desc.K14.Honest.Inputs) (hsz : 0 < (Desc.K14.withOmega Q.S).size)
    (S : OnBytes.Statement) (x : OnBytes.Oracle) (hx : S.oracles[2]? = some x)
    (hs : x.shape = ((Desc.K14.withOmega Q.S).getD 0 default).shape) (part : OnBytes.Part)
    (i : Nat) (hb : OnBytes.Means.realRows S 2 part ≤ i % 2 ^ S.rowBits 2 part) :
    words2 Q sentU (Desc.K14.first Q.codes key) r H 2 part i = 0 := by
  have e : (Desc.K14.Law.parO Q).sent = Desc.K14.withOmega Q.S := Desc.K14.Law.parK1_sent _ _ _ _
  exact Johnson.Prover.Send.padded_new _ (0 + 2) (Desc.K14.Law.parO Q) _ S 0 (by rw [e]; exact hsz)
    x hx (by
      rw [hs]
      show _ = ((Desc.K14.Law.parO Q).sent.getD 0 default).shape
      rw [e]) part i hb

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **AT EVERY INDEX: the words that the library's reading takes off lastWitness at the message
number 2, where it sits at Omega's seat and has Omega's shape, are words2's at the number 2.** -/
theorem omega_words_last (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (k : Coins A.B) (w : Local W₀ Rc ProofFile.Inst Tr)
    (heard : List Fmt.Drawn) (seatAt : Nat → Option (Nat × Nat)) (S : OnBytes.Statement)
    (hseat : seatAt 2 = some (h.sharedNumbers.tenant .oOmega))
    (hx : (S.oracles[2]?).map (·.shape) = some (sharedShape A.Z h.places .oOmega))
    (part : OnBytes.Part) (i : Nat) :
    wordsBy (P5J.At.arr A.Z) seatAt S (lastWitness h first reads k w heard) 2 part i =
      words2 (qAt A.Z h.places) (sentFirstOf A.Z h.places)
        (Desc.K14.first (qAt A.Z h.places).codes (A.H.key w.x))
        (firstRv (heard.drop
          (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length))
        (holds2 (qAt A.Z h.places) reads.weights reads.rand k ⟨w.w₀, w.rc, A.H.key w.x⟩)
        2 part i := by
  by_cases hr : i % 2 ^ S.rowBits 2 part < OnBytes.Means.realRows S 2 part
  · exact wordsBy_lastWitness h first reads k w heard .oOmega seatAt S 2 hseat hx part i hr
  · obtain ⟨y, hy, ey⟩ := Option.map_eq_some_iff.1 hx
    have hsz : 0 < (Desc.K14.withOmega (qAt A.Z h.places).S).size := by
      rw [Desc.K14.Law.withOmega_split (sendings_at_head h.head).2.1]
      exact Nat.zero_lt_two
    rw [VerifiableInference.Desc.Sound.padded_wordsBy (P5J.At.arr A.Z) seatAt S _ 2 part i
      (Nat.not_lt.1 hr), words2_beyond _ _ _ _ _ hsz S y hy ey part i (Nat.not_lt.1 hr)]

/-- **So they are the words that the shared chain's witness holds at the number 2**, read at any
list of challenges with the same first member as the list that lastWitness hands on. -/
theorem omega_words_shared {Wt : Type} (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (sh : SharedThreadParts A Wt) (k : Coins A.B)
    (w : Local W₀ Rc ProofFile.Inst Tr) (heard hd' : List Fmt.Drawn)
    (hd : firstRv hd' = firstRv (heard.drop
      (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length))
    (seatAt : Nat → Option (Nat × Nat)) (S : OnBytes.Statement)
    (hseat : seatAt 2 = some (h.sharedNumbers.tenant .oOmega))
    (hx : (S.oracles[2]?).map (·.shape) = some (sharedShape A.Z h.places .oOmega))
    (part : OnBytes.Part) (i : Nat) :
    wordsBy (P5J.At.arr A.Z) seatAt S (lastWitness h first reads k w heard) 2 part i =
      sh.lens.get (witL sh.lens (qAt A.Z h.places) (sentFirstOf A.Z h.places)
        (holds2 (qAt A.Z h.places) reads.weights reads.rand) sh.rest k ⟨w.w₀, w.rc, A.H.key w.x⟩
        hd') 2 part i := by
  rw [omega_words_last h first reads k w heard seatAt S hseat hx part i,
    shared_words sh.lens _ _ _ sh.rest k _ _ 2 (ours_at_head h .oOmega) part i, hd]

/-- **OMEGA's SAMPLE ROWS AT THE SHARED CHAIN's END SAY THEIR CLAIMS OF lastWitness's WORDS**, where
they say them of the shared chain's own witness. -/
theorem omega_samples {Wt : Type} (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (sh : SharedThreadParts A Wt) (k : Coins A.B)
    (w : Local W₀ Rc ProofFile.Inst Tr) (heard hd' : List Fmt.Drawn)
    (hd : firstRv hd' = firstRv (heard.drop
      (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length))
    (t : Nat) (e₂ : St) (hI : OnBytes.Means.InOrder e₂.st) (ho : e₂.loc.oOmega = 2)
    (hseat : seatBy (noShared t) e₂.book 2 = some (h.sharedNumbers.tenant .oOmega))
    (hx : (e₂.st.oracles[2]?).map (·.shape) = some (sharedShape A.Z h.places .oOmega))
    (hS : SmpOwn 2 e₂ (sh.lens.get (witL sh.lens (qAt A.Z h.places) (sentFirstOf A.Z h.places)
      (holds2 (qAt A.Z h.places) reads.weights reads.rand) sh.rest k
      ⟨w.w₀, w.rc, A.H.key w.x⟩ hd'))) :
    ∀ e, Desc.K14.ended e₂ = some e →
      SampleSays rdE (sharedOfEnd e).st (sharedOfEnd e).omega
        (wordsShared (P5J.At.arr A.Z) t (sharedOfEnd e).st (sharedOfEnd e).book
          (lastWitness h first reads k w heard)) := by
  intro e he
  unfold Desc.K14.ended at he
  split at he
  · obtain rfl := Option.some.inj he
    show SampleSays rdE e₂.st e₂.loc.oOmega
      (wordsBy (P5J.At.arr A.Z) (seatBy (noShared t) e₂.book) e₂.st
        (lastWitness h first reads k w heard))
    rw [ho]
    intro y hy r hr
    obtain ⟨y', hy', hs⟩ := hS
    obtain rfl : y' = y := Option.some.inj (hy'.symm.trans hy)
    refine (OnBytes.Means.says_agree_in rdE (hI.samples 2 y' hy r hr) fun o hm part i _ => ?_).2
      (hs r hr)
    obtain rfl : o = 2 := by simpa using hm
    exact omega_words_shared h first reads sh k w heard hd' hd _ e₂.st hseat hx part i
  · cases he

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.words2_beyond
#print axioms ProofFile.Honest.K14.omega_words_last
#print axioms ProofFile.Honest.K14.omega_words_shared
#print axioms ProofFile.Honest.K14.omega_samples
