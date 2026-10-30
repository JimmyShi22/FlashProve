-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K14/WordsAtLastWitness.lean: kind K14: the second chain's honest
witness (lastWitness, Honest/Thread/TheFirstThread.lean) holds, at the seats of the shared chain's
three sampled messages, the same words as the shared chain's own honest witness holds at these
messages' numbers in that chain. One abbreviation; statements with their proofs.

Two chains read the messages o_u, o_omega and o_sp off two witnesses of two types. The shared
chain's thread reads a family of words, by the message's number in that chain's statement (0, 2 and
3: num, Honest/K14/Thread2.lean), which this kind's maker witL lays. The second chain's thread reads
a witness of tables, by the message's seat (tree and tenant), through the library's one reading
wordsBy (Johnson/Desc/Sound/WordsAt.lean); there lastWitness lays the three messages over the first
chain's witness. This file says that both are one text, words2 (Johnson/Desc/K14/Honest/
ChainHolds.lean) at what the prover holds.

  laidTable           the table that lastWitness lays for a message, under a name
  find_sampled        a search of the list of the three messages by the value of a function that is
                      one to one finds the message itself
  lastWitness_pad, lastWitness_msg   what lastWitness holds at a message's seat, and at the number
                      that the numbering of seats gives that seat: the message's table
  sharedTenantsApart  the numbering of seats gives the three messages numbers of their own, apart
                      from every tenant of the first chain's trees: the sentence SharedTenantsApart
                      of Honest/Thread/TheFirstThread.lean, from Honest/K14/ArrAtHead.lean
  lastWitness_first   so at the tenants of the first chain's trees lastWitness holds what the first
                      chain's witness holds
  lastWitness_tab     the library's accessor Wit.tab returns a message's table at its seat
  wordsBy_lastWitness **the words that wordsBy reads off lastWitness at a message o of a statement S
                      that sits at the seat of m and has m's shape are words2's at m's number**, at
                      each real row
  shared_words        the words that the shared chain's witness witL holds at m's number are
                      words2's, at what the prover holds: whatever the letter rest is
  ours_at_head        at the full size the three numbers are among those that witL lays
  one_text            **both in one**: at the full size the two witnesses hold the same words there,
                      where the shared chain's witness is read at ANY list of challenges with the
                      same first member as the list that lastWitness hands on

Premises.
  * hseat, hx: the message o sits at m's seat and has m's shape in S. Which messages of the second
    chain's statement do is not said here.
    For Omega they can be met at the second chain's book: seat_taken (Johnson/Desc/Sound/TabAt.lean)
    and omegaSits_of_plan
    (Johnson/LLT25R/LastOmegaSits.lean); that chain takes over Omega's tree alone.
  * h : HeadAtReturn holds that A is a return of onlineProverFromPublicFiles, and the library's hypothesis on the public
    files at the full size (P5J.AtMgA, Johnson/P5J/MgAtAll.lean) at A's public part. It is a
    hypothesis: no file that this one imports builds a member of HeadAtReturn.

Limits.
  * THE TWO LISTS OF CHALLENGES NEED NOT BE EQUAL. Each thread hands its witness what has been
    heard, followed by any continuation. lastWitness hands on the list that it is given, less as
    many as the first chain declares rounds. Where that list and the list at which the shared
    chain's witness is read have the same first member (the premise hd of one_text) the words
    agree, because at the numbers that this kind lays the words hang on the list through its first
    member alone (firstRv, Honest/K14/Thread2.lean; shared_words). hd fails where the shared chain
    has heard nothing and the continuation begins otherwise. That a run's two lists have one first
    member, and that a run's list begins with just so many challenges of the first chain, is not
    shown here.
  * The input ⟨w.w₀, w.rc, A.H.key w.x⟩ is the one that the frame's routine ready lays for the
    shared chain beside the run's own (Honest/Frame.lean): so by its text; no statement here says
    it.
  * AT EACH REAL ROW ONLY (the premise hr). The library's laws that carry a row's sentence from one
    family of words to another ask the equation at every index. Beyond the real rows both sides are
    0: the left by padded_wordsOn (Johnson/Desc/Means/ItemsTab.lean), the right by padded_new
    (Johnson/Prover/Send/Held.lean), since the number is one that this kind lays: a caller of such
    a law owes it. For Omega it is proved: omega_words_last,
    Honest/K14/OmegaSamplesAtLastWitness.lean.
  * lastWitness_first speaks of numbers that the numbering gives a tenant of a tree of the first
    chain. Of the second chain's own messages, and of the messages of the shared chain's two
    proximity tests, lastWitness lays nothing: there it holds whatever the first chain's witness
    holds.
  * The message number 1 of the shared chain (the first mask) is laid by lastWitness nowhere, and
    nothing is said of it.

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Desc.ProofFile.Honest.K14.ArrAtHead
import Johnson.Desc.ProofFile.Honest.K14.MaskTie
import Johnson.Desc.ProofFile.Honest.K14.FreshRows
import Johnson.Desc.ProofFile.Honest.K14.SendingsAtHead
import Johnson.Desc.Sound.WordsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc.Shared (Msg2)
open VerifiableInference.Desc.Sound (MsgT wordsBy tabAt)
open VerifiableInference.Desc.K1 (qAt)
open Desc.K14.Honest (words2)
open ProofFile.Honest.FirstThread

/-- A search of the list of the three messages by the value of a function that is one to one finds
the message itself. -/
theorem find_sampled {β : Type} [BEq β] [LawfulBEq β] (f : Msg2 → β)
    (hf : Function.Injective f) (m : Msg2) :
    ([.oU, .oOmega, .oSp] : List Msg2).find? (fun m' => f m' == f m) = some m := by
  have n : ∀ a b : Msg2, a ≠ b → (f a == f b) = false := fun a b hab =>
    beq_eq_false_iff_ne.2 fun e => hab (hf e)
  cases m
  · simp only [List.find?_cons, beq_self_eq_true]
  · simp only [List.find?_cons, beq_self_eq_true, n .oU .oOmega (by intro e; cases e)]
  · simp only [List.find?_cons, beq_self_eq_true, n .oU .oSp (by intro e; cases e),
      n .oOmega .oSp (by intro e; cases e)]

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- The table that lastWitness lays for the message m: sharedTable at the run's coins, at the shared
chain's input made of the run's, and at the challenges behind the first chain's. -/
noncomputable abbrev laidTable (h : HeadAtReturn files A) (reads : IndexReaders W₀ Rc)
    (k : Coins A.B) (w : Local W₀ Rc ProofFile.Inst Tr) (heard : List Fmt.Drawn) (m : Msg2) : MsgT :=
  sharedTable h reads k ⟨w.w₀, w.rc, A.H.key w.x⟩
    (heard.drop (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length) m

/-- **At a message's seat lastWitness holds the message's table.** -/
theorem lastWitness_pad (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (k : Coins A.B) (w : Local W₀ Rc ProofFile.Inst Tr)
    (heard : List Fmt.Drawn) (m : Msg2) :
    (lastWitness h first reads k w heard).pad (h.sharedNumbers.tenant m).1
        (h.sharedNumbers.tenant m).2 = laidTable h reads k w heard m := by
  show (match ([.oU, .oOmega, .oSp] : List Msg2).find? (fun m' => h.sharedNumbers.tenant m' ==
      ((h.sharedNumbers.tenant m).1, (h.sharedNumbers.tenant m).2)) with
    | some m' => laidTable h reads k w heard m'
    | none => _) = _
  rw [show ((h.sharedNumbers.tenant m).1, (h.sharedNumbers.tenant m).2) =
    h.sharedNumbers.tenant m from rfl,
    find_sampled h.sharedNumbers.tenant (tenant_shNums h.head.toAtMg _) m]

/-- **At the number that the numbering of seats gives a message's seat lastWitness holds the
message's table.** -/
theorem lastWitness_msg (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (k : Coins A.B) (w : Local W₀ Rc ProofFile.Inst Tr)
    (heard : List Fmt.Drawn) (m : Msg2) :
    (lastWitness h first reads k w heard).msg
        (P5J.At.arr A.Z (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2) =
      laidTable h reads k w heard m := by
  show (match ([.oU, .oOmega, .oSp] : List Msg2).find? (fun m' =>
      P5J.At.arr A.Z (h.sharedNumbers.tenant m').1 (h.sharedNumbers.tenant m').2 ==
        P5J.At.arr A.Z (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2) with
    | some m' => laidTable h reads k w heard m'
    | none => _) = _
  rw [find_sampled (fun m : Msg2 =>
    P5J.At.arr A.Z (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2)
    (harr_at_head h.head.toAtMg _) m]

/-- **The three messages have numbers of their own**: the sentence that
Honest/Thread/TheFirstThread.lean states beside lastWitness. -/
theorem sharedTenantsApart (h : HeadAtReturn files A) : SharedTenantsApart h :=
  ⟨harr_at_head h.head.toAtMg _, off_at_head h.head.toAtMg _⟩

/-- **At the tenants of the first chain's trees lastWitness holds what the first chain's witness
holds**: nothing of the shared chain is laid over it there. -/
theorem lastWitness_first (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (k : Coins A.B) (w : Local W₀ Rc ProofFile.Inst Tr)
    (heard : List Fmt.Drawn) (j t : Nat) (hj : j < h.description.t₁) :
    (lastWitness h first reads k w heard).msg (P5J.At.arr A.Z j t) =
        (first.script.wit k w heard).msg (P5J.At.arr A.Z j t) ∧
      (lastWitness h first reads k w heard).pad j t = (first.script.wit k w heard).pad j t := by
  have n1 : ([.oU, .oOmega, .oSp] : List Msg2).find? (fun m' =>
      P5J.At.arr A.Z (h.sharedNumbers.tenant m').1 (h.sharedNumbers.tenant m').2 ==
        P5J.At.arr A.Z j t) = none :=
    List.find?_eq_none.2 fun m' _ e => (sharedTenantsApart h).2 m' j t hj (beq_iff_eq.1 e).symm
  have off : ∀ m', h.sharedNumbers.tenant m' ≠ (j, t) := fun m' =>
    seat_off_at_head h.head.toAtMg _ m' j t hj
  have n2 : ([.oU, .oOmega, .oSp] : List Msg2).find? (fun m' =>
      h.sharedNumbers.tenant m' == (j, t)) = none :=
    List.find?_eq_none.2 fun m' _ e => off m' (beq_iff_eq.1 e)
  constructor
  · show (match ([.oU, .oOmega, .oSp] : List Msg2).find? (fun m' =>
        P5J.At.arr A.Z (h.sharedNumbers.tenant m').1 (h.sharedNumbers.tenant m').2 ==
          P5J.At.arr A.Z j t) with
      | some m' => laidTable h reads k w heard m'
      | none => (first.script.wit k w heard).msg (P5J.At.arr A.Z j t)) = _
    rw [n1]
  · show (match ([.oU, .oOmega, .oSp] : List Msg2).find? (fun m' =>
        h.sharedNumbers.tenant m' == (j, t)) with
      | some m' => laidTable h reads k w heard m'
      | none => (first.script.wit k w heard).pad j t) = _
    rw [n2]

/-- **So the library's accessor returns that table there**, at every table of codes and shape. -/
theorem lastWitness_tab (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (k : Coins A.B) (w : Local W₀ Rc ProofFile.Inst Tr)
    (heard : List Fmt.Drawn) (m : Msg2)
    (cs : OnBytes.Codes) (s : OnBytes.OracleShape) :
    (lastWitness h first reads k w heard).tab cs s
        (P5J.At.arr A.Z (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2)
        (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2 =
      laidTable h reads k w heard m := by
  funext mask row place
  unfold VerifiableInference.Desc.Wit.tab
  rw [lastWitness_pad, lastWitness_msg h first reads k w heard m]
  split <;> rfl

/-- **THE WORDS THAT THE LIBRARY's READING TAKES OFF lastWitness AT A MESSAGE THAT SITS AT m's SEAT
AND HAS m's SHAPE ARE words2's AT m's NUMBER**, at each real row. -/
theorem wordsBy_lastWitness (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (k : Coins A.B) (w : Local W₀ Rc ProofFile.Inst Tr)
    (heard : List Fmt.Drawn) (m : Msg2)
    (seatAt : Nat → Option (Nat × Nat)) (S : OnBytes.Statement) (o : Nat)
    (hseat : seatAt o = some (h.sharedNumbers.tenant m))
    (hx : (S.oracles[o]?).map (·.shape) = some (sharedShape A.Z h.places m))
    (part : OnBytes.Part) (i : Nat)
    (hr : i % 2 ^ S.rowBits o part < OnBytes.Means.realRows S o part) :
    wordsBy (P5J.At.arr A.Z) seatAt S (lastWitness h first reads k w heard) o part i =
      words2 (qAt A.Z h.places) (sentFirstOf A.Z h.places)
        (Desc.K14.first (qAt A.Z h.places).codes (A.H.key w.x))
        (firstRv (heard.drop
          (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length))
        (holds2 (qAt A.Z h.places) reads.weights reads.rand k ⟨w.w₀, w.rc, A.H.key w.x⟩)
        (num m) part i := by
  obtain ⟨y, hy, ey⟩ := Option.map_eq_some_iff.1 hx
  have hT : tabAt S.codes (P5J.At.arr A.Z) seatAt S (lastWitness h first reads k w heard) o =
      laidTable h reads k w heard m := by
    unfold tabAt
    rw [hseat, hy]
    exact lastWitness_tab h first reads k w heard m S.codes y.shape
  unfold wordsBy
  rw [VerifiableInference.Desc.Sound.wordsOn_congr S S (fun _ => laidTable h reads k w heard m) _
    o o rfl hT part i]
  exact wordsOn_tableOfWords (x := ⟨sharedShape A.Z h.places m, 0⟩) hx _ part i hr

/-- **The words that the shared chain's witness holds at a number that this kind lays are words2's,
at what the prover holds**: whatever the letter rest is. -/
theorem shared_words {Bk : ProverCoinCounts} {Wt : Type} (ℓ : WitLens Wt) (Q : Desc.K14.P14)
    (sentU : Array OnBytes.OracleNotice)
    (holds : Coins Bk → Common W₀ Rc TableKey → Desc.K14.Honest.Inputs)
    (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt) (k : Coins Bk)
    (w : Common W₀ Rc TableKey) (hd : List Fmt.Drawn) (o : Nat) (ho : Ours Q sentU o)
    (part : OnBytes.Part) (i : Nat) :
    ℓ.get (witL ℓ Q sentU holds rest k w hd) o part i =
      words2 Q sentU (Desc.K14.first Q.codes w.key) (firstRv hd) (holds k w) o part i := by
  rw [get_witL]
  exact words2_ours Q sentU w.key (firstRv hd) (holds k w) _ o ho part i

/-- **At the full size the three messages' numbers are among those that this kind lays.** -/
theorem ours_at_head (h : HeadAtReturn files A) (m : Msg2) :
    Ours (qAt A.Z h.places) (sentFirstOf A.Z h.places) (num m) := by
  obtain ⟨hfit, hsp, -, -, hm, -⟩ := sendings_at_head h.head
  have e2 : (sentFirstOf A.Z h.places).size = 2 := by
    have t := u_two ⟨qAt A.Z h.places, 0⟩ hfit hm
    rwa [show (jobU ⟨qAt A.Z h.places, 0⟩).Q.sent = sentFirstOf A.Z h.places from
      Desc.K14.Law.parK1_sent _ _ _ _] at t
  have e3 : (Desc.K14.withOmega (qAt A.Z h.places).S).size = 2 := by
    rw [Desc.K14.Law.withOmega_split hsp]
    rfl
  unfold Ours
  rw [e2, e3]
  cases m
  · exact Or.inl (by decide)
  · exact Or.inr (by decide)
  · exact Or.inr (by decide)

/-- **BOTH IN ONE: AT THE FULL SIZE THE TWO WITNESSES HOLD THE SAME WORDS**: what the library's
reading takes off lastWitness at a message at m's seat and of m's shape is what the shared chain's
witness holds at m's number, at the same coins and readers, at the shared chain's input made of the
run's, at any list hd' of challenges whose first member is that of the list behind the first
chain's. -/
theorem one_text {Wt : Type} (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (sh : SharedThreadParts A Wt) (k : Coins A.B)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (heard hd' : List Fmt.Drawn)
    (hd : firstRv hd' = firstRv (heard.drop
      (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length)) (m : Msg2)
    (seatAt : Nat → Option (Nat × Nat)) (S : OnBytes.Statement) (o : Nat)
    (hseat : seatAt o = some (h.sharedNumbers.tenant m))
    (hx : (S.oracles[o]?).map (·.shape) = some (sharedShape A.Z h.places m))
    (part : OnBytes.Part) (i : Nat)
    (hr : i % 2 ^ S.rowBits o part < OnBytes.Means.realRows S o part) :
    wordsBy (P5J.At.arr A.Z) seatAt S (lastWitness h first reads k w heard) o part i =
      sh.lens.get (witL sh.lens (qAt A.Z h.places) (sentFirstOf A.Z h.places)
        (holds2 (qAt A.Z h.places) reads.weights reads.rand) sh.rest k ⟨w.w₀, w.rc, A.H.key w.x⟩
        hd') (num m) part i := by
  rw [wordsBy_lastWitness h first reads k w heard m seatAt S o hseat hx part i hr,
    shared_words sh.lens _ _ _ sh.rest k _ _ (num m) (ours_at_head h m) part i, hd]

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.find_sampled
#print axioms ProofFile.Honest.K14.lastWitness_pad
#print axioms ProofFile.Honest.K14.lastWitness_msg
#print axioms ProofFile.Honest.K14.sharedTenantsApart
#print axioms ProofFile.Honest.K14.lastWitness_first
#print axioms ProofFile.Honest.K14.lastWitness_tab
#print axioms ProofFile.Honest.K14.wordsBy_lastWitness
#print axioms ProofFile.Honest.K14.shared_words
#print axioms ProofFile.Honest.K14.ours_at_head
#print axioms ProofFile.Honest.K14.one_text
