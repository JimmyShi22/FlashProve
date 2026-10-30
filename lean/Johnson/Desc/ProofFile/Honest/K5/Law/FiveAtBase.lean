-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/FiveAtBase.lean: conditional: the five statements that a
sub-protocol owes at its border, for the attention sub-protocol (kind K5), at each of its twelve
borders, at the first thread (firstThread, Honest/Thread/TheFirstThread.lean) of a prover that the maker
returns at the filling onlineProverPartsInUse. The index type, the filling's reader of the index, its sizes
and its opening are letters, and so is the first thread's script. No definition.

  k5_lot_among_lots             K5's lot is among the filling's lots
  k5_lot_alone                  no other lot of the filling lays a side of the kind K5
  place_at_border_is_kindFive   the written place at the border of group g is of the kind K5
  firstClause_gives_k5Keeps     there the first thread's clause of keeps gives the kind's keeper
  kindFive_five_at_letters      FiveAtBorder at the first thread's letters, those that the kind does not
                                read free
  kindFive_five_at_first_thread FiveAtBorder at the border of group g, at every Said and every fall
  kindFive_five_at_every_member the same at every member of the first chain of the kind K5

The premises of kindFive_five_at_first_thread, all of them: head, the library's head at the return;
keyReader, the filling's reader of the key points is the kind's; made, the maker returns; that g is below
12; and three on the first thread's script (kindFive_five_at_every_member has the same, with a member of
the kind in the stead of g, and scriptHoldsK5 at each group):
  treesFixed     the table of each of the script's own trees is fixed once the rounds in front of it are
                 played, at every border of the chain;
  scriptHoldsK5  K5ScriptQ at every input that meets ReadyInput: at all coins and at all lists of
                 challenges of the border's length or more, reached by a run or not;
  validCellsHold where the run's input meets ReadyInput, the script's stored table holds some index.

How. k5_five_at_filling_with_clause_letter (FiveAtClauseLetter.lean in this folder) at this filling. The thread's clause
of keeps is met in both directions at the member: into the kind's keeper by its first part, and back
from the form behind the member (formsBehind_of_form). Then each statement is lifted to the letter Said.
Nothing of Said is spent.

Limits.
  * Conditional. treesFixed, scriptHoldsK5 and validCellsHold are proved of no script here, and the
    first thread's script has no value yet. Everything that the five statements say of values sits in
    scriptHoldsK5.
  * Each statement is an implication from the thread's invariant with Said in front of the member.
    Nobody has a state that meets it at one of these twelve borders; where none does they say nothing.
    ReadyInput is empty where the prover has no trace.
  * This is not the kind's acceptance. That also asks the kind's sides to be lent their coins, a script
    with a value, and states that reach these borders.
  * The index being a letter is no generality: paying scriptHoldsK5 needs facts on the trace and
    planesAtRef sizes = Sz.ref, and at another reader or other sizes it is most likely false of every
    script.
  * NOT IN FRONT OF A LAW OVER COINS. The full size alone, at the earlier hash
    OnBytes.secondHashFunction.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.FiveAtClauseLetter
import Johnson.Desc.ProofFile.Honest.Law.FillPairs
import Johnson.Desc.ProofFile.Honest.K5.Law.FindAtBase
import Johnson.Desc.ProofFile.Honest.K5.Law.KindFivePlaces
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Desc.ProofFile.Honest.Thread.FiveAtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.First.Look (lookAt)
open H2K5.Honest (K5KeepsAt)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (Script WtF lettersHead b0Head_closed HeadAtReturn FirstThreadParts
  firstThread firstClauses formsBehind_of_form)
open P5J (TS CellsM)

section Lots
variable {W₀ : Type} (index : WiderIn W₀) (hash : SecondHashFunctionArgument) (sizes : OnBytes.HonestTrace.Sz)
  (opening : OnlineProverArguments)

/-- K5's lot is among the filling's lots. -/
theorem k5_lot_among_lots (keyReader : opening.keyOf = keyOfK3) (publicPart : ProofFile.Pub)
    (ground : Ground) :
    ∃ lot ∈ (onlineProverPartsInUse index hash sizes opening).lots,
      lot.halves publicPart ground = (k5LotK id keyOfK3).halves publicPart ground :=
  ⟨k5LotK id opening.keyOf, by
    rw [fillPairs_lots]
    exact List.mem_map.2 ⟨_, k5_pair_mem index hash sizes opening, rfl⟩, by rw [keyReader]⟩

/-- Every other lot of the filling lays no side of the kind K5. -/
theorem k5_lot_alone (keyReader : opening.keyOf = keyOfK3) (publicPart : ProofFile.Pub)
    (ground : Ground) :
    ∀ lot ∈ (onlineProverPartsInUse index hash sizes opening).lots,
      (∀ side ∈ lot.halves publicPart ground, side.place.kind ≠ .K5) ∨
        lot.halves publicPart ground = (k5LotK id keyOfK3).halves publicPart ground := by
  intro lot member
  rcases lot_alone index hash sizes opening (k5_pair_only index hash sizes opening) publicPart ground
    lot member with rfl | other
  · exact Or.inr (by rw [keyReader])
  · exact Or.inl other

end Lots

variable {files : VerifierAndGoals.PublicFiles} {W₀ : Type} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

section Clauses
variable (head : HeadAtReturn files A) {g : Nat} (groupInRange : g < 12)
include groupInRange

/-- The place at the border of group g is of the kind K5. -/
theorem place_at_border_is_kindFive {p : Place} (atBorder : P5J.At.ps[borderOf g]? = some p) :
    p.kind = KindName.K5 := by
  have written := writtenPlaces_borders_are_kindFive g groupInRange
  rw [atBorder] at written
  exact beq_iff_eq.1 written

/-- At the border the first thread's clause of keeps gives the kind's keeper. -/
theorem firstClause_gives_k5Keeps {p : Place} (atBorder : P5J.At.ps[borderOf g]? = some p)
    {s s' : TS} (clause : kpBy (firstClauses head) p s s') : K5KeepsAt (P5J.At.X A.Z) p s s' :=
  ((kpBy_at _ (place_at_border_is_kindFive groupInRange atBorder) s s').1 clause).1.1.1.1.1

end Clauses

/-- **The five statements at the letters of the first thread**, with the letters that the kind does not
read left free: the test, the carry, the counts of trees, the riders' three letters. b₀ is the border of
the reply. -/
theorem kindFive_five_at_letters (head : HeadAtReturn files A) (index : WiderIn W₀)
    (sizes : OnBytes.HonestTrace.Sz) (opening : OnlineProverArguments) (keyReader : opening.keyOf = keyOfK3)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse index OnBytes.secondHashFunction sizes opening) = .ok A)
    (script : Script A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (replyBorder : b₀ = 339) (nextSlot : Nat) (stateSentence : Nat → TS → Prop)
    (heardSentence : Nat → Option OnBytes.Model.Forest.Heard → Prop)
    (input : Local W₀ IndexCommitterCoins ProofFile.Inst Cells) {g : Nat} (groupInRange : g < 12)
    (treesFixed : ∀ b, b ≤ head.firstChain.blocksInOrder.length → ∀ j, j < treesTo head.firstChain.blocksInOrder b →
      script.fixed (.own j) ≤ roundsTo head.firstChain.blocksInOrder b)
    (scriptHoldsK5 : ∀ a x₁, (P5J.At.X A.Z).A[g]? = some a →
      lookAt (P5J.At.X A.Z) (2 * g + 1) false = some x₁ →
      K5ScriptQ head.head script (ReadyInput head.description A.H)
        (roundsTo head.firstChain.blocksInOrder (borderOf g)) x₁ a id
        (seatOf keyOfK3 A.Z A.G head.firstChain g a) (OnBytes.Model.Forest.elems a.fs))
    (validCellsHold : ReadyInput head.description A.H input →
      ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (script.cells input) i)
    (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    FiveAtBorder (lettersHead head.head A.H script test carryX item n₁ n₂ b₀
      (ReadyInput head.description A.H) (ridersOf (csHead nextSlot stateSentence heardSentence))
      (kpBy (firstClauses head)) input).thread Said fall (borderOf g) := by
  have all := k5_five_at_filling_with_clause_letter head.head script test carryX item n₁ n₂
    (ReadyInput head.description A.H) nextSlot stateSentence heardSentence
    (kpBy (firstClauses head)) input groupInRange made
    (k5_lot_among_lots index OnBytes.secondHashFunction sizes opening keyReader A.Z A.G)
    (k5_lot_alone index OnBytes.secondHashFunction sizes opening keyReader A.Z A.G) treesFixed
    (fun _ atBorder _ _ _ _ _ _ clause => firstClause_gives_k5Keeps head groupInRange atBorder clause)
    (fun _ atBorder _ _ _ s _ _ _ _ _ s' _ _ _ formBehind _ keeper =>
      (kpBy_at _ (place_at_border_is_kindFive groupInRange atBorder) s s').2
        ⟨⟨⟨⟨⟨keeper, formsBehind_of_form head.head A.H script _ _ _ _ _ _ _ _ _ input atBorder
          formBehind⟩, trivial⟩, trivial⟩, trivial⟩, trivial⟩)
    scriptHoldsK5 validCellsHold
  rw [b0Head_closed.2, ← replyBorder] at all
  exact
    { plays := playsS_of _ Said all.1.1
      behind := behindS_of _ Said all.1.2.1
      exchange := exchangeS_of _ Said all.1.2.2.1
      ridesPast := ridesPastS_of _ Said all.1.2.2.2
      accepted := acceptedS_of _ Said (all.2 fall) }

/-- **THE FIVE STATEMENTS AT THE FIRST THREAD.** Conditional: every premise stands, by name, in the
file's head. Each statement is an implication from the thread's invariant with Said in front of the
member. -/
theorem kindFive_five_at_first_thread (head : HeadAtReturn files A) (index : WiderIn W₀)
    (sizes : OnBytes.HonestTrace.Sz) (opening : OnlineProverArguments) (keyReader : opening.keyOf = keyOfK3)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse index OnBytes.secondHashFunction sizes opening) = .ok A)
    (parts : FirstThreadParts A) (input : Local W₀ IndexCommitterCoins ProofFile.Inst Cells) {g : Nat}
    (groupInRange : g < 12)
    (treesFixed : ∀ b, b ≤ head.firstChain.blocksInOrder.length → ∀ j, j < treesTo head.firstChain.blocksInOrder b →
      parts.script.fixed (.own j) ≤ roundsTo head.firstChain.blocksInOrder b)
    (scriptHoldsK5 : ∀ a x₁, (P5J.At.X A.Z).A[g]? = some a →
      lookAt (P5J.At.X A.Z) (2 * g + 1) false = some x₁ →
      K5ScriptQ head.head parts.script (ReadyInput head.description A.H)
        (roundsTo head.firstChain.blocksInOrder (borderOf g)) x₁ a id
        (seatOf keyOfK3 A.Z A.G head.firstChain g a) (OnBytes.Model.Forest.elems a.fs))
    (validCellsHold : ReadyInput head.description A.H input →
      ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (parts.script.cells input) i)
    (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    FiveAtBorder (firstThread head parts input) Said fall (borderOf g) :=
  kindFive_five_at_letters head index sizes opening keyReader made parts.script _ _ _ _ _ _ rfl _ _ _
    input groupInRange treesFixed scriptHoldsK5 validCellsHold Said fall

/-- **AT EACH MEMBER OF THE FIRST CHAIN OF THE KIND K5** the five statements hold. The other two chains
have no member of the kind: kindFive_not_in_shared, kindFive_not_in_second (KindFivePlaces.lean in this
folder). Conditional: as kindFive_five_at_first_thread, with scriptHoldsK5 at each group. -/
theorem kindFive_five_at_every_member (head : HeadAtReturn files A) (index : WiderIn W₀)
    (sizes : OnBytes.HonestTrace.Sz) (opening : OnlineProverArguments) (keyReader : opening.keyOf = keyOfK3)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse index OnBytes.secondHashFunction sizes opening) = .ok A)
    (parts : FirstThreadParts A) (input : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (treesFixed : ∀ b, b ≤ head.firstChain.blocksInOrder.length → ∀ j, j < treesTo head.firstChain.blocksInOrder b →
      parts.script.fixed (.own j) ≤ roundsTo head.firstChain.blocksInOrder b)
    (scriptHoldsK5 : ∀ g, g < 12 → ∀ a x₁, (P5J.At.X A.Z).A[g]? = some a →
      lookAt (P5J.At.X A.Z) (2 * g + 1) false = some x₁ →
      K5ScriptQ head.head parts.script (ReadyInput head.description A.H)
        (roundsTo head.firstChain.blocksInOrder (borderOf g)) x₁ a id
        (seatOf keyOfK3 A.Z A.G head.firstChain g a) (OnBytes.Model.Forest.elems a.fs))
    (validCellsHold : ReadyInput head.description A.H input →
      ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (parts.script.cells input) i)
    (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) {b : Nat}
    {member : VerifiableInference.Desc.Block TS ProofFile.Cl}
    (atNumber : head.firstChain.blocksInOrder[b]? = some member) (ofTheKind : member.place.kind = .K5) :
    FiveAtBorder (firstThread head parts input) Said fall b := by
  obtain ⟨g, groupInRange, rfl⟩ := kindFive_only_at_borders head.head atNumber ofTheKind
  exact kindFive_five_at_first_thread head index sizes opening keyReader made parts input groupInRange
    treesFixed (scriptHoldsK5 g groupInRange) validCellsHold Said fall

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_lot_among_lots
#print axioms ProofFile.Honest.K5.k5_lot_alone
#print axioms ProofFile.Honest.K5.firstClause_gives_k5Keeps
#print axioms ProofFile.Honest.K5.kindFive_five_at_letters
#print axioms ProofFile.Honest.K5.kindFive_five_at_first_thread
#print axioms ProofFile.Honest.K5.kindFive_five_at_every_member
