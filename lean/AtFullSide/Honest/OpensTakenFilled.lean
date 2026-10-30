-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/OpensTakenFilled.lean: ONE FIELD OF `TheThreadsHalf` (TheOneObject.lean of this
folder), IN THAT STRUCTURE's OWN FIELD TYPE, at every value of its two open letters: `opensTaken`:
at the second chain, each source that a round opens and that is declared as taken over from an
earlier chain stands in the thread's list of taken trees.

How. The thread's list of taken trees is `takenLast` (Honest/K12/AtFile/WLaidDefs.lean), a closed
list of three sources. The thread's list of members is the online description's second chain, which
under the head is alike, member by member, to the written description `WP`
(Johnson/AtFull/ProofPlan/WP.lean): alike members declare the same rounds. So the sentence is one
pass over a closed list, and Lean's kernel evaluates it.

Main names.
  `listedIfTaken`, `takenOpensListed`   the pass: a test on one source, and on a list of members
  `taken_opens_listed`    the pass says yes at the written second chain and `takenLast`
  `taken_opens_bent_zero`, `_one`, `_two`, `_none`   controls: with any one of the three sources left out of
                          the list, and with the empty list, the pass says no: so the pass can
                          refuse, each of the three is opened, and none of them is idle
  `listed_of_pass`        what a yes of the pass means, at any list of members
  `opensTaken_filled`     the field
At the file's end a check by Lean's elaborator that the statement has the field's type.

Limits. A public sentence on declared rounds and on a written list: no run, no coin, no table. O, P:
the structure's two open letters; P holds propositions, and that a value of P exists is not shown
here. The full size, and the hash function `OnBytes.secondHashFunction`, alone.

What is not claimed. This is none of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import AtFullSide.Honest.TheOneObject
import Johnson.AtFull.ProofPlan.WP
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OpensLaw
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm AtPublicFiles.Committed AtPublicFiles.TheFalls
open OnBytes.Slice (frS)
open VerifierAndGoals (PublicFiles readFiles)
open VerifiableInference.Desc (Block)
open P2Law.ProofPlan (WP)
open ProofFile.Honest.K12.AtFile (takenLast roundsTrees rounds_alike)

/-! ## The pass -/

/-- A source passes if it is one of the chain's own, or stands in the list. -/
def listedIfTaken (taken : List Fmt.TreeSource) : Fmt.TreeSource → Bool
  | .own _ => true
  | .taken c j => decide (Fmt.TreeSource.taken c j ∈ taken)

/-- Every source that a round of these members opens passes. A member is given as `roundsTrees`
gives it: its declared rounds, and a count that this pass does not read. -/
def takenOpensListed (taken : List Fmt.TreeSource) (R : List (List Fmt.DeclaredRound × Nat)) : Bool :=
  R.all fun x => x.1.all fun d => d.opens.all fun o => listedIfTaken taken o.2

/-- **The pass at the written second chain and the three sources: yes.** -/
theorem taken_opens_listed :
    takenOpensListed takenLast (WP.second.blocksInOrder.map roundsTrees) = true := by decide +kernel

/-- Control: without the first of the three sources, no. -/
theorem taken_opens_bent_zero :
    takenOpensListed (takenLast.eraseIdx 0) (WP.second.blocksInOrder.map roundsTrees) = false := by
  decide +kernel

/-- Control: without the second, no. -/
theorem taken_opens_bent_one :
    takenOpensListed (takenLast.eraseIdx 1) (WP.second.blocksInOrder.map roundsTrees) = false := by
  decide +kernel

/-- Control: without the third, no. -/
theorem taken_opens_bent_two :
    takenOpensListed (takenLast.eraseIdx 2) (WP.second.blocksInOrder.map roundsTrees) = false := by
  decide +kernel

/-- Control: with the empty list, no: some round of the chain opens a source that is taken over. -/
theorem taken_opens_bent_none :
    takenOpensListed [] (WP.second.blocksInOrder.map roundsTrees) = false := by decide +kernel

/-- **What a yes of the pass means**, at any list of members and any list of sources. -/
theorem listed_of_pass {S Cl : Type} {bs : List (Block S Cl)} {taken : List Fmt.TreeSource}
    (hp : takenOpensListed taken (bs.map roundsTrees) = true) :
    ∀ d ∈ bs.flatMap (·.rounds), ∀ o ∈ d.opens, ∀ c j, o.2 = .taken c j → o.2 ∈ taken := by
  intro d hd o ho c j e
  obtain ⟨b, hb, hdb⟩ := List.mem_flatMap.1 hd
  unfold takenOpensListed at hp
  simp only [List.all_eq_true] at hp
  have ho' : listedIfTaken taken o.2 = true := hp _ (List.mem_map_of_mem hb) d hdb o ho
  rw [e] at ho' ⊢
  exact of_decide_eq_true ho'

/-! ## The field -/

/- The three instances that the structure's own file gives by hand. -/
local instance (priority := high) nonemptyPadZ_opensTaken : Nonempty PadZ :=
  pads_nonempty frS 402653181

local instance (priority := high) nonemptyRunValue_opensTaken : Nonempty RunValue :=
  ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_opensTaken : Inhabited RunValue :=
  ⟨fun _ => 0⟩

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)
  {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) {O : TheLetters.OpenShared A}
  (P : TheLetters.OpenLast h O)

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- The pass at the online description's second chain, under the head. -/
theorem taken_opens_listed_at_head :
    takenOpensListed takenLast (h.description.second.blocksInOrder.map roundsTrees) = true := by
  rw [← rounds_alike (ProofFile.Honest.K14.alike_last_at_laid h.head.scope h.head.laid)]
  exact taken_opens_listed

/-- **The field opensTaken.** The thread's members are the description's second chain and its list
of taken trees is `takenLast`, both by unfolding. -/
theorem opensTaken_filled :
    ∀ r : TiedRun h hr, Socket.opensTaken h (TheLetters.first h) (TheLetters.reads h)
      (lastParts h (TheLetters.first h) (TheLetters.last h P)) r.R :=
  fun _ => listed_of_pass (taken_opens_listed_at_head h)

/-- A check by Lean's elaborator that the statement has the field's type: a value of the structure
with this field laid anew. It takes a value T for the other fields: so it shows nothing of the
others, and is no payment. -/
example (T : TheThreadsHalf h hr) : TheThreadsHalf h hr :=
  { T with opensTaken := opensTaken_filled h hr T.open₃ }

end AtFullSide.Honest

#print axioms AtFullSide.Honest.taken_opens_listed
#print axioms AtFullSide.Honest.taken_opens_bent_zero
#print axioms AtFullSide.Honest.taken_opens_bent_one
#print axioms AtFullSide.Honest.taken_opens_bent_two
#print axioms AtFullSide.Honest.taken_opens_bent_none
#print axioms AtFullSide.Honest.listed_of_pass
#print axioms AtFullSide.Honest.taken_opens_listed_at_head
#print axioms AtFullSide.Honest.opensTaken_filled
