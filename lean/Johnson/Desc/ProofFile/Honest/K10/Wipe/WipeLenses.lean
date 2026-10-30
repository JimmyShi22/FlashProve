-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/WipeLenses.lean: how the readers and writers by which K1, K9, K4 and the first
chain's last block reach that chain's state behave at a wiped state; those of Johnson/Desc/First/State.lean itself stand
in Wipe/WipeLaws.lean. Three definitions with code; the rest are theorems.

Words. The wiped state (`wipeS`, Honest/K10/WipeS.lean) is the state with these targets set to zero: those of the
statement's rows, of the carried rows in each frame that the state holds and, at the finish, of the batched row; the
rows on the table (the pile `out.pending`, and the claim at the chain's end) keep theirs.

What is proved.
  1  K1: `k1Owed_wipe`, `stateOf_wipe`, `laid_wipe`
  2  K9: `k9Owed_wipe`, `usedOf_wipe`; its lens: `atSGet_wipe`, `atSSet_wipe`, over `wipePart`
  3  K4: `k4Part_wipe`, `k4Set_wipe`, over `wipeK4`
  4  the first chain's last block: `endAsks_wipe`: the list of clauses that it asks is the same list at a state and at
     that state wiped

By what. A state is taken apart into its fields and the six kinds of place at which the chain can stand; then both sides
are the same term. For the last block's clauses, what is read of an oracle message or a group at a number goes by
`wipeSt_oracle_at` and `wipeSt_group_at` (Honest/K10/BatWipe.lean).

Limits. K10's own part (recOf, putRec) stands in Wipe/KeepK10.lean. The lenses of K8's claims and of the tests behind
the adding are not treated here. The laws hold at all states, whether a run can reach them or not. No property of the
protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.WipeGround
import Johnson.Desc.K1.AtS
import Johnson.Desc.First.Batch.AtS
import Johnson.Desc.First.K4.AtS
import Johnson.Desc.K13.FirstEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open Desc.Plain (DState)
open VerifiableInference.Desc.First (S untestedButOwnL endAsks)

/-! ## 1 K1's readers and its laying back (Johnson/Desc/K1/AtS.lean) -/

/-- The debt of rows as K1 is handed it is the same at a state and at that state wiped. -/
theorem k1Owed_wipe (s : S) : VerifiableInference.Desc.K1.owedOf (wipeS s) = VerifiableInference.Desc.K1.owedOf s := rfl

/-- The statement's part of the wiped state is that of the state, wiped. -/
theorem stateOf_wipe {L : Type} (s : S) (l : L) :
    VerifiableInference.Desc.K1.stateOf (wipeS s) l = wipeD (VerifiableInference.Desc.K1.stateOf s l) := rfl

/-- Laying K1's record back and then wiping gives what laying the wiped record into the wiped state gives. -/
theorem laid_wipe {L : Type} (s : S) (d : DState L) :
    wipeS (VerifiableInference.Desc.K1.laid s d) = VerifiableInference.Desc.K1.laid (wipeS s) (wipeD d) := rfl

/-! ## 2 K9's readers and its lens (Johnson/Desc/First/Batch/AtS.lean) -/

/-- The rows that are still owed a count, as K9 and K10 are handed them, are the same at a state and at that state
wiped. -/
theorem k9Owed_wipe (s : S) : VerifiableInference.Desc.K9.owedOf (wipeS s) = VerifiableInference.Desc.K9.owedOf s := rfl

/-- The slots that the open segment's messages have taken are the same at a state and at that state wiped. -/
theorem usedOf_wipe (s : S) : VerifiableInference.Desc.K9.usedOf (wipeS s) = VerifiableInference.Desc.K9.usedOf s := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-- K9's part of the state, wiped: the link's context and the carried record. -/
def wipePart (p : VerifiableInference.Desc.K9.Part) : VerifiableInference.Desc.K9.Part :=
  { p with L := wipeCtx p.L, d := wipeD p.d }

/-- K9's part of the wiped state is K9's part of the state, wiped. -/
theorem atSGet_wipe (s : S) :
    VerifiableInference.Desc.K9.atS.get? (wipeS s) = (VerifiableInference.Desc.K9.atS.get? s).map wipePart := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _ | _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-- Laying K9's part back and then wiping gives what laying the wiped part into the wiped state gives. -/
theorem atSSet_wipe (s : S) (p : VerifiableInference.Desc.K9.Part) :
    wipeS (VerifiableInference.Desc.K9.atS.set s p) = VerifiableInference.Desc.K9.atS.set (wipeS s) (wipePart p) := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-! ## 3 K4's part (Johnson/Desc/First/K4/AtS.lean) -/

/-- K4's part of the state, wiped: the link's context in what a layers' link holds. -/
def wipeK4 (x : OnBytes.Desc.First.K4.Part) : OnBytes.Desc.First.K4.Part :=
  ({ x.1 with L := wipeCtx x.1.L }, x.2)

/-- K4's part of the wiped state is K4's part of the state, wiped. -/
theorem k4Part_wipe (s : S) :
    OnBytes.Desc.First.K4.part? (wipeS s) = (OnBytes.Desc.First.K4.part? s).map wipeK4 := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl

/-- Laying K4's part back and then wiping gives what laying the wiped part into the wiped state gives. -/
theorem k4Set_wipe (s : S) (x : OnBytes.Desc.First.K4.Part) :
    wipeS (OnBytes.Desc.First.K4.setPart s x) = OnBytes.Desc.First.K4.setPart (wipeS s) (wipeK4 x) := rfl

/-! ## 4 What the first chain's last block asks (Johnson/Desc/K13/FirstEnd.lean) -/

/-- `Option.all` at the image of a value is `Option.all` at the value, with the test asked of the image. -/
theorem oall_map {α β : Type} (x : Option α) (f : α → β) (p : β → Bool) : (x.map f).all p = x.all fun a => p (f a) := by
  cases x <;> rfl

/-- `Option.any` at the image of a value is `Option.any` at the value, with the test asked of the image. -/
theorem oany_map {α β : Type} (x : Option α) (f : α → β) (p : β → Bool) : (x.map f).any p = x.any fun a => p (f a) := by
  cases x <;> rfl

/-- What goes on to the third chain, its statement wiped. -/
def wipeEnd (e : OnBytes.Proof.FirstEnd) : OnBytes.Proof.FirstEnd := { e with st := wipeSt e.st }

/-- What goes on to the third chain, at the wiped state, is the state's, wiped. -/
theorem firstEnd?_wipe (s : S) : (wipeS s).firstEnd? = s.firstEnd?.map wipeEnd := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ | _ | _ | ⟨_, _, _ | l⟩, _⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · show (if (l.w != OnBytes.noId) = true then some _ else none) =
      Option.map wipeEnd (if (l.w != OnBytes.noId) = true then some _ else none)
    cases (l.w != OnBytes.noId) <;> rfl

/-- The four clauses on what is left untested are the same list at a state and at that state wiped. -/
theorem untested_wipe (s : S) : untestedButOwnL (wipeS s) = untestedButOwnL s := by
  unfold VerifiableInference.Desc.First.untestedButOwnL
  rw [firstEnd?_wipe]
  cases s.firstEnd? <;>
    simp only [st_wipe, wipeSt_size, wipeSt_gsize, wipeSt_oracle_at, wipeSt_group_at, oall_map, oany_map] <;> rfl

/-- **What the first chain's last block asks is the same list of clauses at a state and at that state wiped.** -/
theorem endAsks_wipe (s : S) : endAsks (wipeS s) = endAsks s := by
  unfold VerifiableInference.Desc.First.endAsks
  rw [untested_wipe, closeOk_wipe]

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.k1Owed_wipe
#print axioms ProofFile.Honest.K10.stateOf_wipe
#print axioms ProofFile.Honest.K10.laid_wipe
#print axioms ProofFile.Honest.K10.k9Owed_wipe
#print axioms ProofFile.Honest.K10.usedOf_wipe
#print axioms ProofFile.Honest.K10.wipePart
#print axioms ProofFile.Honest.K10.atSGet_wipe
#print axioms ProofFile.Honest.K10.atSSet_wipe
#print axioms ProofFile.Honest.K10.wipeK4
#print axioms ProofFile.Honest.K10.k4Part_wipe
#print axioms ProofFile.Honest.K10.k4Set_wipe
#print axioms ProofFile.Honest.K10.oall_map
#print axioms ProofFile.Honest.K10.oany_map
#print axioms ProofFile.Honest.K10.wipeEnd
#print axioms ProofFile.Honest.K10.firstEnd?_wipe
#print axioms ProofFile.Honest.K10.untested_wipe
#print axioms ProofFile.Honest.K10.endAsks_wipe
