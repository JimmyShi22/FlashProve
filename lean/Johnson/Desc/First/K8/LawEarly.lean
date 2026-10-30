-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawEarly.lean: THE SMALLNESS TEST: THE LETTERS' "EARLY" CELLS ARE THE CELLS OF
THE ARRAYS THAT THE RUNNING TEXT'S GUARD OF ORDER WALKS: SO EVERY EARLY CELL'S ARRAY LIES IN A
MESSAGE THAT IS SENT BEFORE THE MATRIX IS DRAWN.

The count of the round of the draw fixes a tuple of messages M. At the letters of the library M is
cut by `early tl` (OnBytes/Tie/Pv/Tail/LettersAt.lean): the cells of the arrays in `tl.gtTree` and
of the first four vectors of reads. Our laws at the plan run over `Named.arrays tl`
(Johnson/Desc/First/K8/Named.lean). That the two are one set is the lemma
`early_iff_arrays` (Johnson/Desc/Ok/EarlyArrays.lean): CALLED here:
  `early_iff_named`: a cell of array t is early if and only if t is among `Named.arrays tl`.
  `early_before_at_entry`: **at an entry of the first chain's flat list with `LikeP`, under the
    file's test on the plan and `Named.namedB`: the array of every early cell lies, now, in a
    message that the statement and the book have, in a tree that is sent strictly in front of the
    round of the draw.**
  `caller_before_at_entry`: THE LAW'S CALLER, BY NAME: under the same premises `CallerAt` is had at
    the caller over the members' messages, with `sym_dep` and `tab_dep` (every member counted as
    read), a member's number its tree's, and every such tree sent in front of the draw.
Statements and proofs: by calls.
Limits. Those of Johnson/Desc/First/K8/LawSeatedPlan.lean. MESSAGE-WISE: where inside its message
the cell lies is not said. A mask's address is never early (`early_mask`).

-/
import Johnson.Desc.First.K8.LawSeatedPlan
import Johnson.Desc.Ok.EarlyArrays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

/-- A cell of array t is early if and only if t is among the arrays that the matrix multiplies. -/
theorem early_iff_named (tl : OnBytes.Model.HTailF2) (t r c : ℕ) :
    OnBytes.Tie.Pv.Tail.early tl (.cell t r c) = true ↔ t ∈ Named.arrays tl :=
  Johnson.Desc.Ok.early_iff_arrays tl t r c

/-- **Every early cell's array lies in a message that is sent strictly in front of the round of the
draw.** -/
theorem early_before_at_entry {Xi : Type} (F : FileDescription Xi) {seat : Seat F.S₁} {p : Par}
    {b : Block F.S₁ F.Cl} (h : LikeP seat p b) (i : Nat) (hb : F.first.blocksInOrder[i]? = some b)
    (hF : F.planOk = true) (S₀ : OnBytes.Statement) (book : OnBytes.TreeBook)
    (tl : OnBytes.Model.HTailF2) (L : OnBytes.Model.LinkCtx)
    (hN : Named.namedB p S₀ book tl L = true) (t r c : ℕ)
    (he : OnBytes.Tie.Pv.Tail.early tl (.cell t r c) = true) :
    ∃ o m j, Named.msgNow L t = some o ∧ Named.memberAt S₀ book o = some m ∧
      sendRound F.roundsDeclaredByBlocks.1 m.2.1 = some j ∧ j < roundsIn (F.first.blocksInOrder.take i) :=
  arrays_before_at_entry F h i hb hF S₀ book tl L hN t ((early_iff_named tl t r c).1 he)

section
open Cb Cb.Pv.Tail KObj Johnson.Pack VerifiableInference.Desc.Sound

/-- **The law's caller, by name**: under the same premises there is what a caller of the proved
block owes (`CallerAt`, Johnson/Desc/First/K8/LawBefore.lean), at the caller over the members'
messages:
`Named.namedCallerAt`: its symbols and its tables are functions of the members' messages (`sym_dep`,
`tab_dep`, with every member counted as read); a member's number is its tree's; and every such tree
is sent strictly in front of the round of the draw. -/
theorem caller_before_at_entry {Xi : Type} (F : FileDescription Xi) {seat : Seat F.S₁} {p : Par}
    {b : Block F.S₁ F.Cl} (h : LikeP seat p b) (i : Nat) (hb : F.first.blocksInOrder[i]? = some b)
    (hF : F.planOk = true) (cs : OnBytes.Codes) (rad : OnBytes.OracleShape → Nat)
    (S₀ : OnBytes.Statement) (book : OnBytes.TreeBook) (tl : OnBytes.Model.HTailF2)
    (L : OnBytes.Model.LinkCtx) (tl0 : OnBytes.Model.HTailF2)
    (Θ : TLetters Cb.Gl.E (OnBytes.Tie.Pv.Tail.sizeOf tl0))
    (rdm : (sigOf cs (Named.listOf rad S₀ book tl L)).Msg → Θ.M)
    (hN : Named.namedB p S₀ book tl L = true) :
    ∃ C : CallerAt p (tailCallerOf (OnBytes.Tie.Pv.Tail.sizeOf tl0) Θ
        (sigOf cs (Named.listOf rad S₀ book tl L)) rdm),
      (∀ a, C.dep a) ∧ (∀ a, C.no a = (Named.seatFn rad S₀ book tl L a).1) ∧
      ∀ a, ∃ j, sendRound F.roundsDeclaredByBlocks.1 (C.no a) = some j ∧ j < roundsIn (F.first.blocksInOrder.take i) :=
  ⟨Named.namedCallerAt cs rad S₀ book tl L tl0 Θ rdm p hN, fun _ => trivial, fun _ => rfl,
    fun a => (before_at_entry F h i hb hF).2.1 _ (Named.named_of_test hN rad a)⟩

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.caller_before_at_entry
#print axioms VerifiableInference.Desc.First.K8.early_iff_named
#print axioms VerifiableInference.Desc.First.K8.early_before_at_entry
