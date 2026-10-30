-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/TraceCells.lean: THE CELLS OF THE OUTPUT HEAD, READ OFF A TRACE
THAT MEETS THE BUNDLE OF STATEMENTS ON THE HONEST TRACE (Johnson/HonestTrace/Full.lean: MeetsAll),
MEET WHAT THE HONEST SIDE OF THE SUB-PROTOCOL "the output head's own rounds" IS ASKED OF ITS CELLS:
the normalization's 17 identities at every position ((dataOf c).Holds), HonestHead c.toCells
(Kinds/Law/OpenedHead.lean), and the nine keys' fields (NineKeys, Kinds/Law/OutCallBack.lean: each
key, at each entry and position, is a row of its table). One definition, for statements alone, and
four statements with their proofs, by calls.

What it is not. CONDITIONAL ON THE BUNDLE, which is a hypothesis here: that it holds of a trace is
another file's (Johnson/Goal/HonestTrace/FullInScope.lean: meetsAll_in_scope, which this file does
not import): OF THE LIBRARY's HONEST TRACE trFull; a runnable model's trace is another text, tied to
it by no theorem. That the premises hold together of some X, i, x and T is not shown here: the proof
of headCells_honest_in_scope (TraceCellsInScope.lean) meets this file's premises from its own, and
that file's head says what is had of these. THE FULL SIZE ALONE: the bundle is typed at the
reference sizes, and FullH is a premise; so are digSh = 8, the kind's tests on the plan, the
request's form (Head3) and "the table is the library's EX on 16 bits". traceCells IS NOT WHAT THE
HONEST SIDE READS: that its own reader of cells agrees with traceCells inside the ranges that the
head's relation names is not said here. The identities and the two sums are 0 modulo the field's
prime. No verifier's state, no round and no run stands in it: that the sub-protocol's forms are 0 on
what the honest side sends is not said here. Nothing on soundness, on completeness or on what a
proof hides.

  traceCells          the sub-protocol's structure of cells made of the library's reading of list
                      24 of the trace, with the output matrix that the library reads in the index.
  cellsN_traceCells   the library's structure made of these cells is that reading: by unfolding.
  traceCells_headCl   the library's clauses on the head hold at it: the bundle's own field.
  traceCells_small    every cell is small (below 2^18, inside the ranges): each is an entry of the
                      trace.
  headCells_honest    the main statement.
CALLED: honest_atX (Kinds/Law/HonestOfHeadCl.lean); cellsBack (Kinds/Law/K6Comp.lean).
-/
import Johnson.Desc.Kinds.Law.HonestOfHeadCl
import Johnson.Desc.Kinds.Law.K6Comp
import Johnson.HonestTrace.Full

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open Inst.Model (ppref AcceptancePolicy Mat Instance)
open OnBytes.Road.Hd (FullH)
open OnBytes.HonestTrace (MeetsAll Tr)
open VerifiableInference.Desc.Kinds.HeadJoin (cellsN)

/-- **The sub-protocol's structure of cells, off a trace**: the library's reading of the head's
list, and the output matrix that the library reads in the index's matrix of the weights' digits. A
definition for statements alone: no definition of the honest side names it. -/
noncomputable def traceCells (X : OnBytes.Model.Verify.Public) (i : Cm.Idx) (T : Tr) : NCells :=
  cellsBack
    (OnBytes.Road.Hd.cellsH X.hS X.HLy (OnBytes.Model.Verify.borderOf X.y) (T 24))
    (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef i.mat).H

variable {X : OnBytes.Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- The library's structure made of these cells is the library's reading of the list: by unfolding.
-/
theorem cellsN_traceCells (X : OnBytes.Model.Verify.Public) (i : Cm.Idx) (T : Tr) :
    cellsN (traceCells X i T) =
      OnBytes.Road.Hd.cellsH X.hS X.HLy (OnBytes.Model.Verify.borderOf X.y) (T 24) := rfl

/-- The library's clauses on the head hold at these cells: the bundle's own field. -/
theorem traceCells_headCl (M : MeetsAll X i x T) :
    _root_.Policy.HeadCl (OnBytes.Road.Hd.npOf X.hS) (OnBytes.Road.Hd.polOf X.hS) i.mat x
      (cellsN (traceCells X i T)) :=
  M.ords.head.2.1

/-- Every cell is small (below 2^18, inside the ranges): each is an entry of the trace, and these
are below 129. -/
theorem traceCells_small (M : MeetsAll X i x T) :
    Inst.Model.Head.Small (cellsN (traceCells X i T)) := by
  have hb : ∀ a r c, |T 24 a r c| < 2 ^ 18 := fun a r c =>
    lt_trans (M.small 24 a r c) (by norm_num)
  rw [cellsN_traceCells]
  unfold Inst.Model.Head.Small
  intro t _
  exact ⟨fun _ _ => hb _ _ _, fun _ _ => hb _ _ _, fun _ _ => hb _ _ _, fun _ _ => hb _ _ _⟩

/-- **THE CELLS OFF A TRACE THAT MEETS THE BUNDLE ARE HONEST.** work: a letter, which stands in the
policy's term and in the premise on the plan. tab: a letter, which is asked to be the library's EX
on 16 bits. -/
theorem headCells_honest (M : MeetsAll X i x T) (hF : FullH X.hS) (h8 : X.hS.digSh = 8)
    (work : Nat) (hplan : (parOf X.hS work).ok = true) (h3 : Inst.Model.Head3 x)
    (tab : Nat → Nat) (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u) :
    letI := VerifiableInference.Desc.Kinds.Head.sizesOf X.hS
    letI : Policy := (parOf X.hS work).policy
    letI := reqX x
    letI : Token := ⟨x.y.val⟩
    (dataOf (traceCells X i T)).Holds ∧ HonestHead (traceCells X i T).toCells ∧
      NineKeys tab (traceCells X i T) :=
  honest_atX X.hS work x i.mat tab (traceCells X i T) hF h8 hplan h3 htab rfl
    (traceCells_small M) (traceCells_headCl M)

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.traceCells
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.cellsN_traceCells
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.traceCells_headCl
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.traceCells_small
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.headCells_honest
