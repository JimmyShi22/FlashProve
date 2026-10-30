-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/PlanOwn.lean (the moment is written out):
the four fields of PlanAt (K1/Law/NewAtSending.lean) that read the place P alone: one, pad, row,
part: as one
structure, each field to the letter; a test with code for each, with its law; the accepts by Lean's
kernel at the placeholder qFull (Johnson/Desc/K1/Law/QFull.lean) at all 52 places of the kind K1 in
the proof file's first chain; a negative test a clause; and the carrying to a computed value. A law
file; no running text imports it. Why apart. The four name no round's data d₁ d₂, no frame, no list
of members: so they stand whatever form the quantifier over d₁ d₂ in the laws above takes.
  PlanOwn P: one (a message with an OOD sample has one answer) · pad (its pad can be laid) · row (it
      has a row) · part (no two messages of the place have one seat)
  oneB, padB, rowB, partB, planOwnB; planOwn_of: the accept gives the structure
  saysB P: the place has a message with an OOD sample, and sends two messages at least: so that none
      of the four clauses is true for want of a case
  gpFull := ⟨1, 0⟩; the places: firstPar qFull gpFull · parLater qFull gpFull l (k1Ix l d + 1)
      (cond d 2 1) at l < 25, both d · parW qFull gpFull 4 msg at what linMessageW qFull.lin gives
  own_first, own_fifty, own_w: the accepts: Lean's kernel; says_first, says_w: the like for saysB
      (five messages at the opening, two with W); says_fifty: each of the fifty sends ONE message,
      and it has an OOD sample: SO "part" HAS NO CASE AT THE FIFTY: it is true there for want of one
  teeth_one, teeth_pad, teeth_row, teeth_part: the negative tests, at the first segment's opening:
      every answer count doubled · the code table emptied · every row count turned to 0 · mask rows
      of two lengths in one tree (no layout can be made: all seats read (0, 0)). With the code
      table emptied a layout is still made and partB still accepts: the only reject of partB that
      this file shows is at a place whose trees cannot be laid
  planOwn_first, planOwn_later, planOwn_w: at every q with LikeFull q and gp = gpFull

What is not claimed. LikeFull at a seat, gp = ⟨1, 0⟩ at a seat: other files' theorems in scope,
under the door's pin. The seven other fields of PlanAt. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.QFull
import Johnson.IMR.K1Scope
import Johnson.Desc.K1.Law.BookAtRecord
import Johnson.Desc.K1.Law.Port6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params _root_.Desc.Plain
open IM (k1Ix)

/-- **What PlanAt asks of the place alone.** -/
structure PlanOwn (P : Par) : Prop where
  one : ∀ j : Fin (shapesOf P).length, sampledAt P j → (shapeAt P j).answers = 1
  pad : ∀ j : Fin (shapesOf P).length, sampledAt P j →
    (OnBytes.Send.pad P.codes (shapeAt P j)).isSome = true
  row : ∀ j : Fin (shapesOf P).length, sampledAt P j →
    0 < (shapeAt P j).mainRows ∨ 0 < (shapeAt P j).maskRows
  part : ∀ i i' : ℕ, i < P.sent.size → i' < i →
    ((layOf P).tree.getD i' 0, (layOf P).part.getD i' 0) ≠
      ((layOf P).tree.getD i 0, (layOf P).part.getD i 0)

def oneB (P : Par) : Bool := (List.finRange (shapesOf P).length).all fun j =>
  !decide (sampledAt P j) || decide ((shapeAt P j).answers = 1)

def padB (P : Par) : Bool := (List.finRange (shapesOf P).length).all fun j =>
  !decide (sampledAt P j) || (OnBytes.Send.pad P.codes (shapeAt P j)).isSome

def rowB (P : Par) : Bool := (List.finRange (shapesOf P).length).all fun j =>
  !decide (sampledAt P j) ||
    (decide (0 < (shapeAt P j).mainRows) || decide (0 < (shapeAt P j).maskRows))

def partB (P : Par) : Bool := (List.range P.sent.size).all fun i => (List.range i).all fun i' =>
  decide (((layOf P).tree.getD i' 0, (layOf P).part.getD i' 0) ≠
    ((layOf P).tree.getD i 0, (layOf P).part.getD i 0))

def planOwnB (P : Par) : Bool := oneB P && padB P && rowB P && partB P

theorem planOwn_of {P : Par} (h : planOwnB P = true) : PlanOwn P := by
  unfold planOwnB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun i i' hi hi' => ?_⟩
  · have := List.all_eq_true.1 h1 j (List.mem_finRange j)
    simpa [hj] using this
  · have := List.all_eq_true.1 h2 j (List.mem_finRange j)
    simpa [hj] using this
  · have := List.all_eq_true.1 h3 j (List.mem_finRange j)
    simpa [hj] using this
  · exact of_decide_eq_true (List.all_eq_true.1
      (List.all_eq_true.1 h4 i (List.mem_range.2 hi)) i' (List.mem_range.2 hi'))

/-- No clause is true for want of a case. -/
def saysB (P : Par) : Bool :=
  ((List.finRange (shapesOf P).length).any fun j => decide (sampledAt P j)) &&
    decide (2 ≤ P.sent.size)

def gpFull : GPar := ⟨1, 0⟩

def laterFull (l : ℕ) (d : Bool) : Par := parLater qFull gpFull l (k1Ix l d + 1) (cond d 2 1)

theorem own_first : planOwnB (firstPar qFull gpFull) = true := by decide +kernel

theorem own_fifty : ((List.range 25).all fun l => planOwnB (laterFull l true) &&
    planOwnB (laterFull l false)) = true := by decide +kernel

theorem own_w : ((linMessageW qFull.lin).any fun msg => planOwnB (parW qFull gpFull 4 msg)) =
    true := by decide +kernel

theorem says_first : saysB (firstPar qFull gpFull) = true := by decide +kernel

theorem says_w : ((linMessageW qFull.lin).any fun msg => saysB (parW qFull gpFull 4 msg)) =
    true := by decide +kernel

/-- At each of the fifty the one message that is sent has an OOD sample. (So "part" has no case
there: the place sends one message.) -/
theorem says_fifty : ((List.range 25).all fun l => [true, false].all fun d =>
    decide ((laterFull l d).sent.size = 1) &&
      (List.finRange (shapesOf (laterFull l d)).length).all fun j =>
        decide (sampledAt (laterFull l d) j)) = true := by decide +kernel

/-! ## The negative tests, at the first segment's opening -/

/-- Every notice's shape turned by f. -/
def bend (f : OracleShape → OracleShape) (P : Par) : Par :=
  { P with parts := P.parts.map fun x => (x.1, x.2.map fun n => { n with shape := f n.shape }) }

theorem teeth_one : oneB (bend (fun s => { s with answers := 2 * s.answers })
    (firstPar qFull gpFull)) = false := by decide +kernel

theorem teeth_pad : padB { firstPar qFull gpFull with codes := {} } = false := by decide +kernel

theorem teeth_row : rowB (bend (fun s => { s with mainRows := 0, maskRows := 0 })
    (firstPar qFull gpFull)) = false := by decide +kernel

/-- Every message gets one mask row under the mask code that bears its main code's number: mask rows
of two lengths then meet in one tree, no layout can be made, and all seats read (0, 0). -/
theorem teeth_part : partB (bend (fun s => { s with maskRows := 1, maskCode := s.code })
    (firstPar qFull gpFull)) = false := by decide +kernel

/-! ## At a computed value -/

theorem planOwn_first {q : Params.First} {gp : GPar} (h : LikeFull q) (hg : gp = gpFull) :
    PlanOwn (firstPar q gp) := by
  rw [firstPar_full h, hg]
  exact planOwn_of own_first

theorem planOwn_later {q : Params.First} {gp : GPar} (h : LikeFull q) (hg : gp = gpFull) (l : ℕ)
    (hl : l < 25) (d : Bool) : PlanOwn (parLater q gp l (k1Ix l d + 1) (cond d 2 1)) := by
  rw [parLater_full h, hg]
  have h1 := List.all_eq_true.1 own_fifty l (List.mem_range.2 hl)
  rw [Bool.and_eq_true] at h1
  cases d with
  | true => exact planOwn_of h1.1
  | false => exact planOwn_of h1.2

theorem planOwn_w {q : Params.First} {gp : GPar} (h : LikeFull q) (hg : gp = gpFull)
    {msg : Array OracleNotice} (hm : linMessageW q.lin = some msg) :
    PlanOwn (parW q gp 4 msg) := by
  rw [parW_full h, hg]
  have h1 := own_w
  rw [← wMsg_full h, hm, Option.any_some] at h1
  exact planOwn_of h1

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.says_fifty
#print axioms VerifiableInference.Desc.K1.teeth_one
#print axioms VerifiableInference.Desc.K1.teeth_pad
#print axioms VerifiableInference.Desc.K1.teeth_row
#print axioms VerifiableInference.Desc.K1.teeth_part
#print axioms VerifiableInference.Desc.K1.planOwn_first
#print axioms VerifiableInference.Desc.K1.planOwn_later
#print axioms VerifiableInference.Desc.K1.planOwn_w
#print axioms VerifiableInference.Desc.K1.planOwn_of
#print axioms VerifiableInference.Desc.K1.own_first
#print axioms VerifiableInference.Desc.K1.own_fifty
#print axioms VerifiableInference.Desc.K1.own_w
#print axioms VerifiableInference.Desc.K1.says_first
#print axioms VerifiableInference.Desc.K1.says_w
