-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/SendsAll.lean: at every sending of the seven plans, at both examples: how the verifier's
own layout places the oracle messages in trees, against the typed codes of Johnson/Pack/; and
which of the conditions that a walk over a sending asks hold where. Statements that are proved by
evaluation in Lean's kernel.

A walk of the verifier's routine over a sending asks conditions on the sending that name no
written round: what is announced, in which order, with which shapes, and how it is laid in trees.
Here these conditions are written as tests that can be evaluated, over the written lists of
Johnson/G/SendsLit.lean (what the verifier is told) and Johnson/G/PackLit.lean (the sampled
messages with their radii), and evaluated at all sendings. Definitions, statements and proofs.

Main names:
  `codesAtFull`, `codesAtSmall`: the codes of a file's chains, by the file's number. `full_codes`,
    `small_codes`: a row's codes, which come from the one list, are those of the file that the
    other list names.
  `Row`: a sending of both lists: the codes, the notices, the sampled messages with their radii.
  `rowsOf`, `rowsFull`, `rowsSmall`: the two lists set side by side.
  `sameB`: the sampled messages of the one list are those of the other, in order.
  `laidB`: the verifier's layout (`OnBytes.layTrees`) exists; every sampled message's tree has 2 ^
    a leaves for the a of the message's typed code (`aOf`), and as many as its main code has
    positions where it has main rows.
  `firstB`: the sampled messages come first among the notices. `caseEB`: every sampled shape has a
    mask row or main rows over the extension field (`CaseE`). `padB`: every sampled shape has a
    pad by the verifier's function.
  `full_same`, `full_laid`, `full_pad`, `small_same`, `small_laid`, `small_pad`: `sameB`, `laidB`
    and `padB` are true at ALL sendings: 119 and 46.
  `full_notFirst`, `small_notFirst`: `firstB` is false at one sending of each example, number 24
    and number 17 from 0: the first sending of the proof file's first chain.
  `full_notE`, `small_notE`: no sending of the key file or of the entry file has a sampled shape
    outside `CaseE`; 50 and 10 of the proof file's have one.

Limits: those of the lists: "every sending" is every entry "SEND seed" of a plan: where a fold
sends its fresh mask itself, the root goes in the fold's own entry, and that message is in neither
list; where the mask is sent ahead, in a sending, it is a notice of that sending, without a
sample. The statements speak of the written lists; that these are the planner's is held by tests
by evaluation in other files. Nothing on a run of the verifier, on a written round, on soundness,
on the honest prover or on hiding.
-/
import Johnson.G.SendsLit
import Johnson.G.PackLit
import OnBytes.Iop.Send

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G.SendsAll
open OnBytes Johnson.Pack Johnson.G

/-- The codes of a file's chains, by the file's number, at the two examples. -/
def codesAtFull : Nat → Codes
  | 0 => codesFull0
  | 1 => codesFull1
  | _ => codesFull2

def codesAtSmall : Nat → Codes
  | 0 => codesSmall0
  | 1 => codesSmall1
  | _ => codesSmall2

/-- A sending of both lists. -/
structure Row where
  file : Nat
  cs : Codes
  notices : List OracleNotice
  l : List (OracleShape × Nat)

/-- The two lists side by side. -/
def rowsOf (S : List SendLit) (P : List (Codes × List (OracleShape × Nat))) : List Row :=
  (S.zip P).map fun x => ⟨x.1.1, x.2.1, x.1.2.2.2, x.2.2⟩

def rowsFull : List Row := rowsOf sendsFullLit packFullLit
def rowsSmall : List Row := rowsOf sendsSmallLit packSmallLit

instance (s : OracleShape) : Decidable (CaseE s) := by unfold CaseE; infer_instance

namespace Row
variable (r : Row)

/-- the places of the sampled messages among the notices -/
def places : List Nat :=
  (r.notices.zipIdx.filter fun n => decide (0 < n.1.shape.answers)).map (·.2)

/-- The sampled messages of the one list are those of the other, in order. -/
def sameB : Bool :=
  (r.notices.filter fun n => decide (0 < n.shape.answers)).map (·.shape) == r.l.map (·.1)

/-- The tree of the message at a place. -/
def treeAt (L : TreeLay) (i : Nat) : TreeShape := L.shapes.getD (L.tree.getD i 0) default

/-- The layout exists, and every position of a sampled message's typed word is a leaf. -/
def laidB : Bool :=
  match layTrees r.cs r.notices.toArray with
  | none => false
  | some L => r.places.all fun i =>
      let s := (r.notices.getD i default).shape
      (treeAt L i).logN == aOf r.cs s &&
        (s.mainRows == 0 || (treeAt L i).logN == (cMain r.cs s).a)

/-- The sampled messages come first. -/
def firstB : Bool := r.places == List.range r.l.length

/-- Every sampled shape has a mask row or main rows over the extension field. -/
def caseEB : Bool := r.l.all fun x => decide (CaseE x.1)

/-- Every sampled shape has a pad. -/
def padB : Bool := r.l.all fun x => (Send.pad r.cs x.1).isSome

end Row

theorem lengths : (sendsFullLit.length, packFullLit.length, sendsSmallLit.length,
    packSmallLit.length) = (119, 119, 46, 46) := by decide +kernel

/-- A row's codes, which come from the one list, are those of the file that the other list names. -/
theorem full_codes : (rowsFull.all fun r => r.cs == codesAtFull r.file) = true := by decide +kernel
theorem small_codes : (rowsSmall.all fun r => r.cs == codesAtSmall r.file) = true := by
  decide +kernel

theorem full_same : (rowsFull.all Row.sameB) = true := by decide +kernel
theorem full_laid : (rowsFull.all Row.laidB) = true := by decide +kernel
theorem full_pad : (rowsFull.all Row.padB) = true := by decide +kernel
theorem small_same : (rowsSmall.all Row.sameB) = true := by decide +kernel
theorem small_laid : (rowsSmall.all Row.laidB) = true := by decide +kernel
theorem small_pad : (rowsSmall.all Row.padB) = true := by decide +kernel

/-- the numbers of the sendings at which a test is false -/
def failsAt (R : List Row) (t : Row → Bool) : List Nat :=
  (R.zipIdx.filter fun x => !t x.1).map (·.2)

/-- how many sendings of each file fail a test: key, entry, proof -/
def failsBy (R : List Row) (t : Row → Bool) : Nat × Nat × Nat :=
  let n := fun f => (R.filter fun x => x.file == f && !t x).length
  (n 0, n 1, n 2)

/-- At one sending of each example a message without a sample stands before a sampled one: the
first sending of the proof file's first chain (the closing fold's fresh mask before the batch's
message of masks for the index). -/
theorem full_notFirst : failsAt rowsFull Row.firstB = [24] := by decide +kernel
theorem small_notFirst : failsAt rowsSmall Row.firstB = [17] := by decide +kernel

/-- No sending of the key file or of the entry file has a sampled shape outside `CaseE`; 50 and 10
of the proof file's have one (main rows over the base field and no mask row). -/
theorem full_notE : failsBy rowsFull Row.caseEB = (0, 0, 50) := by decide +kernel
theorem small_notE : failsBy rowsSmall Row.caseEB = (0, 0, 10) := by decide +kernel

end Johnson.G.SendsAll

#print axioms Johnson.G.SendsAll.full_codes
#print axioms Johnson.G.SendsAll.full_same
#print axioms Johnson.G.SendsAll.full_laid
#print axioms Johnson.G.SendsAll.small_laid
#print axioms Johnson.G.SendsAll.full_notFirst
#print axioms Johnson.G.SendsAll.full_notE
