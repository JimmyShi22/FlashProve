-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
One file of the set of files on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/Desc/Key/KeyK3W.lean: the table of joints of the key file: K3's base letters at the key file: what the pattern of K3's files (the letters zero · key · bit) leaves to «the closed caller»: at which tree and place a key or a bit
lies. Definitions with code, over the plan's public values and plain functions that read the witness. They read the witness and nothing that was heard. No Mathlib.
  keyVec m L mat part i   key number i of a part, padding counted: i = column + 2^kCol · place [Wf.pendingRow's head, OnBytes/Iop/Wf.lean:236-238: «The point is (column | place), the column in the low coordinates»]: at a place that a run
                          covers: KeyWords.keyAt; at a place of padding: the lookup's public paddingKey

  blockPlace rb logEll b e   where entry e of a block of planes lies in B's main table, by the library's own index
  bitVec                  bit i read as the library reads it: the sum over the lookup's blocks that hold the plane, at blockPlace; 0 at a slot that no block holds.
  hidden F home mk j      the world of a ledger and a witness: the hidden value under slot j is vp[j] − mf[j] · (the mask entry at home j) [OnBytes/Model/Hide.lean:167-176, as K3Key.lean's head cites it]
  affAt · Zero            a form over hidden values, at that world; «it is worth 0» (a form that names an entry of a virtual row is worth nothing here: Zero is false)
Limits: machine elements (KeyWords.lean's). keyVec's numbering is held against the program's text by reading alone. Nothing on soundness.
-/
import Johnson.Desc.Key.KeyWords
import OnBytes.Model.Hide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes
open OnBytes.Params (WfRun WfPart WfLookup WfPublic)
open OnBytes.Model (Fork Aff)

/-- **Key number i of a part.** -/
def keyVec (m : Wf.Matrix) (L : WfLookup) (mat : Nat → Nat → F) (part i : Nat) : E :=
  let c := i % 2 ^ m.kCol
  let place := i / 2 ^ m.kCol
  match ((L.parts[part]?).map (·.runs)).getD [] |>.find? fun r => decide (r.firstPlace ≤ place) && decide (place < r.firstPlace + r.places) with
  | some r => keyAt L mat r (place - r.firstPlace) c
  | none => ofF L.paddingKey

/-- **Where entry e of a block of planes lies in B's main table, BY THE LIBRARY's OWN INDEX** (by blockPlace_eq, Johnson/RunOne/Law/TiePlanes.lean, this is the library's Planes.blockIdx rb logEll b e). -/
def blockPlace (rb logEll : Nat) (b : Wf.Block) (e : Nat) : Nat :=
  b.row % 2 ^ rb +
    (e % 2 ^ b.bits + b.firstPlace / 2 ^ b.bits % 2 ^ (logEll - b.bits) * 2 ^ b.bits +
      e / 2 ^ b.bits * 2 ^ (b.bits + (logEll - b.bits))) * 2 ^ rb

/-- **Bit i, READ AS THE LIBRARY READS IT**: the sum, over the lookup's blocks that hold the plane, of B's main table's entries at the library's index (bitVecL of Johnson/RunOne/Law/TiePlanes.lean, laid to the letter under bitVec's name and in its place). valB: B's main table. A NARROWER READING (the entry at the FIRST block that holds the plane, at a plain index: row + 2 ^ rowBits · (firstPlace + the entry's number)): the two read alike wherever no two of the lookup's blocks hold the plane and the holding block lies as Wf.layout's docstring says (read_bitVecL_old, Johnson/RunOne/Law/TiePlanes.lean); they can part where two blocks hold one plane, or a block's row is not below 2 ^ rowBits, or its first place is no multiple of its size, or it runs over the row's end. THAT «bit i» IS ONE ENTRY OF B's TABLE, A DIFFERENT ONE FOR EACH i, RESTS ON THESE FACTS ON Wf.layout: unproved. -/
def bitVec (x : WfPublic) (codes : Codes) (l : Nat) (valB : Nat → E) (i : Nat) : E :=
  let mu := (x.lookups.getD l default).mu
  let j := i % 2 ^ mu
  let t := i / 2 ^ mu
  let code := codes.base.getD x.message.shape.code default
  ((Wf.layout x.lookups code.ell).filter (·.lookup == l)).foldl (fun s b =>
    if b.first ≤ j ∧ j < b.first + 2 ^ b.logPlanes then
      addE s (valB (blockPlace (ceilLog2 x.message.shape.mainRows) code.logEll b
        (j - b.first + 2 ^ b.logPlanes * t)))
    else s) zeroE

/-- **The hidden value under slot j.** -/
def hidden (G : Fork) (home : Array Slot) (mk : Slot → E) (j : Nat) : E :=
  subE (G.vp.getD j zeroE) (mulE (G.mf.getD j zeroE) (mk (home.getD j default)))

/-- A form over hidden values, at that world. -/
def affAt (G : Fork) (home : Array Slot) (mk : Slot → E) (a : Aff) : E :=
  a.slots.foldl (fun s t => addE s (mulE t.2 (hidden G home mk t.1))) a.const

/-- **The form is worth 0.** -/
def Zero (same : E → E → Prop) (G : Fork) (home : Array Slot) (mk : Slot → E) (a : Aff) : Prop :=
  a.ents.isEmpty = true ∧ (∀ t ∈ a.slots, t.1 < home.size) ∧ same (affAt G home mk a) zeroE

end VerifiableInference.Desc.Key
