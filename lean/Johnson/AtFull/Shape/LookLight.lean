-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LookLight.lean: THE LIGHT TABLE OF STEPS ON SHAPES (`cellsH`, TabLight.lean)
WITH TWO MORE KINDS OF LIGHT CELLS AT THE LINKS 0 TO 23: THE LOOKUP ON THE CALLS AND THE LOOKUP ON
THE DIGITS, EACH WITH THE LEDGER's MARKS LAID BY THEIR CLOSED FORM (`lookUpdL`,
Johnson/Desc/ProofFile/Honest/K3/Shape/ClosedGot.lean): `cellsH2 hint L`; AND THE TIE: `cellsH2_eq`:
THEY ARE TabLight.lean's CELLS, AT EVERY HINT, LETTERS AND NUMBER. NO PREMISE. So the run over them
is JoinPieces.lean's runH: `runH2_eq`. Six definitions, seven theorems. General in the letters L;
nothing is evaluated.

Purpose. A piece of the run on shapes is meant to be shown by one line of Lean's kernel that
compares what the run returns with a written border; in JoinPieces.lean and JoinMany.lean such lines
are premises, and none stands in the library. At a piece that holds a lookup such a line makes the
ledger's list of marks whole, through two layers for each step `.sum` of the lookup
(ClosedGot.lean's head). TIMED TRIALS, OUTSIDE THE LIBRARY, NOT SHOWN HERE ("lean
-j1 --tstack=131072"; the stored full-size example; link 1's first eight members, 15 to 22; over
laws.12's sealed library with 201 files not sealed then, JoinPieces.lean among them, laid and built
on it; two jobs; resident peak | address space): lessB over runH 31.3 | 37.5 GiB; lessB over this
file's runH2, at this file's code, 18.0 | 23.5 GiB.

The two kinds of cells (n = 14 l + j + 1, l < 24; at n = 0 and from 337 on the cell is
TabLight.lean's).
* j = 2, the lookup on the calls: `callsGL` for callsG.
* j = 7, the lookup on the digits: `digitsGL` for digitsG.

THE LIGHT STEPS ARE WRITTEN OUT HERE: callsUL and digitsUL are the lookups' house's callsU and
digitsU (Johnson/Desc/ProofFile/Honest/K3/Law/Thread/CarriesCalls.lean, CarriesDigits.lean) but for
ONE name each: lookUpdL for lookUpd at the ledger's seat (and h's type is spelled Forest.Shape for
the house's local notation FShape). If that house turns its text so that the two no longer agree,
callsUL_eq or digitsUL_eq fails and this file does not build. WHAT STAYS OF THE HOUSE's FOLD:
lookUpdL f L holds lookUpd f L for the twelve components other than the marks; digitsUL reads
(lookUpd …).next at slotB; the guard digitsB, which is called and not written out, holds a lookUpd
of its own, read for .next (callsB holds none). So the fold over the lookup's steps still runs in
both cells; the marks alone are laid otherwise. Every other cell, and every cell's test on values,
is TabLight.lean's. Where a cell's letters are lacking, the cell is TabLight.lean's.

Main names.
* `digitsUL`, `digitsGL`, `callsUL`, `callsGL`; `digitsUL_eq`, **`digitsGL_eq`**, `callsUL_eq`,
  **`callsGL_eq`**: each is the house's, at every argument.
* `cellsH2`, **`cellsH2_eq`**.
* `runH2 hint X m k a`: the run of k members from m on over these cells at LWn X; marked
  noncomputable as runH is: it is meant for Lean's kernel alone. **`runH2_eq`**: runH2 hint X m k a
  = runH hint X m k a. `runH2_fun`: the same as an equation of functions: a closed fact on runH2 is
  turned into one on runH by rewriting.

Limits. EQUATIONS OF TERMS. THAT A CELL IS LIGHT IS SAID BY NO THEOREM: the ties say that the two
texts are equal, not what either costs; the trials above are all that speaks for it. NOR IS IT TIED
BY ANY THEOREM WHICH ARM OF lookUpdL RUNS WHERE A GUARD ACCEPTS. By laws that stand (sizedB and
freeB; slots_elems, Honest/K3/Law/SlotsElems.lean; lookOps_len, Honest/K3/Shape/Closed.lean) a
guard's yes gives lookUpdL's test wherever (faceOf h).ok = true, by hand; face_ok_site
(FaceAtSites.lean) has ok at the lookups' sites. That the shape in a cell's letter is such a site is
not shown here, and no theorem joins these. Where the test fails the cell is the heavy one, in
silence. THE HEAD's LINK IS NOT LIGHTENED: neither its lookup on the calls (340) nor its own lookup
on the digits (headDigitsG, 345); nor is anything else from 337 on. Nothing says that a step
returns. No join is restated over runH2: whoever holds a line over runH2 rewrites it. Nothing on
soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.JoinPieces
import Johnson.Desc.ProofFile.Honest.K3.Shape.ClosedGot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.K3 (faceOf)
open ProofFile.Honest.K3.Shape (lookUpd lookUpdL lookUpdL_eq lookHeardSh)
open ProofFile.Honest.K3.Law.AtThr (callsB callsG callsU digitsB digitsG digitsU setPlan)

/-! ## 1 The two light steps -/

/-- digitsU's text (CarriesDigits.lean) with lookUpdL for lookUpd AT THE LEDGER's SEAT; at slotB,
where the count of slots alone is read, lookUpd stays. -/
def digitsUL (h : Forest.Shape) (claims : Nat) (a : ChainSh) : ChainSh :=
  match a.tl, a.led with
  | some T, some Ld =>
    ChainSh.mk a.marked a.here
      (some { T with
        foldDrawn := T.foldDrawn + 1, slotA := Ld.next, slotB := (lookUpd (faceOf h) Ld).next,
        heard := some (lookHeardSh h Ld.next Ld.owed.length) })
      (some (setPlan (lookUpdL (faceOf h) Ld) claims)) a.tables a.rowsOwed a.core a.reply
      a.indexMasks a.pile a.atEnd a.check a.link a.look a.lookHeard a.own a.head a.att a.fin
  | _, _ => a

/-- It is digitsU. No premise. -/
theorem digitsUL_eq (h : Forest.Shape) (claims : Nat) (a : ChainSh) :
    digitsUL h claims a = digitsU h claims a := by
  unfold digitsUL digitsU
  simp only [lookUpdL_eq]
  rfl

/-- digitsG's text with digitsUL for digitsU: the same guard, the same refusal. -/
def digitsGL (h : Forest.Shape) (first used claims : Nat) (a : ChainSh) : Except String ChainSh :=
  if digitsB h first used a then .ok (digitsUL h claims a)
  else .error "K3: the lookup on the digits"

/-- **It is digitsG**, at every shape. No premise. -/
theorem digitsGL_eq (h : Forest.Shape) (first used claims : Nat) (a : ChainSh) :
    digitsGL h first used claims a = digitsG h first used claims a := by
  unfold digitsGL digitsG
  rw [digitsUL_eq]

/-- callsU's text (CarriesCalls.lean) with lookUpdL for lookUpd at the ledger's seat. -/
def callsUL (h : Forest.Shape) (a : ChainSh) : ChainSh :=
  match a.led with
  | some Ld =>
    ChainSh.mk a.marked a.here a.tl (some (lookUpdL (faceOf h) Ld)) a.tables a.rowsOwed a.core
      a.reply a.indexMasks a.pile a.atEnd a.check a.link
      (if a.here == 3 then a.look else some (lookHeardSh h Ld.next Ld.owed.length))
      (some (lookHeardSh h Ld.next Ld.owed.length)) a.own a.head a.att a.fin
  | none => a

/-- It is callsU. No premise. -/
theorem callsUL_eq (h : Forest.Shape) (a : ChainSh) : callsUL h a = callsU h a := by
  unfold callsUL callsU
  simp only [lookUpdL_eq]
  rfl

/-- callsG's text with callsUL for callsU: the same guard, the same refusal. -/
def callsGL (h : Forest.Shape) (first : Nat) (a : ChainSh) : Except String ChainSh :=
  if callsB h first a then .ok (callsUL h a) else .error "K3: the lookup on the calls"

/-- **It is callsG**, at every shape. No premise. -/
theorem callsGL_eq (h : Forest.Shape) (first : Nat) (a : ChainSh) :
    callsGL h first a = callsG h first a := by
  unfold callsGL callsG
  rw [callsUL_eq]

/-! ## 2 The table -/

/-- **TabLight.lean's CELLS WITH THE TWO LIGHT LOOKUPS**: at the links 0 to 23: at the lookup on the
digits digitsGL, at the lookup on the calls callsGL; every other cell, and either cell where one of
its letters is lacking, is TabLight.lean's. -/
def cellsH2 (hint : Nat → List (Nat × Nat)) (L : TabLetters) (n : Nat) : Cell :=
  if n = 0 ∨ 337 ≤ n then cellsH hint L n
  else
    let l := (n - 1) / 14
    let j := (n - 1) % 14
    if j = 7 then
      match L.look l true, lookUC L.XZ l with
      | some s, some (u, c) => (liftQ (digitsGL s.1 s.2 u c), noVals)
      | _, _ => cellsH hint L n
    else if j = 2 then
      match L.look l false with
      | some s => (liftQ (callsGL s.1 s.2), noVals)
      | none => cellsH hint L n
    else cellsH hint L n

/-- **THE TIE: THEY ARE TabLight.lean's CELLS**, at every hint, letters and number. No premise. -/
theorem cellsH2_eq (hint : Nat → List (Nat × Nat)) (L : TabLetters) (n : Nat) :
    cellsH2 hint L n = cellsH hint L n := by
  unfold cellsH2
  by_cases h0 : n = 0 ∨ 337 ≤ n
  · rw [if_pos h0]
  rw [if_neg h0]
  obtain ⟨l, j, hl, hj, rfl⟩ : ∃ l j, l < 24 ∧ j < 14 ∧ n = 14 * l + j + 1 :=
    ⟨(n - 1) / 14, (n - 1) % 14, by omega, by omega, by omega⟩
  have el : (14 * l + j + 1 - 1) / 14 = l := by omega
  have ej : (14 * l + j + 1 - 1) % 14 = j := by omega
  have ec : TabL.cells L (14 * l + j + 1) = (TabL.linkRow L l).at j := table_link _ _ _ _ l j hl hj
  simp only [el, ej]
  by_cases h7 : j = 7
  · subst h7
    have eH : cellsH hint L (14 * l + 7 + 1) = TabL.lookDigits L l := by
      unfold cellsH
      rw [if_neg h0]
      simp only [el, ej]
      rw [if_neg (by omega), if_neg (by omega), ec]
      rfl
    rw [if_pos rfl, eH]
    unfold TabL.lookDigits
    cases h1 : L.look l true with
    | none => rfl
    | some s =>
      cases h2 : lookUC L.XZ l with
      | none => rfl
      | some uc =>
        have e : digitsGL s.1 s.2 uc.1 uc.2 = digitsG s.1 s.2 uc.1 uc.2 :=
          funext fun a => digitsGL_eq _ _ _ _ a
        simp only [e]
  rw [if_neg h7]
  by_cases h2 : j = 2
  · subst h2
    have eH : cellsH hint L (14 * l + 2 + 1) = TabL.lookCalls L l := by
      unfold cellsH
      rw [if_neg h0]
      simp only [el, ej]
      rw [if_neg (by omega), if_neg (by omega), ec]
      rfl
    rw [if_pos rfl, eH]
    unfold TabL.lookCalls
    cases h1 : L.look l false with
    | none => rfl
    | some s =>
      have e : callsGL s.1 s.2 = callsG s.1 s.2 := funext fun a => callsGL_eq _ _ a
      simp only [e]
  · rw [if_neg h2]

/-! ## 3 The run -/

/-- The run of k members from m on, over these cells at LWn X. -/
noncomputable def runH2 (hint : Nat → List (Nat × Nat)) (X : Verify.Public) (m k : Nat) (a : ShA) :
    Except String ShA :=
  (firstZA (fun n => (cellsH2 hint (LWn X) n).1) fun n => (cellsH2 hint (LWn X) n).2).runFrom m k a

/-- **IT IS JoinPieces.lean's runH.** No premise. -/
theorem runH2_eq (hint : Nat → List (Nat × Nat)) (X : Verify.Public) (m k : Nat) (a : ShA) :
    runH2 hint X m k a = runH hint X m k a :=
  runFrom_congr (funext fun n => congrArg Prod.fst (cellsH2_eq hint _ n))
    (funext fun n => congrArg Prod.snd (cellsH2_eq hint _ n)) m k a

/-- The same as an equation of functions. -/
theorem runH2_fun : runH2 = runH := by
  funext hint X m k a
  exact runH2_eq hint X m k a

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.digitsUL
#print axioms Johnson.AtFull.Shape.digitsUL_eq
#print axioms Johnson.AtFull.Shape.digitsGL
#print axioms Johnson.AtFull.Shape.digitsGL_eq
#print axioms Johnson.AtFull.Shape.callsUL
#print axioms Johnson.AtFull.Shape.callsUL_eq
#print axioms Johnson.AtFull.Shape.callsGL
#print axioms Johnson.AtFull.Shape.callsGL_eq
#print axioms Johnson.AtFull.Shape.cellsH2
#print axioms Johnson.AtFull.Shape.cellsH2_eq
#print axioms Johnson.AtFull.Shape.runH2
#print axioms Johnson.AtFull.Shape.runH2_eq
#print axioms Johnson.AtFull.Shape.runH2_fun
