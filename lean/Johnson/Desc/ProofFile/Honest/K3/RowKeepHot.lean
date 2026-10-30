-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/RowKeepHot.lean: the two letters of the row that passes its tables
on, filled so that the inner loops are those of Honest/K3/Hot.lean; that this filling is `fastKeeps`
(Honest/K3/RowKeepFill.lean); and the lots at it, which are the lots at `fastKeeps`. Definitions
with code, and theorems without a hypothesis.

Terms. Honest/K3/GLOSSARY.md.

Why. Honest/K3/Hot.lean imports little, so that its compiled code can be loaded beside Lean's
evaluator. Under the option interpreter.prefer_native the evaluator takes compiled code for a name
that a loaded library holds, and evaluates every other name without a word; the jobs of `fastKeeps`
call `Fast.keptRound` and `Fast.keptBind`, and its store's maker calls `Fast.lvlsUp`; their files
import Mathlib. In their loops the jobs of this file call the names of Honest/K3/Hot.lean; they
still call `Fast.keptStart`, `keyBelow`, `tabBelow` and `bitOff`, and take `base`, `inY` and `ends`
over as they are (`leavesKeepHot` its `start` too). As terms they are the same jobs.

What is defined.
  `hotStoreOf`, `hotStoreAt`: `Fast.storeOf` and `storeAt` (Honest/K3/StoreMake.lean) with the
    tables, the leaves and the levels made by `Hot.bitTab`, `Hot.facTab`, `Hot.keyLeaves`,
    `Hot.leafTab` and `Hot.lvlsUp`. The input is applied once.
  `keyKeepHot`, `tabKeepHot`, `leavesKeepHot`, `bitsKeepHot`: the jobs with a kept state at the four
    sorts of stage that have variables, with `Hot.bind` and `Hot.round`; a level's two tables by
    `Hot.halves`; the bits' second table by `Hot.lessOne`.
  `hotKeeps R row a`: these four, the three jobs without a variable as `fastKeeps` has them, and
    `hotStoreAt`.
  `hotFillKeep`, `theLotKeepHot`, `theLotInstKeepHot`: the lot's letters and the lots, as
    `fastFillKeep`, `theLotKeepBound` and `theLotInstKeepBound` (Honest/K3/LotInstKeepBound.lean).

What is shown.
  `hotStoreOf_eq`, `hotStoreAt_eq`: the stores are the same.
  `keyKeepHot_eq`, `tabKeepHot_eq`, `leavesKeepHot_eq`, `bitsKeepHot_eq`: the jobs are the same.
  `hotKeeps_eq`: **`hotKeeps R row a = fastKeeps R row a`.** So a theorem on `fastKeeps` is one on
    `hotKeeps`, by rewriting.
  `hotFillKeep_eq`: the lot's letters are `fastFillKeep`'s, at every table's rows and every reader
    of the input.
  `theLotKeepHot_eq`, `theLotInstKeepHot_eq`: the lots are `theLotKeepBound` and
    `theLotInstKeepBound`.

In whose place. `theLotInstKeepHot` in the place of `theLotInstKeepBound`, never beside it; and so
of every lot that bears the one lot's name: only one of them may stand in a list of lots' honest
sides at a time (Honest/K3/LotInstKeepBound.lean). A caution: nothing here shows or tests it.

Imported. Honest/K3/HotLaw.lean, Honest/K3/RowKeepFill.lean, Honest/K3/LotInstKeepBound.lean. The
frame's files lie beneath them.

Users. Honest/K3/Tab/HotTabAll2.lean; Honest/K3/Law/CoverageLotsNamed.lean. Meant for a filling of
the honest prover that is played with compiled code loaded.

Limits. Where no store is passed on, a job's start still makes its tables by
Honest/K3/JobsFast.lean. The readers of a key, a bit and a row are the caller's functions: a loop of
Honest/K3/Hot.lean calls them once for each entry. `hotKeeps` and `hotFillKeep` keep the table's
rows a letter; the two lots lay `codeRows` (Honest/K3/LotInstKeepCode.lean). `keyKeepHot`,
`tabKeepHot` and `bitsKeepHot` take `inY` from `keyKeep`, `tabKeep` and `bitsKeep`, and the three
jobs without a variable are `fastKeeps`' own: `inY` does not reject: a mask entry beyond the list's
end counts as 0. At the list that the masked sumcheck's part hands over, entries laid behind it
change nothing in what `inY` returns: `no_pad_at_keep` (Honest/K3/Law/Keep/MasksAtKeep.lean
[not in this library]), at `fastKeeps`; `hotKeeps_eq` carries it here. `inY` reads the kept state's
values by a default too (`K.vals.getD`, `(Fast.keptEnds K).getD`): nothing here bounds these. A lot
lays a half only at an address at which a site can be made (`lotBy`, Honest/K3/Lot.lean); that the
two lots' halves are those of `rowLotKeep` at their letters: `theLotKeepHot_halves`,
`theLotInstKeepHot_halves` (Honest/K3/Law/CoverageLotsNamed.lean). How long anything takes is not
said here.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.HotLaw
import Johnson.Desc.ProofFile.Honest.K3.RowKeepFill
import Johnson.Desc.ProofFile.Honest.K3.LotInstKeepBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE oneE)

/-! ## 1 The store -/

/-- `Fast.storeOf`, its loops by Honest/K3/Hot.lean. -/
def hotStoreOf (f : LFace) (row : E → Nat → E) (w : Hidden) (theta alpha : E) : Store :=
  let b := Hot.bitTab f.mu f.d f.planes w.bit
  let a := Hot.facTab f.mu f.d alpha (row theta)
  { keyLvls := (Array.range f.parts.length).map fun i =>
      Hot.lvlsUp (f.parts.getD i 0) (Hot.keyLeaves alpha (f.parts.getD i 0) (w.key theta i))
    tabLvls := Hot.lvlsUp f.d (Hot.leafTab b a)
    bitTab := b
    facTab := a }

/-- It is `Fast.storeOf`. -/
theorem hotStoreOf_eq (f : LFace) (row : E → Nat → E) (w : Hidden) (theta alpha : E) :
    hotStoreOf f row w theta alpha = Fast.storeOf f row w theta alpha := by
  show (⟨(Array.range f.parts.length).map fun i =>
      Hot.lvlsUp (f.parts.getD i 0) (Hot.keyLeaves alpha (f.parts.getD i 0) (w.key theta i)),
    Hot.lvlsUp f.d (Hot.leafTab (Hot.bitTab f.mu f.d f.planes w.bit)
      (Hot.facTab f.mu f.d alpha (row theta))),
    Hot.bitTab f.mu f.d f.planes w.bit, Hot.facTab f.mu f.d alpha (row theta)⟩ : Store) = _
  rw [Hot.lvlsUp_eq]
  simp only [Hot.keyLeaves_eq f row w theta alpha]
  rfl

/-- `storeAt`, its loops by Honest/K3/Hot.lean. The points are read once, and the input is applied
once. -/
def hotStoreAt (R : Reads) (row : E → Nat → E) (a : At) : Ask → List Fmt.Drawn → Store :=
  fun w h =>
  let p := R.pts a.face a.base h
  hotStoreOf a.face row (w p.heard) p.theta p.alpha

/-- It is `storeAt`. -/
theorem hotStoreAt_eq (R : Reads) (row : E → Nat → E) (a : At) :
    hotStoreAt R row a = storeAt R row a :=
  funext fun w => funext fun h =>
    hotStoreOf_eq a.face row (w (R.pts a.face a.base h).heard) (R.pts a.face a.base h).theta
      (R.pts a.face a.base h).alpha

/-! ## 2 The jobs -/

/-- `keyKeep`, its loops by Honest/K3/Hot.lean. -/
def keyKeepHot (R : Reads) (row : E → Nat → E) (a : At) (i k : Nat) :
    KeepJob Ask (Option Store) Kept :=
  { keyKeep R row a i k with
    start := fun w h x =>
      let p := R.pts a.face a.base h
      Fast.keptStart k (Hot.halves k (keyBelow a.face row i (k + 1) w p x)) (p.keyPt i k)
    bind := Hot.bind (a.face.orders i k)
    round := Hot.round zeroE k (a.face.orders i k) }

theorem keyKeepHot_eq (R : Reads) (row : E → Nat → E) (a : At) (i k : Nat) :
    keyKeepHot R row a i k = keyKeep R row a i k := rfl

/-- `tabKeep`, its loops by Honest/K3/Hot.lean. -/
def tabKeepHot (R : Reads) (row : E → Nat → E) (a : At) (l : Nat) :
    KeepJob Ask (Option Store) Kept :=
  { tabKeep R row a l with
    start := fun w h x =>
      let p := R.pts a.face a.base h
      Fast.keptStart (a.face.mu + l)
        (Hot.halves (a.face.mu + l) (tabBelow a.face row (l + 1) w p x)) (p.tabPt l)
    bind := Hot.bind (OnBytes.Model.orderDefault (a.face.mu + l))
    round := Hot.round zeroE (a.face.mu + l) (OnBytes.Model.orderDefault (a.face.mu + l)) }

theorem tabKeepHot_eq (R : Reads) (row : E → Nat → E) (a : At) (l : Nat) :
    tabKeepHot R row a l = tabKeep R row a l := rfl

/-- `leavesKeep`, its loops by Honest/K3/Hot.lean. -/
def leavesKeepHot (R : Reads) (row : E → Nat → E) (a : At) : KeepJob Ask (Option Store) Kept :=
  { leavesKeep R row a with
    bind := Hot.bind (OnBytes.Model.orderDefault (a.face.mu + a.face.d))
    round := fun K =>
      (Hot.round oneE (a.face.mu + a.face.d)
        (OnBytes.Model.orderDefault (a.face.mu + a.face.d)) K).take
        (if K.bound < a.face.d then 3 else 2) }

theorem leavesKeepHot_eq (R : Reads) (row : E → Nat → E) (a : At) :
    leavesKeepHot R row a = leavesKeep R row a := rfl

/-- `bitsKeep`, its loops by Honest/K3/Hot.lean. -/
def bitsKeepHot (R : Reads) (row : E → Nat → E) (a : At) : KeepJob Ask (Option Store) Kept :=
  { bitsKeep R row a with
    start := fun w h x =>
      let p := R.pts a.face a.base h
      let b := bitOff a.face row w p x
      Fast.keptStart (a.face.mu + a.face.d) [b, Hot.lessOne b] p.zeroPt
    bind := Hot.bind (OnBytes.Model.orderDefault (a.face.mu + a.face.d))
    round := Hot.round zeroE (a.face.mu + a.face.d)
      (OnBytes.Model.orderDefault (a.face.mu + a.face.d)) }

theorem bitsKeepHot_eq (R : Reads) (row : E → Nat → E) (a : At) :
    bitsKeepHot R row a = bitsKeep R row a := rfl

/-! ## 3 The row's letters -/

/-- **The row's two letters, filled, the inner loops by Honest/K3/Hot.lean.** -/
def hotKeeps (R : Reads) (row : E → Nat → E) (a : At) : Keeps :=
  { job := fun
      | .key i k => some (keyKeepHot R row a i k)
      | .tab l => some (tabKeepHot R row a l)
      | .leaves => some (leavesKeepHot R row a)
      | .bits => some (bitsKeepHot R row a)
      | s => (fastKeeps R row a).job s
    store := hotStoreAt R row a }

/-- **It is `fastKeeps`.** -/
theorem hotKeeps_eq (R : Reads) (row : E → Nat → E) (a : At) :
    hotKeeps R row a = fastKeeps R row a := by
  have hj : (hotKeeps R row a).job = (fastKeeps R row a).job :=
    funext fun s => by cases s <;> rfl
  have hs : (hotKeeps R row a).store = (fastKeeps R row a).store := hotStoreAt_eq R row a
  calc hotKeeps R row a = ⟨(hotKeeps R row a).job, (hotKeeps R row a).store⟩ := rfl
    _ = ⟨(fastKeeps R row a).job, (fastKeeps R row a).store⟩ := by rw [hj, hs]
    _ = fastKeeps R row a := rfl

/-! ## 4 The lots -/

variable {X : Type} {W₀ Rc Xi Tr : Type}

/-- The lot's letters at `hotKeeps`. -/
def hotFillKeep {W : Type} (row : Site → E → Nat → E) (wit : Site → W → Ask) : FillKeep W :=
  { keeps := fun s => hotKeeps theReads (row s) s.at_
    wit := wit }

/-- They are `fastFillKeep`'s. -/
theorem hotFillKeep_eq {W : Type} (row : Site → E → Nat → E) (wit : Site → W → Ask) :
    hotFillKeep row wit = fastFillKeep row wit := by
  unfold hotFillKeep fastFillKeep
  simp only [hotKeeps_eq]

/-- **The lot's honest side, the inner loops by Honest/K3/Hot.lean**: the table's rows in closed
form, the reader of the input `boundWit`; at a letter for the reader of the instance. In the place
of `theLotKeepBound`, never beside it. -/
def theLotKeepHot (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn)
    (set : X → RowOwn → X) : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  rowLotKeepAt (fun Z => hotFillKeep (codeRows Z) (boundWit cells weights req Z)) get set

/-- It is `theLotKeepBound`. -/
theorem theLotKeepHot_eq (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (get : X → RowOwn)
    (set : X → RowOwn → X) :
    theLotKeepHot (Rc := Rc) cells weights req get set =
      theLotKeepBound cells weights req get set := by
  unfold theLotKeepHot theLotKeepBound
  simp only [hotFillKeep_eq]

/-- **The same at the proof file's own instance.** In the place of `theLotInstKeepBound`, never
beside it. -/
def theLotInstKeepHot (cells : Tr → Cells) (weights : W₀ → Weights) (get : X → RowOwn)
    (set : X → RowOwn → X) : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  rowLotKeepAt (fun Z => hotFillKeep (codeRows Z) (boundWit cells weights (reqAt Z) Z)) get set

/-- It is `theLotInstKeepBound`. -/
theorem theLotInstKeepHot_eq (cells : Tr → Cells) (weights : W₀ → Weights) (get : X → RowOwn)
    (set : X → RowOwn → X) :
    theLotInstKeepHot (Rc := Rc) cells weights get set =
      theLotInstKeepBound cells weights get set := by
  unfold theLotInstKeepHot theLotInstKeepBound
  simp only [hotFillKeep_eq]

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.hotStoreOf_eq
#print axioms ProofFile.Honest.K3.hotStoreAt_eq
#print axioms ProofFile.Honest.K3.keyKeepHot_eq
#print axioms ProofFile.Honest.K3.tabKeepHot_eq
#print axioms ProofFile.Honest.K3.leavesKeepHot_eq
#print axioms ProofFile.Honest.K3.bitsKeepHot_eq
#print axioms ProofFile.Honest.K3.hotKeeps_eq
#print axioms ProofFile.Honest.K3.hotFillKeep_eq
#print axioms ProofFile.Honest.K3.theLotKeepHot_eq
#print axioms ProofFile.Honest.K3.theLotInstKeepHot_eq
