-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/TailClaims/TestsShape.lean: the smallness test's three steps behind a sub-proof's
last claim (testsP, Johnson/Desc/First/TailClaims/SelfRows.lean): ONE TEST AND ONE UPDATE ON TYPED
SHAPES: of the smallness test's own structure (TailSh, Johnson/Desc/First/Shape/Tail.lean) and of
the ledger (LedSh, Johnson/Desc/First/Shape/Parts.lean): neither holds a field element. General
laws; nothing is evaluated.

How. The test on shapes is no second text of the guards: the guards of shapeL
(Johnson/Desc/First/TailClaims/TestsReturns.lean) are run at the structure that TailSh.blank makes
of a shape: the same numbers, names and marks, and zeros of the same sizes. What is owed for that is
a law: the guards say the same at a structure and at the blank one of its shape. (In that law's
proof one guard, readL, is written once more over the tables' shapes: readS, tied by readL_funs; no
statement of the end names it.)

  `size_blankRow`, `readL_funs`, ..: sizes and tables at a blank structure.
  **`shapeL_blank`**: shapeL nU tl g .. L = shapeL nU (tailSh tl).blank (heardAll g).blank .. L: SO
    THE GUARDS READ OF THE SMALLNESS TEST's STRUCTURE AND OF WHAT ITS LOOKUP HEARD THE SHAPE ALONE:
    by Lean. `updCoef_blank`: the like for the update.
  `testsB nU a L`: the test on shapes: what the lookup heard, the number of its join's claim and the
    list of pieces are there, and shapeL accepts at the blank structures and the updated ledger's
    shape. `testsU a L`: the update: the ledger's shape with the weights' sizes laid.
  `testsG nU a L`: the two as one step: .ok (testsU a L) where testsB accepts; else a refusal.
  **`tests_shape`**: testsG nU (tailSh tl) (ledSh F) = .ok t, and the named tests on values accept
    (valsAt) ⊢ there is Fc with testsP nU tl F = .ok Fc and ledSh Fc = t.
  **`tests_carries`**: testsP nU tl F = .ok Fc ⊢ testsG nU (tailSh tl) (ledSh F) = .ok (ledSh Fc):
    an accept of the steps carries the step on shapes.

Limits. That testsB accepts at any shape of the protocol is not shown. The three steps leave the
smallness test's structure as it is: so its shape has no update here. valsAt is asked at the
structures themselves. Whoever evaluates testsB or testsU builds the blank structures' arrays of
zeros only to count them. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.TailClaims.TestsReturns
import Johnson.Desc.First.Shape.Tail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law.Tests
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.Shape (LedSh ledSh TailSh tailSh HeardAll heardAll FunSh funSh
  funSh_blank blankRows)

/-! ## 1 Sizes and tables at a blank structure -/

theorem size_blankRows (a : Array (Array E)) :
    (blankRows (a.toList.map (·.size))).size = a.size := by
  simp [blankRows]

theorem size_blankRow (a : Array (Array E)) (i : Nat) :
    ((blankRows (a.toList.map (·.size))).getD i #[]).size = (a.getD i #[]).size := by
  unfold blankRows
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_map, List.getElem?_map, Array.getElem?_toList]
  cases a[i]? with
  | none => rfl
  | some x => exact Array.size_replicate ..

/-- readL, as a function of the tables' shapes. -/
def readS (tl : HTailF2) (funs : List FunSh) (n : Nat) : Bool :=
  let read := funs.filter fun Fn => decide (Fn.mat < tl.NM) && (Fn.tree == 0 || Fn.tree == 2)
  n == 2 * tl.mz &&
    (read.all fun Fn =>
      let m := (tl.mats.getD Fn.mat {}).m
      m != 0 && Fn.len != 0 && m % Fn.len == 0 && Fn.weights == Fn.len) &&
    read.foldl (fun q Fn => q + (tl.mats.getD Fn.mat {}).m / Fn.len) 0 == tl.nX4Laid &&
    (List.range tl.NM).foldl (fun n mu => n + (tl.mats.getD mu {}).m) 0 == tl.mz

theorem readL_funs (tl : HTailF2) (n : Nat) :
    readL tl n = readS tl (tl.funs.toList.map funSh) n := by
  unfold readL readS
  simp only [← Array.foldl_toList, ← Array.all_toList, Array.toList_filter, List.filter_map,
    List.all_map, List.foldl_map]
  rfl

/-! ## 2 The guards read the shape alone -/

variable {nU : Array Nat} {tl : HTailF2} {F Fc : Fork} {g : Forest.Heard} {jo nbW : Nat}
  {Wn : List Want}

theorem forest_blank : tl.forestHeld g = (tailSh tl).blank.forestHeld (heardAll g).blank := by
  unfold forestHeld
  show _ = (_ && (Array.replicate g.zy.size zeroE).size == _ &&
    (Array.replicate g.zx.size zeroE).size == _ && (Array.replicate g.e.size zeroE).size == 2)
  simp only [Array.size_replicate]
  rfl

theorem call_blank (q : Nat) :
    tl.callHeld g nbW q = (tailSh tl).blank.callHeld (heardAll g).blank nbW q := by
  have e : (((heardAll g).blank.zk).getD q #[]).size = (g.zk.getD q #[]).size :=
    size_blankRow g.zk q
  unfold callHeld
  rw [e]
  rfl

theorem headL_blank (L : LedSh) :
    headL tl g nbW L = headL (tailSh tl).blank (heardAll g).blank nbW L := by
  have e : tl.callHeld g nbW = (tailSh tl).blank.callHeld (heardAll g).blank nbW :=
    funext call_blank
  unfold headL
  rw [forest_blank, e]
  rfl

theorem piecesL_blank (L : LedSh) (W : List Want) :
    piecesL tl L W = piecesL (tailSh tl).blank L W := rfl

theorem tieL_blank (L : LedSh) (mu : Nat) : tieL tl L mu = tieL (tailSh tl).blank L mu := by
  have e1 : (((tailSh tl).blank.rowX).getD mu #[]).size = (tl.rowX.getD mu #[]).size :=
    size_blankRow tl.rowX mu
  have e2 : (((tailSh tl).blank.loX).getD mu #[]).size = (tl.loX.getD mu #[]).size :=
    size_blankRow tl.loX mu
  have e3 : (((tailSh tl).blank.gamX).getD mu #[]).size = (tl.gamX.getD mu #[]).size :=
    size_blankRow tl.gamX mu
  have e4 : (((tailSh tl).blank.gamV).getD mu #[]).size = (tl.gamV.getD mu #[]).size :=
    size_blankRow tl.gamV mu
  unfold tieL
  rw [e1, e2, e3, e4]
  rfl

theorem planesL_blank (L : LedSh) :
    planesL tl L g = planesL (tailSh tl).blank L (heardAll g).blank := by
  have e0 : (heardAll g).blank.zb0.size = g.zb0.size := Array.size_replicate ..
  have e1 : (heardAll g).blank.zb1.size = g.zb1.size := Array.size_replicate ..
  unfold planesL
  rw [e0, e1]
  rfl

theorem sizesL_blank (L : LedSh) :
    sizesL tl g nbW L = sizesL (tailSh tl).blank (heardAll g).blank nbW L := by
  have e1 : (tailSh tl).blank.gamX.size = tl.gamX.size := size_blankRows tl.gamX
  have e2 : (tailSh tl).blank.gamV.size = tl.gamV.size := size_blankRows tl.gamV
  have e3 : tieL tl L = tieL (tailSh tl).blank L := funext (tieL_blank L)
  unfold sizesL
  rw [e1, e2, ← e3, ← planesL_blank]
  rfl

theorem readL_blank (n : Nat) : readL tl n = readL (tailSh tl).blank n := by
  rw [readL_funs, readL_funs]
  have e : (tailSh tl).blank.funs.toList.map funSh = tl.funs.toList.map funSh := by
    show ((tl.funs.toList.map funSh).map FunSh.blank).toArray.toList.map funSh = _
    rw [List.toList_toArray, List.map_map]
    have : (funSh ∘ FunSh.blank) = id := funext funSh_blank
    rw [this, List.map_id]
  rw [e]
  rfl

/-- **THE GUARDS READ THE SHAPE ALONE.** -/
theorem shapeL_blank (L : LedSh) : shapeL nU tl g nbW Wn L =
    shapeL nU (tailSh tl).blank (heardAll g).blank nbW Wn L := by
  have e : (tailSh tl).blank.lsTail.size = tl.lsTail.size := Array.size_replicate ..
  unfold shapeL
  rw [e, ← headL_blank, ← piecesL_blank, ← sizesL_blank, ← readL_blank]
  rfl

theorem coefWrites_blank (zb0 zb1 : Nat) (isTable : Nat → Bool) (rows : Nat → Nat) :
    coefWrites tl zb0 zb1 isTable rows = coefWrites (tailSh tl).blank zb0 zb1 isTable rows := by
  have e1 : (tailSh tl).blank.vt.size = tl.vt.size := Array.size_replicate ..
  have e2 : (tailSh tl).blank.vp.size = tl.vp.size := Array.size_replicate ..
  have e3 : (fun mu => (((tailSh tl).blank.gtTree).getD mu 0, 0,
      (((tailSh tl).blank.rowX).getD mu #[]).size, false, 0) : Nat → Write) =
      fun mu => (tl.gtTree.getD mu 0, 0, (tl.rowX.getD mu #[]).size, false, 0) :=
    funext fun mu => by rw [show (((tailSh tl).blank.rowX).getD mu #[]).size = _ from
      size_blankRow tl.rowX mu]; rfl
  unfold coefWrites
  rw [e1, e2, e3]
  rfl

theorem updCoef_blank (zb0 zb1 : Nat) (L : LedSh) :
    updCoef tl zb0 zb1 L = updCoef (tailSh tl).blank zb0 zb1 L := by
  unfold updCoef
  rw [coefWrites_blank]

/-! ## 3 One test and one update on typed shapes -/

/-- **The update**: the ledger's shape with the weights' sizes laid. Where nothing was heard: as it
was (testsB rejects there). -/
def testsU (a : TailSh) (L : LedSh) : LedSh :=
  match a.heard with
  | some h => updCoef a.blank h.zb0 h.zb1 L
  | none => L

/-- **The test.** -/
def testsB (nU : Array Nat) (a : TailSh) (L : LedSh) : Bool :=
  match a.heard, a.joinObj9, a.blank.wants with
  | some h, some _, some (nbW, Wn) => shapeL nU a.blank h.blank nbW Wn (testsU a L)
  | _, _, _ => false

/-- **The step on shapes.** -/
def testsG (nU : Array Nat) (a : TailSh) (L : LedSh) : Except String LedSh :=
  if testsB nU a L then .ok (testsU a L) else .error "K8.tests: the shape"

/-- The named tests on values, at the structures themselves. -/
def valsAt (nU : Array Nat) (tl : HTailF2) (F : Fork) : Bool :=
  match tl.heard, tl.joinObj9, tl.wants with
  | some g, some jo, some (nbW, Wn) => valsT nU tl F g jo nbW Wn (coefBody tl g F)
  | _, _, _ => false

theorem testsU_at (hg : tl.heard = some g) :
    testsU (tailSh tl) (ledSh F) = ledSh (coefBody tl g F) := by
  have e : (tailSh tl).heard = some (heardAll g) := by
    show tl.heard.map heardAll = _
    rw [hg]
    rfl
  unfold testsU
  rw [e, ledSh_coefBody, updCoef_blank]
  rfl

theorem testsB_at (hg : tl.heard = some g) (hjo : tl.joinObj9 = some jo)
    (hw : tl.wants = some (nbW, Wn)) :
    testsB nU (tailSh tl) (ledSh F) = shapeT nU tl g nbW Wn (coefBody tl g F) := by
  have e : (tailSh tl).heard = some (heardAll g) := by
    show tl.heard.map heardAll = _
    rw [hg]
    rfl
  have ej : (tailSh tl).joinObj9 = some jo := hjo
  have ew : (tailSh tl).blank.wants = some (nbW, Wn) := hw
  unfold testsB
  rw [e, ej, ew]
  show shapeL nU (tailSh tl).blank (heardAll g).blank nbW Wn (testsU (tailSh tl) (ledSh F)) = _
  rw [testsU_at hg, ← shapeL_blank, shapeT_eq]

/-- **THE STEP ON SHAPES RETURNS AND THE VALUES PASS: THE THREE STEPS RETURN, WITH THAT SHAPE.** -/
theorem tests_shape {t : LedSh} (h : testsG nU (tailSh tl) (ledSh F) = .ok t)
    (hV : valsAt nU tl F = true) : ∃ Fc, testsP nU tl F = .ok Fc ∧ ledSh Fc = t := by
  unfold valsAt at hV
  cases hg : tl.heard with
  | none => rw [hg] at hV; cases hV
  | some g =>
    cases hjo : tl.joinObj9 with
    | none => rw [hg, hjo] at hV; cases hV
    | some jo =>
      cases hw : tl.wants with
      | none => rw [hg, hjo, hw] at hV; cases hV
      | some w =>
        obtain ⟨nbW, Wn⟩ := w
        rw [hg, hjo, hw] at hV
        unfold testsG at h
        by_cases hb : testsB nU (tailSh tl) (ledSh F) = true
        · rw [if_pos hb] at h
          rw [testsB_at hg hjo hw] at hb
          exact ⟨_, tests_returns hg hjo hw hb hV, (testsU_at hg).symm.trans (Except.ok.inj h)⟩
        · rw [if_neg hb] at h
          cases h

/-- **AN ACCEPT OF THE THREE STEPS CARRIES THE STEP ON SHAPES.** -/
theorem tests_carries (h : testsP nU tl F = .ok Fc) :
    testsG nU (tailSh tl) (ledSh F) = .ok (ledSh Fc) := by
  obtain ⟨g, jo, nbW, Wn, hg, hjo, hw, rfl, hS, -⟩ := tests_iff.1 h
  unfold testsG
  rw [if_pos (by rw [testsB_at hg hjo hw]; exact hS), testsU_at hg]

end VerifiableInference.Desc.First.TailClaims.Law.Tests

#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.readL_funs
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.shapeL_blank
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.updCoef_blank
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.tests_shape
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.tests_carries
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.size_blankRows
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.size_blankRow
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.readS
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.forest_blank
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.call_blank
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.headL_blank
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.piecesL_blank
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.tieL_blank
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.planesL_blank
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.sizesL_blank
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.readL_blank
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.coefWrites_blank
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.testsU
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.testsB
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.testsG
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.valsAt
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.testsU_at
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.testsB_at
