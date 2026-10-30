-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/JointFour.lean: THE FOUR CLAUSES ON THE FIRST TABLE's MEANING THAT ROW 0 OF THE
LAST TABLE SPENDS: the table's owner's JointSays (Johnson/Desc/Sound/PointAtLayers.lean) WITHOUT
ITS CLAUSE pileOne. One structure, four theorems.

Why. JointSays has five equations of fields. Row 0's laws spend four: pin · wrow · the public
tests evalLaid and "K13.wSits". The fifth, pileOne, is an equation of functions at a reader of the
pending rows' mask entries that is NOT cut to the table's size (witOf … maskOf); the composed
meaning's part for the last sub-protocols reads them CUT (rwBook … maskCut,
Johnson/Desc/K13/Law/ReaderByBook.lean), at a matrix and a number of rows of its own. So JointSays
may have no member at the composed meaning, through a clause that row 0 never reads. Here that
clause is left out.

How. The owner's two lemmas hEL_layers | hW_layers are CALLED, not typed anew: at the meaning {
Mg₁ with pileOne := ‹JointSays' sentence› }, which meets JointSays by make. The first chain's last
promise ocEnd … reads no item's sentence: at the two meanings it is one term up to unfolding: Lean
takes the one for the other.

  JointFour        pin · wrow · evalLaid · wSits: JointSays' own four, sign for sign.
  JointSays.four   whoever has the five has the four.
  says_with        the four give the five at { Mg₁ with pileOne := … }.
  hEL_four         the owner's hEL_layers, from the four.
  hW_four          the owner's hW_layers, from the four.
What is not claimed. That the four hold at any composed meaning. Nothing on soundness.

-/
import Johnson.Desc.Sound.PointAtLayers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack (sigOf)
open Cb
open VerifiableInference.Desc (Strs Wit FileDescription Place First.S)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets)
open VerifiableInference.Desc.Sound (MsgT Mem Sending ocEnd pinJT)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalLaid laidOf evalLaidB wSitsItem wSitsB wSeatB witOf matBy
  RowsTrue WRow)

variable {P₁ P₀ Xi Cells Tok : Type}

/-- **What row 0 of the last table spends of the first table's meaning.** -/
structure JointFour (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem) (stOf₁ : P₀ × First.S → Statement)
    (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT) (Pw : Where) (wSeat : Nat × Nat)
    (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT)) : Prop where
  pin : Mg₁.pin = fun j t a y w => pinJT cs G arr smp₁ ms₁ j t a y w
  wrow : Mg₁.wrow = fun a _ w => WRow Pw a.2 (wordsOn (stOf₁ a) (tabP₁ a w))
  evalLaid : ∀ a, Mg₁.pub .evalLaid a = evalLaidB Pw a.2
  wSits : ∀ a, Mg₁.pub wSitsItem a = (wSitsB cs Pw a.2 && wSeatB wSeat a.2)

section
variable (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
  (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms₁ : List Mem) (stOf₁ : P₀ × First.S → Statement)
  (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT) (Pw : Where) (wSeat : Nat × Nat)
  (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))

/-- Whoever has the five has the four. -/
theorem JointSays.four {cs : OnBytes.Codes} {G : FileDescription Xi} {arr : Nat → Nat → Nat}
    {smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp}
    {ms₁ : List Mem} {stOf₁ : P₀ × First.S → Statement}
    {tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT} {Pw : Where} {wSeat : Nat × Nat}
    {matC : Cells → Nat → Nat → GE} {Mg₁ : Meaning P₀ (Wit Cells Tok MsgT)}
    (J : JointSays cs G arr smp₁ ms₁ stOf₁ tabP₁ Pw wSeat matC Mg₁) :
    JointFour cs G arr smp₁ ms₁ stOf₁ tabP₁ Pw wSeat Mg₁ :=
  ⟨J.pin, J.wrow, J.evalLaid, J.wSits⟩

/-- The meaning with JointSays' own sentence laid at pileOne. -/
abbrev withPile (matC : Cells → Nat → Nat → GE) : Meaning P₀ (Wit Cells Tok MsgT) :=
  { Mg₁ with
    pileOne := fun a _ w =>
      RowsTrue (nR := Pw.lin.matrixRows) (k := Pw.lin.kCol)
        (fun w' : Wit Cells Tok MsgT =>
          witOf (matBy Pw.lin.kCol (matC w'.cells)) (wordsOn (stOf₁ a) (tabP₁ a w')))
        a.2 w }

variable {cs G arr smp₁ ms₁ stOf₁ tabP₁ Pw wSeat Mg₁}

/-- The four give the five there. -/
theorem says_with (J : JointFour cs G arr smp₁ ms₁ stOf₁ tabP₁ Pw wSeat Mg₁)
    (matC : Cells → Nat → Nat → GE) :
    JointSays cs G arr smp₁ ms₁ stOf₁ tabP₁ Pw wSeat matC (withPile stOf₁ tabP₁ Pw Mg₁ matC) :=
  ⟨J.pin, rfl, J.wrow, J.evalLaid, J.wSits⟩

variable (J : JointFour cs G arr smp₁ ms₁ stOf₁ tabP₁ Pw wSeat Mg₁)
  (get : P₁ → P₀ × First.S) (N₁ : Numbers) (links : List ModelPart)
  (ps : List VerifiableInference.Desc.Place)
include J

/-- The owner's hEL_layers, from the four. -/
theorem hEL_four (h2 : Pub.evalLaid ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD []) :
    ∀ p y, ocEnd get N₁ Mg₁ links ps p y → (get p).2.failed = none → EvalLaid Pw (get p).2 :=
  hEL_layers cs G arr smp₁ ms₁ stOf₁ tabP₁ Pw wSeat (fun _ _ _ => 0) _
    (says_with J fun _ _ _ => 0) get N₁ links ps h2

/-- The owner's hW_layers, from the four. -/
theorem hW_four (xW : Mem) (lay₀ : VectorLay) (stOf : P₁ → Statement)
    (tabP : P₁ → Wit Cells Tok MsgT → Nat → MsgT)
    (h3 : wSitsItem ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (hst : ∀ p, stOf p = (get p).2.st) (hlay : lay₀ = linLayW cs Pw.lin)
    (hbook : ∀ p (w : Wit Cells Tok MsgT) n j t sh, (get p).2.book.place[n]? = some (j, t) →
      ((get p).2.st.oracles[n]?).map (·.shape) = some sh → tabP p w n = w.tab cs sh (arr j t) j t)
    (hsh : Pw.lin.w = (xW.1.l.get xW.2).1) (hseat : xW.1.seat xW.2 = wSeat) :
    ∀ p y D, ocEnd get N₁ Mg₁ links ps p y →
      (get p).2.failed = none → laidOf Pw (get p).2 = some D →
      WSits cs arr xW lay₀ stOf tabP p D :=
  hW_layers cs G arr smp₁ ms₁ stOf₁ tabP₁ Pw wSeat (fun _ _ _ => 0) _
    (says_with J fun _ _ _ => 0) get N₁ links ps xW lay₀ stOf tabP h3 hst hlay hbook hsh hseat

end

end Desc.K14.Law
