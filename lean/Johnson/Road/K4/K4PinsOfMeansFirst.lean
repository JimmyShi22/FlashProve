-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsOfMeansFirst.lean: THE BRIDGE TO WHAT THE FIRST GROUP ALONE ASKS: `K4Means Mg
Dk` (Johnson/Road/K4/K4Means.lean: all that K4's files read of the table of joints' meaning, over
the owners' data Dk) GIVES THE LINE order OF `K4IdnFitF` (Johnson/Road/K4/K4PinsEndFirst.lean), AND
SO, UNDER TWO TIES ON Dk's LETTERS, `K4IdnFitF`. It stands beside
Johnson/Road/K4/K4PinsOfMeans.lean, whose `meanEqs_of_means` names no group and serves the first
group as it stands. Two theorems, by unfolding. No draw, no count.

  `order_of_means`: "in order" at Mg gives: the words in the verifier's state are Dk.reqW's, and
    `backReq` reads something off Dk.reqB's bytes: the third and the fifth of the five conjuncts of
    `K4Means`' field inOrder.
  `idnFit_of_means`: `K4IdnFitF` at oW, wOf := Dk.L3's · put, H, reqB, reqW := Dk's, from `K4Means`,
    `ReqTies` at Dk's four letters, and the line enc.

OBJECT: none of its own. USER: none here; meant: the assembly of K4's law at all places. LETTERS:
Dk, Mg, enc, Zt: free.

Limits. K04_law IS NOT PROVED BY THIS. OF `K4IdnFitF`'s THREE LINES ONE IS PAID HERE (order); ties
AND enc ARE HANDED THROUGH AS PREMISES (K4PinsEndFirst.lean's Limits say of what kind they are).
That "in order" rides past K4's own sub-protocol is `K4Keeps`' line, not treated here. IT WILL TURN
WHEN `K4Means` TURNS. The cells are a matrix on the reference rows and columns.
-/
import Johnson.Road.K4.K4PinsEndFirst
import Johnson.Road.K4.K4Means

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open OnBytes.Model.Verify (Public)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.Sound (MsgT)
open Inst.Model.Layout (kRef hRef)

variable {Xi P Tok : Type} {rows cols nR kC : ℕ} {X : Public}

/-- **"In order" gives the two facts on the request**, at every meaning with `K4Means`. -/
theorem order_of_means {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)}
    {Dk : K4Data Xi P Tok rows cols nR kC X} (E : K4Means Mg Dk) (Zt : P) (t : S)
    (h : Mg.inOrder (Zt, t) = true) :
    t.req = Dk.reqW Zt ∧ (_root_.Meaning.backReq (Dk.reqB Zt)).isSome = true := by
  rw [E.inOrder] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1.1.2, h.2⟩

/-- **`K4Means` gives `K4IdnFitF`**, under `ReqTies` at the data's four letters and the line enc. -/
theorem idnFit_of_means {Mg : Meaning P (Wit (CellsK hRef (2 ^ kRef)) Tok MsgT)}
    {Dk : K4Data Xi P Tok hRef (2 ^ kRef) nR kC X} (E : K4Means Mg Dk)
    {enc : CellsK hRef (2 ^ kRef) → Dk.L3.oW.Msg}
    (Tz : ReqTies Dk.reqB Dk.reqW Dk.H.req Dk.put)
    (he : ∀ (w : Wit (CellsK hRef (2 ^ kRef)) Tok MsgT) (r : Fin hRef) (c : Fin (2 ^ kRef)),
      Dk.L3.wOf (enc w.cells) r.val c.val = w.cells r c) (Zt : P) :
    K4IdnFitF (X := X) Dk.L3.oW enc Dk.L3.wOf Mg Zt Dk.put Dk.H Dk.reqB Dk.reqW where
  ties := Tz
  order := order_of_means E Zt
  enc := he

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.order_of_means
#print axioms OnBytes.Road.K4.idnFit_of_means
