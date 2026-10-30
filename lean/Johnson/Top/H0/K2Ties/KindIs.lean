-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/KindIs.lean: THE FORM IN WHICH THE CODE SWITCH's LAW IS COUNTED (`K02Counted`,
    Counted.lean) IS THE TABLE's OWN FIELD FOR A KIND AT THE COMPOSED MEANING's CONSTANT
    (`P5J.AtMg.Kind`, Johnson/P5J/RowsAtMg.lean), AT THE KIND K2: HELD BY LEAN. Two theorems. A law
    file: no sub-protocol imports it.

What is said.
  `k02Counted_is_kind`: under the constant's head h, at any structure of parameters D₀ and any of
      that file's free parameters L₀: `h.Kind D₀ L₀ KindName.K2` is `K02Counted` at D := the head's
      structure over D₀, the closed base `mgBase`, Rch := "reached" along the seated description
      (`RchAt`, Johnson/Top/H0/Walk/ReachAt.lean), the constant's list of segments and of places, c₀
      := L₀'s, tokOf := the constant's, and the list of pieces `h.row L₀`: BY `Iff.rfl`: the two are
      one sentence up to unfolding.
  `k02_kind`: so `K2PlaceOwes` at every place of the kind, at these terms, gives the field.

Limits. A check of form and one call. A MEMBER OF THE CONSTANT's HEAD IS PROVED AT `storedPublicFiles` AND
    `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/); NO MEMBER OF `K2PlaceOwes` IS SHOWN. The
    join's files take the field at "reached" with one conjunct more on the public part:
    `KindTiedR.mono` (Johnson/Desc/Sound/TiedRMono.lean) carries a law from here to there; not
    called here. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P5J.RowsAtMg
import Johnson.Top.H0.K2Ties.Counted

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes.Maker (WholeD)
open OnBytes.Flat (numsFull)
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.Sound
open Johnson.Desc.First.Walk.Tied (RchAt)
open P5J (AtMg TS colsAt F0T Free fullLinks)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np
                        : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **The counted form is that field, at K2.** -/
theorem k02Counted_is_kind (h : AtMg o Z D r Zp Np cF) {nR : ℕ} (D₀ : MgData ProofFile.Inst ProofFile.InstPub
    P5J.At.Tok numsFull.rows (colsAt numsFull) nR (P5J.At.X Zp)) (L₀ : Free numsFull D (F0T o Zp Np
    cF) P5J.At.Tok) :
    h.Kind D₀ L₀ KindName.K2 ↔ K02Counted (h.𝔇 D₀) mgBase (RchAt (F0T o Zp Np cF)) fullLinks
        P5J.At.ps L₀.c₀ P5J.At.tokOf (h.row L₀) :=
  Iff.rfl

/-- **What is owed at every place of the kind gives the field.** -/
theorem k02_kind (h : AtMg o Z D r Zp Np cF) {nR : ℕ} (D₀ : MgData ProofFile.Inst ProofFile.InstPub P5J.At.Tok
    numsFull.rows (colsAt numsFull) nR (P5J.At.X Zp)) (L₀ : Free numsFull D (F0T o Zp Np cF)
    P5J.At.Tok) (H : ∀ i q a, (h.row L₀)[i]? = some q → P5J.At.ps[i]? = some a → a.kind =
    KindName.K2 → K2PlaceOwes (h.𝔇 D₀) mgBase (RchAt (F0T o Zp Np cF)) fullLinks P5J.At.ps L₀.c₀ i
        q) :
    h.Kind D₀ L₀ KindName.K2 :=
  (k02Counted_is_kind h D₀ L₀).2 (k02_counted _ _ _ _ _ _ _ _ H)

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.k02Counted_is_kind
#print axioms VerifiableInference.Desc.First.K2Caller.k02_kind
