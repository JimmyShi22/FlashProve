-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/AtMeans.lean: THREE THEOREMS OF THIS FOLDER AT THE ONE LEAN STRUCTURE OF
EQUATIONS OF THE MEANING's FIELDS (`K4Means`, Johnson/Road/K4/K4Means.lean, in the form that has the
fields sd, sentIs, treesAre and room), SO THAT THEIR PREMISES ON THE MEANING ARE THAT STRUCTURE
ALONE, but for one. Statements and proofs: calls. GLUE. HERE LEAN CHECKS that the premises which the
three theorems name one by one ARE that structure's fields.

  **`recIs_at`**: `K4Means Mg D`; `openAllB D.moreL links ps k m` is true: at an unmarked statement
    inside the promise of the table of joints at border k: `RecIs` (Johnson/Road/K4/Rec/Whole.lean):
    the open segment's part of the verifier's state reads as the public parameters say.
  **`inT_four_at`**: with three more tests on the public parameters: the four fields hK, mask,
    oneRow, reads of `InTAsks` at the verifier's state behind every accepting run of K4's
    sub-protocol (`Four`, Johnson/Road/K4/Rec/InTFour.lean).
  **`nextEntry_at`**: `K4Means Mg D`; eW; `openNextB` and `nextFitsB` are true: the number of the
    index masks' message, and the entry that its ledger hands out next, are two numbers of the
    public parameters (Johnson/Road/K4/Rec/NextEntryStatement.lean): the premise hname of
    Johnson/Road/K4/K4LinesWo.lean, to the letter.

OBJECT: none of its own. USER: meant: the assembly of K4's row. LETTERS, filled by nobody: Mg, D, Z,
links, ps, k, j, m, par, q.

Limits. `K4Means` IS A PREMISE. eW (`EWithin`: where the item "K13.pileWithin" is true every ledger
in the statement is that of some number of takes since it was made) IS A PREMISE BESIDE IT: the
structure has no field for that item, and the implication hangs on a statement that its owners have
not yet proved. (Where this and lean/THEOREM.md
differ, the page holds.) THE TESTS ON THE PUBLIC PARAMETERS HAVE BEEN EVALUATED AT NO PARAMETERS.
K04_law, the law of K4's sub-protocol itself, IS NOT PROVED BY THIS. Nothing on soundness.

-/
import Johnson.Road.K4.Rec.InTFour
import Johnson.Road.K4.Rec.NextEntry

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Rec
open Iop OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par seatS)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.First (S ModelPart Pub Meaning Numbers pubSets)
open VerifiableInference.Desc.First.Pend (takeEntry)
open VerifiableInference.Desc.First.RecordPlan (maskSeatP)
open VerifiableInference.Desc.Sound (Frame Piece MsgT onQ)
open Johnson.Desc.First.Walk.Law (ledgerAt)

variable {Xi P Tok Cl : Type} {rows cols nR kC : ℕ} {X : Verify.Public} {Fr : Frame}
  {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {D : K4Data Xi P Tok rows cols nR kC X}

/-- **`RecIs` under `K4Means` alone**, and one test on the public parameters. -/
theorem recIs_at (E : K4Means Mg D) (Z : P) (links : List ModelPart) (ps : List Place) (k m : ℕ)
    (b : S × Fr.E.Str) (A : Part9) (hO : openAllB D.moreL links ps k m = true)
    (h : AtBorder D.N Mg Z links ps k b A) :
    RecIs A (recPlanOf D D.sd) (D.N.msgsAt ps[k]?) m :=
  recIs_of_means E D.sd E.sentIs E.treesAre D.N Z links ps k m b A hO h

/-- **The four fields behind every accepting run, under `K4Means` alone**, and four tests on the
public parameters. -/
theorem inT_four_at (E : K4Means Mg D) (Z : P) (links : List ModelPart) (ps : List Place) (k m : ℕ)
    (par : Par) (q : Piece (ckP .two) Fr S Cl (Wit (CellsK rows cols) Tok MsgT))
    (hO : openAllB D.moreL links ps k m = true)
    (hL : ((pubSets D.moreL links ps)[k]?.getD []).contains (.ledger m) = true)
    (hM : (maskSeatP D.D3.shape D.sd (D.N.sent m 0) D.d12.L.places (D.N.msgsAt ps[k]?) m).isSome =
      true)
    (hB : readsArrayP par.hp D.D3.shape D.D3.layout (D.D3.arrayOf.getD m #[]) m (D.sd.trees m) =
      true)
    (a : S × Fr.E.Str) (τ : Tr (uLT (ckP .two) q.ds)) (fo : Forest.Heard) (o : Own) (G : Fork)
    (ha : onQ D.N Mg links ps (fun s => (Z, s)) k a) (hu : a.1.failed = none)
    (y : Yes seatS par q a τ fo o G) :
    Four (D.N.sent m 0) par (behindOf seatS q a τ o G).1 :=
  inT_four_of_front E D.sd E.sentIs E.treesAre Z links ps k m par q hO hL hM hB a τ fo o G ha hu y

/-- **The index masks' message's number and its ledger's next entry, under `K4Means` and eW**, and
two tests on the public parameters. -/
theorem nextEntry_at (E : K4Means Mg D) (eW : EWithin Mg) (Z : P) (links : List ModelPart)
    (ps : List Place) (j m : ℕ) (hO : openNextB D.moreL links ps j m = true)
    (hF : nextFitsB D.cs D.d12.M (D.N.msgsAt ps[j]?) D.N.indexNo D.free0 D.fvs m = true)
    (b : S × Fr.E.Str) (hb : onQ D.N Mg links ps (fun s => (Z, s)) j b)
    (hu : b.1.failed = none) :
    b.1.out.indexMasks = D.N.indexNo ∧
      ∀ l c l', ledgerAt b.1 = some l → takeEntry l = some (c, l') →
        c = nextNoP D.d12.M (D.N.msgsAt ps[j]?) D.N.indexNo D.fvs m :=
  nextEntryIs P _ Fr D.N Mg Z links ps j m D.d12.M D.cs D.free0 D.fvs E.indexIs E.msgShapes
    (recMeans_of_means E D.sd E.sentIs E.treesAre).codes eW E.room (by rw [E.more]; exact hO) hF
    b hb hu

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.recIs_at
#print axioms OnBytes.Road.K4.Rec.inT_four_at
#print axioms OnBytes.Road.K4.Rec.nextEntry_at
