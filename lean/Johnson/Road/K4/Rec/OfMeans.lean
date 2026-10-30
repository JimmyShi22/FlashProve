-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/OfMeans.lean: THE SEVEN EQUATIONS THAT "THE OPEN SEGMENT's PART OF THE
VERIFIER's STATE READS AS THE PLAN SAYS" SPENDS (`RecMeans`, Johnson/Road/K4/Rec/Whole.lean) OUT OF
THE ONE LEAN STRUCTURE OF EQUATIONS OF THE MEANING's FIELDS (`K4Means`,
Johnson/Road/K4/K4Means.lean). One definition, statements and proofs: five of the seven by that
structure's own fields (HERE LEAN HOLDS THAT THE TEXTS OF "frame.liveIs" AND linkFresh WHICH
Johnson/Road/K4/Rec/Statement.lean WRITES OUT ARE THEIR OWNER's); two stay premises. GLUE.

  `recPlanOf D sd`: the plan's letters off the structure's data: the codes; the request's shape, the
    layout and the lists of arrays OF THE LOOKUPS' DATA D.D3; the proximity test's door's two lists;
    sd.
  **`recMeans_of_means`**: `K4Means Mg D`, eSent and eTrees at sd: `RecMeans Mg (recPlanOf D sd)`.
  **`recIs_of_means`**: with a yes of `openAllB` AT THE DATA's LETTER D.moreL: `RecIs` at an
    unmarked statement inside the promise at border k.

OBJECT: none of its own. USERS: Rec/AtMeans.lean, Rec/InTFour.lean, More/MadeEleven.lean;
Honest/K4/Law/FrontHead.lean. LETTERS, filled by nobody: Mg, D, sd and the border's.

Limits. `K4Means` IS A PREMISE. eSent AND eTrees ARE PREMISES BESIDE IT: "frame.sentIs" and
"ledger.treesAre" lie in pubAll, but that blocks make or keep them is not shown but on premises
(made_sent, Rec/MadeSent.lean). THE DATA HOLD THE REQUEST's SHAPE AND THE LAYOUT
TWICE (D.shape, D.layout: of "in order"; D.D3.shape, D.D3.layout: of "frame.liveIs"): NOTHING HERE
TIES THE TWO; this file reads the second pair. K04_law, the law of K4's block itself, IS NOT PROVED
BY THIS. Nothing on soundness.
-/
import Johnson.Road.K4.K4Means
import Johnson.Road.K4.Rec.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Rec
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers eqsB)
open VerifiableInference.Desc.First.FillSent (SentData)
open VerifiableInference.Desc.Sound (Frame MsgT)

variable {Xi P Tok : Type} {rows cols nR kC : ℕ} {X : Verify.Public}

/-- The plan's letters off the structure's data. -/
def recPlanOf (D : K4Data Xi P Tok rows cols nR kC X) (sd : SentData) : RecPlan where
  cs := D.cs
  shape := D.D3.shape
  layout := D.D3.layout
  arrs := fun m => D.D3.arrayOf.getD m #[]
  L := D.d12.L
  M := D.d12.M
  d := sd

/-- **`RecMeans` out of `K4Means`**, with eSent and eTrees beside it. -/
theorem recMeans_of_means {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)}
    {D : K4Data Xi P Tok rows cols nR kC X}
    (E : K4Means Mg D) (sd : SentData) (eS : ESent Mg sd) (eT : ETrees Mg sd) :
    RecMeans Mg (recPlanOf D sd) where
  live := fun m a => E.liveIs m a
  fresh := fun m a => E.linkFresh m a
  seats := E.seatsCarried
  shapes := E.msgShapes
  codes := fun a h => by
    rw [E.inOrder a] at h
    simp only [Bool.and_eq_true] at h
    have h1 := h.1.1.1.2
    unfold eqsB at h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact h1.1.1
  sent := eS
  trees := eT

/-- **`RecIs` out of `K4Means`**: the test on the plan at the data's letter for the door's
filling. -/
theorem recIs_of_means {Fr : Frame} {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)}
    {D : K4Data Xi P Tok rows cols nR kC X}
    (E : K4Means Mg D) (sd : SentData) (eS : ESent Mg sd) (eT : ETrees Mg sd) (N : Numbers) (Z : P)
    (links : List ModelPart) (ps : List Place) (k m : ℕ) (b : S × Fr.E.Str) (A : Part9)
    (hO : openAllB D.moreL links ps k m = true) (h : AtBorder N Mg Z links ps k b A) :
    RecIs A (recPlanOf D sd) (N.msgsAt ps[k]?) m :=
  recordIsPlan P _ Fr N Mg Z links ps k m b A (recPlanOf D sd) (recMeans_of_means E sd eS eT)
    (by rw [E.more]; exact hO) h

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.recMeans_of_means
#print axioms OnBytes.Road.K4.Rec.recIs_of_means
