-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/KeepJob.lean: kind K13, the members' batching: THE KIND's JOB IN
THE FORM THAT HANDS ITS TABLES ON FROM ROUND TO ROUND (`KeepJob`, Honest/SumKeep.lean), WITH THE
PART, THE ROW, THE HALF AND THE LOT OVER IT. Definitions with code; no theorem. GENERAL IN THE SIZE.
That the job is faithful to `k13Job` (Part.lean of this folder) is shown by no statement of this
library.

What is kept: for each row of the pile its two tables, in the program's field (TablesE.lean). WHERE
get READS WHAT set HAS LAID they are made once, behind the part's first round, and halved at each
variable's challenge; where get gives none at every state they are made, and halved, anew in every
round.
Main names:
  (`K13Kept`, the type of what is kept, stands in TablesE.lean.)
  `k13Keep nR k`: **the job**: base: `k13Job nR k` · start: `tabsE` at the matrix laid back into the
    program's field, the pile at the challenges in front of the part and the last of these
    challenges · bind: `foldAllE` · round: `quadAllE`'s three, each read and laid back, as the
    earlier job lays its three · no Y, no ends.
  `k13SumKeep p`: the part: `keepPart` under the names of `k13Sum p`.
  `k13RowKeep` · `k13HalfKeep` · `k13LotKeep weights pile get set`: Part.lean's texts over it. get,
    set: WHERE IN THE PROVER's OWN STATE X WHAT IS KEPT LIES: two arguments more than `k13Lot` has.
    WHERE X HAS NO ROOM (get := fun _ => none) THE PART MAKES ITS TABLES ANEW IN EVERY ROUND; THAT
    ITS ROUNDS ARE THEN STILL THOSE OF `k13Row`'s IS SHOWN BY NO THEOREM.

THE MATRIX. The small input `K13Ask` holds the matrix in the library's field; `start` lays each
entry back into the program's field by `k13E`: once for each entry and row of the pile, not once a
round.

What is not claimed. Anything on time. That any prover that is made of lots (`OnlineProverParts`,
Honest/AtPure.lean) has room in its own state. The definitions are none of the library's goals.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.Part
import Johnson.Desc.ProofFile.Honest.K13.TablesE
import Johnson.Desc.ProofFile.Honest.SumKeep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes (E zeroE)
open VerifiableInference.Desc.K13 (Where)
open OnBytes.Model (Reading)

/-- **The job that hands its tables on.** -/
def k13Keep (nR k : Nat) : KeepJob K13Ask Unit K13Kept :=
  { base := k13Job nR k
    start := fun w h _ =>
      tabsE nR k (fun i c => k13E (w.mat i c)) (w.pile h)
        ((drawnE (h.drop (h.length - 1))).headD zeroE)
    bind := fun S g => foldAllE g S
    round := fun S =>
      let c := quadAllE S
      [k13E (Reading.gl.val c.1), k13E (Reading.gl.val c.2.1), k13E (Reading.gl.val c.2.2)]
    inY := fun _ _ => []
    ends := fun _ => [] }

/-- The sumcheck's part over it, under the names of `k13Sum p`. -/
def k13SumKeep (p : Where) : Part Unit K13Ask (Unit × Option K13Kept) :=
  keepPart (runName indexMaskRun ⟨k13Place p, 1⟩ "sum") "no ends"
    (k13Keep p.lin.matrixRows p.lin.kCol)

variable {W₀ Rc Xi Tr X : Type}

/-- The row over it. get, set: where in X what is kept lies. -/
def k13RowKeep (weights : W₀ → Weights) (pile : PileOf Xi) (get : X → Option K13Kept)
    (set : X → Option K13Kept → X) (p : Where) :
    List (Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X) :=
  [quietPart,
   (k13SumKeep p).lift (fun _ => ()) (k13Ask weights pile) (fun x => ((), get x))
     fun x y => set x y.2]

/-- The half over it. -/
def k13HalfKeep (weights : W₀ → Weights) (pile : PileOf Xi) (get : X → Option K13Kept)
    (set : X → Option K13Kept → X) :
    KindHalf Where (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  fun p => ⟨k13Place p, k13RowKeep weights pile get set p⟩

/-- **The lot's honest side over it**, under `k13Lot`'s name. -/
def k13LotKeep (weights : W₀ → Weights) (pile : Pub → Ground → PileOf Xi)
    (get : X → Option K13Kept) (set : X → Option K13Kept → X) :
    HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  { name := "K13: the members' batching"
    halves := fun Z G =>
      [k13HalfKeep weights (pile Z G) get set (VerifiableInference.Desc.K13.whereOf Z)] }

end ProofFile.Honest.K13
