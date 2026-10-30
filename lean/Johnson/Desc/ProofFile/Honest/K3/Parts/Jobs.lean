-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/Jobs.lean: the honest side of the kind "lookup" (K3): THE
SPECIFICATION'S FILLING OF THE ROW'S LETTER AT SEVERAL PARTS OF KEYS. Definitions with
code; one theorem.

Honest/K3/JobsSpec.lean fills the letter at one key vector: it is idle at the parts' step and at a
part other than the first. Here every stage of the row has its job:

  the tie's first step     `tieTop` at Z := the product of all
                           parts' roots (Honest/K3/Parts/Data.lean)
  the tie's later steps    the specification's `tieJob`, at the shared data
  the parts' step i        `splitJob`: the specification's job of a product, without a variable
  part i's level m         the specification's `keyJob`, AT PART i's OWN DATA, at the run's
                           point in front
  table, leaves, bits      the specification's, at the shared data, as at one part

  `dataP`           the data, of the prover's input and the run's points
  `specJobsP`       the filling, at public numbers N, the parts' sizes and orders
  `specJobsPAt`     the same at public numbers made of a face (for toys)
  `part_one`        where the shared numbers hold part 0's size and orders, part 0's data ARE the
                    data at one key vector

Limits. Slow, as Honest/K3/JobsSpec.lean: for statements and toys.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K3.Parts.Data

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts
open OnBytes (E)
open OnBytes.HonestTrace.Look (Job Data tieJob keyJob tabJob leavesJob bitsJob)

variable {P : Type}

/-- **The data at parts**, of the prover's input and the run's points. vs, oK: the parts' numbers of
levels and orders: public. -/
def dataP (N : KE → TwV.Nums P KE) (vs : List Nat) (oK : Nat → Nat → List Nat) (w : Hidden)
    (p : Pts) : DataP P where
  D := dataAt N w p
  vs := vs
  oK := oK
  key := fun i x => up (w.key p.theta i x)

/-- **The specification's filling of the row's letter, at several parts.** -/
def specJobsP (N : KE → TwV.Nums P KE) (vs : List Nat) (oK : Nat → Nat → List Nat) :
    LookJobs Hidden where
  job
    | .tie 0 => carry fun w p =>
        tieTop ((dataP N vs oK w p).rest 0) (dataAt N w p).a ((dataAt N w p).Pc 1)
          ((dataAt N w p).G 0)
    | .tie (s + 1) => carry fun w p => tieJob (dataAt N w p) (s + 1)
    | .split i => carry fun w p => splitJob (dataP N vs oK w p) i
    | .key i m => carry fun w p => keyJob ((dataP N vs oK w p).part i) m (byBit (p.keyPt i m))
    | .tab l => carry fun w p => tabJob (dataAt N w p) l (byBit (p.tabPt l))
    | .leaves => carry fun w p => leavesJob (dataAt N w p) (byBit (p.tabPt (N (up p.theta)).d))
    | .bits => carry fun w p => bitsJob (dataAt N w p) (byBit p.zeroPt)
    | _ => idle

/-- The filling at public numbers made of a face, with the face's own parts and orders. -/
def specJobsPAt (f : LFace) (row : E → Nat → E) (pads : List (Nat × Nat)) : LookJobs Hidden :=
  specJobsP (numsOf f row pads) f.parts f.orders

/-- Where the shared numbers hold part 0's size and orders, part 0's data are the data at one key
vector. -/
theorem part_one (N : KE → TwV.Nums P KE) (vs : List Nat) (oK : Nat → Nat → List Nat) (w : Hidden)
    (p : Pts) (hv : vs.getD 0 0 = (N (up p.theta)).v' + 1) (ho : oK 0 = (N (up p.theta)).oK) :
    (dataP N vs oK w p).part 0 = dataAt N w p := by
  unfold DataP.part dataP
  simp only [hv, ho, Nat.add_sub_cancel]
  rfl

#print axioms ProofFile.Honest.K3.Parts.part_one

end ProofFile.Honest.K3.Parts
