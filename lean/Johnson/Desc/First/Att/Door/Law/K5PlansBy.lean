-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5PlansBy.lean: kind K5: **THE TWO TESTS ON THE PLAN's SEATS AND SHAPES "AT EVERY MEMBER", AS FUNCTIONS OF THE PLAIN PARTS THAT THEY READ.** Over letters.
Why. To carry the two tests from a head's letters to written values, each part must be rewritten by itself; the caller's list stands in a type (the seat's), so it cannot be rewritten in place. Here the seat is a function of the member's
number, and the rule "reads" says what of the planner's sendings the tests read: the request's shape alone: no radius, no map from trees to arrays' names, no look of a ledger's arrays.

Main names:
  seatsAllBy S b tr D rd σ own n m L · shapesAllBy S b tr D rd n m M: the two tests at List.range ‹the list's length›.
  seatsAllBy_reads | shapesAllBy_reads: they are the same at D and D' with one request's shape, at any two radii and any two looks.
  **seatsAllBy_gives | shapesAllBy_gives**: an accept gives the law's own test (seatsPlanB | shapesPlanB, Johnson/Desc/First/Att/K05OwnersSent.lean) at every list of numbers ks.
IS IT EMPTY HERE? Rules over letters.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5PlansAll
import Johnson.Desc.First.Att.Door.Law.K5PairsRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes
open VerifiableInference.Desc.First.Att.P (psOf qsOf seatsPlanB shapesPlanB)
open VerifiableInference.Desc.First.FillSent (SentData sentDataOf TreeLook)
open VerifiableInference.Desc.First.Look (Sent sigListCalls keptAt)
open VerifiableInference.Desc.K12.Door (Laid)

/-- The test on the seats at every member of the caller's list of segment m. -/
def seatsAllBy (S : Params.ReqShape) (b : ℕ → ℕ) (tr : ℕ → List TreeLook) (D : Sent) (rd : OracleShape → ℕ) (σ : ℕ → ℕ × ℕ)
    (own : List (ℕ × ℕ)) (n m : ℕ) (L : Laid) : Bool :=
  seatsPlanB (sentDataOf S b tr) m (keptAt D m).length L
    (psOf (sigListCalls D rd m) (fun j => σ j.1) (List.range (sigListCalls D rd m).length)) own n

/-- The test on the shapes at every member of the caller's list of segment m. -/
def shapesAllBy (S : Params.ReqShape) (b : ℕ → ℕ) (tr : ℕ → List TreeLook) (D : Sent) (rd : OracleShape → ℕ) (n m : ℕ)
    (M : List OracleShape) : Bool :=
  shapesPlanB (sentDataOf S b tr) m (keptAt D m).length M (qsOf (sigListCalls D rd m) (List.range (sigListCalls D rd m).length)) n

/-- **What the test on the seats reads of what the planner sends: the request's shape alone.** -/
theorem seatsAllBy_reads {D D' : Sent} (hD : D.shape = D'.shape) (S : Params.ReqShape) (b : ℕ → ℕ) (tr tr' : ℕ → List TreeLook)
    (rd rd' : OracleShape → ℕ) (σ : ℕ → ℕ × ℕ) (own : List (ℕ × ℕ)) (n m : ℕ) (L : Laid) :
    seatsAllBy S b tr D rd σ own n m L = seatsAllBy S b tr' D' rd' σ own n m L := by
  unfold seatsAllBy
  rw [kept_shape hD, psOf_len _ (sigListCalls D' rd' m) σ (calls_len hD rd rd' m), calls_len hD rd rd' m]
  rfl

/-- **The like for the test on the shapes.** -/
theorem shapesAllBy_reads {D D' : Sent} (hD : D.shape = D'.shape) (S : Params.ReqShape) (b : ℕ → ℕ) (tr tr' : ℕ → List TreeLook)
    (rd rd' : OracleShape → ℕ) (n m : ℕ) (M : List OracleShape) :
    shapesAllBy S b tr D rd n m M = shapesAllBy S b tr' D' rd' n m M := by
  unfold shapesAllBy
  rw [kept_shape hD, qsOf_shapes _ (sigListCalls D' rd' m) (calls_shapes hD rd rd' m), calls_len hD rd rd' m]
  rfl

/-- **An accept gives the law's own test on the seats, at every list of numbers.** -/
theorem seatsAllBy_gives {S : Params.ReqShape} {b : ℕ → ℕ} {tr : ℕ → List TreeLook} {D : Sent} {rd : OracleShape → ℕ} {σ : ℕ → ℕ × ℕ}
    {own : List (ℕ × ℕ)} {n m : ℕ} {L : Laid} (h : seatsAllBy S b tr D rd σ own n m L = true) (ks : List ℕ) :
    seatsPlanB (sentDataOf S b tr) m (keptAt D m).length L (psOf (sigListCalls D rd m) (fun j => σ j.1) ks) own n = true :=
  seatsPlan_of_all h ks

/-- **An accept gives the law's own test on the shapes, at every list of numbers.** -/
theorem shapesAllBy_gives {S : Params.ReqShape} {b : ℕ → ℕ} {tr : ℕ → List TreeLook} {D : Sent} {rd : OracleShape → ℕ} {n m : ℕ}
    {M : List OracleShape} (h : shapesAllBy S b tr D rd n m M = true) (ks : List ℕ) :
    shapesPlanB (sentDataOf S b tr) m (keptAt D m).length M (qsOf (sigListCalls D rd m) ks) n = true :=
  shapesPlan_of_all h ks

end H2K5.Door

#print axioms H2K5.Door.seatsAllBy_reads
#print axioms H2K5.Door.shapesAllBy_reads
#print axioms H2K5.Door.seatsAllBy_gives
#print axioms H2K5.Door.shapesAllBy_gives
