-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestAttentionHonest.lean: the check of the attention sub-proof, run on the messages
and challenges that the C++ verifier saw in one honest proof, and compared with the C++ verifier's
state. Of the seven parts that OnBytes/Model/Attention.lean lists it covers parts 1 to 3 and, of
part 6, the claims before those of the smallness test.

The tests run when this file is compiled. The program does not import this file.

The data (OnBytes/Model/TestAttentionHonestData.lean) comes from a run of the C++ verifier on the
first attention sub-proof of a proof at a small configuration, spelled out in
OnBytes/Model/TestAttentionConfig.lean (exampleScan and the definitions beside it). The head of the
data file says how it was made. No file of the repository is read; the examples under
prover/examples may have other numbers.

The steps and what is compared stand in the sections What is done here and What is compared.

What is not run: the function run of OnBytes/Model/Attention.lean. walkClaims calls hear, tables and
claims in the order of run. What these need from run it repeats by hand: the start state
(Seam.start), setPlanClaims, and the three steps of t2Batch (OnBytes/Model/Trees.lean) that set up
the batching. A change to those routines is not seen here. Nothing else of run is done: not the
tests between the parts, noFreeSlot, the closing steps (Seam.finish) or countsHeld.

What is not compared: the smallness test and its claims; the chain's own steps, among them the
commitments; how the elements are drawn, since they are taken from the record; the weights of the
virtual rows on the rows of their arrays; the claims one by one. The configuration is small: a point
on the heads of keys and values has one coordinate, the four lookup calls have one key point, and lt
is even, so a reversed bit order there, a wrong call's key point or a sign that is taken lt times
would not show. The proof is one honest proof, so the tests show nothing about a proof that must be
refused. A vector is compared through its length and one element (Replay.sumAt).
-/
import OnBytes.Model.Attention
import OnBytes.Model.TestReplay
import OnBytes.Model.TestAttentionConfigWhole
import OnBytes.Model.TestAttentionHonestData

namespace OnBytes.Attention.TestHonest

open OnBytes.Model

/-! ## What is done here

 1. The plan is made by Attention.config from the small configuration's numbers, as
    OnBytes/Model/TestAttentionConfigWhole.lean has them.
 2. walkClaims runs parts 1 and 2 of the check (OnBytes/Model/Attention.lean) on the recorded rounds
    and builds the tables (part 3). It skips the messages of the smallness test and the draw after
    them, and takes the recorded batching element instead. Then it adds the claims of part 6 up to
    those of the smallness test.
 3. What is reached is compared with what the C++ verifier printed.
-/

/-- The plan of the small configuration's attention sub-proof number g. -/
def planOf (g : Nat) : Option Plan :=
  (TestConfig.wholeOf TestConfig.exampleScan).toOption.bind (·.plans[g]?)

/-- Parts 1 to 3 of the check and the claims of part 6 up to those of the smallness test. The
batching element is passed in. Returns the tables. -/
def walkClaims (P : Plan) (endSlot : Nat) (theta : E) : SubM Tables := do
  let f ← hear P
  SubM.must ((← SubM.slot) == endSlot)
  let t ← tables P.S P.mats P.nW f.g f.planes f.scores f.d f.x
  SubM.setPlanClaims P.nLin
  SubM.change fun F => some (t2FillL F P.seam.Tp)
  SubM.batchBy theta
  modify fun F => { F with kapMapF := Array.replicate F.planClaimsF false }
  claims P
    { S := P.S, g := f.g, planes := f.planes, scores := f.scores, d := f.d, x := f.x, t := t,
      iU3 := P.iU3 }
  pure t

/-- The tables and the state that the walk reaches on a record's rounds. Returns none if the walk
fails or leaves a round unused. -/
def stateOn (P : Plan) (p : Replay.Record) : Option (Tables × Fork) := do
  let endSlot ← p.number "end-hear"
  let theta ← p.element "theta"
  match Blk.walk ((walkClaims P endSlot theta).run (P.seam.Fp.fillL.slots P.ns)) p.start []
      p.rounds.toList with
  | some (x, []) => some x
  | _ => none

/-! ## What is compared

 - The sequence of the 891 rounds. A round can only be closed under the recorded name, with all
   recorded scalars taken, and with the recorded numbers of draws and of batched rows.
 - The numbers of the plan: the sub-proof's number, slots, scalars (equal to the slots here),
   claims, calls, pairs, and the length of the vector of tables.
 - Each table: its matrix, the rows of a block, which vector holds it (counted from 0: 2 is U3, the
   vector of tables), its first entry, and its weights.
 - The one equation (the sum of all claims under the powers of the batching element; Fork.settle in
   OnBytes/Model/Hide.lean) after the last claim of the sub-proof and of its lookup: the number of
   claims, the constant, the coefficients on the slots, and the weights on the vector of tables. All
   weights on the other arrays are 0, and each array has the recorded number of virtual rows.
 - For each slot of the record: what was shown, the factor of its mask entry, and that the slot was
   filled.
A vector is compared through its length and one element (Replay.sumAt).
-/

/-- A vector as it is compared: its length and one element. -/
def sized (v : Array E) : Nat × E := (v.size, Replay.sumAt v)

/-- What is compared of the tables. -/
def tablesOf (t : Tables) : List (Nat × Nat × Nat × Nat × Nat × E) :=
  t.funs.toList.map fun f => (f.mat, f.len, f.tree, f.start, sized f.phi)

/-- What is compared of the one equation: the number of claims; the constant; the coefficients on
the slots; the weights of each virtual row of the vector of tables; the number of virtual rows of
each array; and whether all weights on all other arrays are 0. -/
def equationOf (iU3 : Nat) (F : Fork) : Nat × E × (Nat × E) × List (Nat × E) × List Nat × Bool :=
  (F.nClaim, F.c0, sized F.LS, ((F.trees.getD iU3 {}).rows.toList.map fun r => sized r.L),
    F.trees.toList.map (·.rows.size),
    F.trees.toList.zipIdx.all fun X => X.2 == iU3 || X.1.rows.all fun r => r.L.all isZeroE)

/-- What is compared of the first n slots: what was shown, the factors of the mask entries, and how
many of the slots were filled. -/
def slotsOf (n : Nat) (F : Fork) : (Nat × E) × (Nat × E) × Nat :=
  (sized (F.vp.extract 0 n), sized (F.mf.extract 0 n), ((F.gotF.extract 0 n).filter id).size)

-- the record: 891 rounds, 1,929 scalars, 854 elements drawn
#guard ((Replay.ofText heard).map (·.counts)) == some (891, 1929, 854)
-- The numbers of the C++ verifier's plan are those of the plan here. The last pair only holds the
-- 1929 of the next guard to the record (walkClaims compares the slot itself).
#guard ((Replay.ofText heard).map fun p =>
    ["gid", "ns", "nMsg", "nLin", "NC", "NP", "nW", "planClaims", "end-hear"].map p.number) ==
  (planOf 0).map fun P =>
    [P.inp.gid, P.ns, P.nMsg, P.nLin, P.NC, P.NP, P.nW, P.nLin, 1929].map some
-- the tables, the one equation and the slots
#guard (do
    let P ← planOf 0
    let x ← stateOn P (← Replay.ofText heard)
    pure (tablesOf x.1, equationOf P.iU3 x.2, slotsOf 1929 x.2)) ==
  some (seenTables, (nClaim, c0, onSlots, onTables, rowsOf, othersZero),
    (shownUnder, factors, filled))

end OnBytes.Attention.TestHonest
