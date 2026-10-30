-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysClaimsRun.lean: the five stretches of Johnson/Road/FormsKeysClaims.lean, run
from a made-up state.

The theorems of FormsKeysClaims.lean begin "whenever the stretch returns". This file runs the
verifier's own five routines, one after the other, and shows that they do return; beside that it
evaluates what the theorems conclude.

The line "#guard" is evaluated when this file is compiled, by Lean's interpreter, and the
compilation fails if the value is not true. It is a run. It is no theorem: nothing that only a guard
shows can be used in a proof, and it speaks of these numbers alone. This file holds no theorem.

What is evaluated. The made-up shape hR8 with the calls pcR8, in both groups of layers; the
environment and the points of Johnson/Road/FormsKeysRunP.lean (withP). Made up here: the slots and
the batching powers of the record of what was heard (heardC); a sumcheck's state of one variable for
the token sumcheck of the row products; a state (forkC) with 400 slots, of which the 4 NI end
values' are filled, one array with one virtual row for the reads, and a drawn theta; a context
that is no dry run. No message is read: the five routines read none.

The marks, for each group. For claimsNorms, claimRowBatch, claimsLedger5, claimsOneHot and, in the
first group, claimEmbedding, each run from the state and context that the one before has left:
 1 to 5. the routine returns; the list of FormsKeysClaims.lean is there; it has 3, 1, 1 + 21 NI,
    LamM, 1 members; and Fork.lins with that list, from the state before, leaves the coefficients on
    the slots, the constant, the number of claims and the weights on the virtual row that the run
    has left. In the second group mark 5 says that embL is not there: no table at Z_E.
 6. A control: with the list of claimsNorms in another order the comparison of mark 1 fails.
 7. claimsLedger5 has filled slots that were free: the run's state is not the state that Fork.lins
    leaves.

What is not run: the nine other stretches; the caller; a state that a run of the check has made. The
program does not import this file.
-/
import Johnson.Road.FormsKeysClaims
import Johnson.Road.FormsKeysRunP

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model (Fork SubM Aff)
open OnBytes.Model.Layer (Heard Pub readsOf tailsOf shownRun claimsNorms claimRowBatch claimsLedger5
  claimsOneHot claimEmbedding)

/-- The record of RunP with slots and batching powers: the end values of the product layer of the
squares under 0 and 1, its claim a made-up form; the hidden sum of the token sumcheck under 3; the
sums from 10 on, the products behind them, the end values behind these, the sumcheck's own slots
last. -/
def heardC (r : RunP) : Heard :=
  let NI := r.v.y.NI
  { r.H with
    sW := 10, sPv := 10 + 9 * NI, gp := elemsR 4100 9, omV := elemsR 4300 (7 * NI),
    wpl := { r.H.wpl with sL := 0, sR := 1, row := Aff.slot 2 },
    tV := { r.H.tV with
      sCl := 3, sEnd := 10 + 16 * NI,
      p := { start := Aff.slot 3, target := Model.ofNat 5, eps := Model.ofNat 7,
             claim := Model.ofNat 9, first := 10 + 20 * NI, vars := #[OnBytes.Psc.Weight.plain 3],
             r := #[Model.ofNat 11], started := true } } }

/-- The made-up state. -/
def forkC (r : RunP) : Fork :=
  let NI := r.v.y.NI
  let got (j : ℕ) : Bool := decide (10 + 16 * NI ≤ j) && decide (j < 10 + 20 * NI)
  { trees := #[{ K := r.v.K3, R := 1, rows := #[{ L := Array.replicate r.v.K3 zeroE }] }],
    ns := 400, next := 400,
    vp := (Array.range 400).map fun j => if got j then Model.ofNat (1000 + j) else zeroE,
    mf := (Array.range 400).map fun j => if got j then Model.ofNat 13 else zeroE,
    LS := Array.replicate 400 zeroE, gotF := (Array.range 400).map got,
    theta := Model.ofNat 12345, thetaDrawnF := true, planClaimsF := 100000 }

/-- What of a state the one equation is made of, in a form that can be compared. -/
def sumC (F : Fork) : Array E × E × ℕ × Array (Array (Array E)) :=
  (F.LS, F.c0, F.nClaim, F.trees.map fun X => X.rows.map (·.L))

/-- One stretch: it returns; the list is there and has n members; Fork.lins with it leaves what the
run has left. Returns the mark and where the run ended. -/
def stretchC (m : SubM Unit) (ol : Option (List Aff)) (n : ℕ) (F : Fork) (c : Ctx) :
    Bool × Fork × Ctx :=
  match m F c, ol with
  | .ok (((), G), c'), some l =>
    (l.length == n && ((F.lins l).map sumC == some (sumC G)), G, c')
  | _, _ => (false, F, c)

/-- The marks, in one group. -/
def claimsB (r : RunP) : List Bool :=
  match readsOf r.v.y with
  | .error _ => []
  | .ok rd =>
    let y := r.v.y
    let H := heardC r
    let P : Pub := { y, rd, sc := r.v.sc, rope := r.ce.rope, wsLay := r.ce.wsLay, V := 16,
                     tokv := #[], tails := tailsOf y, set := {} }
    let F0 := forkC r
    let c0 : Ctx := { ch := { dry := false, entries := [] } }
    let s1 := stretchC (claimsNorms P r.v H) (normsL P r.v H) 3 F0 c0
    let s2 := stretchC (claimRowBatch y H) (some [rowBatchForm y H]) 1 s1.2.1 s1.2.2
    let sh : Array E := match shownRun H.tV.sEnd (4 * y.NI) s2.2.1 s2.2.2 with
      | .ok ((x, _), _) => x
      | .error _ => #[]
    let s3 := stretchC (claimsLedger5 r.v H) (ledgerL r.v H sh) (1 + 21 * y.NI) s2.2.1 s2.2.2
    let s4 := stretchC (claimsOneHot r.v) (oneHotL r.v) y.LamM s3.2.1 s3.2.2
    let s5 := stretchC (claimEmbedding r.v H 4) (embL r.v H 4) 1 s4.2.1 s4.2.2
    [s1.1, s2.1, s3.1, s4.1, if r.v.g == 0 then s5.1 else (embL r.v H 4).isNone,
     !(stretchC (claimsNorms P r.v H) ((normsL P r.v H).map List.reverse) 3 F0 c0).1,
     s3.2.1.gotF != s2.2.1.gotF]

/- all marks, in both groups of layers -/
#guard withP false hR8 pcR8 claimsB == List.replicate 2 (List.replicate 7 true)

end OnBytes.Road
