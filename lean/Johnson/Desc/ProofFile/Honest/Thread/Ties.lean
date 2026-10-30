-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/Ties.lean: from the six hypotheses on a sub-protocol
(Honest/Thread/Pays.lean) to the two conditions on a sub-protocol that the lemma for a whole chain
uses (`PlaysOn`, `SaysYes`: Honest/Law/ThreadC.lean), at A := the invariant before the sub-protocol,
B := the invariant after it. Conditional lemmas on this folder's own definitions, general in the
`Thread`'s parameters.

  `step_takes`   a step that accepts at the columns which `fillCols` has filled for the sub-protocol
     takes them all
  `playsOn_of_pays`   `Plays`, `Behind`, `Exchange`, `RidesPast` and `MadeNext`, with `T.fits` up to
     a border beyond the sub-protocol, give `PlaysOn`
  `saysYes_of_accepted`   `Accepted` gives `SaysYes`, at `fall b`

Limits.
  * Their hypotheses are proved here of no description.
  * They are none of the library's goals, and no goal follows from them without these hypotheses.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw
import Johnson.Desc.ProofFile.Honest.Law.ThreadC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- A step that accepts at the columns which `fillCols` has filled for the sub-protocol's own reads
takes them all. -/
theorem step_takes {blk : Block S Cl} {chain ft : Nat}
    {stored : Nat → Nat → Option (List UInt64)} {tree : Fmt.TreeSource → Option (Place × Table)}
    {ds : List Fmt.Drawn} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {s s' : S} {n : Nat}
    (hdr : rs.map (·.drawn) = ds)
    (hc : fillCols (readsOf chain ft stored tree blk.rounds ds) [] = .ok cols)
    (hs : blk.step ft s rs cols = .ok (s', n)) : n = cols.length := by
  have h3 := ((step_iff ft blk s s' rs cols n).1 hs).2.2
  have e := congrArg List.length (fillCols_kept _ _ _ hc)
  rw [readsOf_wants, List.length_map] at e
  rw [h3, e]
  unfold Block.want
  rw [hdr]

variable (T : Thread Bk S Cl V W X Pb)

/-- **From the five hypotheses that say nothing of a fall.** A conditional lemma on this folder's
own definitions. It is none of the library's goals. -/
theorem playsOn_of_pays {n b : Nat} {blk : Block S Cl} (hfit : T.fits n = true) (hb : b < n)
    (hblk : T.bs[b]? = some blk) (hP : Plays T b) (hB : Behind T b) (hX : Exchange T b)
    (hR : RidesPast T b) (hM : MadeNext T b) :
    PlaysOn T.φ Bk T.chain T.ft T.hs blk (Thr T b) (Thr T (b + 1)) := by
  intro k s m E ds l hA hd hst hl
  obtain ⟨y, cols, hMv, hT⟩ := hP blk hblk k s m E ds l hA hd hst hl
  have hMv' := hMv
  unfold Thread.Moved at hMv'
  obtain ⟨⟨l', hl', hy⟩, hc⟩ := hMv'
  rw [hl] at hl'
  cases hl'
  refine ⟨y, cols, hy, hc, fun s' j hs => ?_⟩
  have hj : j = cols.length :=
    step_takes (yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)) hc hs
  subst hj
  have hS : T.Stepped blk k s m E ds y cols s' := by
    unfold Thread.Stepped
    exact ⟨hMv, hs⟩
  exact thr_behind T hfit hb hblk hA hd hS hT hB hX hR hM

/-- **From the sixth.** A conditional lemma on this folder's own definitions. It is none of the
library's goals. -/
theorem saysYes_of_accepted {b : Nat} {blk : Block S Cl}
    {fall : Nat → S → List Fmt.Drawn → Option String} (hblk : T.bs[b]? = some blk)
    (hA : Accepted T fall b) :
    SaysYes T.φ Bk T.chain T.ft T.hs blk (fall b) (Thr T b) := by
  intro k s m E ds l y cols h0 hd hst hf hl hy hc
  have hMv : T.Moved blk k m E ds y cols := by
    unfold Thread.Moved
    exact ⟨⟨l, hl, hy⟩, hc⟩
  obtain ⟨s', hS⟩ := hA blk hblk k s m E ds y cols h0 hd hst hf hMv
  unfold Thread.Stepped at hS
  exact ⟨s', cols.length, hS.2⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.step_takes
#print axioms ProofFile.Honest.playsOn_of_pays
#print axioms ProofFile.Honest.saysYes_of_accepted
