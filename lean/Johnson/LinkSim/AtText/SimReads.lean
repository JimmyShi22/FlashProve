-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/SimReads.lean: what the simulator's algorithm reads of the data: the two
keys, and the stored columns at the positions that are opened. It proves Spec.simReads
(Johnson/LinkSim/AtText/SpecShift.lean).
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. simReads proves Spec.simReads: for all parameters, coins and challenges, if
two data have the same two keys and their stored columns agree at every position that the algorithm
opens, the simulator's algorithm gives the same output at both. Nothing is asked of the tables'
rows. On the way it proves that the prover's algorithm and its last stage give the same output at
two data with the same rows, the same keys, and stored columns that agree where they are opened
(linkAll_congr, linkEnd_congr).

How. The prover's algorithm (linkAll, Johnson/Prover/Link/LinkAll.lean) reads its data at five
places: the two tables' rows, in the two folded rows' oracle messages (lMem); the stored columns, in
the two lists of opened stored columns; and the keys, at the start of the verifier's state. The
simulator's algorithm runs the prover's algorithm at data whose rows are 0 (zeroIn), so the rows
play no part. The two lists read the stored columns only at the positions sampled in round 3,
reduced modulo the table's length.

How it fits. In this folder, SeamInput.lean uses simReads (simOfAns); through it and Exact.lean it
is used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean). The congruence lemmas are used
in this file alone.

Main names (namespace OnBytes.LinkSim.AtText): simReads (above); lStored_congr and lStoredCols_congr
(the two lists); lMem_congr (the two folded rows); lT_congr (the verifier's state behind the first
five rounds); linkAll_congr and linkEnd_congr (above).

Limits. It says what the algorithm reads, not what follows from that.

Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.SpecShift

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (P15 p12Of readsAtLink)
open H2K.Pub (sgOf)
open Johnson.Prover.Link

variable (P : P15) (S : Sz) (t : ℕ) {X X' : LIn S} (C : LCoins) (D : ℕ → Fmt.Drawn)

theorem lStored_congr (hy : SameStored P D X.y X'.y) : lStored P S X D = lStored P S X' D := by
  unfold lStored
  refine List.map_congr_left fun st hst => List.map_congr_left fun x hx => ?_
  rw [hy st hst x hx]

theorem lStoredCols_congr (hy : SameStored P D X.y X'.y) :
    lStoredCols P S X D = lStoredCols P S X' D := by
  unfold lStoredCols
  refine congrArg List.flatten (List.map_congr_left fun st hst => ?_)
  refine List.map_congr_left fun x hx => ?_
  rw [hy st hst x hx]

theorem lMem_congr (h0 : X.M₀ = X'.M₀) (h1 : X.M₁ = X'.M₁) : lMem S X C D = lMem S X' C D := by
  unfold lMem
  rw [h0, h1]

theorem lT_congr (h0 : X.M₀ = X'.M₀) (h1 : X.M₁ = X'.M₁) (hk : X.keys = X'.keys)
    (hy : SameStored P D X.y X'.y) : lT P S t X C D = lT P S t X' C D := by
  unfold lT lFront
  rw [lMem_congr S C D h0 h1, lStoredCols_congr P S D hy, hk]

/-- The prover's algorithm at two data with the same rows, the same keys and stored columns that
agree where they are opened. -/
theorem linkAll_congr (h0 : X.M₀ = X'.M₀) (h1 : X.M₁ = X'.M₁) (hk : X.keys = X'.keys)
    (hy : SameStored P D X.y X'.y) : linkAll P S t X C D = linkAll P S t X' C D := by
  unfold linkAll lFront lPS lCol
  rw [lMem_congr S C D h0 h1, lT_congr P S t C D h0 h1 hk hy, lStored_congr P S D hy]

theorem linkEnd_congr (h0 : X.M₀ = X'.M₀) (h1 : X.M₁ = X'.M₁) (hk : X.keys = X'.keys)
    (hy : SameStored P D X.y X'.y) : linkEnd P S t X C D = linkEnd P S t X' C D := by
  unfold linkEnd lPS lCol
  rw [lMem_congr S C D h0 h1, lT_congr P S t C D h0 h1 hk hy]

/-- Proves Spec.simReads: of its data, the simulator's algorithm reads only the two keys and the
stored columns at the opened positions. -/
theorem simReads : Spec.simReads := by
  intro P S t X X' C D hk hy
  unfold simAll
  rw [linkAll_congr P S t (X := zeroIn X) (X' := zeroIn X') C D rfl rfl hk hy,
    linkEnd_congr P S t (X := zeroIn X) (X' := zeroIn X') C D rfl rfl hk hy]

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.linkAll_congr
#print axioms OnBytes.LinkSim.AtText.simReads
