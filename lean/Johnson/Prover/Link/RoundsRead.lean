-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/RoundsRead.lean: WHAT THE LIBRARY's LAWS READ OF A TYPED VERIFIER MESSAGE IS
WHAT A VIEW SHOWS OF IT. At a written round rvW d m c (OnBytes/Slice/BlkHead.lean): the point, the
seed and the two lists of positions that are read off the typed values (gVec, gSeed, gLoc at valsOf
d c: OnBytes/Slice/CorePeel.lean) are those read off the round's record of what was drawn (readP,
readL: OnBytes/Slice/ProgField.lean). And: such a round shows no sealed digest, unless its kind is
the sealed one: so a block is shown the round itself.

Main names (namespace Johnson.Prover.Link).
  noDigest_rvW   a round whose kind is not the sealed one is itself without the digest.
  getD_read   entry i of a list of triples, read either way.
  gVec_read, gSeed_read, gSeed_read_take, gLoc_read   THE READ-OFFS.

By: rvOf_els, rvOf_poss (OnBytes/Slice/RoundsOf.lean) · dr_noDigest, noDigest_of_none
(Johnson/Desc/Sound/ShownRounds.lean) · readE_zero (OnBytes/Slice/ProgField.lean) · readP_take
(OnBytes/Slice/BlkSendTake.lean).

Limits. Equations on one round. The prover's message m is idle in the four read-offs: it stands
there for rvW's type. No premise on what the round draws: where there are fewer elements than are
read, both sides read 0.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.ShownRounds
import OnBytes.Slice.BlkHead
import OnBytes.Slice.RoundsOf
import OnBytes.Slice.CorePeel
import OnBytes.Slice.BlkSendTake

set_option autoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice _root_.Run Iop
open VerifiableInference.Desc (noDigest)

variable (d : PQ.RD) (m : (wRound d).Msg) (c : (wRound d).Chal)

/-- A written round whose kind is not the sealed one shows no digest. -/
theorem noDigest_rvW (hk : d.kind ≠ .sealed) : noDigest (rvW d m c) = rvW d m c :=
  VerifiableInference.Desc.Sound.noDigest_of_none _
    (VerifiableInference.Desc.Sound.dr_noDigest .two d.entry d.kind hk _)

/-- Entry i of a list of triples, read in the field: either way. -/
theorem getD_read : ∀ (l : List Fmt.Ext) (i : ℕ),
    (l.map toE).getD i 0 = readL (l.map E.ofTriple) i
  | [], _ => readE_zero.symm
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getD_read l i

/-- **The point.** -/
theorem gVec_read (n : ℕ) :
    gVec n _ (valsOf d c) = readP n ((rvW d m c).drawn.elems.map E.ofTriple) := by
  funext i
  show (elemsV _ (valsOf d c)).getD i.val 0 = _
  rw [← rvOf_els d m c]
  exact getD_read _ _

/-- **The seed.** -/
theorem gSeed_read (n : ℕ) :
    gSeed n _ (valsOf d c) =
      (readP n ((rvW d m c).drawn.elems.map E.ofTriple),
        unitOf (readL ((rvW d m c).drawn.elems.map E.ofTriple) n)) := by
  refine Prod.ext (gVec_read d m c n) ?_
  show unitOf ((elemsV _ (valsOf d c)).getD n 0) = _
  rw [← rvOf_els d m c]
  exact congrArg unitOf (getD_read _ _)

/-- The seed, its point read off the first n elements. -/
theorem gSeed_read_take (n : ℕ) :
    gSeed n _ (valsOf d c) =
      (readP n (((rvW d m c).drawn.elems.map E.ofTriple).take n),
        unitOf (readE (((rvW d m c).drawn.elems.map E.ofTriple).getD n zeroE))) := by
  rw [readP_take]
  exact gSeed_read d m c n

/-- **The two lists of positions.** -/
theorem gLoc_read (a t0 t1 : ℕ) :
    gLoc a t0 t1 _ (valsOf d c) =
      (fun i => ⟨(rvW d m c).drawn.poss.getD i.val 0 % 2 ^ a, Nat.mod_lt _ (Nat.two_pow_pos a)⟩,
        fun i => ⟨(rvW d m c).drawn.poss.getD (t0 + i.val) 0 % 2 ^ a,
          Nat.mod_lt _ (Nat.two_pow_pos a)⟩) := by
  have e : possV _ (valsOf d c) = (rvW d m c).drawn.poss := (rvOf_poss d m c).symm
  refine Prod.ext (funext fun i => Fin.ext ?_) (funext fun i => Fin.ext ?_)
  · show (possV _ (valsOf d c)).getD i.val 0 % 2 ^ a = _
    rw [e]
  · show (possV _ (valsOf d c)).getD (t0 + i.val) 0 % 2 ^ a = _
    rw [e]

end Johnson.Prover.Link
