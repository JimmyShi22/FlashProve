-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyDefs.lean: the written rounds of a key file's three chains, as plain lists made by
recursion over the blocks.

A key file has three chains of rounds. The program that checks it goes through them block by block
(OnBytes/Key/OneTime.lean, OnBytes/Proof/Tail.lean), and the blocks have loops: over the lookups,
the planes of bits and the parts of a lookup, the levels of a product tree, the variables of a
sumcheck, the stages of a proximity test. This file holds the public numbers that these loops run
over and one written round for each kind and size of round, and makes the three lists of written
rounds from them with ::, ++, map, flatten, replicate and `joinFrom`
(OnBytes/Slice/KeyStepLists.lean). All of it can be evaluated.

The course of blocks is one branch of the program's: no row of the table's record; masks ride with
their messages or go ahead of their tests; the fold's row is split between two groups; no second
split; no shift in a lookup; two planes or more; two pending rows or more. The round of the second
chain whose message holds two roots is two written rounds here.

Chain 1: SEND (the index masks) . SEND (the multiplicities) . a lookup for each member of a list .
a proximity test . BAT-sigma . a sumcheck without a shown map . SEND (W) . SEAL. A lookup: LKP . the
tie (a sumcheck without variables that shows three values, then one that shows two for each further
plane but the last) . the parts' roots (one for each part but the last) . JOIN . a tree for each
part . the table's tree . a sumcheck without a shown map . ZERO . a sumcheck that shows one value. A
tree: for each level a sumcheck that shows two values, and LINE. Chain 2: LIN point . SEND . LOC .
SEND in three rounds . LIN zeta . SPLIT . two proximity tests . SEAL. Chain 3: a proximity test.

Main definitions.
 `KRds`      the rounds of a sumcheck, LINE and LKP, one for each kind and size.
 `LkN`       a lookup's numbers and its two own rounds. `StageR`, `TestR`: the rounds of a folded
             stage and of a proximity test.
 `KeyN`      all of these for a key file.
 `KRds.pscY`, `pscN`, `level`, `tree`, `LkN.rds`, `TestR.chain`, `TestR.rds`   the blocks' lists.
 `KeyN.rds₁`, `rds₂`, `rds₃`   the three chains' lists. `KeyN.cut`: the place in the second of the
             first of the two rounds that stand for one.
Not claimed. No theorem is in this file. That these are the rounds which the program's dry runs
state is proved nowhere.


Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyStepLists

set_option autoImplicit false

namespace OnBytes.Slice
open Run

/-- The written rounds that occur at many places, one for each kind and size. eps: the first round
of a sumcheck. r2, r3: the round of a variable whose polynomials have 2 or 3 coefficients. y2, y3:
the round of the further variable, of degree 2 or 3. v1, v2, v3: the round of 1, 2 or 3 shown
values. line, lkp: the rounds LINE and LKP. -/
structure KRds where
  (eps r2 r3 y2 y3 v1 v2 v3 line lkp : PQ.RD)

namespace KRds

variable (R : KRds)

/-- A sumcheck with shown maps: the first round, the variables' rounds, the further variable's, the
shown values'. -/
def pscY (xs : List PQ.RD) (y v : PQ.RD) : List PQ.RD := R.eps :: (xs ++ [y, v])

/-- A sumcheck without a shown map. -/
def pscN (xs : List PQ.RD) : List PQ.RD := R.eps :: xs

/-- A level of a product tree with n variables. -/
def level (n : ℕ) : List PQ.RD := R.pscY (List.replicate n R.r3) R.y2 R.v2 ++ [R.line]

/-- A product tree of k levels whose top level has `more` variables. -/
def tree (more k : ℕ) : List PQ.RD := joinFrom (fun l => R.level (l + more)) k 0

end KRds

/-- A lookup's numbers: the table has 2 ^ d rows; there are `planes` planes of bits of at most
2 ^ mu; part number i has 2 ^ parts[i] keys. join, zero: the rounds JOIN and ZERO, which draw mu and
mu + d elements. -/
structure LkN where
  (d mu planes : ℕ)
  parts : List ℕ
  (join zero : PQ.RD)

/-- The rounds of a lookup. -/
def LkN.rds (R : KRds) (L : LkN) : List PQ.RD :=
  R.lkp :: (R.pscY [] R.y3 R.v3 ++
    ((List.replicate (L.planes - 2) (R.pscY [] R.y3 R.v2)).flatten ++
      ((List.replicate (L.parts.length - 1) (R.pscY [] R.y2 R.v2)).flatten ++
        (L.join :: ((L.parts.map fun v => R.tree 0 v).flatten ++
          (R.tree L.mu L.d ++
            (R.pscN (List.replicate L.d R.r3 ++ List.replicate L.mu R.r2) ++
              (L.zero :: R.pscY (List.replicate (L.mu + L.d) R.r3) R.y2 R.v1))))))))

/-- The rounds of a stage that is folded: FOLD epsilon, k times FOLD round, SEND seed, CS. -/
structure StageR where
  k : ℕ
  (dE dT dS dC : PQ.RD)

/-- The rounds of a proximity test: BAT, the folded stages, BASE lambda, BASE. -/
structure TestR where
  bat : PQ.RD
  folds : List StageR
  (dL dB : PQ.RD)

/-- The rounds after BAT. -/
def TestR.chain (t : TestR) : List PQ.RD :=
  (t.folds.map fun s => s.dE :: (List.replicate s.k s.dT ++ [s.dS, s.dC])).flatten ++ [t.dL, t.dB]

/-- The rounds of a proximity test. -/
def TestR.rds (t : TestR) : List PQ.RD := t.bat :: t.chain

/-- The public numbers of a key file's loops, and its written rounds. -/
structure KeyN where
  R : KRds
  lks : List LkN
  /-- the number of column variables of the matrix -/
  kCol : ℕ
  /-- the four SENDs of two rounds: SEND seed, SEND answer -/
  (zSeed zAns mSeed mAns wSeed wAns uSeed uAns : PQ.RD)
  /-- the SEND of two roots: the two halves of SEND seed, and SEND answer -/
  (oSeed kSeed okAns : PQ.RD)
  (sigma seal₁ pt loc zeta split seal₂ : PQ.RD)
  /-- the four proximity tests -/
  (tG tU tO tW : TestR)

namespace KeyN

variable (N : KeyN)

/-- The rounds of chain 1. -/
def rds₁ : List PQ.RD :=
  N.zSeed :: N.zAns :: N.mSeed :: N.mAns :: ((N.lks.map (LkN.rds N.R)).flatten ++
    (N.tG.rds ++ (N.sigma :: (N.R.pscN (List.replicate N.kCol N.R.r3) ++
      [N.wSeed, N.wAns, N.seal₁]))))

/-- The rounds of chain 2. -/
def rds₂ : List PQ.RD :=
  N.pt :: N.uSeed :: N.uAns :: N.loc :: N.oSeed :: N.kSeed :: N.okAns :: N.zeta :: N.split ::
    (N.tU.rds ++ (N.tO.rds ++ [N.seal₂]))

/-- The rounds of chain 3. -/
def rds₃ : List PQ.RD := N.tW.rds

/-- The place in chain 2, counted from 0, of the first of the two rounds that stand for the round
with two roots. -/
def cut : ℕ := 4

end KeyN

end OnBytes.Slice
