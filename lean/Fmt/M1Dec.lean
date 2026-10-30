-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1Dec.lean: the verifier's decision for the first toy (a product test), from the view of a
transcript, with the blocks' functions as parameters. It is `decWith`, the function that strings all
blocks together: below, "the string".

The first toy is a test protocol for the claim that three rows a, b, c of one oracle message have
a_i b_i = c_i for every i (the heads of Fmt/M1Types.lean and Fmt/M1Psc.lean). Definitions that
compute. Core Lean; total; generic in the sizes and in the blocks: the six functions of the blocks
are the fields of a record (`Blocks`), so that the string can be read, and tried, by itself. The
blocks themselves: Fmt/M1Send.lean, M1Psc.lean, M1Fold.lean, M1Cs.lean; all put together:
Fmt/M1All.lean.
(In this head "the programs" are the C++ implementation that comes with this Lean code, and "the
format page" is docs/format/FORMAT.md, which comes with the programs.)

What the string does (their section 5, and part 4's section 5). It takes the rounds off the list one
after the other. Each round has its numbers of elements sent, elements drawn and positions drawn; a
round with other numbers is refused. On its way the string carries the claim: a row on a group
(`GRow`) or a claim on three virtual rows (`SRow`), each a linear equation (the head of
Fmt/M1Types.lean). ZERO is the zero-check, PSC the sum-check, BAT the batching block, CS the code
switch, BASE the last block.
  SEND     The seed (a point of na coordinates (`Stage.na`), then a factor); then a round with the
           one answer, nothing drawn. Gives the sample row.
  ZERO     Nothing sent; K elements drawn.
  PSC      One element, one drawn; K times: two elements, one drawn; two elements, one drawn (never
           0: the draw's matter, not tested here); two elements, nothing drawn. Gives three rows.
  BAT      Nothing sent; one element x drawn. Gives one row on the group: the sum of the three rows,
           then the sample row, under 1, x, x^2, x^3 (`sumRows`).
  for each stage but the last:
    FOLD   One element, one drawn; k times: two elements, one drawn. Gives one claim on three
           virtual rows.
    SEND   The seed of the next stage's message.
    CS     The answer; drawn: t positions, then one element. With this stage's opened columns it
           gives one row on the next stage's group.
  BASE     One element, one drawn; then l + l_zk + r + r_zk elements in the clear, t positions
           drawn. The two checks: the linear one; the one at every position, with the last tree's
           opened columns.
  and no round is left.
(Their step between the last CS and BASE, part 4's 5.6: in the programs the last group has formally
one row variable, with a second row that nobody sent, and the variable is fixed at 0:
c_last[j] = c'[2 j]. Here the code switch's row lies on the new message's own tables, so that at
k = 0 this step is the identity: it does not appear.)

The trees. Stage number i's tree is tree number i. A column (`stageCol`, Fmt/M1Types.lean;
`lastCol`) holds:
  of the first tree: three words (a, b, c), then the old and the fresh mask symbols;
  of a later stage but the last: 2^k main symbols over E, then the mask symbols;
  of the last: the last message's and the masking word's main symbols, then their mask symbols.

Main names:
  `stagesOK`: the sizes fit. Its clauses:
      the blocks' own test between neighbours (`fitsAll`);
      all message lengths are powers of two;
      every stage but the last has k ≥ 1;
      the first stage has k = 2, h = 0, rows of 2^K entries and a mask row of at least 2 K + 5 + 1
        entries;
      the last has k = 0, h = 0;
      the public vector of the hiding polynomial of every stage but the last has room in a mask row
        (`hideFits`). Else Fmt/M1Fold.lean's `hideVec` would cut it without a word.
        This clause is this library's own: a narrowing of what the decision takes as sizes: the
        programs' text names no such test of a reader; its layout of a fold's fresh mask presupposes
        the room.
        Sizes that meet every other clause and fail this one are in a guard (a test, #guard) of
        Fmt/M1All.lean.

Limits:
  (D1) form, (D2) work, (D3) openings are not tested here. They belong to the reader of a proof file
    and to the compiled verifier (the head of Fmt/M1Types.lean, which tells (D1) to (D5)).
  Not rendered: their verifier also refuses, before it reads a byte, parameters whose round errors
    miss the target: a test on public parameters, no part of the decision on a file.
  The last block gets the positions as drawn, repeats kept: the same verdict as at their sorted set.
  That this is what the programs decide is not proved.
  This file's sources include no file of theirs. The verdicts have been compared on the programs'
    own files, honest, altered and false, and the nineteen intermediate values on their honest
    proofs: Fmt/M1FullProg.lean and the files that it gathers (tests, no theorem).

Terms: lean/GLOSSARY.md.
-/
import Fmt.M1Types
import Fmt.View

namespace Fmt.M1

/-- the exponent of a power of two -/
def lg (n : Nat) : Nat := Nat.log2 n

/-- Of a message the elements of E, answers among them; its other items are passed over. -/
def sentOf : List ItemValue → List E
  | [] => []
  | .e x :: l => x :: sentOf l
  | .answer x :: l => x :: sentOf l
  | _ :: l => sentOf l

/-- From the general view (Fmt/View.lean) to the toy's own. -/
def ofView (V : _root_.Fmt.View) : View :=
  ⟨V.rounds.map fun r => ⟨sentOf r.vals, r.drawn.elems, r.drawn.poss⟩, V.opened⟩

/-- The six functions of the blocks. The comments on the fields name the arguments after `Fld`, in
their order. -/
structure Blocks where
  /-- main table of 2^Am entries, mask table of 2^Az; the point, the factor, the answer -/
  sample : Fld → (Am Az : Nat) → List E → E → E → GRow
  /-- K, the mask row's length; zeta; mu'; the K pairs; (p_1, p_2); (v_1, v_2); eps; gamma; beta:
  the three rows in BAT's order -/
  psc    : Fld → (K lzk : Nat) → List E → E → List (E × E) → E × E → E × E →
    E → List E → E → List GRow
  /-- k, h; the group's row; sigma, eps; the k pairs; the k challenges -/
  fold   : Fld → (k h : Nat) → GRow → E → E → List (E × E) → List E → SRow
  fits   : Stage → Stage → Bool
  /-- old stage, new stage; the fold's claim; the new message's sample row; the positions as drawn;
  theta; the old tree's columns -/
  cs     : Fld → Stage → Stage → SRow → GRow → List Nat → E → (Nat → Option Col) → Option GRow
  /-- the codes; c, d, tau; tau*, lambda; M'_0, M'_1, R'_0, R'_1; the positions; the last tree's
  columns -/
  base   : Fld → Code → Code → Array E → Array E → E → E → E → List E → List E → List E → List E →
    List Nat → (Nat → Option (E × E × E × E)) → Bool

/-- n rounds, each with two elements sent and one drawn: the pairs, the drawn elements -/
def takeRounds : Nat → Rs → Option (List (E × E) × List E × Rs)
  | 0, rs => some ([], [], rs)
  | n + 1, rs =>
    match nextN 2 1 0 rs with
    | some (⟨[a, b], [g], _⟩, rs') =>
      (takeRounds n rs').map fun x => ((a, b) :: x.1, g :: x.2.1, x.2.2)
    | _ => none

/-- the bits of a stage's two tables -/
def Stage.Am (s : Stage) : Nat := s.k + lg s.C.l
def Stage.Az (s : Stage) : Nat := s.h + lg s.Z.l
/-- the coordinates of the point of its sample -/
def Stage.na (s : Stage) : Nat := max s.Am s.Az + 1

/-- a seed: the point, the factor -/
def seedOf (na : Nat) (rs : Rs) : Option (List E × E × Rs) :=
  match nextN 0 (na + 1) 0 rs with
  | some (v, rs') => some (v.els.take na, v.els.getD na Fld.zeroE, rs')
  | none => none

/-- the last tree's column -/
def lastCol (V : View) (tree x : Nat) : Option (E × E × E × E) :=
  match (colAt V tree x).bind (cutCol 0 2 2) with
  | some ([a, b], [c, d]) => some (a, b, c, d)
  | _ => none

/-- The proximity test from a group's row on. tree: the number of the present stage's tree; mF, mE:
the main rows that were sent at this stage (over the base field, over E). -/
def iopp (B : Blocks) (f : Fld) (V : View) : List Stage → (tree mF mE : Nat) → GRow → Rs → Bool
  | [], _, _, _, _, _ => false
  | [s], tree, _, _, G, rs =>
    match nextN 1 1 0 rs with
    | some (⟨[tauS], [lam], _⟩, rs1) =>
      match nextN (s.C.l + s.Z.l + s.C.r + s.Z.r) 0 s.t rs1 with
      | some (v, []) =>
        B.base f s.C s.Z G.c G.d G.t tauS lam (v.sent.take s.C.l)
          ((v.sent.drop s.C.l).take s.Z.l) ((v.sent.drop (s.C.l + s.Z.l)).take s.C.r)
          (v.sent.drop (s.C.l + s.Z.l + s.C.r)) v.poss (lastCol V tree)
      | _ => false
    | _ => false
  | s :: s' :: more, tree, mF, mE, G, rs =>
    match nextN 1 1 0 rs with
    | some (⟨[sigma], [eps], _⟩, rs1) =>
      match takeRounds s.k rs1 with
      | some (qs, g, rs2) =>
        match seedOf s'.na rs2 with
        | some (z, beta, rs3) =>
          match nextN 1 1 s.t rs3 with
          | some (⟨[alpha], [theta], xs⟩, rs4) =>
            match B.cs f s s' (B.fold f s.k s.h G sigma eps qs g)
                (B.sample f s'.Am s'.Az z beta alpha) xs theta
                (fun x => (colAt V tree x).bind (stageCol s mF mE)) with
            | some G' => iopp B f V (s' :: more) (tree + 1) 0 (2 ^ s'.k) G' rs4
            | none => false
          | _ => false
        | none => false
      | none => false
    | _ => false

/-- neighbours fit -/
def fitsAll (B : Blocks) : List Stage → Bool
  | s :: s' :: more => B.fits s s' && fitsAll B (s' :: more)
  | _ => true

/-- the public vector of a stage's hiding polynomial (h + 2 (k - h) + 1 entries) has room in a mask
row -/
def hideFits (s : Stage) : Bool := decide (s.h + 2 * (s.k - s.h) + 1 ≤ s.Z.l)

/-- The sizes fit. The clauses in words: the head, `stagesOK`. -/
def stagesOK (B : Blocks) (P : Par) : Bool :=
  fitsAll B P.stages &&
  P.stages.all (fun s => s.C.l == 2 ^ lg s.C.l && s.Z.l == 2 ^ lg s.Z.l) &&
    P.stages.dropLast.all (fun s => decide (1 ≤ s.k)) &&
  (match P.stages.head? with
    | some s =>
      s.k == 2 && s.h == 0 && s.C.l == 2 ^ P.K &&
        s.Z.l == 2 ^ lg s.Z.l && decide (2 * P.K + 5 + 1 ≤ s.Z.l)
    | none => false) &&
  (match P.stages.getLast? with
    | some s => s.k == 0 && s.h == 0
    | none => false) &&
  P.stages.dropLast.all hideFits

-- the room: k = 2, h = 0: five entries;  k = h = 1: two
#guard hideFits ⟨⟨4, 4, 1⟩, ⟨4, 8, 1⟩, 2, 0, 1⟩ && !hideFits ⟨⟨4, 4, 1⟩, ⟨4, 4, 1⟩, 2, 0, 1⟩ && hideFits ⟨⟨4, 4, 1⟩, ⟨4, 2, 1⟩, 1, 1, 1⟩ && !hideFits ⟨⟨4, 4, 1⟩, ⟨4, 1, 1⟩, 1, 1, 1⟩

/-- The decision, given the blocks. -/
def decWith (B : Blocks) (P : Par) (V : View) : Bool :=
  stagesOK B P &&
  match P.stages with
  | [] => false
  | s :: _ =>
    match seedOf s.na V.rounds with
    | none => false
    | some (z, beta, rs1) =>
      match nextN 1 0 0 rs1 with
      | some (⟨[y], _, _⟩, rs2) =>
        match nextN 0 P.K 0 rs2 with
        | some (vz, rs3) =>
          match nextN 1 1 0 rs3 with
          | some (⟨[mu], [eps], _⟩, rs4) =>
            match takeRounds P.K rs4 with
            | some (qs, gamma, rs5) =>
              match nextN 2 1 0 rs5 with
              | some (⟨[p1, p2], [bY], _⟩, rs6) =>
                match nextN 2 0 0 rs6 with
                | some (⟨[v1, v2], _, _⟩, rs7) =>
                  match nextN 0 1 0 rs7 with
                  | some (⟨_, [x], _⟩, rs8) =>
                    iopp B P.fld V P.stages 0 3 0
                      (sumRows P.fld x
                        (B.psc P.fld P.K s.Z.l vz.els mu qs (p1, p2) (v1, v2) eps gamma bY ++
                          [B.sample P.fld s.Am s.Az z beta y])) rs8
                  | _ => false
                | _ => false
              | _ => false
            | none => false
          | _ => false
        | none => false
      | _ => false

/-- how many rounds the string takes -/
def nRounds (P : Par) : Nat :=
  2 + 1 + (P.K + 3) + 1 + ((P.stages.dropLast.map fun s => s.k + 3).sum) + 2

-- the toy's thirty rounds
#guard nRounds ⟨.two, 12, [⟨⟨15, 4096, 73⟩, ⟨15, 32, 73⟩, 2, 0, 73⟩, ⟨⟨14, 2048, 74⟩, ⟨14, 256, 74⟩, 1, 1, 74⟩, ⟨⟨14, 2048, 74⟩, ⟨14, 1024, 74⟩, 0, 0, 74⟩], 20, 40⟩ == 30
-- the numbers of drawn elements of the three seeds: 16, 14, 13
#guard ([⟨⟨15, 4096, 73⟩, ⟨15, 32, 73⟩, 2, 0, 73⟩, ⟨⟨14, 2048, 74⟩, ⟨14, 256, 74⟩, 1, 1, 74⟩, ⟨⟨14, 2048, 74⟩, ⟨14, 1024, 74⟩, 0, 0, 74⟩] : List Stage).map (fun s => s.na + 1) == [16, 14, 13]

end Fmt.M1
