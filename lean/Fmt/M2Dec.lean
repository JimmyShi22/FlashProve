-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2Dec.lean: the second toy (a chain of three links): the verifier's decision, as one pass
through the rounds of a transcript.

The second toy is a test protocol of the programs (the C++ implementation that comes with this Lean
code). Its purpose is to show, for vectors x_1, b_m, c_m over the base field, that x_(m+1) = c_m =
x_m b_m entry by entry, for m = 1, 2, 3. Each link has oracle messages of its own. At the end of a
link all its open claims are batched into one row, folded, and carried into the next link's
messages; one proximity test closes the chain. This file defines the decision: the algebraic part of
the check, a function of the view (what a reader hands on: for every round what was sent and what
was drawn, and the opened columns). It is generic in the sizes, in the number of links and in the
blocks: the functions of the single blocks are the fields of a record, so that the pass can be read,
and tried, by itself. Core Lean, no Mathlib; every function is total.
A row is a linear claim on oracle messages: forms (vectors of coefficients) on their tables, and a
target. A block is one step of the protocol (a sample, a sum-check, a fold, the switch from one link
to the next), given as a function of plain arguments. In this file a block is an argument. So what
is told under 1. of a block's rows is said of the blocks of Fmt/M2All.lean.

Sources. Written from the programs' description of the toy, in a revised version: its section 5 and,
in its part on the frame of a chain of links, sections 2 and 5 to 8.

1. What the file contains.
   The pass. It takes the rounds off the list one after the other, each with its numbers of elements
   sent, elements drawn and positions drawn (a round with other numbers is refused), and carries a
   claim along. For the links m = 1 .. L (L: the number of links, `Par.links`):
   first(m): two rounds. The first round is a seed: one point is drawn for all sampled messages of
     the prover's message, then a factor. The second round sends the answers, one for each sampled
     message in the order of sending. At m = 1 the second round draws nothing. At m > 1 the second
     round draws t positions and no element. These positions are the list at which the former
     link's tree is opened; each of them is a draw.
   the link: ZERO, the zero-check: V elements are drawn. PSC, the sum-check, has these rounds:
       one element sent, one drawn;
       V times two elements sent, one drawn;
       two elements sent, one drawn;
       two elements sent, nothing drawn.
     This gives three rows.
   close(m): the link's open rows are batched into one row, and that row is folded.
     The oracle messages of one prover's message that are tested together form a group; they are its
     members. A message that the next link reads again is kept. The next prover's message begins
     with a carrying message and holds the kept message, sent anew (the second sending).
     One element theta is drawn. All open rows of the group are summed with the coefficients
     1, theta, theta^2, .., in this order:
       the claim carried over from the former link (m > 1);
       the old sample row of the former link's kept message, as a row of its own:
         it is read on the second sending;
         at the pad's three places it is read on the old pad in the carrying message;
         its target is the old answer;
       the link's three rows;
       the sample rows, member by member;
       for each draw of the list, as drawn, repeats counted, these rows: main, kept row (if the
         former group had one), old mask, fresh mask.
     Then FOLD: one element sent, one drawn; k times two elements sent, one drawn. This gives a
     claim on virtual rows and on the kept table.
   finish: one row on the last group is made. After a seed, a round sends the one answer and draws
     t positions and no element: the list at which link L's tree is opened. Then one element is
     drawn, and with its powers as coefficients the carried claim, the sample row and three rows for
     each draw are summed.
   Then comes the last proximity test, as in the first toy (a product test). Its first stage is
   written here, because the last group has no mask row of its own: an opened column has the fresh
   mask symbol alone, and the old one counts as 0.
   The heads of Fmt/M2Types.lean (groups, kept messages), Fmt/M2Loc.lean (the carrying message, the
   second sending, the pads) and Fmt/M1Fold.lean (virtual rows) say more.
   No equation between field elements is tested before the last block. (Before it the pass tests the
   sizes, each round's numbers of elements and positions, and that each drawn column was opened and
   has its width.) This is said of the pass itself and of the blocks of Fmt/M2All.lean: here a block
   is an argument.
   How the rows are summed. The rows of the draws are not written out here. The block `sumDraws`
   adds them, with the running powers as coefficients, onto the sum so far (its parts on the
   carrying message and on the kept message sent anew). So the terms are added in the order given
   under close(m). `sumDraws` is a field of `Blocks`; Fmt/M2All.lean fills it with `sumDrawsFrom`
   (Fmt/M2Loc.lean).
   The trees. Group m's tree has the number m - 1; the trees of the last test's later stages follow.
   `Form3`: a form on one row of l entries, a form on the link's mask row, a target.
   `Blocks`: the record of the blocks' functions: the first toy's six, and `sample` (a member's
     sample row on its own tables, all three kinds of pad), `psc`, `foldK`, `carried`, `oldRow`,
     `sumDraws`.
   `goLinks` keeps a log of values on the way, so that the values in it are made by the same pass as
     the decision. The other values of the list that the programs print are made by copies of the
     pass's steps (Fmt/M2Targets.lean); the copy of the last test's later stages runs at the first
     toy's own blocks.
   `sizesOK`: the test on the sizes. Its clauses:
       There is at least one link.
       Lengths are powers of two.
       A main row has at least four places, so a kept row has its three pad places; this is a
         condition of both theorems that say that the fast sum of the draws' rows is its meaning
         (`sumDrawsLit`, `sumDrawsFromLit`, Fmt/M2Loc.lean): `sumDraws_eq` and `sumDrawsFrom_eq`
         (Fmt/M2LocEq.lean). The second theorem asks more, of the row that it starts from.
       The sum-check's mask entries and the pad have room in the link's mask row.
       What a closing carries on (`restLen` entries) and the pad of the carrying message have room
         in one row of that message.
       The last test's first stage is the last group's (C, Z, k, h, t).
       The last test has at least two stages.
       The first toy's tests between the stages and on the later stages hold.
       In every stage of the last test but the last, the public vector of the fold's hiding
         polynomial (h + 2 (k - h) + 1 entries) fits the mask row. Without this clause `hideVec`
         (Fmt/M1Fold.lean) would silently cut that vector to the length of the mask row.
   `Batch`, `decBy`: the pass takes the way of batching as an argument, so that the meaning (every
     row written out: `batchLit`, Fmt/M2Close.lean) can be run in the place of the fast way
     (`batch`).
   `decWith B P V : Bool`, `nRounds P`: the decision, given the blocks; the number of rounds.

2. What is checked when the file compiles (#guard). The number of rounds, and the number of entries
   of what a closing carries on with a kept row and without, at the programs' full parameters and at
   their tiny parameters. The blocks are put in, and the test on sizes is tried, in Fmt/M2All.lean.

3. Theorems. None in this file. That, at the blocks of Fmt/M2All.lean, the decision with the fast
   way of batching is the decision with every row written out, for all sizes and all views, is
   proved in Fmt/M2DecEq.lean (`dec_eq`).

4. What is not claimed.
   Form, proof of work and Merkle openings are not tested here; they are the strict reader's and the
   compiled verifier's matter.
   The programs' test that parameters reach their security target is not rendered.
   No theorem says that this is what the programs decide. It is a reading of their description. It
   is compared with the programs on their own files by tests (#guard): the parameter bytes, every
   round, 34 intermediate values and the outcome on three honest proofs, 39 altered copies and 27
   false proofs. These tests are in Fmt/M2Theirs.lean, Fmt/M2EngineLT.lean, Fmt/M2EngineLR.lean,
   Fmt/M2EngineLF.lean and the files beside them (the verifier on bytes) and in Run/M2EngineT1.lean
   and the files beside it (the run functions of the generic construction). In Fmt/ and Run/ no
   altered copy of theirs is shown to reach the decision: in Fmt/M2EngineLTw.lean, M2EngineLRw.lean
   and M2EngineLFwa.lean to M2EngineLFwe.lean the strict reader refuses each of them before the
   decision is run, and in Run/M2Engine*.lean which check of the verifier, or of the reader, refuses
   is not shown (the head of Fmt/M2All.lean, 4.). The tests named here stand on the files that come
   with this code.
   No statement on soundness follows.

Notation:
   C, Z (`Par.C`, `Par.Z`): the links' main code and mask code;
   `Code`, written ⟨a, l, r⟩: a code: codewords of length 2^a, messages of l entries, a random tail
     of r entries (Fmt/M1Codes.lean).
   The rest are natural numbers.
   l, l_zk (in code lz): the number of entries of a main row (the pass hands in the l of C), of a
     mask row (the l of Z);
   V (`Par.V`): the number of variables of a link's sum-check (in `decWith B P V`, and wherever the
     code has `V : M1.View`, V is the view);
   k, h: of a group (`kOf`, `hOf`, Fmt/M2Types.lean): 2^k rows hold the main blocks of rows, 2^h
     rows the mask blocks; of a stage: `Stage.k`, `Stage.h` (Fmt/M1Types.lean);
   t (`Par.t`, `Stage.t`): the number of positions drawn at a list;
   2 V + 5 + 1 (in `sizesOK`): 2 V + 5 mask entries that the sum-check takes (`pscTakes`,
     Fmt/M1Psc.lean), and the pad.
   (`Par`; `toK`, for l and lz: Fmt/M2Types.lean)

Terms: lean/GLOSSARY.md.
-/
import Fmt.M2Types
import Fmt.M1Dec

namespace Fmt.M2
open Fmt.M1

abbrev Form3 : Type := Array E × Array E × E

/-- The blocks. -/
structure Blocks where
  m1       : M1.Blocks
  /-- Arguments after the field, in order: l, l_zk; the member; the point, the factor, the answer.
  Result: the form on the member's own main table, on its own mask table. -/
  sample   : Fld → (l lz : Nat) → Mem → List E → E → E → Array E × Array E
  /-- Arguments after the field, in order: V, l, l_zk; zeta; mu'; the V pairs; (p_1, p_2); (v_1,
  v_2); eps; gamma; beta. Result: the rows on c, on x, on b. -/
  psc      : Fld → (V l lz : Nat) → List E → E → List (E × E) → E × E → E × E → E → List E →
    E → Form3 × Form3 × Form3
  /-- Arguments after the field, in order: k, h; the group's row; sigma, eps; the k pairs; the k
  challenges. -/
  foldK    : Fld → (k h : Nat) → KRow → E → E → List (E × E) → List E → KSRow
  /-- Arguments after the field, in order: the codes; whether the old group has a kept row; what its
  fold handed on. -/
  carried  : Fld → Code → Code → Bool → KSRow → LRow
  /-- Arguments after the field, in order: the codes; the old sample row's form on the kept table;
  the old answer. Result: that row carried over. -/
  oldRow   : Fld → Code → Code → Array E → E → LRow
  /-- Arguments after the field, in order: the codes, kept, the fold's claim; theta; the sum so far;
  the next power; the positions as drawn; the old tree's columns. Result: all draws' rows added onto
  the sum so far, and the next power. -/
  sumDraws : Fld → Code → Code → Bool → KSRow → E → LRow → E → List Nat →
    (Nat → Option KCol) → Option (LRow × E)

/-- A link's sub-proof: its three rows. -/
def readSub (B : Blocks) (P : Par) (rs : Rs) : Option ((Form3 × Form3 × Form3) × Rs) :=
  match nextN 0 P.V 0 rs with
  | some (vz, rs3) =>
    match nextN 1 1 0 rs3 with
    | some (⟨[mu], [eps], _⟩, rs4) =>
      match takeRounds P.V rs4 with
      | some (qs, gamma, rs5) =>
        match nextN 2 1 0 rs5 with
        | some (⟨[p1, p2], [bY], _⟩, rs6) =>
          match nextN 2 0 0 rs6 with
          | some (⟨[v1, v2], _, _⟩, rs7) =>
            some (B.psc P.fld P.V P.C.l P.Z.l vz.els mu qs (p1, p2) (v1, v2) eps gamma bY, rs7)
          | _ => none
        | _ => none
      | none => none
    | _ => none
  | none => none

/-- The three rows, member by member: one on each of the vectors c, x, b. Where each vector is:
  c: the link's "c";
  x: at link 1 row 0 of "b", later the second sending of the former "c";
  b: at link 1 row 1 of "b", later its one row.
The mask entries: the link's mask row. -/
def pscM (P : Par) (m : Nat) (F : Form3 × Form3 × Form3) : List MRow :=
  let n := (memsOf P.links m).length
  let iB := if m == 1 then 0 else 2
  let iP := if m == 1 then 1 else 3
  [⟨oneAt n iP F.1.1, oneAt n iB F.1.2.1, F.1.2.2⟩,
    ⟨if m == 1 then oneAt n 0 (lay 1 0 0 (2 * P.C.l) F.2.1.1) else oneAt n 1 F.2.1.1,
      oneAt n iB F.2.1.2.1,
      F.2.1.2.2⟩,
    ⟨if m == 1 then oneAt n 0 (lay 1 1 0 (2 * P.C.l) F.2.2.1) else oneAt n 2 F.2.2.1,
      oneAt n iB F.2.2.2.1,
      F.2.2.2.2⟩]

/-- the sample rows, member by member, in the order of joining; i: the member's number; ys: the
answers that are left -/
def samplesGo (B : Blocks) (P : Par) (n : Nat) (z : List E) (beta : E) :
    List Mem → Nat → List E → List MRow
  | [], _, _ => []
  | m :: ms, i, ys =>
    if m.sampled then
      match ys with
      | y :: ys' => (let s := B.sample P.fld P.C.l P.Z.l m z beta y; ⟨oneAt n i s.1, oneAt n i s.2, y⟩) :: samplesGo B P n z beta ms (i + 1) ys'
      | [] => []
    else samplesGo B P n z beta ms (i + 1) ys

def samplesM (B : Blocks) (P : Par) (m : Nat) (z : List E) (beta : E) (ys : List E) : List MRow :=
  samplesGo B P (memsOf P.links m).length z beta (memsOf P.links m) 0 ys

/-- What waits from the former link: what its fold handed on; the list drawn since; its kept
message's sample row (the form on that message's table, the answer), if it has one. -/
structure Wait where
  S   : KSRow
  xs  : List Nat
  old : Option (Array E × E) := none

/-- The rows in front of a link's own. The first is the claim carried over. The second is the old
sample row of the kept message, if there is one, carried over in the same way. At the blocks of
Fmt/M2All.lean (`oldSample`, Fmt/M2Loc.lean) this means: its coefficients go to the same places of
the second sending, those at the pad's places to the old pad's entries in the carrying message; its
target is the old answer. -/
def frontRows (B : Blocks) (P : Par) (kept : Bool) (w : Wait) : List LRow :=
  B.carried P.fld P.C P.Z kept w.S :: (match kept, w.old with
    | true, some (Q, y) => [B.oldRow P.fld P.C P.Z Q y]
    | _, _ => [])

/-- All open rows of group m into one; plain: the link's three rows, then the sample rows. -/
def batch (B : Blocks) (P : Par) (V : M1.View) (m : Nat) (wait : Option Wait)
    (plain : List MRow) (theta : E) : Option KRow :=
  let ms := memsOf P.links m
  match wait with
  | none => some (toK ms P.C.l P.Z.l (sumM P.fld theta plain))
  | some w =>
    let kept := decide (m - 1 < P.links)
    let M := sumMFrom P.fld theta Fld.oneE ((frontRows B P kept w).map (·.toM ms.length) ++ plain)
    match B.sumDraws P.fld P.C P.Z kept w.S theta ⟨M.1.main.getD 0 #[], M.1.main.getD 1 #[], M.1.t⟩
        M.2 w.xs (fun x => (colAt V (m - 2) x).bind (groupCol (memsOf P.links (m - 1)) 1)) with
    | some (D, _) =>
      some (toK ms P.C.l P.Z.l ⟨(D.g :: D.p :: M.1.main.drop 2).take ms.length, M.1.mask, D.t⟩)
    | none => none

/-- How the open rows of a group become one. Arguments, in order: the group's number; what waits;
the plain rows; the batching element. -/
abbrev Batch : Type := Nat → Option Wait → List MRow → E → Option KRow

/-- the kept member's sample row: the form on its own table, its answer -/
def keptSample (B : Blocks) (P : Par) (z : List E) (beta : E) :
    List Mem → List E → Option (Array E × E)
  | [], _ => none
  | m :: ms, ys =>
    if m.sampled then
      match ys with
      | y :: ys' =>
        if m.kept then some ((B.sample P.fld P.C.l P.Z.l m z beta y).1, y)
        else keptSample B P z beta ms ys'
      | [] => none
    else keptSample B P z beta ms ys

/-- first(m)'s two rounds. Result: the point, the factor, the answers, the list, the rounds left. -/
def readFirst (P : Par) (m : Nat) (rs : Rs) : Option (List E × E × List E × List Nat × Rs) :=
  let ms := memsOf P.links m
  match seedOf (seedLen (lg P.C.l) (lg P.Z.l) ms) rs with
  | some (z, beta, rs1) =>
    match nextN (ms.filter (·.sampled)).length 0 (if m == 1 then 0 else P.t) rs1 with
    | some (v, rs2) => some (z, beta, v.sent, v.poss, rs2)
    | none => none
  | none => none

/-- the three folded symbols (main, old mask, fresh mask) at the first draw of the list that opens
group m's tree; nothing if there is no draw or no column -/
def yFirst (P : Par) (V : M1.View) (m : Nat) (S : KSRow) (xs : List Nat) : List E :=
  match xs.head?.bind fun x => (colAt V (m - 1) x).bind (groupCol (memsOf P.links m) 1) with
  | some c =>
    let gh := S.s.g.take (hOf (memsOf P.links m))
    [foldV P.fld S.s.g c.col.main, foldV P.fld gh c.col.mask, foldV P.fld gh c.col.fresh]
  | none => []

/-- The links. Arguments:
  todo: how many are left;
  m: the next one's number;
  prev: what the former link's fold handed on, and its kept message's sample row, if it has one;
  log: VALUES ON THE WAY, for a comparison with what another program prints (the decision does not
  read them): for each link:
    the folded symbols at the first draw of the former link's list (`yFirst`; if there is a former
    link);
    the group row's target;
    the target after its fold. -/
def goLinks (B : Blocks) (P : Par) (V : M1.View) (bt : Batch) :
    Nat → Nat → Option (KSRow × Option (Array E × E)) → Rs → List E →
    Option (Option (KSRow × Option (Array E × E)) × Rs × List E)
  | 0, _, prev, rs, log => some (prev, rs, log)
  | todo + 1, m, prev, rs, log =>
    match readFirst P m rs with
    | some (z, beta, ys, xs, rs2) =>
      match readSub B P rs2 with
      | some (F, rs3) =>
        match nextN 0 1 0 rs3 with
        | some (⟨_, [theta], _⟩, rs4) =>
          match bt m (prev.map fun S => ⟨S.1, xs, S.2⟩)
              (pscM P m F ++ samplesM B P m z beta ys) theta with
          | some R =>
            match nextN 1 1 0 rs4 with
            | some (⟨[sigma], [eps], _⟩, rs5) =>
              match takeRounds (kOf (memsOf P.links m)) rs5 with
              | some (qs, g, rs6) =>
                let S :=
                  B.foldK P.fld (kOf (memsOf P.links m)) (hOf (memsOf P.links m)) R sigma eps qs g
                goLinks B P V bt todo (m + 1) (some (S, keptSample B P z beta (memsOf P.links m) ys)) rs6 (log ++ (match prev with
                  | some S0 => yFirst P V (m - 1) S0.1 xs
                  | none => []) ++ [R.t, S.s.t])
              | none => none
            | _ => none
          | none => none
        | _ => none
      | none => none
    | none => none

/-- The last proximity test, from the last group's row on: its first stage here, the rest the first
toy's. -/
def lastTest (B : Blocks) (P : Par) (V : M1.View) (G : GRow) (rs : Rs) : Bool :=
  match P.stages with
  | s :: s' :: more =>
    match nextN 1 1 0 rs with
    | some (⟨[sigma], [eps], _⟩, rs1) =>
      match takeRounds s.k rs1 with
      | some (qs, g, rs2) =>
        match seedOf s'.na rs2 with
        | some (z, beta, rs3) =>
          match nextN 1 1 s.t rs3 with
          | some (⟨[alpha], [theta], xs⟩, rs4) =>
            match B.m1.cs P.fld s s' (B.m1.fold P.fld s.k s.h G sigma eps qs g)
                (B.m1.sample P.fld s'.Am s'.Az z beta alpha) xs theta (fun x =>
                  ((colAt V P.links x).bind (groupCol (memsOf P.links (P.links + 1)) 1)).map
                      (·.col)) with
            | some G' => iopp B.m1 P.fld V (s' :: more) (P.links + 1) 0 (2 ^ s'.k) G' rs4
            | none => false
          | _ => false
        | none => false
      | none => false
    | _ => false
  | _ => false

/-- what a closing carries on, in entries of one row of the carrying message -/
def restLen (P : Par) (kept : Bool) : Nat :=
  2 * P.Z.l + P.C.r + (if kept then P.C.r else 0) + 2 * P.Z.r + (if kept then 3 else 0)

/-- The sizes fit. -/
def sizesOK (B : Blocks) (P : Par) : Bool :=
  decide (1 ≤ P.links) && P.C.l == 2 ^ lg P.C.l && P.Z.l == 2 ^ lg P.Z.l && decide (2 ≤ lg P.C.l) &&
  decide (2 * P.V + 5 + 1 ≤ P.Z.l) && decide (restLen P (decide (1 < P.links)) + 1 ≤ P.C.l) &&
  (match P.stages.head? with
    | some s =>
      s.C == P.C && s.Z == P.Z && s.k == kOf (memsOf P.links (P.links + 1)) &&
        s.h == hOf (memsOf P.links (P.links + 1)) && s.t == P.t
    | none => false) &&
  decide (2 ≤ P.stages.length) && fitsAll B.m1 P.stages &&
  P.stages.all (fun s => s.C.l == 2 ^ lg s.C.l && s.Z.l == 2 ^ lg s.Z.l) &&
    P.stages.dropLast.all (fun s => decide (1 ≤ s.k)) &&
  (match P.stages.getLast? with
    | some s => s.k == 0 && s.h == 0
    | none => false) &&
  P.stages.dropLast.all (fun s => decide (s.h + 2 * (s.k - s.h) + 1 ≤ s.Z.l))

/-- The decision, given the blocks and a way of batching. -/
def decBy (B : Blocks) (P : Par) (V : M1.View) (bt : Batch) : Bool :=
  sizesOK B P &&
  match goLinks B P V bt P.links 1 none V.rounds [] with
  | some (some S, rs, _) =>
    match readFirst P (P.links + 1) rs with
    | some (z, beta, ys, xs, rs2) =>
      match nextN 0 1 0 rs2 with
      | some (⟨_, [theta], _⟩, rs3) =>
        match bt (P.links + 1) (some ⟨S.1, xs, S.2⟩)
            (samplesM B P (P.links + 1) z beta ys) theta with
        | some R => lastTest B P V R.toG rs3
        | none => false
      | _ => false
    | none => false
  | _ => false

/-- The decision, given the blocks. -/
def decWith (B : Blocks) (P : Par) (V : M1.View) : Bool := decBy B P V (batch B P V)

/-- how many rounds the pass takes -/
def nRounds (P : Par) : Nat :=
  ((List.range P.links).map fun i => 2 + 1 + (P.V + 3) + 1 + 1 + kOf (memsOf P.links (i + 1))).sum +
    3 + ((P.stages.dropLast.map fun s => s.k + 3).sum) + 2

#guard nRounds toyPar == 76 && nRounds tinyPar == 58
#guard (restLen toyPar true, restLen toyPar false, restLen tinyPar true, restLen tinyPar false) == (359, 283, 47, 41)

end Fmt.M2
