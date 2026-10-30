-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Job.lean: what the closing of a segment (K10) hands to a fold: the
batched row and the group's tables, as plain data. This file defines part of the honest prover.
Definitions with code; no theorem.

A fold's prover sums, over the cube of the k row variables,
   U(X) + eps ( <c(X), m(X)> + <d(X_1 .. X_h), mu(X_1 .. X_h)> X_(h+1) .. X_k
                + (1 - X_1) .. (1 - X_k) V )
(OnBytes/Iop/Fold.lean, the section "FOLD"). Of these the closing knows all but eps:
  c, d   the batched row's coefficients on the group's main table and mask table. The row is made by
         the verifier's own text of the batching (`Close.bat`, Johnson/Desc/First/Close/Closing.lean),
         called here at the statement in front of "BAT" and at the element that "BAT" drew: the
         batching is written nowhere a second time
  m, mu  the messages of the group's main rows and mask rows, each member's rows laid at the block
         that the layout names; rows that nobody sent are 0. No row's random tail is read
  V      the value of the row's forms on the kept members' own main tables
  U      its 2 k + 1 coefficients: the run that the part spends
The row's target is not among them: no message of the fold's prover reads it.

  `FoldAsk`      these, as plain data
  `MemberRows`, `GroupData`, `CloseJob`   the parameters of a place: the statement in front of "BAT"; the
                 group's rows as the prover holds them, member by member, or a refusal
  `GroupData.base`, `GroupData.zk`   the group's two codes
  `rising`, `rowsFit`, `rowsAt`   the public test that these rows fit the statement's group; an entry by the
                 oracle message's number
  `addUp`, `wordAt`, `closeMain`, `closeMask`, `closeKept`   the laying of the tables: by the library's own
                 text of where a member's rows lie in the group's tables: the group's layout is read
                 nowhere a second time (the rule for the index of a member's own table stands in
                 `wordAt`)
  `closeAsk`     the data, of a job, the input, what was shown, the challenges and the coins
  `closeCut`, `closeAtHand`, `closeAskAt`   the same at the fold's move number n: the cut of what a move
                 is handed; the test that the statement is at hand there; the data
  `FoldWords`, `foldShell`   the words, a parameter of both callers; the older caller of the fold (not the row's:
                 that is `foldShellT true`, Honest/K10/Sim.lean): the prover's side of "FOLD epsilon" and the k
                 rounds "FOLD round", general in two pure functions of these data and of the fold's
                 own challenges so far: whoever has the fold on words lays these two in

The order of U's coefficients in `FoldAsk.w` is the order of the run that is spent, which the book of
coins fixes, at every h: (1,1) (1,2) .. (k-1,1) (k-1,2) (k,0) (k,1) (k,2): the constant before the last
pair; (l,t) is the coefficient of X_l^t X_(l+1) .. X_k and (k,0) the constant. A coin's number says
nothing of the column of the fresh mask's table in which the coefficient lies: that is the packing's.

The index of a table: the row's number in the low bits: entry p of row b of a table of 2^n rows has
the index b + 2^n p (`groupIndex`, OnBytes/Iop/Ground.lean).

Limits. Each entry of a group's table is a sum over all oracle messages: for tests and laws, not for the sizes of the
programs; and this file imports the library's files of laws in which these weights are defined. Nothing ties `stAt` to a
description's state, or `rows` to what the senders of the group's messages send: these are parameters here (`rows` as a
term: Honest/K10/SegmentClosing.lean; `stAt`: a filler that is to be laid in no lot yet: see the head of
Honest/K10/StAt.lean). `FoldWords` is a parameter: the fold on words is written elsewhere (laid in:
Honest/K10/Words.lean). An entry beyond a row's message is not asked for. Where the older caller (`foldShell`) sends
zeros nothing ties what was shown to a state: whoever states a law of that part says that tie (`closeAtHand` is the test
for it); the row's part sends there what the words say at empty tables and the run (`bareAsk`, Honest/K10/Sim.lean). The
refusals that this file calls "aloud" are those of `closeAsk`, `closeAskAt` and the older caller: the row's part
(`foldShellT true`, through `askOr true`, Sim.lean) makes nothing of every one of them and sends the words at `bareAsk`.
No property of the protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Half
import Johnson.Desc.ProofFile.Honest.Sum
import Johnson.Desc.First.Close.Closing
import Johnson.Desc.Means.Says

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (E zeroE addE Statement GroupLayout ceilLog2 noId)
open VerifiableInference.Desc.First.Close (Par entries bat)

variable {W X : Type}

/-- **What a fold's prover reads**, but for eps and the rounds' challenges. -/
structure FoldAsk where
  k : Nat
  h : Nat
  /-- the row's coefficients on the group's main table, written out -/
  c : Array E
  /-- on the group's mask table -/
  d : Array E
  /-- the group's main table: the rows' messages -/
  m : Array E
  /-- the group's mask table -/
  mu : Array E
  /-- the value of the row's forms on the kept members' main tables -/
  keptV : E
  /-- the hiding polynomial's 2 k + 1 coefficients, typed at their number, in the book's order: the
  constant before the last pair (this file's head) -/
  w : Fin (2 * k + 1) → E

/-- **One member of the group, as the prover holds it**: its shape; whether it is kept; and the messages of
its main rows and of its mask rows: by row and place. No row's random tail. -/
structure MemberRows where
  shape : OnBytes.OracleShape
  kept : Bool
  main : Nat → Nat → E
  mask : Nat → Nat → E

/-- **The group's rows, as the prover holds them**: the chain's codes by which they were laid, the numbers
of the group's two codes among them, and the members in the order of sending. -/
structure GroupData where
  codes : OnBytes.Codes
  code : Nat
  maskCode : Nat
  members : List MemberRows

/-- The group's code for main rows; for mask rows. -/
def GroupData.base (R : GroupData) : OnBytes.Code := R.codes.base.getD R.code default
def GroupData.zk (R : GroupData) : OnBytes.Code := R.codes.mask.getD R.maskCode default

/-- **The parameters of a place.** -/
structure CloseJob (W : Type) where
  pub : ClosePub
  /-- the statement in front of "BAT", and the number of the segment's group: of the input, what was
  shown in front of "BAT" (a `Seen`: the rounds, and the opened columns where they are handed) and the rounds'
  challenges: these three are the field's only arguments; what its value closes over no type here says. That it reads of
  the input what is public alone is a law on a job, defined nowhere in this library, not this type's. Of the
  statement the rows' coefficients are read and no target -/
  stAt : W → Seen → List Fmt.Drawn → Except String (Statement × Nat)
  /-- The group's rows: of the input, the challenges in front of "BAT" and the carried coins. A refusal
  where something does not fit: `closeAsk` hands it on, aloud -/
  rows : W → List Fmt.Drawn → CsAll (closeCarries pub) → Except String GroupData

/-- The numbers rise strictly. -/
def rising : List Nat → Bool
  | a :: b :: l => decide (a < b) && rising (b :: l)
  | _ => true

/-- **A public test: the group's rows fit the statement's group.** The codes by which the rows were laid are
the statement's, and the two codes' numbers the group's; both codes' message lengths are powers of two
(so both codes are there: the default code that else stands in has the length 0). The group has as many
members as there are rows' members, and as many marks "kept". The members' numbers in the statement rise (the
verifier's own text lays a member into a group's list at its number's place: `Blk.join`,
OnBytes/Iop/Ground.lean; the description's: `Ground.joinP`, Johnson/Desc/First/Base/Ground.lean, over
`withMessageInGroup`, OnBytes/Slice/BlkCalls.lean): the statement numbers oracle messages as they are received, so the
group's list then stands in the order of sending, as the rows do; that is read in that text and shown by no
theorem. Member by member: the statement's shape; the group's mark "kept"; the shape names the group's code
for its main rows and the group's mask code for its mask rows. -/
def rowsFit (S : Statement) (G : OnBytes.Group) (R : GroupData) : Bool :=
  S.codes == R.codes && G.code == R.code && G.maskCode == R.maskCode &&
    OnBytes.powerOfTwo R.base.ell && OnBytes.powerOfTwo R.zk.ell &&
    rising G.members.toList &&
    G.kept.size == G.members.size &&
    R.members.length == G.members.size &&
    (G.members.toList.zipIdx.zip R.members).all fun x =>
      (S.oracles[x.1.1]?).map (·.shape) == some x.2.shape &&
        G.kept.getD x.1.2 false == x.2.kept &&
        (x.2.shape.mainRows == 0 || x.2.shape.code == G.code) &&
        (x.2.shape.maskRows == 0 || x.2.shape.maskCode == G.maskCode)

/-- **An entry of a member's rows, by the oracle message's number in the statement**: the member's place in
the statement's list of members picks it. 0 at a number that is no member's, and beyond the rows'
members. Neither is read where something is due (Honest/K10/AskLaw.lean): under `rowsFit` a member's number
reads the rows' member at its place (`rowsAt_member`); at the layout that the verifier's text makes of the
group a table reads members alone (`weight_member`); under the facts on the record in front each kept form
is on a member (`kept_on_member`). f: which rows. -/
def rowsAt (G : OnBytes.Group) (R : GroupData) (f : MemberRows → Nat → Nat → E) (o b p : Nat) : E :=
  match (G.members.idxOf? o).bind fun i => R.members[i]? with
  | some x => f x b p
  | none => zeroE

/-- The sum of f 0 .. f (n - 1), in the program's arithmetic. -/
def addUp (n : Nat) (f : Nat → E) : E := (List.range n).foldl (fun a i => addE a (f i)) zeroE

/-- **The entry at the index i of an oracle message's own table**: the row's number in the low bits. 0 at
a row that nobody sent and beyond a row's message. ell: the message length of the table's code. at_: the
entries, by the oracle message's number, the row, the place. -/
def wordAt (S : Statement) (ell : Nat) (at_ : Nat → Nat → Nat → E) (o : Nat) (part : OnBytes.Part)
    (i : Nat) : E :=
  if i % 2 ^ S.rowBits o part < OnBytes.Means.realRows S o part && i / 2 ^ S.rowBits o part < ell then
    at_ o (i % 2 ^ S.rowBits o part) (i / 2 ^ S.rowBits o part)
  else zeroE

/-- **The group's main table**: by the library's own text of where a member's rows lie in it (`mainWeight`,
`mainBack`, OnBytes/Iop/RowLaws.lean; the text of `tablesOf`, Johnson/Desc/Means/Says.lean): at the index J
the sum, over all oracle messages, of the message's own entry where the library's weight is 1 (for a
block that is aligned and inside the table: where J's row is in the message's block). w: the entries of
the messages' own main tables. -/
def closeMain (S : Statement) (L : GroupLayout) (w : Nat → Nat → E) : Array E :=
  Array.ofFn (n := 2 ^ (L.k + L.logEll)) fun J =>
    addUp S.oracles.size fun o =>
      if OnBytes.mainWeight (K := Int) S L o J.val = 1 then w o (OnBytes.mainBack S L o J.val) else zeroE

/-- **The group's mask table**: the like (`maskWeight`, `maskBack`, OnBytes/Iop/MaskLaws.lean). -/
def closeMask (S : Statement) (L : GroupLayout) (w : Nat → Nat → E) : Array E :=
  Array.ofFn (n := 2 ^ (L.h + L.logEllZk)) fun J =>
    addUp S.oracles.size fun o =>
      if OnBytes.maskWeight (K := Int) S L o J.val = 1 then w o (OnBytes.maskBack S L o J.val) else zeroE

/-- **The value of the row's forms on the kept members' own main tables.** -/
def closeKept (S : Statement) (Ks : Array OnBytes.KeptForm) (w : Nat → Nat → E) : E :=
  Ks.toList.foldl (fun s f =>
    addE s (addUp (OnBytes.Means.tableSize S f.oracle .main) fun i =>
      OnBytes.mulE (f.c.entry i) (w f.oracle i))) zeroE

/-- **What the closing hands to the fold.** seen, front: what was shown in front of "BAT", and the challenges heard
there. x: what "BAT" drew. u: the run that is spent. ca: the runs that are carried. Nothing where the statement is not
at hand (`stAt` refuses). A refusal, aloud, where something does not fit: the verifier's text of the batching refuses
(at the statement: it holds the place's count of rows against it, among others; or at x, where that has not the form of
"BAT"'s challenge: one element, no position and no matrix entry; the digest is not looked at); the layout's k and h are
not the place's; the batched row has not as many coefficients on the mask table as that table has entries; the job's
`rows` refuses; `rowsFit` says no. No entry of a table is made where one of these refuses. (The refusal on the batched
row's size is tried by no line: under the facts on the record in front it is shown not to be met:
Honest/K10/AskLaw.lean, `ask_of_base`.) (Two more refusals stand in the text and cannot be reached: the kind always has
an entry, and the batching has refused where the group is not there.) -/
def closeAsk (J : CloseJob W) (w : W) (seen : Seen) (front : List Fmt.Drawn) (x : Fmt.Drawn)
    (u : Fin (2 * J.pub.par.k + 1) → E) (ca : CsAll (closeCarries J.pub)) :
    Except String (Option FoldAsk) := do
  let eB ← match (entries J.pub.par).head? with
    | some e => pure e
    | none => throw "K10: no entry"
  match J.stAt w seen front with
  | .error _ => pure none
  | .ok (S, g) =>
    let (row, L, S1) ← (bat S g eB ⟨[], x⟩).mapError fun e =>
      "K10: the verifier's batching refuses: " ++ e
    if L.k != J.pub.par.k || L.h != J.pub.par.h then
      throw "K10: the layout's k, h are not the place's"
    if row.d.size != 2 ^ (L.h + L.logEllZk) then
      throw "K10: the batched row does not fit the mask table"
    let G ← match S.groups[g]? with
      | some G => pure G
      | none => throw "K10: no group"
    let R ← J.rows w front ca
    if !rowsFit S G R then throw "K10: the group's rows do not fit the statement's group"
    let mainW := fun o => wordAt S1 R.base.ell (rowsAt G R (·.main)) o .main
    let maskW := fun o => wordAt S1 R.zk.ell (rowsAt G R (·.mask)) o .mask
    pure (some
      { k := J.pub.par.k, h := J.pub.par.h
        c := row.c.writeOut (L.k + L.logEll), d := row.d
        m := closeMain S1 L mainW, mu := closeMask S1 L maskW
        keptV := closeKept S1 row.kept mainW
        w := u })

/-- **What stands in front of "BAT", cut off what the fold's move number n is handed**, n from 0 ("FOLD epsilon"): the
last n challenges heard are the fold's own (eps first), the one in front of them is "BAT"'s; so with the rounds shown.
-/
def closeCut (n : Nat) (s : Seen) (t : State W X) : Seen × List Fmt.Drawn :=
  (s.front (n + 1), t.heard.take (t.heard.length - (n + 1)))

/-- **The statement is at hand at the fold's move number n**: `stAt` yields one at the state's input and the cut pair.
A test with code, for whoever states a law of the part: where it says no the older caller (`foldShell`) sends zeros,
unless `closeAskAt` has refused first ("BAT"'s challenge not yet heard, or one of the fold's own challenges without its
form): then it refuses. The row's part sends the words at `bareAsk` in both cases. -/
def closeAtHand (J : CloseJob W) (n : Nat) (s : Seen) (t : State W X) : Bool :=
  match J.stAt t.input (closeCut n s t).1 (closeCut n s t).2 with
  | .ok _ => true
  | .error _ => false

/-- **What the closing hands to the fold, at the fold's move number n**, from 0 ("FOLD epsilon"): of what
a move is handed: `closeAsk` at `closeCut`'s pair and at "BAT"'s challenge. It yields the data and the
fold's own challenges so far, as elements; nothing and a refusal as `closeAsk`; a refusal too where
"BAT"'s challenge has not been heard, and where one of the fold's own challenges so far has not drawn
just one element. -/
def closeAskAt (J : CloseJob W) (n : Nat)
    (c : Handed ⟨0, 0⟩ (closeSpends J.pub.par) (closeCarries J.pub)) (s : Seen) (t : State W X) :
    Except String (Option (FoldAsk × List E)) :=
  let a := t.heard.length - (n + 1)
  let u : Cs ⟨0, 2 * J.pub.par.k + 1⟩ × Unit := c.2.1
  match (t.heard.drop a).head? with
  | some x =>
    if t.heard.length < n + 1 then .error "K10: the challenge of BAT has not been heard"
    else if !(t.lately n).all (·.elems.length == 1) then
      .error "K10: a challenge of the fold has not its form"
    else
      (closeAsk J t.input (closeCut n s t).1 (closeCut n s t).2 x
        (fun i => E.ofTriple (OnBytes.Slice.ofE (u.1.e i))) c.2.2).map fun A =>
          A.map fun A => (A, drawnE (t.lately n))
  | none => .error "K10: the challenge of BAT has not been heard"

/-! ### The caller of the fold -/

/-- **What the fold's rounds send, as two pure functions** of what the closing hands over. -/
structure FoldWords where
  /-- "FOLD epsilon": the one scalar -/
  sigma : FoldAsk → E
  /-- a "FOLD round": of the data, what "FOLD epsilon" drew, and what the rounds "FOLD round" in front
  of this one drew: the two scalars: the round polynomial's constant and quadratic coefficients -/
  round : FoldAsk → E → List E → E × E

/-- **The older caller. Not the row's**: that is `foldShellT true` (Honest/K10/Sim.lean). The prover's side of
"FOLD epsilon" and k times "FOLD round" at a place: each move makes the data by `closeAskAt` and sends what F says of
them. It spends the kind's one run and carries the kind's runs; no stop. Where the statement is not at hand (`stAt`
refuses) it sends zeros of the round's shape: a law that binds the stand freely wants a value there. All of
`closeAskAt`'s refusals stay refusals: public data that do not fit; a stand at which "BAT"'s challenge has not been
heard, or has not its form; one of the fold's own challenges that has not drawn just one element. What a law of this
older part carries for the zeros: `closeAtHand`. Where the list of the fold's own challenges is empty the factor is laid
0 (`headD zeroE`): not met, for `closeAskAt` yields as many as the move's number (by reading; no theorem). -/
def foldShell {V W X : Type} (J : CloseJob W) (F : FoldWords) : Part V W X :=
  { takes := ⟨0, 0⟩, spends := closeSpends J.pub.par, carries := closeCarries J.pub
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves :=
      ⟨fun c s t => (closeAskAt J 0 c s t).map fun
          | some y => sayE [F.sigma y.1]
          | none => sayE [zeroE], fun t => t.own⟩ ::
      (List.range J.pub.par.k).map fun j =>
        ⟨fun c s t => (closeAskAt J (j + 1) c s t).map fun
            | some y =>
              let q := F.round y.1 (y.2.headD zeroE) (y.2.drop 1)
              sayE [q.1, q.2]
            | none => sayE [zeroE, zeroE], fun t => t.own⟩ }

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.FoldAsk
#print axioms ProofFile.Honest.K10.MemberRows
#print axioms ProofFile.Honest.K10.GroupData
#print axioms ProofFile.Honest.K10.GroupData.base
#print axioms ProofFile.Honest.K10.GroupData.zk
#print axioms ProofFile.Honest.K10.CloseJob
#print axioms ProofFile.Honest.K10.rising
#print axioms ProofFile.Honest.K10.rowsFit
#print axioms ProofFile.Honest.K10.rowsAt
#print axioms ProofFile.Honest.K10.addUp
#print axioms ProofFile.Honest.K10.wordAt
#print axioms ProofFile.Honest.K10.closeMain
#print axioms ProofFile.Honest.K10.closeMask
#print axioms ProofFile.Honest.K10.closeKept
#print axioms ProofFile.Honest.K10.closeAsk
#print axioms ProofFile.Honest.K10.closeCut
#print axioms ProofFile.Honest.K10.closeAtHand
#print axioms ProofFile.Honest.K10.closeAskAt
#print axioms ProofFile.Honest.K10.FoldWords
#print axioms ProofFile.Honest.K10.foldShell
