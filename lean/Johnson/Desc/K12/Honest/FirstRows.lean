-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/FirstRows.lean: `hy_atFirst` (Johnson/Desc/K12/Honest/FirstReads.lean), the
theorem on what the first code switch of a proximity test reads, with the prover's data as plain
functions of numbers. There the members' messages and tails are functions on the index types of a
group, `GroupAt hok`, whose type depends on a proof, hok. A sender, the prover's text for the
sub-protocol that sends oracle messages (Johnson/Prover/Send/Core.lean), has its rows by number
(`Rows`) and writes columns (`col`). Here the rows are one structure of plain functions,
`PlainRows`, and what `hy_atFirst` assumes of the prover's data is one proposition on plain data,
`ColsAt`. Its clauses on the rows go seat by seat, so that whoever proves them can start from lemmas
on a sender's written columns; this file has no such lemma. General in every parameter of
`hy_atFirst` but its messages and tails, and in the rows. `hy_atFirst_test`
(Johnson/Desc/K12/Honest/FirstTest.lean) calls the main theorem, `first_V`
(Johnson/Desc/K12/Honest/FirstValues.lean) the three theorems `cols_main`, `cols_mask` and
`cols_fresh`. Definitions, and theorems with their proofs. It does not depend on the frame for an
honest side (Johnson/Desc/ProofFile/Honest/Frame.lean).

In the list and below: p (`P12`, Johnson/Desc/K12/Frame.lean) holds the numbers of the place of the
test. a and next (`Fmt.M1.Stage`) are the first and the second stage, rest the stages after them.
`a.C` is the code of a main row, `a.Z` the code of a mask row. `sg a`
(Johnson/Desc/K12/Law/FirstOkLaw.lean) and `sgOf a` (Johnson/Desc/K12/Law/ChainOf.lean) are a in the
library's form (`Sg`), with the numbers h and g = k - h. A code (`Fmt.M1.Code`) has messages of l
entries and tails of r entries. K, P, D and o are parameters of the states `t1At` and `t3At` named
below; D n is what round number n samples. Dp (`Plain`, Johnson/Desc/K12/Law/FirstOk.lean) are the
plain data of the group under test: among them a book (`TreeBook`, OnBytes/Iop/Ground.lean: the
trees, and for each oracle message its tree and its part of that tree), the members `mems`, the
fresh table `fresh`, and the places `ts` of their trees. A tree's place is its index in
`book.trees`. A seat (`Seat1`, FirstOk.lean) is an oracle message as a part of a tree: its shape
`sh`, its tree's place `t` and shape `tsh`, and the number `part` of its part. Each member and the
fresh table is a seat. c u x is the column, a list of words, of the tree at the place u at the
position x. The first skip of a seat s is `skM s.tsh s.part`, the second `skZ s.tsh s.part`
(FirstOk.lean): the numbers of the words at which the main symbols and the mask symbols of the
seat's part begin in a column. The fresh table's seat's skip is its `skZ`. A row's symbol at a
position is `symG` (Johnson/Prover/Link/Base.lean) of the row's code, the position, the row's
message and its tail. `read1` reads one word of a column as an element of the base field, `read3`
three words as an element of the extension field (Johnson/Desc/K12/Honest/Written.lean). hok is a
proof that Dp passes the library's test `gpL` (FirstOk.lean). `GroupAt hok` and `DataAt hok`
(FirstReads.lean) are the library's group and its public data, made of Dp.

  `hy_atFirst_rows`: `hy_atFirst` at plain rows, with `ColsAt` in the place of its hypotheses hw,
    hMain, hMask and hF on the prover's data. The conclusion is that of `hy_atFirst` at the messages
    `msgsOf R hok`, the tails `tailsOf R hok` and, for the fresh table, `freshOf R (sg a)` and
    `freshTlOf R (sg a)`. There are `rows`, `gp`, `out`, `row'`, `lay'`, `theta` and `Dk` such that:
    `t1At`, the state after the fold, passes the single rows `rows` with the number `gp`; `Did`
    (Johnson/Desc/K12/Law/SwDid.lean: what a switch and the batching after it have done) holds of
    them, from `t1At` to `t3At`, the state after that batching (both
    Johnson/Desc/K12/Honest/FirstYes.lean); `t3At` passes the claim of `row'` with `lay'`; and the
    last clause: for every Qs that lists the positions `Dk.rC.drawn.poss`, every i and every α,
    `(sg a).cMid.T` of the code word `(sg a).cMid.enc` of `foldMsg` and `foldTl`
    (Johnson/Prover/Link/FoldEnc.lean), taken at `Qs i` and α, is
    `symS (sg a) rows out.positions Dk.y` (OnBytes/Slice/BlkRead.lean) at that position and α.
    `foldMsg` and `foldTl` are at these messages and tails, put on the stage's tables by `layJ` and
    `layQ` (Johnson/Desc/K12/Honest/Group.lean), and at the point `aPoint a o D`
    (Johnson/Desc/K12/Honest/Stages.lean). The head of FirstReads.lean says more on each clause
  `ColsAt a Dp c R`: every tree's column has the book's width · `MemAt` at every member's seat and
    every position of its tree · the fresh table's rows' symbols stand behind its seat's skip. In
    Lean, a structure of three fields. `width`: at every place u in `Dp.ts` and every x below
    `2 ^ logAt Dp.book u`, the column c u x has `widthAt Dp.book u` words (`logAt`, `widthAt`:
    FirstOk.lean). `mem`: for every member, with its number j in `Dp.mems`, and every x below 2 to
    the `tsh.logN` of its seat: `MemAt` at that seat, at j and at x, for the column of the seat's
    tree at x. `fresh`: for every x below 2 to `Dp.fresh.tsh.logN` and every b below `2 ^ a.h`:
    `read3` of the column of the fresh table's tree at x, at word
    `skZ Dp.fresh.tsh Dp.fresh.part + 3 * b`, is `symG a.Z (x % 2 ^ a.Z.a) (R.F b) (R.FT b)`
  `MemAt a col R s j x`: at one seat and one position: the seat's main rows' symbols stand behind
    the seat's first skip (one word each over the base field, else three), its mask rows' behind the
    second. In Lean, a structure of two fields. `main`: for every i below `s.sh.mainRows`,
    `symG a.C x (R.M j i) (R.T j i)` is `read1 col` at word `skM s.tsh s.part + i` where
    `s.sh.mainDeg` is 1, else `read3 col` at word `skM s.tsh s.part + 3 * i`. `mask`: for every i
    below `s.sh.maskRows`, `symG a.Z (x % 2 ^ a.Z.a) (R.Z j i) (R.ZT j i)` is `read3 col` at word
    `skZ s.tsh s.part + 3 * i`
  `PlainRows`: the prover's rows as plain functions of numbers: for each member its main rows, their
    tails, its mask rows, their tails; the fresh table's rows and tails. A structure; its fields, in
    this order: M, T, Z, ZT, F, FT
  `msgsOf`, `tailsOf`, `freshOf`, `freshTlOf`: definitions: these rows as the arguments of
    `hy_atFirst` for the members' messages, the members' tails, the fresh table's message and its
    tails. A row of the fresh table is indexed there by h bits; its number is `Sz.rowNo`
    (OnBytes/Slice/LinkAt.lean)
  `cols_main`, `cols_mask`, `cols_fresh`: `ColsAt` gives the hypotheses hMain, hMask and hF of
    `hy_atFirst` at these arguments, word for word
  `symG_ext0`: `symG` at a message and a tail that are cut at the code's l and r and go on with 0
    (`ext0`, Johnson/Prover/Link/SymTie.lean) is `symG` at the message and the tail themselves

By what. `hy_atFirst_rows` is one call of `hy_atFirst`, with the field `width` of `ColsAt` for hw
and the three theorems `cols_main`, `cols_mask`, `cols_fresh`. Each of these is a field of `ColsAt`
(for the first two: `mem`, then a field of `MemAt`) followed by `symG_ext0`; that the depths, codes,
numbers of rows and offsets in `GroupAt hok` and `DataAt hok` are the seats' holds by unfolding
`gpG`, `gpP` and `mbOf` (FirstOkLaw.lean). `cols_fresh` takes b below `2 ^ a.h` from `rowNo_lt`
(OnBytes/Slice/Cells.lean). `symG_ext0` is `symG_congr` (Base.lean).

Hypotheses of `hy_atFirst_rows`. All but hC are hypotheses of `hy_atFirst`, word for word.
  he, h1: the masks come early and a sample has one answer. In Lean: `p.early = true` and
    `p.answers = 1`
  hl: the declared rounds l are `laidS p` (Johnson/Desc/K12/Law/ReadsK.lean): the place's own,
    without the first
  hp: t (`T12`, Johnson/Desc/K12/Join.lean), the state before the fold, passes a claim: row with the
    layout L
  hD, hok: `gpOf p t a L` (FirstOk.lean) returns Dp, and Dp passes every clause of `gpL`
  hhk, hs: `a.h ≤ a.k`; the stage's sizes meet `Sg.Sized` (OnBytes/Slice/Numbers.lean)
  hcu, hnx: `stageAt` (Join.lean) returns cu for a at the number 0 and nx for next at the number 1
  hcode: in the statement of `t1At` the base code number `cu.code` has `logN = a.C.a`
  hC: `ColsAt a Dp c R`
  Y: `FirstYes` (FirstYes.lean) at the trees `groupTrees Dp.ts (logAt Dp.book) c`
    (Johnson/Desc/K12/Honest/GroupState.lean): among its fields, that the fold, the switch and the
    batching after it accept
  hr, ht: the positions that round number o + 2 + (h + g) samples are below `2 ^ a.C.a`, and they
    are `a.t` many

Limits. `ColsAt` is a hypothesis; it is not shown here. It speaks of the prover's data at every
position of every tree that it names, not at the sampled positions only. The acceptances in
`FirstYes` are hypotheses too, not shown. No value that meets all hypotheses is given in this file.
Rows are read below their codes' lengths only: `symG` adds up a message's places below the code's l
and a tail's below r, and `msgsOf` and the three definitions after it are functions on these places.
At a stage that samples no position the last clause of `hy_atFirst_rows` is vacuous. Nothing on
completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.FirstReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)

/-- The prover's rows, as plain functions. Member, row, place; for the fresh table: row, place.
M, T: a member's main rows and their tails. Z, ZT: its mask rows and their tails. F, FT: the fresh
table's rows and their tails. -/
structure PlainRows where
  M : ℕ → ℕ → ℕ → GE
  T : ℕ → ℕ → ℕ → GE
  Z : ℕ → ℕ → ℕ → GE
  ZT : ℕ → ℕ → ℕ → GE
  F : ℕ → ℕ → GE
  FT : ℕ → ℕ → GE

section Letters
variable {p : P12} {a : Fmt.M1.Stage} {row : GroupRow} {Dp : Plain} (R : PlainRows)
  (hok : ok (gpL p a row Dp) = true)

/-- The members' messages made of R: main rows from `R.M`, mask rows from `R.Z`. -/
def msgsOf : (GroupAt hok).Msgs := fun j e =>
  match e with
  | .inl x => R.M (j : Fin Dp.mems.length).val x.1.val x.2.val
  | .inr x => R.Z (j : Fin Dp.mems.length).val x.1.val x.2.val

/-- The members' tails made of R: the main rows' from `R.T`, the mask rows' from `R.ZT`. -/
def tailsOf : Tails (GroupAt hok) := fun j e =>
  match e with
  | .inl x => R.T (j : Fin Dp.mems.length).val x.1.val x.2.val
  | .inr x => R.ZT (j : Fin Dp.mems.length).val x.1.val x.2.val

end Letters

/-- The fresh table's message made of R: from `R.F`, at the row's number `Sz.rowNo`. -/
def freshOf (R : PlainRows) (s : Sg) : s.cFr.J → GE := fun x => R.F (Sz.rowNo x.1) x.2.val
/-- The fresh table's tails made of R: from `R.FT`, at the row's number `Sz.rowNo`. -/
def freshTlOf (R : PlainRows) (s : Sg) : s.cFr.Q → GE := fun x => R.FT (Sz.rowNo x.1) x.2.val

theorem symG_ext0 (C : Fmt.M1.Code) (x : ℕ) (f g : ℕ → GE) :
    symG C x (ext0 fun e : Fin C.l => f e.val) (ext0 fun q : Fin C.r => g q.val) = symG C x f g :=
  symG_congr C x _ _ _ _ (fun _ hj => dif_pos hj) fun _ hq => dif_pos hq

/-- One seat's rows at one position. col: the column of the seat's tree at x. j: the member's
number. -/
structure MemAt (a : Fmt.M1.Stage) (col : List UInt64) (R : PlainRows) (s : Seat1) (j x : ℕ) :
    Prop where
  main : ∀ i, i < s.sh.mainRows →
    (if s.sh.mainDeg == 1 then read1 col (skM s.tsh s.part + i)
      else read3 col (skM s.tsh s.part + 3 * i)) = symG a.C x (R.M j i) (R.T j i)
  mask : ∀ i, i < s.sh.maskRows →
    read3 col (skZ s.tsh s.part + 3 * i) = symG a.Z (x % 2 ^ a.Z.a) (R.Z j i) (R.ZT j i)

/-- The hypothesis on the prover's data. c u x: the column of the tree at the place u at x. -/
structure ColsAt (a : Fmt.M1.Stage) (Dp : Plain) (c : ℕ → ℕ → List UInt64) (R : PlainRows) :
    Prop where
  width : ∀ u ∈ Dp.ts, ∀ x, x < 2 ^ logAt Dp.book u → (c u x).length = widthAt Dp.book u
  mem : ∀ (j : Fin Dp.mems.length) (x : ℕ), x < 2 ^ (Dp.mems.get j).tsh.logN →
    MemAt a (c (Dp.mems.get j).t x) R (Dp.mems.get j) j.val x
  fresh : ∀ x, x < 2 ^ Dp.fresh.tsh.logN → ∀ b, b < 2 ^ a.h →
    read3 (c Dp.fresh.t x) (skZ Dp.fresh.tsh Dp.fresh.part + 3 * b) =
      symG a.Z (x % 2 ^ a.Z.a) (R.F b) (R.FT b)

section Cols
variable {p : P12} {a : Fmt.M1.Stage} {row : GroupRow} {Dp : Plain} {c : ℕ → ℕ → List UInt64}
  {R : PlainRows} (hC : ColsAt a Dp c R) (hok : ok (gpL p a row Dp) = true)
include hC

theorem cols_main : ∀ j x, x < 2 ^ ((GroupAt hok).mb j).a → ∀ i : Fin ((GroupAt hok).mb j).nM,
    (if ((DataAt hok).lay j).base then
        read1 (c ((DataAt hok).tp j) x) (((DataAt hok).lay j).oM + i.val)
      else read3 (c ((DataAt hok).tp j) x) (((DataAt hok).lay j).oM + 3 * i.val)) =
      symG ((GroupAt hok).mb j).C x (ext0 fun e => msgsOf R hok j (.inl (i, e)))
        (ext0 fun q => tailsOf R hok j (.inl (i, q))) := fun j x hx i =>
  ((hC.mem j x hx).main i.val i.isLt).trans
    (symG_ext0 a.C x (R.M j.val i.val) (R.T j.val i.val)).symm

theorem cols_mask : ∀ j x, x < 2 ^ ((GroupAt hok).mb j).a → ∀ i : Fin ((GroupAt hok).mb j).nZ,
    read3 (c ((DataAt hok).tp j) x) (((DataAt hok).lay j).oZ + 3 * i.val) =
      symG ((GroupAt hok).mb j).Z (x % 2 ^ ((GroupAt hok).mb j).Z.a)
        (ext0 fun e => msgsOf R hok j (.inr (i, e)))
        (ext0 fun q => tailsOf R hok j (.inr (i, q))) := fun j x hx i =>
  ((hC.mem j x hx).mask i.val i.isLt).trans
    (symG_ext0 a.Z _ (R.Z j.val i.val) (R.ZT j.val i.val)).symm

theorem cols_fresh : ∀ x, x < 2 ^ (DataAt hok).aF → ∀ b : Fin (sg a).h → Bool,
    read3 (c (DataAt hok).ft x) ((DataAt hok).oF + 3 * Sz.rowNo b) =
      symG (sg a).Z (x % 2 ^ (sg a).Z.a) (ext0 fun e => freshOf R (sg a) (b, e))
        (ext0 fun q => freshTlOf R (sg a) (b, q)) := fun x hx b =>
  (hC.fresh x hx (Sz.rowNo b) (rowNo_lt b)).trans
    (symG_ext0 a.Z _ (R.F (Sz.rowNo b)) (R.FT (Sz.rowNo b))).symm

end Cols

/-- **What the first switch reads, at plain rows.** -/
theorem hy_atFirst_rows (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (a next : Fmt.M1.Stage)
    (l : Laid) (o : ℕ) (t : T12) (P : PS) (D : ℕ → Fmt.Drawn)
    (he : p.early = true) (h1 : p.answers = 1)
    (hl : l = laidS p)
    (row : GroupRow) (L : GroupLayout) (hp : t.pass = .claim row L)
    (Dp : Plain) (hD : gpOf p t a L = some Dp) (hok : ok (gpL p a row Dp) = true)
    (hhk : a.h ≤ a.k) (hs : (sg a).Sized)
    (cu nx : IoppStage) (hcu : stageAt p 0 a = some cu) (hnx : stageAt p 1 next = some nx)
    (hcode : ((t1At p K 0 a l o t P D).st.codes.base[cu.code]?).map (·.logN) = some a.C.a)
    (c : ℕ → ℕ → List UInt64) (R : PlainRows) (hC : ColsAt a Dp c R)
    (Y : FirstYes p K rest 0 a next l o t P (groupTrees Dp.ts (logAt Dp.book) c) D)
    (hr : ∀ x ∈ (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss, x < 2 ^ a.C.a)
    (ht : (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss.length = a.t) :
    ∃ (rows : SingleRows) (gp : ℕ) (out : Switched) (row' : GroupRow) (lay' : GroupLayout)
      (theta : E) (Dk : Taken),
      (t1At p K 0 a l o t P D).pass = .single rows gp ∧
      Did p.nums.firstTree
        (keyed p (((l.drop (1 + a.k)).take 2).map (·.1))
          (aGroups a o (groupTrees Dp.ts (logAt Dp.book) c) D)) rows
        (switchTargetStage nx.code nx.maskCode nx.k nx.h 1) gp (othersOf rest.isEmpty nx)
        (t1At p K 0 a l o t P D).st (t1At p K 0 a l o t P D).book (t1At p K 0 a l o t P D).roots
        (t3At p K rest 0 a next l o t P (groupTrees Dp.ts (logAt Dp.book) c) D).st
        (t3At p K rest 0 a next l o t P (groupTrees Dp.ts (logAt Dp.book) c) D).book out row' lay'
        theta Dk ∧
      (t3At p K rest 0 a next l o t P (groupTrees Dp.ts (logAt Dp.book) c) D).pass =
        .claim row' lay' ∧
      (∀ (Qs : Fin (sg a).t → (sg a).Ps),
        (∀ i, (Qs i).val = Dk.rC.drawn.poss.getD i.val 0) →
        ∀ i α, (sg a).cMid.T ((sg a).cMid.enc
            (foldMsg (sg a) (layJ (GroupAt hok) (msgsOf R hok)) (freshOf R (sg a)) (aPoint a o D))
            (foldTl (sg a) (layQ (GroupAt hok) (tailsOf R hok)) (freshTlOf R (sg a))
              (aPoint a o D)))
            (Qs i) α = symS (sg a) rows out.positions Dk.y (Qs i).val α) :=
  hy_atFirst p K rest a next l o t P D he h1 hl row L hp Dp hD hok hhk hs cu nx hcu hnx hcode c
    hC.width Y hr ht (msgsOf R hok) (tailsOf R hok) (freshOf R (sg a)) (freshTlOf R (sg a))
    (cols_main hC hok) (cols_mask hC hok) (cols_fresh hC hok)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.symG_ext0
#print axioms ProofFile.Honest.K12.cols_main
#print axioms ProofFile.Honest.K12.cols_mask
#print axioms ProofFile.Honest.K12.cols_fresh
#print axioms ProofFile.Honest.K12.hy_atFirst_rows
#print axioms ProofFile.Honest.K12.PlainRows
#print axioms ProofFile.Honest.K12.msgsOf
#print axioms ProofFile.Honest.K12.tailsOf
#print axioms ProofFile.Honest.K12.freshOf
#print axioms ProofFile.Honest.K12.freshTlOf
#print axioms ProofFile.Honest.K12.MemAt
#print axioms ProofFile.Honest.K12.ColsAt
