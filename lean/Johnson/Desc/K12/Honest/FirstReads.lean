-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/FirstReads.lean: what the first code switch reads, at the term's own pieces,
from acceptances and one public test. The term is `stagesAll` (Johnson/Desc/K12/Honest/Stages.lean):
a definition of the rounds, the trees and the groups of opened columns of a proximity test's stages.
Its pieces at the first stage have names in Johnson/Desc/K12/Honest/FirstYes.lean. `hy_group`
(Johnson/Desc/K12/Honest/GroupReads.lean) says what the first switch reads of a group of several
members in several trees, under a long list of hypotheses. The main theorem here, `hy_atFirst`, has
the conclusion of `hy_group` at the term's pieces and derives most of these hypotheses from others,
so that they are seen to hold together wherever the hypotheses of `hy_atFirst` hold. General in the
place's numbers, the two stages, the verifier's state before the fold, the group's layout and the
trees' columns. Theorems with their proofs, and definitions. It does not depend on the frame for an
honest side (Johnson/Desc/ProofFile/Honest/Frame.lean).

In the list and below: p (`P12`, Johnson/Desc/K12/Frame.lean) holds the numbers of the place of the
test. a and next (`Fmt.M1.Stage`) are the first and the second stage, rest the stages after them.
`sg a` (Johnson/Desc/K12/Law/FirstOkLaw.lean) and `sgOf a` (Johnson/Desc/K12/Law/ChainOf.lean), two
definitions with one text, are the sizes of a in the library's form (`Sg`): the codes C and Z, the
numbers h and g = k - h, and the number of positions. t (`T12`, Johnson/Desc/K12/Join.lean) is the
verifier's state before the fold. It has a statement `st`, a book `book` (`TreeBook`,
OnBytes/Iop/Ground.lean: the trees sent so far, and for each oracle message its tree and its part of
that tree) and the field `pass`: what one part of the test passes to the next. After a batching that
is a claim, a row (`GroupRow`) with a layout (`GroupLayout`); after a fold, the single rows
(`SingleRows`, OnBytes/Iop/Fold.lean) and the new group's number. A tree's place is its index in
`book.trees`. K (`BCoins`, Johnson/Prover/Link/BodyAll.lean), P (`PS`,
Johnson/Prover/Link/BodyState.lean) and D are parameters of the term; D n is what round number n
samples. o is the number of the stage's first round. The pieces, written here without their
arguments: `rfAt` are the fold's rounds, `t1At` is the verifier's state after the fold, `t3At` the
one after the switch and the batching after it. Dp (`Plain`, Johnson/Desc/K12/Law/FirstOk.lean) are
the group's plain data: the statement and the book after the fresh table has entered, the layout,
the members and the fresh table, each as a part of a tree (`Seat1`), the trees' places `ts` and the
declared openings. The fresh table is `Dp.fresh`; the library's text calls it the first fold's mask
(`entered`, same file). c u x is the column, a list of words, of the tree at the place u at the
position x.

  `hy_atFirst`: under the hypotheses below there are `rows`, `gp`, `out`, `row'`, `lay'`, `theta`
    and `Dk` such that: `t1At` passes the single rows `rows` with the number `gp`; `Did`
    (Johnson/Desc/K12/Law/SwDid.lean: what a switch and the batching after it have done) holds of
    them, from the statement, the book and the count of roots of `t1At` to the statement and the
    book of `t3At`, on the term's groups of columns (`aGroups`, Stages.lean) with the keys of
    `keyed` (Join.lean); `t3At` passes the claim of `row'` with `lay'`; and at each sampled position
    the code word of (`foldMsg`, `foldTl`) at the members' messages and tails, folded at the term's
    own point (`aPoint`), shows what was read. In Lean, the last clause: for every Qs that lists the
    positions `Dk.rC.drawn.poss`, every i and every coordinate α of a long symbol: `(sg a).cMid.T`
    of the code word `(sg a).cMid.enc` of `foldMsg` and `foldTl` (Johnson/Prover/Link/FoldEnc.lean),
    at `Qs i` and α, is `symS (sg a) rows out.positions Dk.y` (OnBytes/Slice/BlkRead.lean) at that
    position and α. `cMid` (OnBytes/Slice/Stage.lean) is the code of the three folded rows.
    `foldMsg` is taken at `layJ` of m and at φ, `foldTl` at `layQ` of r and at ψ (`layJ`, `layQ`:
    Johnson/Desc/K12/Honest/Group.lean), both at `aPoint a o D`
  `fresh_long`: the library's test on the plain data asks that the mask code is not longer than the
    fresh table's tree. In Lean: where Dp passes `gpL`, `a.Z.a ≤ Dp.fresh.tsh.logN`: the clause
    "f:zshort"
  `gammaAt`, `point_gammaAt`: a definition: of each of the fold's rounds but the first, with its
    digest removed (`noDigest`, Johnson/Desc/Block.lean), the element that it sampled first
    (`drawnOf`, Johnson/Prover/Link/FormFold.lean). The theorem: read as a point of h + g
    coordinates (`readP`, OnBytes/Slice/ProgField.lean), these elements are `aPoint` (Stages.lean),
    the point at which the term folds. At every stage number j; no hypothesis
  `dTree a W`, `dBook book u`: definitions: a round's data (`PQ.RD`, Run/PlanQTypes.lean) with a
    tree of the depth a and the width W; its other fields are fixed: an entry with an empty name,
    the kind `.elems`, no item, no opening, the tree number 0. The same at the depth and the width
    that the book states for the tree at the place u (`logAt`, `widthAt`, FirstOk.lean; both 0 where
    the book has no tree there)
  `GroupAt hok`, `DataAt hok`: definitions: the library's group (`gpG`) and its public data (`gpP`,
    both FirstOkLaw.lean), made of plain data Dp that pass `gpL`. All radii are 0. The rounds' data
    of the members' trees and of the fresh table's tree are `dBook Dp.book` at these trees' places

By what. `hy_atFirst` ends in a call of `hy_group` at `GroupAt hok` and `DataAt hok`, and derives
that theorem's other hypotheses as follows. `made_of` and `first_at` (FirstOkLaw.lean) give
`GpData.Pub` and `GpData.LayG` (OnBytes/Slice/BlkProxGp.lean), that the claim's row has no kept
form, and, with `OpensAre.keys` (Johnson/Desc/K12/Law/FirstSrc.lean), the keys of the declared
openings. Where a part accepts, the term's state is what the part returns (`getD_of_ok`,
Johnson/Prover/Link/BodyYes.lean). `fold_exact` (Johnson/Desc/K12/Honest/FirstSeenExact.lean) turns
the fold's acceptance into the state after the fold and the single rows that it passes, so that "the
old rows are the first fold's output" holds at the point at which the term folds (`point_gammaAt`;
the number of rounds: `length_aFold`, Johnson/Desc/K12/Honest/Causal.lean). By `entered_of_case`
(FirstOkLaw.lean) the fresh table that the fold took, with the statement and the book after its
entering, is the plain data's. The members' and the fresh table's places (`PartsP`,
Johnson/Desc/K12/Law/FirstRead.lean) at the state before the switch come from the state after the
table's entering, through the fold (`Part1P.keeps`, same file; `shapes_spent`, FirstSeenExact.lean).
`switchUnfolds` (Johnson/Desc/K12/Law/SwUnfold.lean), after `ranged_ok`
(Johnson/Desc/K12/Law/BaseGives.lean), turns the acceptances of the switch and of the batching after
it into `Did`. `pos_groups` and `cols_groups` (Johnson/Desc/K12/Honest/GroupState.lean) give the two
hypotheses on the dealt groups; the columns' widths come from hw and `keyAt_of` (FirstOkLaw.lean).
The two hypotheses on the rounds' data hold by unfolding `DataAt`. hcode and `Did.code` give the
depth of the old rows' code. Derived too: that the mask code is not longer than the fresh table's
tree (`fresh_long`: a clause of the library's test). `point_gammaAt` rewrites by `point_eq`,
`fold_eq` (Stages.lean) and `gam_at` (Johnson/Prover/Link/BodyStepAt.lean).

Hypotheses of `hy_atFirst`. Called public here: he to hcode. They speak of the place's numbers, the
stages and the verifier's states; hcode is stated at `t1At`, which is an expression in K, P and D
too.
  he, h1: the masks come early and a sample has one answer. In Lean: `p.early = true` and
    `p.answers = 1`
  hl: the declared rounds l are the place's own, without the first: `laidS p`
    (Johnson/Desc/K12/Law/ReadsK.lean)
  hp: t passes a claim, as a state after the batching does: row with the layout L
  hD, hok: the one public test: `gpOf p t a L` returns Dp, and Dp passes every clause of `gpL` (both
    FirstOk.lean). `gpOk` (same file), which the batching's part of `guardedProximityTestParts` asks in its guard (g)
    (Johnson/Desc/K12/JoinGuarded.lean), is this test at the first stage in `p.nums.stages`. That a is
    that stage is no hypothesis here
  hhk, hs: `a.h ≤ a.k`; the stage's sizes meet `Sg.Sized` (OnBytes/Slice/Numbers.lean)
  hcu, hnx: `stageAt` (Join.lean) returns cu for a as stage number 0 and nx for next as stage number
    1: `p.idx` has a pair of code numbers for each
  hcode: after the fold the first stage's main code has the stage's depth in the state's list of
    codes: in the statement of `t1At` the base code number `cu.code` has `logN = a.C.a`
  Y: the acceptances: `FirstYes` (FirstYes.lean) at the trees `groupTrees Dp.ts (logAt Dp.book) c`
    (GroupState.lean): the fold, the switch and the batching after it accept the term's own rounds
    and groups. Of the fields of `FirstYes` the proof uses these three only
  hr, ht: of the challenges: the switch's positions, which round number o + 2 + (h + g) samples, are
    below `2 ^ a.C.a`, and they are `a.t` many
  hw: of the prover's data: at every place in `Dp.ts` and every position of that tree the column has
    the width that the book states
  hMain, hMask, hF: of the prover's data, for the members' messages m and tails r and the fresh
    table's φ and ψ: the symbols (`symG`, Johnson/Prover/Link/Base.lean) of the members' main rows
    (hMain) and mask rows (hMask) and of the fresh table's rows (hF) are in the columns, at the
    offsets that `DataAt hok` takes from the tree shapes in the book: one word for a main row over
    the base field (`read1`), three words for every other row (`read3`, both
    Johnson/Desc/K12/Honest/Written.lean)

Limits. The acceptances are hypotheses; they are not shown. That the columns hold the symbols is a
hypothesis. hw, hMain, hMask and hF speak of every position of a tree, not of the sampled positions
only. No hypothesis but Y ties P, an argument of the term's rounds, to m, r, φ and ψ, whose symbols
the columns hold: that they are the message, the tails and the fresh table of P is not asked. Both
arms of the first fold are covered (`MaskCase`, Johnson/Desc/K12/Law/JointK.lean): the fresh table
came earlier, or the fold's own first message brings it. At a stage that samples no position the
last clause is vacuous. The conclusion does not state that `Dk.rC`, whose positions the last clause
takes, is the term's round; the proof has that equation, and it is not among the conclusions. No
value that meets all hypotheses is given in this file. `first_V`
(Johnson/Desc/K12/Honest/FirstValues.lean) does not call this theorem: it goes the same way by
`switch_V_group` (Johnson/Desc/K12/Honest/GroupSwitch.lean). Nothing on completeness, on soundness
or on what is hidden.
-/
import Johnson.Desc.K12.Honest.FirstSeenExact
import Johnson.Desc.K12.Honest.FirstYes
import Johnson.Desc.K12.Honest.GroupState
import Johnson.Desc.K12.Law.FirstOkLaw
import Johnson.Desc.K12.Law.FirstSrc
import Johnson.Desc.K12.Law.SwUnfold
import Johnson.Desc.K12.Law.ReadsK
import Johnson.Prover.Link.BodyStepAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)

/-- A round's data with a tree of the depth a and the width W. The other fields are fixed: an entry
with an empty name, the kind `.elems`, no item, the tree number 0, no opening. -/
def dTree (a W : ℕ) : PQ.RD :=
  ⟨{ name := "" }, .elems, [], some { a := a, W := W, tree := 0 }, []⟩

/-- The same at the depth and the width that a book states for the tree at the place u. Both are 0
where the book has no tree at u. -/
def dBook (book : TreeBook) (u : ℕ) : PQ.RD := dTree (logAt book u) (widthAt book u)

section
variable {p : P12} {a : Fmt.M1.Stage} {row : GroupRow} {Dp : Plain}

/-- The library's group (`gpG`), made of the plain data; all radii are 0. -/
abbrev GroupAt (hok : ok (gpL p a row Dp) = true) : Gp (sg a) :=
  gpG (good_of_ok p a row Dp hok) fun _ => 0

/-- Its public data (`gpP`), with the rounds' data taken from the book (`dBook`). -/
abbrev DataAt (hok : ok (gpL p a row Dp) = true) : GpData (GroupAt hok) :=
  gpP (good_of_ok p a row Dp hok) (fun _ => 0) (fun i => dBook Dp.book (Dp.mems.get i).t)
    (dBook Dp.book Dp.fresh.t)

end

/-- The library's test on the plain data asks that the mask code is not longer than the fresh
table's tree. -/
theorem fresh_long {p : P12} {a : Fmt.M1.Stage} {row : GroupRow} {Dp : Plain}
    (hok : ok (gpL p a row Dp) = true) : a.Z.a ≤ Dp.fresh.tsh.logN := by
  have h := List.all_eq_true.1 hok ("f:zshort", decide (a.Z.a ≤ Dp.fresh.tsh.logN))
    (by unfold gpL; simp)
  exact of_decide_eq_true h

/-- The elements that the fold's rounds sampled, one of each round, without the first round's. -/
def gammaAt (K : BCoins) (j : ℕ) (a : Fmt.M1.Stage) (o : ℕ) (t : T12) (P : PS) (D : ℕ → Fmt.Drawn) :
    List E := ((rfAt K j a o t P D).map noDigest).tail.map drawnOf

/-- Read as a point, they are `aPoint`: the point at which the term folds. -/
theorem point_gammaAt (K : BCoins) (j : ℕ) (a : Fmt.M1.Stage) (o : ℕ) (t : T12) (P : PS)
    (D : ℕ → Fmt.Drawn) :
    readP ((sgOf a).h + (sgOf a).g) (gammaAt K j a o t P D) = aPoint a o D := by
  rw [← point_eq K j a o P (Johnson.Prover.Link.rowOf t) D, gam_at, fold_eq]
  rfl

/-- **What the first switch reads, from acceptances.** -/
theorem hy_atFirst (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (a next : Fmt.M1.Stage)
    (l : Laid) (o : ℕ) (t : T12) (P : PS) (D : ℕ → Fmt.Drawn)
    (he : p.early = true) (h1 : p.answers = 1)
    (hl : l = laidS p)
    (row : GroupRow) (L : GroupLayout) (hp : t.pass = .claim row L)
    (Dp : Plain) (hD : gpOf p t a L = some Dp) (hok : ok (gpL p a row Dp) = true)
    (hhk : a.h ≤ a.k) (hs : (sg a).Sized)
    (cu nx : IoppStage) (hcu : stageAt p 0 a = some cu) (hnx : stageAt p 1 next = some nx)
    (hcode : ((t1At p K 0 a l o t P D).st.codes.base[cu.code]?).map (·.logN) = some a.C.a)
    (c : ℕ → ℕ → List UInt64)
    (hw : ∀ u ∈ Dp.ts, ∀ x, x < 2 ^ logAt Dp.book u → (c u x).length = widthAt Dp.book u)
    (Y : FirstYes p K rest 0 a next l o t P (groupTrees Dp.ts (logAt Dp.book) c) D)
    (hr : ∀ x ∈ (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss, x < 2 ^ a.C.a)
    (ht : (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss.length = a.t)
    (m : (GroupAt hok).Msgs) (r : Tails (GroupAt hok)) (φ : (sg a).cFr.J → GE)
    (ψ : (sg a).cFr.Q → GE)
    (hMain : ∀ j x, x < 2 ^ ((GroupAt hok).mb j).a → ∀ i : Fin ((GroupAt hok).mb j).nM,
      (if ((DataAt hok).lay j).base then
          read1 (c ((DataAt hok).tp j) x) (((DataAt hok).lay j).oM + i.val)
        else read3 (c ((DataAt hok).tp j) x) (((DataAt hok).lay j).oM + 3 * i.val)) =
        symG ((GroupAt hok).mb j).C x (ext0 fun e => m j (.inl (i, e)))
          (ext0 fun q => r j (.inl (i, q))))
    (hMask : ∀ j x, x < 2 ^ ((GroupAt hok).mb j).a → ∀ i : Fin ((GroupAt hok).mb j).nZ,
      read3 (c ((DataAt hok).tp j) x) (((DataAt hok).lay j).oZ + 3 * i.val) =
        symG ((GroupAt hok).mb j).Z (x % 2 ^ ((GroupAt hok).mb j).Z.a)
          (ext0 fun e => m j (.inr (i, e))) (ext0 fun q => r j (.inr (i, q))))
    (hF : ∀ x, x < 2 ^ (DataAt hok).aF → ∀ b : Fin (sg a).h → Bool,
      read3 (c (DataAt hok).ft x) ((DataAt hok).oF + 3 * Sz.rowNo b) =
        symG (sg a).Z (x % 2 ^ (sg a).Z.a) (ext0 fun e => φ (b, e)) (ext0 fun q => ψ (b, q))) :
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
            (foldMsg (sg a) (layJ (GroupAt hok) m) φ (aPoint a o D))
            (foldTl (sg a) (layQ (GroupAt hok) r) ψ (aPoint a o D)))
            (Qs i) α = symS (sg a) rows out.positions Dk.y (Qs i).val α) := by
  have hm := made_of p t a L Dp hD
  have hkk : (sg a).h + (sg a).g = a.k := by
    show a.h + (a.k - a.h) = a.k
    omega
  have hck : cu.k = a.k ∧ cu.h = a.h := by
    unfold stageAt at hcu
    obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.1 hcu
    exact ⟨rfl, rfl⟩
  -- the fold
  obtain ⟨t₁, hf1⟩ := Y.fold
  have e1 : t1At p K 0 a l o t P D = t₁ := getD_of_ok hf1
  have hn : ((rfAt K 0 a o t P D).map noDigest).length = 1 + cu.k := by
    rw [List.length_map, length_aFold, hck.1]
    exact congrArg (1 + ·) hkk
  obtain ⟨id, st, book, n, hcase, -, est, hbk, hpass, -⟩ :=
    fold_exact p 0 a _ t t₁ _ row L cu hp hcu hn hf1
  have hsk : ShapesKeep st t₁.st := by
    rw [est]
    exact shapes_spent _ _ _ _
  obtain ⟨rE, rR, hrs⟩ : ∃ rE rR, (rfAt K 0 a o t P D).map noDigest = rE :: rR := ⟨_, _, rfl⟩
  have hpt : aPoint a o D = readP ((sg a).h + (sg a).g) (rR.map drawnOf) := by
    rw [← point_gammaAt K 0 a o t P D]
    unfold gammaAt
    rw [hrs]
    rfl
  have hg : (rR.map drawnOf).length = (sg a).h + (sg a).g := by
    have k := hn
    rw [hrs, List.length_cons, hck.1, ← hkk] at k
    rw [List.length_map]
    omega
  -- the fresh table, and the statement and the book after its entering, are the plain data's
  obtain ⟨cu', hcu', hent⟩ := hm.ent
  obtain rfl : cu' = cu := Option.some.inj (hcu'.symm.trans hcu)
  have e := (entered_of_case p t cu' L id st book hcase).symm.trans hent
  obtain ⟨rfl, e'⟩ := Prod.mk.inj (Option.some.inj e)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
  -- the switch and the batching after it
  obtain ⟨t₂, hs2⟩ := Y.switch
  obtain ⟨t₃, hs3⟩ := Y.behind
  have e2 : aRec2 p K rest 0 a next l o t P (groupTrees Dp.ts (logAt Dp.book) c) D = t₂ :=
    getD_of_ok hs2
  have e3 : t3At p K rest 0 a next l o t P (groupTrees Dp.ts (logAt Dp.book) c) D = t₃ :=
    getD_of_ok hs3
  rw [e2] at hs3
  have hs2' := (ranged_ok _ _ _ _ _ _ hs2).1
  rw [e1] at hs2'
  obtain ⟨out, row', lay', theta, Dk, -, hrC, hdid, hp3, -⟩ :=
    switchUnfolds p 0 a next rest.isEmpty _ t₁ t₂ t₃ _ _ _ _ _ nx he h1 hpass hnx hs2' hs3
  have hlog : Dk.code.logN = (sg a).C.a := by
    have k : t₁.st.codes.base[cu'.code]? = some Dk.code := hdid.code
    rw [e1, k] at hcode
    exact Option.some.inj hcode
  rw [e3, e1]
  refine ⟨_, _, out, row', lay', theta, Dk, hpass, hdid, hp3, fun Qs hQ => ?_⟩
  rw [hpt]
  -- what is public of the group
  have hlogM : ∀ i : Fin Dp.mems.length,
      logAt Dp.book (Dp.mems.get i).t = (Dp.mems.get i).tsh.logN :=
    fun i => (keyAt_of (F := 0) (hm.mem i).2).2
  have hlogF : logAt Dp.book Dp.fresh.t = Dp.fresh.tsh.logN := (keyAt_of (F := 0) hm.fresh).2
  obtain ⟨hPub, ⟨src, hsrc⟩, hkept, hLay, -⟩ := first_at p t a row L Dp hD hok hhk (fun _ => 0)
    (fun i => dBook Dp.book (Dp.mems.get i).t) (dBook Dp.book Dp.fresh.t)
    (fun i => congrArg (2 ^ ·) (hlogM i)) (congrArg (2 ^ ·) hlogF)
  have hparts : PartsP (DataAt hok) t₁.st t₁.book Dp.fresh.id :=
    ⟨fun j => (hm.mem j).2.keeps (by rw [hbk]; exact BookKeeps.refl _) hsk,
      hm.fresh.keeps (by rw [hbk]; exact BookKeeps.refl _) hsk⟩
  have hkeys := hsrc.keys
  rw [hkk, show (((H2U.roundsOfNums p.nums).getD []).zip p.oracles).drop 1 = l from hl.symm]
    at hkeys
  have hposs : Dk.rC.drawn.poss = (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss := by
    rw [hrC]
    rfl
  exact hy_group p _ _ (sg a) hs (GroupAt hok) (DataAt hok) cu' L Dp.fresh.id hdid
    (hck.1.trans hkk.symm) hck.2 hPub hLay hparts hkeys (dBook Dp.book) (fun _ => rfl) rfl c
    (fun j x hx => hw _ ((hPub.mem _).2 (Or.inl ⟨j, rfl⟩)) x
      (lt_of_lt_of_eq hx (congrArg (2 ^ ·) (hlogM j).symm)))
    (fun x hx => hw _ ((hPub.mem _).2 (Or.inr rfl)) x
      (lt_of_lt_of_eq hx (congrArg (2 ^ ·) hlogF.symm)))
    (by rw [hposs]; exact pos_groups a.C.a (logAt Dp.book) c _ hr Dp.ts)
    (cols_groups (dBook Dp.book) (logAt Dp.book) c _ Dp.ts fun u hu => ⟨rfl, hw u hu⟩)
    (fresh_long hok) m r φ ψ hMain hMask hF (spent Dp.st Dp.fresh.id) row (drawnOf rE)
    (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target)) (rR.map drawnOf)
    (by rw [hrs]; rfl) hkept hg hlog Qs hQ
    (by rw [hposs]; exact ht)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.fresh_long
#print axioms ProofFile.Honest.K12.point_gammaAt
#print axioms ProofFile.Honest.K12.hy_atFirst
#print axioms ProofFile.Honest.K12.dTree
#print axioms ProofFile.Honest.K12.dBook
#print axioms ProofFile.Honest.K12.GroupAt
#print axioms ProofFile.Honest.K12.DataAt
#print axioms ProofFile.Honest.K12.gammaAt
