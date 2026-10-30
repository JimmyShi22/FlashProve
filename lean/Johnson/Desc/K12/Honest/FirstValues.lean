-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/FirstValues.lean: one theorem, `first_V`, on the values in the first stage
of a proximity test: where the claim before the first fold is true at the prover's state, the claim
after the first switch is true at the prover's state that the term builds after that switch. The
term is `stagesAll` (Johnson/Desc/K12/Honest/Stages.lean): a definition of the rounds, the trees and
the groups of columns of a test's stages. The theorem is stated at the term's own pieces at the
first stage, which Johnson/Desc/K12/Honest/FirstYes.lean names. That the verifier's parts accept
these pieces is a hypothesis. At a group of any layout, and in both arms of the first fold
(`MaskCase`, Johnson/Desc/K12/Law/JointK.lean): the fresh table came earlier, or the fold's own
first message brings it. A theorem with its proof, a lemma and two definitions. It does not depend
on the frame for an honest side (Johnson/Desc/ProofFile/Honest/Frame.lean).

In the list and below: p (`P12`, Johnson/Desc/K12/Frame.lean) holds the numbers of the place of the
test. a and next (`Fmt.M1.Stage`) are the first and the second stage; `sgOf a` and `sgOf next` are
their sizes (`Sg`): the codes C and Z, the numbers h and g = k - h, and the number of positions. t
(`T12`, Johnson/Desc/K12/Join.lean) is the verifier's state before the fold. Its field `pass` is
what one part of the test passes to the next: after a batching a claim, that is a row (`GroupRow`)
with a layout (`GroupLayout`); after a fold the single rows (`SingleRows`, OnBytes/Iop/Fold.lean). P
(`PS`, Johnson/Prover/Link/BodyState.lean) is the prover's state, tables by index, and `μOf s P` is
its message at the sizes s. K (`BCoins`, Johnson/Prover/Link/BodyAll.lean) and D are parameters of
the term: `K.W` are the coefficients that the fold's rounds are made of, and D n is what round
number n samples. o is the number of the stage's first round. The pieces, written here without their
arguments: `t1At` is the verifier's state after the fold, `t3At` the one after the switch and the
batching after it, `qAt` the prover's state after the switch. A claim is true at a message μ if
`Slf.Holds` (Cb/Ld/LdRel.lean) holds of `stmGk s k h row` (OnBytes/Slice/BlkRead.lean) and μ: the
row's coefficients, read with the layout's two numbers k and h, times the entries of μ add up to the
row's target. The switch's first round samples a seed (`SampleSeed`, OnBytes/Iop/Send.lean), a point
and a factor; its second round sends the answer and samples the positions.

  `first_V`: under the hypotheses below there are a row row' and a layout lay' such that `t3At`
    passes the claim of row' with lay', and this claim, read with `lay'.k` and `lay'.h` at the sizes
    `sgOf next`, is true at the message `μOf (sgOf next)` of `qAt`
  `OldOk s s' codes old nc nz`: a structure of five propositions: what `claim_behind`
    (Johnson/Prover/Link/SwitchHolds.lean) and `switch_V_group`
    (Johnson/Desc/K12/Honest/GroupSwitch.lean) ask of the single rows old before a switch from the
    sizes s to the sizes s'. `prog`: `CsProg` (OnBytes/Slice/BlkCsJoint.lean); `kept`: old has no
    kept form; `d0`, `d1`: the vectors number 0 and 1 of `old.d` have `s.Z.l` entries; `vars`: every
    tensor of `old.c` has `ceilLog2 s.C.l` variables
  `bitsAt p j next t₁`: a definition: how many coordinates the seed's point has. It is the field
    `bits` of `Send.cube` (OnBytes/Iop/Send.lean) at the codes of t₁, the verifier's state after the
    fold, and at the shape of the switch's target (`switchTargetStage`, OnBytes/Iop/Cs.lean) with
    the two code numbers of stage number j + 1; where `stageAt p (j + 1) next` returns nothing, with
    those of the default `IoppStage`
  `groups_shut`: the statement `ledgerShut (Dk.stA T others S) T n` has the groups of S: a sending,
    an admitting (`Taken.stA`, Johnson/Desc/K12/Law/SwDid.lean) and a closing of ledgers
    (`ledgerShut`, OnBytes/Slice/BlkCsRun.lean) leave a statement's groups as they are

By what. The proof goes the way of `hy_atFirst` (Johnson/Desc/K12/Honest/FirstReads.lean) without
calling it, and derives more. `fold_exact` (Johnson/Desc/K12/Honest/FirstSeenExact.lean) gives the
single rows that the accepted fold passes as an expression in the fold's rounds (`foldOutAt`,
Johnson/Prover/Link/FormFold.lean), and the verifier's state after the fold. By `fold_at_S`
(Johnson/Desc/K12/Honest/FirstFoldAt.lean) these rows are true at the three folded messages
(`foldMsg`). `switchUnfolds` (Johnson/Desc/K12/Law/SwUnfold.lean) turns the acceptances of the
switch and of the batching after it into `Did` (Johnson/Desc/K12/Law/SwDid.lean). From `Did` and the
switch's two rounds the proof reads the new group's two codes (with `groups_shut`), the answer, the
seed's point and its factor. The factor reads as an element other than 0, because the switch has
accepted (`Did.factor`; `isZeroE_iff`, OnBytes/Slice/ProgField.lean). That the answer reads as
`gAns` is `ans_at` (Johnson/Prover/Link/BodyStepAt.lean) with `ans_eq`, `point_eq` and `rec1_eq`
(Stages.lean). The group's public data come from `made_of`, `first_at`, `entered_of_case` and
`keyAt_of` (Johnson/Desc/K12/Law/FirstOkLaw.lean). `muOf_state`, `rhoOf_state`, `phiOf_state` and
`psiOf_state` (Johnson/Desc/K12/Honest/FirstState.lean) write the state's message, tails and fresh
table as the members'. The hypotheses of `switch_V_group` on the columns come from `cols_main`,
`cols_mask`, `cols_fresh` (Johnson/Desc/K12/Honest/FirstRows.lean), `pos_groups`, `cols_groups`
(Johnson/Desc/K12/Honest/GroupState.lean) and `fresh_long` (FirstReads.lean). `switch_V_group` gives
the claim after the switch at the new message `gMsg`, which is the message of `qAt` by `muOf_next`
(BodyState.lean).

Hypotheses of `first_V`. The entries down to hr, ht are the hypotheses of `hy_atFirst_rows`
(FirstRows.lean) without its clause hcode on the first stage's main code. Called public in the
limits: he, h1, hl, hp, hD, hok, hhk, hs, hcu, hnx, hf, hhk', hZl and hOld; they speak of the
place's numbers, the stages and the verifier's states. hZl and hOld are stated at `t1At`, which is
an expression in K, P and D too; so is the index in hwords.
  he, h1: `p.early = true` and `p.answers = 1`
  hl: the declared rounds l are `laidS p` (Johnson/Desc/K12/Law/ReadsK.lean): the place's own,
    without the first
  hp: t passes a claim: a row with the layout L
  hD, hok: `gpOf p t a L` returns the group's plain data Dp (`Plain`), and Dp passes every clause of
    `gpL` (all three: Johnson/Desc/K12/Law/FirstOk.lean)
  hhk, hs: `a.h ≤ a.k`; the first stage's sizes meet `Sg.Sized` (OnBytes/Slice/Numbers.lean)
  hcu, hnx: `stageAt` (Join.lean) returns cu for a as stage number 0 and nx for next as stage number
    1: p lists two code numbers for each
  hC: `ColsAt a Dp c R` (FirstRows.lean), on the trees' columns c and the prover's rows R
    (`PlainRows`)
  Y: `FirstYes` (FirstYes.lean) at the trees `groupTrees Dp.ts (logAt Dp.book) c` (GroupState.lean):
    the fold, the switch and the batching after it accept the term's rounds and groups of columns.
    Of the fields of `FirstYes` the proof uses these three only
  hr, ht: the positions that round number o + 2 + (h + g) samples are below `2 ^ a.C.a`, and they
    are `a.t` many; h and g are those of `sgOf a`
  hS, hpk, hroom: of the prover's state: `StateAt` (Johnson/Desc/K12/Honest/FirstState.lean) · its
    fresh table is the packing of the hiding polynomial that the fold's rounds are made of, and
    there is room for it. "The hiding polynomial" is only a name, for `K.W (sgOf a) 0`: nothing here
    says that it hides anything. In Lean, hpk: `P.fM = packedN (sgOf a) (K.W (sgOf a) 0)`
    (Johnson/Prover/Link/BodyPack.lean); hroom: h + 2 * g + 1 ≤ `(sgOf a).Z.l`
  hin, hLk, hLh: the claim before the fold is true at the state's message `μOf (sgOf a) P`, read
    with the layout L that t passes; `L.k` and `L.h` are the stage's h + g and h
  hf: the two stages' sizes fit: `CsFit (sgOf a) (sgOf next)` (OnBytes/Slice/CsData.lean)
  hhk': `next.h ≤ next.k`
  hZl: behind the fold the mask code has the stage's message length. In Lean: in the codes of `t1At`
    the mask code number `cu.maskCode` has `ell = a.Z.l`
  hOld: whatever single rows `t1At` passes meet `OldOk` at the two stages' sizes, the codes of
    `t1At` and the two code numbers of nx
  hwords: the three words of the seed's factor are below the prime (`okE`, OnBytes/Field/Ext.lean).
    The factor is element number `bitsAt p 0 next t1At` of what round number o + 1 + (h + g)
    samples, and `zeroE` where there is no such element

Limits.
- The acceptances are hypotheses; they are not shown.
- Every public clause is a hypothesis.
- Where the seed's factor reads as 0 the verifier's own switch rejects (`Did.factor`,
  Johnson/Desc/K12/Law/SwDid.lean), so the acceptances that are asked fail there: whoever shows that
  an honest run is accepted must set that event aside, at every switch, unless its challenges are
  the format's, which samples a seed's factor among the elements other than 0 (`drawsMarkedNonzeroHaveNonzeroWords`,
  Johnson/Desc/Block.lean). The term answers there with the factor 1 (`orOne`,
  Johnson/Desc/K12/Honest/Fold.lean). The first of these sentences holds where the factor's words
  are below the prime (hwords): `Did.factor` says that the three words are not all 0, and
  `isZeroE_iff` ties that to the field only there. `drawsMarkedNonzeroHaveNonzeroWords` too tests the raw words.
- That the claim before the fold is true (hin), which is the values' half of the batching at a
  group, is not proved here. `bat_claimTrue_state` (Johnson/Desc/K12/Honest/BatState.lean), by
  `bat_claimTrue` (Johnson/Desc/K12/Honest/BatValues.lean), proves it in the form `ClaimTrue`
  (Johnson/Desc/K12/Honest/ClaimTrue.lean). Its hypotheses: he, hp, hD and hS as here; the batching
  accepts and returns t; four numbers of the layout L are the stage's; every row that the test takes
  in says its claim of the words that the rows R make (`AllSay`). The batching's acceptance and the
  hypothesis on `AllSay` are proved in neither file.
- The conclusion states nothing on `lay'.k` and `lay'.h`, the two numbers of the layout that is
  passed after the switch.
- Redundant among the hypotheses, by reading: hr, the positions' range, follows from the guard on
  the range (`ranged`, Johnson/Desc/K12/JoinGuarded.lean; `ranged_ok`,
  Johnson/Desc/K12/Law/BaseGives.lean), up to the declared depth: the guard bounds a position by
  `2 ^ logN` at its round's declared entry, and that this logN is `a.C.a` is not stated in this
  file.
- Redundant too, by reading: four clauses of `OldOk` follow from the text of the fold's output
  (`foldOutput`, OnBytes/Iop/Fold.lean). This file does not state that.
Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.FirstSeenExact
import Johnson.Desc.K12.Honest.FirstFoldAt
import Johnson.Desc.K12.Honest.FirstState
import Johnson.Desc.K12.Honest.GroupSwitch
import OnBytes.Slice.BlkHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)

/-- How many coordinates the seed's point has. t₁: the verifier's state after the fold. Where
`stageAt p (j + 1) next` returns nothing, the two code numbers are those of the default
`IoppStage`. -/
def bitsAt (p : P12) (j : ℕ) (next : Fmt.M1.Stage) (t₁ : T12) : ℕ :=
  (Send.cube t₁.st.codes
    (switchTargetStage ((stageAt p (j + 1) next).getD default).code
      ((stageAt p (j + 1) next).getD default).maskCode ((sgOf next).h + (sgOf next).g)
      (sgOf next).h 1).shape).bits

/-- What `claim_behind` (Johnson/Prover/Link/SwitchHolds.lean) asks of the single rows before a
switch. -/
structure OldOk (s s' : Sg) (codes : Codes) (old : SingleRows) (nc nz : ℕ) : Prop where
  prog : CsProg s s' codes old nc nz
  kept : old.kept = #[]
  d0 : (old.d.getD 0 #[]).size = s.Z.l
  d1 : (old.d.getD 1 #[]).size = s.Z.l
  vars : ∀ v ∈ old.c.tensors, v.vars = ceilLog2 s.C.l

/-- A sending, an admitting and a closing of ledgers leave a statement's groups as they are. -/
theorem groups_shut (Dk : Taken) (T : SwitchTarget) (others : Array OracleNotice) (S : Statement)
    (n : ℕ) : (ledgerShut (Dk.stA T others S) T n).groups = S.groups := by
  unfold ledgerShut
  split <;> rfl

/-- **From a true claim before the first fold to a true claim after the first switch.** -/
theorem first_V (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (a next : Fmt.M1.Stage)
    (l : Laid) (o : ℕ) (t : T12) (P : PS) (D : ℕ → Fmt.Drawn)
    (he : p.early = true) (h1 : p.answers = 1)
    (hl : l = laidS p)
    (row : GroupRow) (L : GroupLayout) (hp : t.pass = .claim row L)
    (Dp : Plain) (hD : gpOf p t a L = some Dp) (hok : ok (gpL p a row Dp) = true)
    (hhk : a.h ≤ a.k) (hhk' : next.h ≤ next.k) (hs : (sg a).Sized)
    (cu nx : IoppStage) (hcu : stageAt p 0 a = some cu) (hnx : stageAt p 1 next = some nx)
    (c : ℕ → ℕ → List UInt64) (R : PlainRows) (hC : ColsAt a Dp c R) (hS : StateAt a Dp P R)
    (Y : FirstYes p K rest 0 a next l o t P (groupTrees Dp.ts (logAt Dp.book) c) D)
    (hr : ∀ x ∈ (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss, x < 2 ^ a.C.a)
    (ht : (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss.length = a.t)
    (hf : CsFit (sgOf a) (sgOf next))
    (hLk : L.k = (sgOf a).h + (sgOf a).g) (hLh : L.h = (sgOf a).h)
    (hin : (Slf.idf (E := GE) (J := (sgOf a).cIn.J)).Holds (stmGk (sgOf a) L.k L.h row)
      (μOf (sgOf a) P))
    (hroom : (sgOf a).h + 2 * (sgOf a).g + 1 ≤ (sgOf a).Z.l)
    (hpk : P.fM = packedN (sgOf a) (K.W (sgOf a) 0))
    (hZl : ((t1At p K 0 a l o t P D).st.codes.mask.getD cu.maskCode default).ell = a.Z.l)
    (hOld : ∀ rows gp, (t1At p K 0 a l o t P D).pass = .single rows gp →
      OldOk (sgOf a) (sgOf next) (t1At p K 0 a l o t P D).st.codes rows nx.code nx.maskCode)
    (hwords : okE (((D (o + 1 + ((sgOf a).h + (sgOf a).g))).elems.map E.ofTriple).getD
      (bitsAt p 0 next (t1At p K 0 a l o t P D)) zeroE) = true) :
    ∃ (row' : GroupRow) (lay' : GroupLayout),
      (t3At p K rest 0 a next l o t P (groupTrees Dp.ts (logAt Dp.book) c) D).pass =
        .claim row' lay' ∧
      (Slf.idf (E := GE) (J := (sgOf next).cIn.J)).Holds (stmGk (sgOf next) lay'.k lay'.h row')
        (μOf (sgOf next) (qAt K rest 0 a next o P D)) := by
  have hm := made_of p t a L Dp hD
  have hkk : (sgOf a).h + (sgOf a).g = a.k := by
    show a.h + (a.k - a.h) = a.k
    omega
  have hkk' : (sgOf next).h + (sgOf next).g = next.k := by
    show next.h + (next.k - next.h) = next.k
    omega
  have hck : cu.k = a.k ∧ cu.h = a.h := by
    unfold stageAt at hcu
    obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.1 hcu
    exact ⟨rfl, rfl⟩
  have hrow : Johnson.Prover.Link.rowOf t = row := by
    unfold Johnson.Prover.Link.rowOf
    rw [hp]
  subst hrow
  -- the fold
  obtain ⟨t₁, hf1⟩ := Y.fold
  have e1 : t1At p K 0 a l o t P D = t₁ := getD_of_ok hf1
  have hlen : ((rfAt K 0 a o t P D).map noDigest).length = 1 + ((sgOf a).h + (sgOf a).g) := by
    rw [List.length_map, length_aFold]
  have hn : ((rfAt K 0 a o t P D).map noDigest).length = 1 + cu.k := by
    rw [hlen, hck.1, hkk]
  obtain ⟨id, st, book, n, hcase, hidx, est, ebook, epass, hfits⟩ :=
    fold_exact p 0 a _ t t₁ _ _ L cu hp hcu hn hf1
  obtain ⟨cu', hcu', hent⟩ := hm.ent
  obtain rfl : cu' = cu := Option.some.inj (hcu'.symm.trans hcu)
  have e := (entered_of_case p t cu' L id st book hcase).symm.trans hent
  obtain ⟨rfl, e'⟩ := Prod.mk.inj (Option.some.inj e)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
  have hnxn : nx = { code := n.1, maskCode := n.2, k := next.k, h := next.h } := by
    unfold stageAt at hnx
    rw [hidx] at hnx
    exact (Option.some.inj hnx).symm
  -- the switch and the batching after it
  obtain ⟨t₂, hs2⟩ := Y.switch
  obtain ⟨t₃, hs3⟩ := Y.behind
  have e2 : aRec2 p K rest 0 a next l o t P (groupTrees Dp.ts (logAt Dp.book) c) D = t₂ :=
    getD_of_ok hs2
  have e3 : t3At p K rest 0 a next l o t P (groupTrees Dp.ts (logAt Dp.book) c) D = t₃ :=
    getD_of_ok hs3
  rw [e2] at hs3
  have hs2' := (ranged_ok _ _ _ _ _ _ hs2).1
  rw [e1] at hs2' hZl hOld hwords
  obtain ⟨out, row', lay', theta, Dk, hrS, hrC, hdid, hp3, -⟩ :=
    switchUnfolds p 0 a next rest.isEmpty _ t₁ t₂ t₃ _ _ _ _ _ nx he h1 epass hnx hs2' hs3
  rw [e3]
  refine ⟨row', lay', hp3, ?_⟩
  -- the fold's rounds, as a first round and the rest
  obtain ⟨rE, rR, hrs⟩ : ∃ rE rR, (rfAt K 0 a o t P D).map noDigest = rE :: rR := ⟨_, _, rfl⟩
  have hpt : aPoint a o D = readP ((sgOf a).h + (sgOf a).g) (rR.map drawnOf) := by
    rw [← point_eq K 0 a o P (Johnson.Prover.Link.rowOf t) D, gam_at, fold_eq]
    show readP _ (((rfAt K 0 a o t P D).map noDigest).tail.map drawnOf) = _
    rw [hrs]
    rfl
  have hγ : (rR.map drawnOf).length = (sgOf a).h + (sgOf a).g := by
    have k := hlen
    rw [hrs, List.length_cons] at k
    rw [List.length_map]
    omega
  -- what is public of the group
  have hlogM : ∀ i : Fin Dp.mems.length,
      logAt Dp.book (Dp.mems.get i).t = (Dp.mems.get i).tsh.logN :=
    fun i => (keyAt_of (F := 0) (hm.mem i).2).2
  have hlogF : logAt Dp.book Dp.fresh.t = Dp.fresh.tsh.logN := (keyAt_of (F := 0) hm.fresh).2
  obtain ⟨hPub, ⟨src, hsrc⟩, hkept, hLay, -⟩ := first_at p t a _ L Dp hD hok hhk (fun _ => 0)
    (fun i => dBook Dp.book (Dp.mems.get i).t) (dBook Dp.book Dp.fresh.t)
    (fun i => congrArg (2 ^ ·) (hlogM i)) (congrArg (2 ^ ·) hlogF)
  have hsk : ShapesKeep Dp.st t₁.st := by
    rw [est]
    exact shapes_spent _ _ _ _
  have hparts : PartsP (DataAt hok) t₁.st t₁.book Dp.fresh.id :=
    ⟨fun j => (hm.mem j).2.keeps (by rw [ebook]; exact BookKeeps.refl _) hsk,
      hm.fresh.keeps (by rw [ebook]; exact BookKeeps.refl _) hsk⟩
  have hkeys := hsrc.keys
  rw [show (sg a).h + (sg a).g = a.k from hkk,
    show (((H2U.roundsOfNums p.nums).getD []).zip p.oracles).drop 1 = l from hl.symm] at hkeys
  have hposs : Dk.rC.drawn.poss = (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss := by
    rw [hrC]
    rfl
  -- the new group's two codes
  have hG : Dk.G = { code := nx.code, maskCode := nx.maskCode } := by
    have k := hdid.group
    rw [groups_shut, est] at k
    have k2 : (Ground.withGroup (spent Dp.st Dp.fresh.id) n.1 n.2).groups[Dp.st.groups.size]? =
        some { code := n.1, maskCode := n.2 } := by
      show (Dp.st.groups.push _)[Dp.st.groups.size]? = _
      exact Array.getElem?_push_size
    rw [k2] at k
    rw [hnxn]
    exact (Option.some.inj k).symm
  have hnk : nx.k = (sgOf next).h + (sgOf next).g := by rw [hnxn, hkk']
  have hnh : nx.h = (sgOf next).h := by rw [hnxn]; rfl
  rw [hnk, hnh] at hdid
  -- the seed's factor, its point, the answer
  have hbits : (Send.cube t₁.st.codes (switchTargetStage nx.code nx.maskCode
      ((sgOf next).h + (sgOf next).g) (sgOf next).h 1).shape).bits = bitsAt p 0 next t₁ := by
    unfold bitsAt
    rw [hnx]
    rfl
  have hrSe : Dk.rS.drawn.elems.map E.ofTriple =
      (D (o + 1 + ((sgOf a).h + (sgOf a).g))).elems.map E.ofTriple := by
    rw [hrS]
    rfl
  have hbeta : Dk.beta = ((D (o + 1 + ((sgOf a).h + (sgOf a).g))).elems.map E.ofTriple).getD
      (bitsAt p 0 next t₁) zeroE := by
    have k := hdid.seed
    rw [hrSe, hbits] at k
    exact (getD_of_drop _ _ _ _ k).symm
  have hnz : readE Dk.beta ≠ 0 := fun h0 => by
    rw [← hbeta] at hwords
    have k := (isZeroE_iff _ hwords).2 h0
    rw [hdid.factor] at k
    cases k
  have hβ : (unitOf (readE Dk.beta)).val = readE Dk.beta := by
    rw [val_unitOf]
    unfold orOne
    rw [if_neg hnz]
  obtain ⟨A, hA0⟩ : ∃ A, A = aAns p 0 a next o D (t1At p K 0 a l o t P D)
      (qAt K rest 0 a next o P D) := ⟨_, rfl⟩
  rw [← hA0] at hrC
  have halpha : Dk.alpha = E.ofTriple (ofE A) := by
    have k := hdid.valsC
    rw [hrC] at k
    have k2 : ofE A = Dk.alpha.triple := by
      injection k with k1 _
      injection k1
    rw [k2, E.ofTriple_triple]
  have hA := ans_at p K 0 a next l o t P (Johnson.Prover.Link.rowOf t) D hf
  rw [ans_eq p K rest.isEmpty 0 a next l o t P (Johnson.Prover.Link.rowOf t) D hf, point_eq,
    rec1_eq] at hA
  have hA' : readE (E.ofTriple (ofE A)) = gAns hf
      (foldMsg (sgOf a) (μOf (sgOf a) P) (φOf (sgOf a) P) (aPoint a o D))
      (foldTl (sgOf a) (ρOf (sgOf a) P) (ψOf (sgOf a) P) (aPoint a o D)) (K.fr 0)
      (readP _ (((D (o + 1 + ((sgOf a).h + (sgOf a).g))).elems.map E.ofTriple).take
          (bitsAt p 0 next t₁)),
        unitOf (readE (((D (o + 1 + ((sgOf a).h + (sgOf a).g))).elems.map E.ofTriple).getD
          (bitsAt p 0 next t₁) zeroE))) := by
    rw [hA0, ← e1]
    exact hA
  -- the state's message and tails are the members'
  have hμ : μOf (sgOf a) P = layJ (GroupAt hok) (msgsOf R hok) := muOf_state hS hok
  have hρ : ρOf (sgOf a) P = layQ (GroupAt hok) (tailsOf R hok) := rhoOf_state hS hok
  have hφ : φOf (sgOf a) P = freshOf R (sg a) := phiOf_state hS
  have hψ : ψOf (sgOf a) P = freshTlOf R (sg a) := psiOf_state hS
  -- the fold's values
  have hin' : (Slf.idf (E := GE) (J := (sgOf a).cIn.J)).Holds
      (stmG (sgOf a) (Johnson.Prover.Link.rowOf t)) (μOf (sgOf a) P) := by
    have e : stmGk (sgOf a) L.k L.h (Johnson.Prover.Link.rowOf t) =
        stmG (sgOf a) (Johnson.Prover.Link.rowOf t) := by rw [stmG_eq, hLk, hLh]
    rw [← e]
    exact hin
  have hH := fold_at_S K 0 a o P (Johnson.Prover.Link.rowOf t) D Dp.st (ioppFoldShape cu' L)
    Dp.fresh.id (hck.1.trans hkk.symm) hck.2 (by rw [Own.foldRowFits_agrees]; exact hfits)
    (by rw [est] at hZl; exact hZl) hin' hroom hpk
  rw [hpt, hμ, hφ] at hH
  rw [hpt, hμ, hρ, hφ, hψ] at hA'
  have hO := hOld _ _ epass
  have hQb : ∀ i : Fin (sg a).t, Dk.rC.drawn.poss.getD i.val 0 < 2 ^ (sg a).C.a := fun i => by
    rw [hposs, List.getD_eq_getElem _ _ (by rw [ht]; exact i.isLt)]
    exact hr _ (List.getElem_mem _)
  have hz : Dk.z (switchTargetStage nx.code nx.maskCode ((sgOf next).h + (sgOf next).g)
      (sgOf next).h 1) t₁.st =
      ((D (o + 1 + ((sgOf a).h + (sgOf a).g))).elems.map E.ofTriple).take (bitsAt p 0 next t₁) := by
    unfold Taken.z
    rw [hrSe, hbits]
  have hV := switch_V_group hf hs (K.fr 0) p _ _ (GroupAt hok) (DataAt hok) cu' L Dp.fresh.id hdid
    hO.prog hO.kept hG hO.d0 hO.d1 hO.vars (by rw [hposs]; exact ht) (by rw [hposs]; exact hr)
    (unitOf (readE Dk.beta)) hβ (fun i => ⟨_, hQb i⟩) (fun _ => rfl) (hck.1.trans hkk.symm) hck.2
    hPub hLay hparts hkeys (dBook Dp.book) (fun _ => rfl) rfl c
    (fun j x hx => hC.width _ ((hPub.mem _).2 (Or.inl ⟨j, rfl⟩)) x
      (lt_of_lt_of_eq hx (congrArg (2 ^ ·) (hlogM j).symm)))
    (fun x hx => hC.width _ ((hPub.mem _).2 (Or.inr rfl)) x
      (lt_of_lt_of_eq hx (congrArg (2 ^ ·) hlogF.symm)))
    (by rw [hposs]; exact pos_groups a.C.a (logAt Dp.book) c _ hr Dp.ts)
    (cols_groups (dBook Dp.book) (logAt Dp.book) c _ Dp.ts fun u hu => ⟨rfl, hC.width u hu⟩)
    (fresh_long hok) (msgsOf R hok) (tailsOf R hok) (freshOf R (sg a)) (freshTlOf R (sg a))
    (cols_main hC hok)
    (cols_mask hC hok) (cols_fresh hC hok) (spent Dp.st Dp.fresh.id) (Johnson.Prover.Link.rowOf t)
    (drawnOf rE)
    (claimOf rR
      (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) (Johnson.Prover.Link.rowOf t).target))
    (rR.map drawnOf) (by rw [hrs]; rfl) hkept hγ hH (by rw [halpha, hz, hbeta]; exact hA')
  show (Slf.idf (E := GE) (J := (sgOf next).cIn.J)).Holds _
    (μOf (sgOf next) (nextPS (sgOf a) (aPoint a o D) (K.fr 0) _ P))
  rw [muOf_next hf, hpt, hμ, hρ, hφ, hψ]
  exact hV

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.groups_shut
#print axioms ProofFile.Honest.K12.first_V
#print axioms ProofFile.Honest.K12.bitsAt
#print axioms ProofFile.Honest.K12.OldOk
