-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ManyBlk.lean: the program's yes on a link's chain gives the yes in the field, for any
number of stages.

OnBytes/Slice/BlkChain.lean follows the program's yes from block to block for three stages, and
OnBytes/Slice/BlkSem.lean concludes the yes in the field. This file does both along the program's
own recursion over its list of stages (OnBytes/Iop/Prox.lean: `ioppStagesVerify`) and the
recursion of a chain (OnBytes/Slice/ManyDefs.lean: `Chain`).

Main definitions.
 `StagesRun`       a run of the stages from one stage on, after which no named test has failed,
                   leads from a joint to a goal.
 `Chain.JointAt`   the joint before a stage whose tree a code switch has sent.
 `Chain.Pub`, `Chain.Own`, `Chain.ReadAs`   what is asked of a chain and the program's stages:
                   public facts on codes, sizes and rounds; on a stage's own tree; how the tree is
                   read.
Main theorems.
 `blk_many`          the program's yes, from the link's steps with the batching and `StagesRun`.
 `stagesRun_chain`   `StagesRun` from `Chain.JointAt` to `Chain.Acc`.
 `acc_of_runs`       `Chain.Acc` from the program's yes on a view, with the first stage's ties as
                     variables. `acc_of_link`: with the ties of a link's group of two members.

Not claimed. That the link's steps and the batching lead to the first joint (`hHead`). The public
facts, which are hypotheses. That the view shows the written trees' columns. Nothing on a link of
one stage; `acc_of_link` asks three stages or more. Nothing is said of a link whose masks do not
ride in the switches' messages. Nothing is said of a link whose first mask is not sent with the
folded rows: the first joint asks that the mask of the first fold has come, so for such a link
`hHead` cannot be met. Nothing on soundness.

-/
import OnBytes.Slice.BlkCuts
import OnBytes.Slice.BlkSem
import OnBytes.Slice.BlkTieFold
import OnBytes.Slice.ManyBlkSwitch
import OnBytes.Slice.ManyShows

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run
open Params (LinkShape IoppStage)

/-! ## The program's recursion over its stages -/

/-- From the joint J, a run of the stage cur and the stages rest after which no named test has
failed gives the goal. -/
def StagesRun (ride : Bool) (cur : IoppStage) (rest : List IoppStage) (J : GroupJoint)
    (Goal : Prop) : Prop :=
  ∀ (answers : Nat) (c : Ctx) (row : GroupRow) (L : GroupLayout) (mask : Option Nat) (c' : Ctx),
    J answers c row L mask → (ioppStagesVerify answers ride cur rest row L mask).Yields c () c' →
    c'.failed = none → Goal

/-- A fold, a code switch and the stages that are left, joined. -/
theorem stagesRun_step (ride : Bool) (cur next : IoppStage) (rest : List IoppStage)
    (J J2 : GroupJoint) (J1 : SingleJoint) (Goal : Prop) (hF : FoldRuns cur J J1)
    (hC : CsRuns ride next rest J1 J2) (hN : StagesRun ride next rest J2 Goal) :
    StagesRun ride cur (next :: rest) J Goal := by
  have tr : ∀ {a b c : Ctx}, Blk.SameButNotes a b → Blk.SameButNotes b c → Blk.SameButNotes a c :=
    fun h1 h2 =>
      ⟨h2.ch.trans h1.ch, h2.st.trans h1.st, h2.book.trans h1.book, h2.failed.trans h1.failed⟩
  intro answers c row L mask c' hJ hrun hfail
  obtain ⟨rows1, a1, a2, to1, a3, s1, row1, L1, a4, a5, a6, a7, a8, mask1, f1, n1, g1, w1, n2, n3,
    n4, n5, hm1, r1⟩ := ioppStages_step_inv _ _ _ _ _ _ _ _ _ _ hrun
  have j1 : J1 answers a1 rows1 := hF answers c row L mask rows1 a1 hJ f1
  have j2 : J2 answers a8 row1 L1 mask1 :=
    hC answers a1 rows1 a2 to1 a3 s1 row1 L1 a4 a8 mask1 j1 (Blk.yields_note _ _ _ _ n1) g1 w1
      (tr (tr (tr (Blk.yields_note _ _ _ _ n2)
        (Blk.yields_noteBy _ _ _ _ n3)) (Blk.yields_note _ _ _ _ n4)) (Blk.yields_note _ _ _ _ n5))
      hm1
  exact hN answers a8 row1 L1 mask1 c' j2 r1 hfail

/-- The program's yes, followed from block to block, for a proximity test of any number of
stages: the link's steps with the batching lead to the joint J0, and the stages lead from J0 to the
goal. -/
theorem blk_many (S : LinkShape) (first further : TableKey) (st : IoppStage)
    (rest : List IoppStage) (htest : S.test = st :: rest) (s : Start) (v : Fmt.View)
    (J0 : GroupJoint) (Goal : Prop) (hHead : HeadRuns S first further st (startCtx s v) J0)
    (hSt : StagesRun S.choice.masksRide st rest J0 Goal)
    (h : (linkVerify S first further).decides s v = true) : Goal := by
  obtain ⟨cEnd, hrun, hfail⟩ := decides_yields _ s v h
  obtain ⟨x, c1, c2, hsteps, htst, hall⟩ := linkVerify_inv S first further _ _ hrun
  rw [htest] at htst
  obtain ⟨answers, ca, St, cb, row, L, cd, ce, G, cf, k1, k2, k3, k4, k5, k6, k7, k8⟩ :=
    ioppVerify_inv _ _ _ _ _ _ _ htst
  have j0 : J0 answers cf row L x.mask :=
    hHead x c1 answers ca St cb row L cd ce G cf hsteps k1 k2 (by rw [htest]; exact k3) k4 k5 k6 k7
  rw [requireAllTested_inv _ _ hall] at hfail
  exact hSt answers cf row L x.mask c2 j0 k8 hfail

/-! ## What is asked of a chain and the program's stages -/

/-- The shapes of the two parts of a tree that a code switch to the stage s sends, if s is not the
last: the stage's oracle message and the mask of its fold. cur: the program's stage. -/
abbrev stageShapes (s : Sg) (cur : IoppStage) : List OracleShape :=
  [(switchTargetStage cur.code cur.maskCode (s.h + s.g) s.h 1).shape,
    (foldMaskNotice (ioppFoldShape cur {})).shape]

/-- Public facts on a fold at the stage s and the code switch to the stage s'. cur, nx: the
program's two stages. K: the statement's codes. n0: the chain's number of weights of the hiding
polynomial. dS, dC: the switch's two rounds. -/
structure StepPub (K : Codes) (s s' : Sg) (cur nx : IoppStage) (n0 : ℕ) (dS dC : PQ.RD) :
    Prop where
  /-- the program's stage has the stage's codes and row variables -/
  codes : StageCodes s cur K
  /-- the hiding polynomial has a weight on each entry of a mask row -/
  n0 : n0 = s.Z.l
  /-- the stage's mask code is among the statement's -/
  zk : (K.mask[cur.maskCode]?).map codeOf = some s.Z
  /-- the next stage's main code is among the statement's -/
  c' : (K.base[nx.code]?).map codeOf = some s'.C
  /-- the next stage's mask code is among the statement's -/
  z' : (K.mask[nx.maskCode]?).map codeOf = some s'.Z
  /-- a position of the stage's tree fits 32 bits -/
  small : s.C.a ≤ 32
  /-- what the switch's two rounds send and draw -/
  rounds : CsRounds s s' dS dC
  /-- the sample of the next stage's tables has the stage's number of variables -/
  bits : (Send.cube K
    (switchTargetStage nx.code nx.maskCode (s'.h + s'.g) s'.h 1).shape).bits = s'.st.na

/-- Public facts on the base case at the stage s. cur: the program's stage. dL, dB: the base
case's two rounds. fu, fs: the chain's readings of what they send. -/
structure LastPub (K : Codes) (s : Sg) (cur : IoppStage) (dL dB : PQ.RD)
    (fu : (wRound dL).Msg → GE) (fs : (wRound dB).Msg → s.cIn.MR) : Prop where
  /-- the program's stage has the stage's codes and row variables -/
  codes : StageCodes s cur K
  /-- the mask code's words are not longer than the main code's -/
  za : s.Z.a ≤ s.C.a
  /-- a position of the stage's tree fits 32 bits -/
  small : s.C.a ≤ 32
  /-- what the second round sends and draws -/
  draws : ∃ nB, SendsDraws dB nB 0 s.t s.C.a
  /-- the first round's message is read as its first element -/
  fu : ∀ m, fu m = lst (sentW dL m) 0
  /-- the second round's message is read as a message and tails of the stage's code -/
  fs : ∀ m, fs m = shownW s (sentW dB m)

/-- Public facts on the tree of a stage s that is folded, sent by a code switch in the round d. -/
structure StepOwn (K : Codes) (s : Sg) (cur : IoppStage) (d : PQ.RD) : Prop where
  /-- the stage has a row variable -/
  k1 : 1 ≤ s.h + s.g
  /-- the width of a column -/
  w : PQ.colW d.tree = 3 * 2 ^ (s.h + s.g) + 3 * (2 * 2 ^ s.h)
  /-- the stage's oracle message and the mask of its fold are placed in one tree -/
  one : OneTree K (sentOf (switchTargetStage cur.code cur.maskCode (s.h + s.g) s.h 1)
    #[foldMaskNotice (ioppFoldShape cur {})]) s.C.a

/-- Public facts on the tree of the last stage s, sent by a code switch in the round d. -/
structure LastOwn (K : Codes) (s : Sg) (cur : IoppStage) (d : PQ.RD) : Prop where
  /-- the stage has no mask row variable -/
  h0 : s.h = 0
  /-- the stage has no other row variable -/
  g0 : s.g = 0
  /-- the width of a column -/
  w : PQ.colW d.tree = 12
  /-- the number of positions -/
  n : PQ.posN d.tree = 2 ^ s.C.a
  /-- the stage's oracle message and the masking oracle are placed in one tree -/
  lay : ∀ lay, layTrees K (sentOf (switchTargetStage cur.code cur.maskCode (s.h + s.g) s.h 1)
    (stageOthers true cur [])) = some lay →
    ∃ shT : TreeShape, lay.shapes = #[shT] ∧ shT.logN = s.C.a ∧
      (∀ i, i < 2 → lay.tree.getD i 0 = 0 ∧ lay.part.getD i 0 = i) ∧
      shT.mainSymbols = #[3, 3] ∧ shT.maskSymbols = #[3, 3]

namespace Chain

/-- Public facts on the tree of the chain's first stage, sent by a code switch in the round d. -/
def Own (K : Codes) : {s : Sg} → Chain s → IoppStage → PQ.RD → Prop
  | _, .last s _ _ _ _ _ _ => fun cur d => LastOwn K s cur d
  | _, .step s _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fun cur d => StepOwn K s cur d

/-- The three words y, z, g are the standard readings of the tree of the chain's first stage, sent
in the message m of the round d. Of a stage that is folded: y and z, off the columns `colSt`. Of the
last stage: y and g, off the columns `lastColW` and `lastMk`. -/
def ReadAs : {s : Sg} → Chain s → (d : PQ.RD) → (wRound d).Msg → s.cIn.Word → s.cFr.Word →
    s.cIn.Word → Prop
  | _, .last s _ _ _ _ _ _ => fun d m y _ g =>
    y = wordIn s (lastColW d m.1) ∧ g = wordMk s (lastMk d m.1)
  | _, .step s _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fun d m y z _ =>
    y = wordIn s (colSt s d m.1) ∧ z = wordFr s (colSt s d m.1)

/-- Public facts on a chain and the program's stages cur :: rest: there are as many stages as the
chain has; `StepPub` at each step and `LastPub` at the end; `Own` of each tree that a switch of the
chain sends; the chain reads each of these trees in the standard way. -/
def Pub (K : Codes) : {s : Sg} → Chain s → IoppStage → List IoppStage → Prop
  | _, .last s _ dL dB fu fs _ => fun cur rest => rest = [] ∧ LastPub K s cur dL dB fu fs
  | _, .step s s' _ n0 _ _ _ dS dC fW fZ fG _ _ next => fun cur rest =>
    ∃ (nx : IoppStage) (later : List IoppStage), rest = nx :: later ∧
      StepPub K s s' cur nx n0 dS dC ∧ next.Own K nx dS ∧
      (∀ m, next.ReadAs dS m (fW m) (fZ m) (fG m)) ∧ next.Pub K nx later

/-- The joint before the chain's first stage, if a code switch has sent the stage's tree. n: the
tree's number. cur: the program's stage. q: the claim. b: the blocks' transcripts. -/
def JointAt (V : Fmt.View) (K : Codes) : {s : Sg} → (c : Chain s) → ℕ → IoppStage →
    GE × (s.cIn.J → GE) → c.Bl → GroupJoint
  | _, .last s _ dL dB _ _ _ => fun n cur q τ =>
    LastAt V K (n + 1) s cur q (PQ.rvSL (ckP .two) [dL, dB] τ) n
  | _, .step s _ _ _ _ dE dT dS dC _ _ _ _ _ next => fun n cur q b =>
    GroupAt V K (n + 1) s q
      (PQ.rvSL (ckP .two) (foldRds s dE dT) b.1 ++
        (PQ.rvSL (ckP .two) [dS, dC] b.2.1 ++ next.rvs b.2.2))
      (GroupTie s n (stageShapes s cur) #[some 0] #[some 0])

/-- The program's first stage has the codes and row variables of the chain's first stage. -/
theorem Pub.codes {K : Codes} {s : Sg} {c : Chain s} {cur : IoppStage} {rest : List IoppStage}
    (h : c.Pub K cur rest) : StageCodes s cur K := by
  cases c with
  | last s e dL dB fu fs εb => exact h.2.codes
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next =>
    obtain ⟨nx, later, _, hS, _⟩ := h
    exact hS.codes

end Chain

/-! ## The code switches, into a chain -/

/-- The code switch after the fold of a stage s whose tree a code switch has sent leads to the joint
before the chain next, under the hypotheses that the statement lists. n: the number of the tree of
s. d, m: the written round that sent it, and its message. pt: the point of the fold. -/
theorem csRuns_later (V : Fmt.View) (K : Codes) (n : ℕ) {s s' : Sg} (hf : CsFit s s')
    (cur nx : IoppStage) (later : List IoppStage) (next : Chain s') (n0 : ℕ) (dS dC : PQ.RD)
    (hP : StepPub K s s' cur nx n0 dS dC) (hO : next.Own K nx dS) (hN : next.Pub K nx later)
    (τC : Tr (PQ.uL (ckP .two) [dS, dC])) (b : next.Bl) (q : GE × (s.cMid.J → GE))
    (pt : Fin (s.h + s.g) → GE) (d : PQ.RD) (m : (wRound d).Msg)
    (hshow : Shows V n (treeCol d m))
    (hW : PQ.colW d.tree = 3 * 2 ^ (s.h + s.g) + 3 * (2 * 2 ^ s.h)) :
    CsRuns true nx later
      (SingleAt V K (n + 1) s q (PQ.rvSL (ckP .two) [dS, dC] τC ++ next.rvs b)
        (SingleTie s s' K nx.code nx.maskCode n (stageShapes s cur) #[some 0] #[some 0] pt))
      (next.JointAt V K (n + 1) nx (csNextW hf dS dC q (wordMid s (colSt s d m.1) pt) τC) b) := by
  have f3 : (foldMaskNotice (ioppFoldShape cur {})).shape.maskRows = 2 ^ s.h := by
    show 2 ^ cur.h = 2 ^ s.h
    rw [hP.codes.h]
  have hK' := hN.codes
  cases next with
  | last s' e dL dB fu fs εb =>
    obtain ⟨rfl, _⟩ := hN
    exact csRuns_second V K (n + 1) hf nx hK' hO.h0 hO.g0 dS dC hP.rounds τC _ q n _ _ pt d m hshow
      hW rfl rfl rfl rfl f3 hP.bits hO.lay
  | step s' s'' hf' n0' e dE dT dS' dC' fW fZ fG εf εc next' =>
    obtain ⟨n3, later', rfl, _⟩ := hN
    exact csRuns_middle V K (n + 1) hf nx n3 later' hK' hO.k1 dS dC hP.rounds τC _ q n _ _ pt d m
      hshow hW rfl rfl rfl rfl f3 hP.bits hO.one

/-- The code switch after the fold of the link's group leads to the joint before the chain next, if
more than one stage is left, under the hypotheses that the statement lists. The group has two
members of equal shape sh and no mask rows; fr: the fresh mask's shape; f1: the first row of the
second member's block. d, m: the written round that sent their tree, which has the number 0, and its
message. -/
theorem csRuns_link (V : Fmt.View) (K : Codes) (S : Sz) {s s' : Sg} (hf : CsFit s s')
    (hs0 : s.h = 0) (nx n3 : IoppStage) (later : List IoppStage) (next : Chain s')
    (dS dC : PQ.RD) (hr : CsRounds s s' dS dC) (hO : next.Own K nx dS)
    (hN : next.Pub K nx (n3 :: later)) (τC : Tr (PQ.uL (ckP .two) [dS, dC])) (b : next.Bl)
    (q : GE × (s.cMid.J → GE)) (sh fr : OracleShape) (pt : Fin (s.h + s.g) → GE)
    (d : PQ.RD) (m : (wRound d).Msg) (hshow : Shows V 0 (treeCol d m))
    (hW : PQ.colW d.tree = Fmt.M2.widthOf S.P.mems 1)
    (mem : Fmt.M2.Mem) (hmems : S.P.mems = [mem, mem]) (hE : mem.overE = true)
    (hm0 : mem.masks = 0) (f1 : ℕ) (hst : (Fmt.M2.starts [mem, mem]).1 = [some 0, some f1])
    (hf1 : mem.rows ≤ f1) (hk : f1 + mem.rows ≤ 2 ^ Fmt.M2.kOf [mem, mem])
    (hR : sh.mainRows = mem.rows) (h3 : sh.mainDeg = 3) (hz : sh.maskRows = 0)
    (hfm : fr.mainRows = 0) (hfz : 0 < fr.maskRows)
    (hbits : (Send.cube K
      (switchTargetStage nx.code nx.maskCode (s'.h + s'.g) s'.h 1).shape).bits = s'.st.na) :
    CsRuns true nx (n3 :: later)
      (SingleAt V K 1 s q (PQ.rvSL (ckP .two) [dS, dC] τC ++ next.rvs b)
        (SingleTie s s' K nx.code nx.maskCode 0 [sh, sh, fr] #[some 0, some f1] #[none, none] pt))
      (next.JointAt V K 1 nx (csNextW hf dS dC q (wordMid s (col1 S d m.1) pt) τC) b) := by
  have hK' := hN.codes
  cases next with
  | last s' e dL dB fu fs εb => exact absurd hN.1 (List.cons_ne_nil _ _)
  | step s' s'' hf' n0' e dE dT dS' dC' fW fZ fG εf εc next' =>
    exact csRuns_first V K 1 S hf hs0 nx n3 later hK' hO.k1 dS dC hr τC _ q 0 sh fr pt d m hshow hW
      mem hmems hE hm0 f1 hst hf1 hk hR h3 hz hfm hfz hbits hO.one

/-! ## The stages, along a chain -/

/-- A run of the program's stages cur :: rest after which no named test has failed leads from the
joint before the chain c to the chain's yes in the field, under the public facts `Pub` and `Own`, if
the view shows the written trees' columns. n: the number of the tree of the chain's first stage. d,
m: the written round that sent it, and its message. y, z, g: its standard readings. -/
theorem stagesRun_chain (V : Fmt.View) (K : Codes) {s : Sg} (c : Chain s) :
    ∀ (n : ℕ) (cur : IoppStage) (rest : List IoppStage) (d : PQ.RD) (m : (wRound d).Msg)
      (q : GE × (s.cIn.J → GE)) (y : s.cIn.Word) (z : s.cFr.Word) (g : s.cIn.Word) (b : c.Bl),
      c.Pub K cur rest → c.Own K cur d → c.ReadAs d m y z g → Shows V n (treeCol d m) →
      c.ShowsFrom V (n + 1) b →
      StagesRun true cur rest (c.JointAt V K n cur q b) (c.Acc q y z g b) := by
  induction c with
  | last s e dL dB fu fs εb =>
    intro n cur rest d m q y z g τ hP hO hR hsh _
    obtain ⟨rfl, hL⟩ := hP
    obtain ⟨rfl, rfl⟩ := hR
    obtain ⟨nB, hB⟩ := hL.draws
    have h := lastRuns_at V K (n + 1) s hO.h0 hO.g0 hL.za hL.small true cur hL.codes d dL dB m hO.w
      hO.n τ [] q n hsh hB
    rw [List.append_nil, ← hL.fu, ← hL.fs] at h
    exact h
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    intro n cur rest d m q y z g b hP hO hR hsh hS
    obtain ⟨nx, later, rfl, hSt, hO', hR', hN⟩ := hP
    obtain ⟨rfl, rfl⟩ := hR
    obtain ⟨hs1, hs2⟩ := hS
    obtain rfl := hSt.n0
    have hF := foldRuns_at V K (n + 1) s cur hSt.codes dE dT q b.1
      (PQ.rvSL (ckP .two) [dS, dC] b.2.1 ++ next.rvs b.2.2) _ _
      (foldTies_at K s s' cur hSt.codes nx.code nx.maskCode n (stageShapes s cur) #[some 0]
        #[some 0] (foldPt s dE dT b.1) _ hSt.zk hSt.c' hSt.z' hSt.small)
    have hC := csRuns_later V K n hf cur nx later next s.Z.l dS dC hSt hO' hN b.2.1 b.2.2
      (foldNext s s.Z.l dE dT q b.1) (foldPt s dE dT b.1) d m hsh hO.w
    have hI := ih (n + 1) nx later dS b.2.1.1
      (csNextW hf dS dC (foldNext s s.Z.l dE dT q b.1)
        (wordMid s (colSt s d m.1) (foldPt s dE dT b.1)) b.2.1)
      (fW b.2.1.1) (fZ b.2.1.1) (fG b.2.1.1) b.2.2 hN hO' (hR' _) hs1 hs2
    rw [← foldWords_std] at hI
    exact stagesRun_step true cur nx later _ _ _ _ hF hC hI

/-! ## From the program's yes -/

/-- The program's yes on a view gives the chain's yes in the field, for a link of two stages or
more whose masks ride, if the link's steps with the batching lead to the joint before the first fold
(`hHead`), the tie goes through the first fold (`hT`) and the first code switch leads to the joint
before the rest of the chain (`hC`). Asked besides: the public facts on the first stage (`hK`,
`hn0`) and on the rest of the chain (`hN`, `hO`, `hR`), and that the view shows the trees of the
chain's switches from the number 1 on (`hS`, `hS'`). Tie0, Tie1: what ties the columns of the first
tree to the written oracles. Λ, first, further, s0: the link's shape, the two tables and the start
of the program's run. -/
theorem acc_of_runs (V : Fmt.View) (Λ : LinkShape) (first further : TableKey) (st1 nx : IoppStage)
    (later : List IoppStage) (htest : Λ.test = st1 :: nx :: later)
    (hride : Λ.choice.masksRide = true) (s0 : Start) (K : Codes) {s s' : Sg} (hf : CsFit s s')
    (n0 e : ℕ) (dE dT dS dC : PQ.RD) (fW : (wRound dS).Msg → s'.cIn.Word)
    (fZ : (wRound dS).Msg → s'.cFr.Word) (fG : (wRound dS).Msg → s'.cIn.Word)
    (εf : Err (PQ.uL (ckP .two) (foldRds s dE dT))) (εc : Err (PQ.uL (ckP .two) [dS, dC]))
    (next : Chain s') (q : GE × (s.cIn.J → GE)) (y : s.cIn.Word) (z : s.cFr.Word)
    (g : s.cIn.Word) (τF : Tr (PQ.uL (ckP .two) (foldRds s dE dT)))
    (τC : Tr (PQ.uL (ckP .two) [dS, dC])) (b : next.Bl) (hK : StageCodes s st1 K)
    (hn0 : n0 = s.Z.l) (Tie0 : Ctx → GroupRow → GroupLayout → Nat → Prop)
    (Tie1 : Ctx → SingleRows → Prop)
    (hHead : HeadRuns Λ first further st1 (startCtx s0 V)
      (GroupAt V K 1 s q (PQ.rvSL (ckP .two) _ τF ++ (PQ.rvSL (ckP .two) _ τC ++ next.rvs b)) Tie0))
    (hT : FoldTies K s st1 (foldPt s dE dT τF) (PQ.rvSL (ckP .two) _ τC ++ next.rvs b) Tie0 Tie1)
    (hC : CsRuns true nx later
      (SingleAt V K 1 s (foldNext s n0 dE dT q τF) (PQ.rvSL (ckP .two) _ τC ++ next.rvs b) Tie1)
      (next.JointAt V K 1 nx
        (csNextW hf dS dC (foldNext s n0 dE dT q τF) (foldWords s y z (foldPt s dE dT τF)) τC) b))
    (hN : next.Pub K nx later) (hO : next.Own K nx dS)
    (hR : ∀ m, next.ReadAs dS m (fW m) (fZ m) (fG m)) (hS : Shows V 1 (treeCol dS τC.1))
    (hS' : next.ShowsFrom V 2 b) (hdec : (linkVerify Λ first further).decides s0 V = true) :
    (Chain.step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next).Acc q y z g (τF, τC, b) := by
  subst hn0
  have hF := foldRuns_at V K 1 s st1 hK dE dT q τF _ Tie0 Tie1 hT
  have hI := stagesRun_chain V K next 1 nx later dS τC.1
    (csNextW hf dS dC (foldNext s s.Z.l dE dT q τF) (foldWords s y z (foldPt s dE dT τF)) τC)
    (fW τC.1) (fZ τC.1) (fG τC.1) b hN hO (hR _) hS hS'
  refine blk_many Λ first further st1 (nx :: later) htest s0 V _ _ hHead ?_ hdec
  rw [hride]
  exact stagesRun_step true st1 nx later _ _ _ _ hF hC hI

/-- The program's yes on a view gives the chain's yes in the field, for a link of at least three
stages whose masks ride and whose group has two members of equal shape sh and no mask rows. Asked:
the public facts `Pub` and those on the group; that the link's steps with the batching lead to the
joint before the first fold (`hHead`); that the view shows the written trees' columns, the link's
tree under the number 0. fr: the fresh mask's shape; f1: the first row of the second member's
block. d, m: the written round that sent the link's tree, and its message. The first tree is read
off the columns `col1`. The word g is not read. -/
theorem acc_of_link (V : Fmt.View) (Λ : LinkShape) (first further : TableKey) (st1 : IoppStage)
    (rest : List IoppStage) (htest : Λ.test = st1 :: rest) (h2 : 2 ≤ rest.length)
    (hride : Λ.choice.masksRide = true) (s0 : Start) (K : Codes) (S : Sz) {s : Sg} (c : Chain s)
    (hs0 : s.h = 0) (hP : c.Pub K st1 rest) (q : GE × (s.cIn.J → GE)) (g : s.cIn.Word) (b : c.Bl)
    (sh fr : OracleShape) (d : PQ.RD) (m : (wRound d).Msg) (hshow : Shows V 0 (treeCol d m))
    (hS : c.ShowsFrom V 1 b) (hW : PQ.colW d.tree = Fmt.M2.widthOf S.P.mems 1)
    (mem : Fmt.M2.Mem) (hmems : S.P.mems = [mem, mem]) (hE : mem.overE = true)
    (hm0 : mem.masks = 0) (f1 : ℕ) (hst : (Fmt.M2.starts [mem, mem]).1 = [some 0, some f1])
    (hf1 : mem.rows ≤ f1) (hk : f1 + mem.rows ≤ 2 ^ Fmt.M2.kOf [mem, mem])
    (hR : sh.mainRows = mem.rows) (h3 : sh.mainDeg = 3) (hz : sh.maskRows = 0)
    (hfm : fr.mainRows = 0) (hfz : 0 < fr.maskRows)
    (hHead : HeadRuns Λ first further st1 (startCtx s0 V)
      (GroupAt V K 1 s q (c.rvs b)
        (GroupTie s 0 [sh, sh, fr] #[some 0, some f1] #[none, none])))
    (hdec : (linkVerify Λ first further).decides s0 V = true) :
    c.Acc q (wordIn s (col1 S d m.1)) (wordFr s (col1 S d m.1)) g b := by
  cases c with
  | last s e dL dB fu fs εb =>
    rw [hP.1] at h2
    exact absurd h2 (by decide)
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next =>
    obtain ⟨nx, later, rfl, hSt, hO, hRd, hN⟩ := hP
    obtain ⟨n3, later', rfl⟩ : ∃ n3 later', later = n3 :: later' := by
      cases later with
      | nil => exact absurd h2 (Nat.lt_irrefl 1)
      | cons a l => exact ⟨a, l, rfl⟩
    have hC := csRuns_link V K S hf hs0 nx n3 later' next dS dC hSt.rounds hO hN b.2.1 b.2.2
      (foldNext s n0 dE dT q b.1) sh fr (foldPt s dE dT b.1) d m hshow hW mem hmems hE hm0 f1 hst
      hf1 hk hR h3 hz hfm hfz hSt.bits
    rw [← foldWords_std] at hC
    exact acc_of_runs V Λ first further st1 nx (n3 :: later') htest hride s0 K hf n0 e dE dT dS dC
      fW fZ fG εf εc next q _ _ g b.1 b.2.1 b.2.2 hSt.codes hSt.n0 _ _ hHead
      (foldTies_at K s s' st1 hSt.codes nx.code nx.maskCode 0 _ _ _ _ _ hSt.zk hSt.c' hSt.z'
        hSt.small) hC hN hO hRd hS.1 hS.2 hdec

end OnBytes.Slice
