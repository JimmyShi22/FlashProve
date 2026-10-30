-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/JointK.lean: the joint of the proximity test's law, three propositions at that
joint, and the induction to `Chain.Acc`.

The law of the proximity test (the kind K12) says: a yes of the block's decision gives the yes of
the field test of the library's proved chain of fold, code switch and base case (`Chain.Acc`,
OnBytes/Slice/ManyDefs.lean). This file names the relation that is carried from stage to stage and
proves the induction. It speaks of the frame Johnson/Desc/K12/Frame.lean at any parts on the record
`T12` (Johnson/Desc/K12/Join.lean): the parts come in through three propositions alone. The cuts of
rounds and groups are those of `Block.andThen`, by `stagesFrom_ok` and `stagesFrom_last`
(Johnson/Desc/K12/FrameLaws.lean).
Main names:
  `JointK`: the joint in front of stage j, between the record t, the rounds rs and groups gs still
    to come, and a chain c from that stage on with its claim q, its words y, z, g and its
    transcripts b. Ten clauses: what passes is one claim (row, L); the stage and the stages behind
    it in the program's form; `Chain.Pub` at the record's codes; the row read in the field is q; the
    row has no kept form and the layout no kept member; rs are the chain's written rounds as
    `Block.step` shows them, without the sealed digest; as many declared rounds are left as the
    chain has; under each later switch's cut of the groups stand columns of that switch's written
    tree (`ShownLater`); a tie on the present tree or trees (`TieNow`); the chain's stages are the
    place's from j on.
  `ReadTie`: the tie in front of a fold: whatever `readOld` (Johnson/Top/H0/Tw/L9/Switch.lean)
    returns on this stage's cut of the columns, at the list of positions made of the drawn ones, at
    a book and a statement that keep the record's, is `foldWords y z` at the listed positions.
  `SingleK`: the joint behind a fold.
  `FoldKeeps`, `SwitchKeeps`, `BaseGives`: three propositions, asserted nowhere in this file: the
    fold's part keeps the joint, the switch's part with the batching behind it keeps it, the base
    case's part spends it. They are proved in Johnson/Desc/K12/Law/FoldKeeps.lean, SwitchKeeps.lean
    and BaseGives.lean.
  `later_law`: under the three, `JointK` and a yes of `stagesFrom X p j cur rest l` give `c.Acc q y
    z g b`. By recursion on the chain.
Limits: The clauses on the written rounds and columns, and the tie at the first stage, are asked of
whoever shows `JointK` in front of stage 0. No quantifier over free views stands here: the rounds
are pinned to written rounds and the columns to written trees, and a written round's positions lie
in their range by `Chain.Pub`. Parts that say no to everything meet every law of the form "a yes
gives ..." by its form; parts that say yes to everything fail `BaseGives`. The joint's clauses that
are Booleans on a record were evaluated at the honest records of the four proximity tests of the two
stored example proofs and were all true [the prints are not in this library]; the clauses in the
field and on the written rounds and columns are no Booleans and were not evaluated. No statement and
no proof of this file reaches a routine that runs in a context of the program `verify-on-bytes`
(`OnBytes.Ctx`, `OnBytes.Blk`, `OnBytes.Chan`); that program's plain records and pure functions,
some with names that begin with `Blk.`, and lemmas on them, are used. No soundness is claimed.
Nothing here is about hiding.
-/
import Johnson.Desc.K12.FrameLaws
import Johnson.Desc.K12.Join
import Johnson.Top.H0.P5Law.Law
import OnBytes.Slice.BlkProxChain

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12

abbrev Gs : Type := List (List (Nat × List UInt64))
abbrev Blk' : Type := Block T12 Unit

/-! ## The frame's cuts, in closed form -/

/-- The groups that declared rounds are owed (Block.openings, of a list). -/
def nOpen (l : List Fmt.DeclaredRound) : Nat :=
  l.foldl (fun n r => n + r.stored.length + r.opens.length) 0

def cutF (l : Laid) (k : Nat) : List Fmt.DeclaredRound := (l.take (1 + k)).map (·.1)
def cutS (l : Laid) (k : Nat) : List Fmt.DeclaredRound := ((l.drop (1 + k)).take 2).map (·.1)
def grpF (l : Laid) (k : Nat) (gs : Gs) : Gs := gs.take (nOpen (cutF l k))
def grpS (l : Laid) (k : Nat) (gs : Gs) : Gs := (gs.drop (nOpen (cutF l k))).take (nOpen (cutS l k))
def grpR (l : Laid) (k : Nat) (gs : Gs) : Gs := gs.drop (nOpen (cutF l k) + nOpen (cutS l k))

/-! ## The joint's clauses -/

/-- The stages from number j on, in the program's form. -/
def stagesAt (p : P12) : Nat → List Fmt.M1.Stage → Option (List IoppStage)
  | _, [] => some []
  | j, s :: l => (stageAt p j s).bind fun c => (stagesAt p (j + 1) l).map (c :: ·)

/-- The fold's fresh mask: its number, and the statement and the book behind its entering: it has
come (the record names it), or the fold's own first message brings it (Closing.foldD's second arm).
-/
def MaskCase (p : P12) (t : T12) (F : FoldShape) (id : Nat) (st : Statement) (book : TreeBook) :
    Prop :=
  (t.mask = some id ∧ st = t.st ∧ book = t.book) ∨
  (t.mask = none ∧ ∃ (opened : List (Nat × Nat × List UInt64)) (ids : Array Nat)
      (d1 : _root_.Desc.Plain.DState Unit),
    Ground.recvP p.nums.firstTree ⟨t.st, t.book, t.roots, opened, ()⟩ #[foldMaskNotice F] =
      some (ids, d1) ∧ ids[0]? = some id ∧ st = d1.st ∧ book = d1.book)

/-- The tie in front of a switch. poss: the positions that the switch's round draws; the list of
positions is made of them. (With a free list the tie would hold at several trees only by the luck of
their widths: a key names no tree where the tree's number less the first tree's is cut off at 0.)
Whatever the reading of the folded rows returns on the columns cols, at any book and statement that
keep book's and st's public part, is the three folded words at the listed positions. -/
def ReadTie (firstTree : Nat) (s : Sg) (y : s.cIn.Word) (z : s.cFr.Word) (F : FoldShape)
    (st : Statement) (book : TreeBook) (id : Nat) (cols : List Tw.L9.Col) (poss : List Nat) : Prop
        :=
  ∀ (i : Tw.L9.SwIn) (pos : Positions) (B : TreeBook) (left : List Tw.L9.Col) (ys : Array E)
    (S : Statement) (row : GroupRow) (eps claim : E) (gamma : List E),
    BookKeeps book i.book → ShapesKeep st i.st → i.firstTree = firstTree → i.opened = cols →
    i.old = foldOutput S F row id eps gamma claim → row.kept = #[] →
    gamma.length = s.h + s.g → pos = Positions.ofDraws s.C.a poss →
    Tw.L9.readOld i pos = .ok (B, left, ys) →
    ∀ (x : s.Ps), x.val ∈ pos.all → ∀ α : s.cMid.Aa,
      s.cMid.T (foldWords s y z (readP (s.h + s.g) gamma)) x α = symS s i.old pos ys x.val α

/-- The tie in front of the base case. -/
def LastTie (s : Sg) (y g : s.cIn.Word) (gs : Gs) : Prop :=
  ∃ (col : ℕ → Fmt.M1.Col) (mk : ℕ → Fmt.M1.E × Fmt.M1.E), y = wordIn s col ∧ g = wordMk s mk ∧
    ∀ grp ∈ gs, ∀ x q, Prox.colOf grp x = some q →
      Fmt.M1.ent (col x).main 0 = q.1 ∧ (mk x).1 = q.2.1 ∧
        Fmt.M1.ent (col x).mask 0 = q.2.2.1 ∧ (mk x).2 = q.2.2.2

def TieNow (p : P12) (cu : IoppStage) (t : T12) (L : GroupLayout) : {s : Sg} → (c : Chain s) →
    s.cIn.Word → s.cFr.Word → s.cIn.Word → c.Bl → Laid → Gs → Prop
  | s, .last _ _ _ _ _ _ _ => fun y _ g _ _ gs => LastTie s y g gs
  | s, .step _ _ _ _ _ _ _ _ dC _ _ _ _ _ _ => fun y z _ b l gs =>
    ∀ id st book, MaskCase p t (ioppFoldShape cu L) id st book →
      ReadTie p.nums.firstTree s y z (ioppFoldShape cu L) st book id
        (keyed p (cutS l cu.k) (grpS l cu.k gs)) (rvOf dC b.2.1.2.2.1 b.2.1.2.2.2.1).poss

/-- Under the cut of the groups that belongs to the chain's first stage stand columns of the tree
that the round d sent (o: its written oracle); and so on behind each switch. -/
def ShownFrom : {s : Sg} → (c : Chain s) → (d : PQ.RD) → (wRound d).Orc → c.Bl → Laid → Gs → Prop
  | _, .last _ _ _ _ _ _ _ => fun d o _ _ gs => ∀ grp ∈ gs, ∀ x ∈ grp, x.2 = colW d o x.1
  | s, .step _ _ _ _ _ _ _ dS _ _ _ _ _ _ next => fun d o b l gs =>
    (∀ grp ∈ grpS l (s.h + s.g) gs, ∀ x ∈ grp, x.2 = colW d o x.1) ∧
      ShownFrom next dS b.2.1.1.1 b.2.2 (l.drop (s.h + s.g + 3)) (grpR l (s.h + s.g) gs)

def ShownLater : {s : Sg} → (c : Chain s) → c.Bl → Laid → Gs → Prop
  | _, .last _ _ _ _ _ _ _ => fun _ _ _ => True
  | s, .step _ _ _ _ _ _ _ dS _ _ _ _ _ _ next => fun b l gs =>
    ShownFrom next dS b.2.1.1.1 b.2.2 (l.drop (s.h + s.g + 3)) (grpR l (s.h + s.g) gs)

def ClaimNow : {s : Sg} → Chain s → GE × (s.cIn.J → GE) → GroupRow → Prop
  | s, .last _ _ _ _ _ _ _ => fun q row => stmGk s 1 0 row = q ∧ FixLaw row.c [zeroE] ∧
      s.h = 0 ∧ s.g = 0
  | s, .step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fun q row => stmG s row = q

/-- The chain's stages, in the format's records. -/
def stagesOf : {s : Sg} → Chain s → List Fmt.M1.Stage
  | s, .last _ _ _ _ _ _ _ => [s.st]
  | s, .step _ _ _ _ _ _ _ _ _ _ _ _ _ _ next => s.st :: stagesOf next

/-- The joint in front of a stage. The file's head lists its ten clauses. -/
def JointK (p : P12) {s : Sg} (c : Chain s) (q : GE × (s.cIn.J → GE)) (y : s.cIn.Word)
    (z : s.cFr.Word) (g : s.cIn.Word) (b : c.Bl) (j : Nat) (cur : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (l : Laid) (t : T12) (rs : List Fmt.RoundView) (gs : Gs) : Prop :=
  ∃ (row : GroupRow) (L : GroupLayout) (cu : IoppStage) (restI : List IoppStage),
    t.pass = .claim row L ∧ stageAt p j cur = some cu ∧ stagesAt p (j + 1) rest = some restI ∧
    c.Pub t.st.codes cu restI ∧ ClaimNow c q row ∧ row.kept = #[] ∧
    (∀ i, i < L.members.size → L.kept.getD i false = false) ∧
    rs = (c.rvs b).map noDigest ∧ l.length = c.rds.length ∧ ShownLater c b l gs ∧
    TieNow p cu t L c y z g b l gs ∧ stagesOf c = cur :: rest

/-- The joint behind the fold of a chain's first step. -/
def SingleK (p : P12) {s s' : Sg} (n0 : ℕ) (dE dT dS dC : PQ.RD) (next : Chain s')
    (fW : (wRound dS).Msg → s'.cIn.Word) (fZ : (wRound dS).Msg → s'.cFr.Word)
    (fG : (wRound dS).Msg → s'.cIn.Word)
    (q : GE × (s.cIn.J → GE)) (y : s.cIn.Word) (z : s.cFr.Word)
    (τF : Tr (PQ.uL (ckP .two) (foldRds s dE dT))) (τC : Tr (PQ.uL (ckP .two) [dS, dC]))
    (bN : next.Bl) (j : Nat) (cur nxt : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid)
    (t : T12) (gs : Gs) : Prop :=
  ∃ (rows : SingleRows) (gp : Nat) (cu nx : IoppStage) (later : List IoppStage),
    t.pass = .single rows gp ∧ stageAt p j cur = some cu ∧ stageAt p (j + 1) nxt = some nx ∧
    stagesAt p (j + 2) rest = some later ∧
    StepPub t.st.codes s s' cu nx n0 dS dC ∧ next.Own t.st.codes nx dS ∧
    (∀ m, next.ReadAs dS m (fW m) (fZ m) (fG m)) ∧ next.Pub t.st.codes nx later ∧
    stmS s rows = foldNext s n0 dE dT q τF ∧
    FoldedFit s s' t.st.codes nx.code nx.maskCode rows ∧
    t.st.groups[gp]? = some { code := nx.code, maskCode := nx.maskCode } ∧
    l.length = (s.h + s.g + 3) + next.rds.length ∧
    ShownFrom next dS τC.1.1 bN (l.drop (s.h + s.g + 3)) (grpR l (s.h + s.g) gs) ∧
    (∀ (i : Tw.L9.SwIn) (pos : Positions) (B : TreeBook) (left : List Tw.L9.Col) (ys : Array E),
      BookKeeps t.book i.book → ShapesKeep t.st i.st → i.firstTree = p.nums.firstTree →
      i.opened = keyed p (cutS l cu.k) (grpS l cu.k gs) → i.old = rows →
      pos = Positions.ofDraws s.C.a (rvOf dC τC.2.2.1 τC.2.2.2.1).poss →
      Tw.L9.readOld i pos = .ok (B, left, ys) →
      ∀ (x : s.Ps), x.val ∈ pos.all → ∀ α : s.cMid.Aa,
        s.cMid.T (foldWords s y z (foldPt s dE dT τF)) x α = symS s rows pos ys x.val α) ∧
    s.st = cur ∧ stagesOf next = nxt :: rest

/-! ## The three owed laws -/

/-- A proposition, asserted nowhere in this file: the fold's part keeps the joint. -/
def FoldKeeps (X : Parts T12) (p : P12) : Prop :=
  ∀ {s s' : Sg} (hf : CsFit s s') (n0 e : ℕ) (dE dT dS dC : PQ.RD)
    (fW : (wRound dS).Msg → s'.cIn.Word) (fZ : (wRound dS).Msg → s'.cFr.Word)
    (fG : (wRound dS).Msg → s'.cIn.Word) (εf : Err (PQ.uL (ckP .two) (foldRds s dE dT)))
    (εc : Err (PQ.uL (ckP .two) [dS, dC])) (next : Chain s')
    (q : GE × (s.cIn.J → GE)) (y : s.cIn.Word) (z : s.cFr.Word) (g : s.cIn.Word)
    (b : (Chain.step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next).Bl)
    (j : Nat) (cur nxt : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid) (t t1 : T12)
    (rs : List Fmt.RoundView) (gs : Gs),
    JointK p (Chain.step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next) q y z g b j cur
      (nxt :: rest) l t rs gs →
    (X.fold p j cur (cutF l cur.k)).decide t
      ((PQ.rvSL (ckP .two) (foldRds s dE dT) b.1).map noDigest) (grpF l cur.k gs) = .ok t1 →
    SingleK p n0 dE dT dS dC next fW fZ fG q y z b.1 b.2.1 b.2.2 j cur nxt rest l t1 gs

/-- A proposition, asserted nowhere in this file: the switch's part and the batching behind it lead
from the joint behind the fold to the joint in front of the next stage, at the claim that the chain
carries and the words that it reads off the switch's message. -/
def SwitchKeeps (X : Parts T12) (p : P12) : Prop :=
  ∀ {s s' : Sg} (hf : CsFit s s') (n0 : ℕ) (dE dT dS dC : PQ.RD)
    (fW : (wRound dS).Msg → s'.cIn.Word) (fZ : (wRound dS).Msg → s'.cFr.Word)
    (fG : (wRound dS).Msg → s'.cIn.Word) (next : Chain s')
    (q : GE × (s.cIn.J → GE)) (y : s.cIn.Word) (z : s.cFr.Word)
    (τF : Tr (PQ.uL (ckP .two) (foldRds s dE dT))) (τC : Tr (PQ.uL (ckP .two) [dS, dC]))
    (bN : next.Bl) (j : Nat) (cur nxt : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid)
    (t1 t2 t3 : T12) (gs : Gs),
    SingleK p n0 dE dT dS dC next fW fZ fG q y z τF τC bN j cur nxt rest l t1 gs →
    (X.switch p j cur nxt rest.isEmpty (cutS l cur.k)).decide t1
      ((PQ.rvSL (ckP .two) [dS, dC] τC).map noDigest) (grpS l cur.k gs) = .ok t2 →
    (X.batBehind p (j + 1) nxt (cutS l cur.k)).decide t2 [] [] = .ok t3 →
    (!p.early || X.maskCame t3) = true →
    JointK p next
      (csNextW hf dS dC (foldNext s n0 dE dT q τF) (foldWords s y z (foldPt s dE dT τF)) τC)
      (fW τC.1) (fZ τC.1) (fG τC.1) bN (j + 1) nxt rest (l.drop (cur.k + 3)) t3
      ((next.rvs bN).map noDigest) (grpR l cur.k gs)

/-- A proposition, asserted nowhere in this file: the base case's yes gives the chain's last test in
the field. -/
def BaseGives (X : Parts T12) (p : P12) : Prop :=
  ∀ (s : Sg) (e : ℕ) (dL dB : PQ.RD) (fu : (wRound dL).Msg → GE)
    (fs : (wRound dB).Msg → s.cIn.MR) (εb : Err (PQ.uL (ckP .two) [dL, dB]))
    (q : GE × (s.cIn.J → GE)) (y : s.cIn.Word) (z : s.cFr.Word) (g : s.cIn.Word)
    (τ : (Chain.last s e dL dB fu fs εb).Bl)
    (j : Nat) (cur : Fmt.M1.Stage) (l : Laid) (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs),
    JointK p (Chain.last s e dL dB fu fs εb) q y z g τ j cur [] l t rs gs →
    (X.base p j cur (l.map (·.1))).decide t rs gs = .ok tE →
    (Chain.last s e dL dB fu fs εb).Acc q y z g τ

/-! ## The induction -/

theorem rvSL_length (C : PQ.CK) : ∀ (ds : List PQ.RD) (τ : Tr (PQ.uL C ds)),
    (PQ.rvSL C ds τ).length = ds.length
  | [], _ => rfl
  | _ :: ds, (_, _, τ) => congrArg (· + 1) (rvSL_length C ds τ)

theorem stageAt_k {p : P12} {j : Nat} {cur : Fmt.M1.Stage} {cu : IoppStage}
    (h : stageAt p j cur = some cu) : cu.k = cur.k := by
  unfold stageAt at h
  cases hi : p.idx[j]? with
  | none => rw [hi] at h; cases h
  | some i => rw [hi] at h; cases h; rfl

theorem stagesAt_nil {p : P12} {j : Nat} {rest : List Fmt.M1.Stage}
    (h : stagesAt p j rest = some []) : rest = [] := by
  cases rest with
  | nil => rfl
  | cons a r =>
    unfold stagesAt at h
    cases ha : stageAt p j a with
    | none => rw [ha] at h; cases h
    | some c =>
      rw [ha] at h
      cases hr : stagesAt p (j + 1) r with
      | none => simp [hr] at h
      | some x => simp [hr] at h

theorem stagesAt_cons {p : P12} {j : Nat} {rest : List Fmt.M1.Stage} {nx : IoppStage}
    {later : List IoppStage} (h : stagesAt p j rest = some (nx :: later)) :
    ∃ nxt rest', rest = nxt :: rest' ∧ stageAt p j nxt = some nx ∧
      stagesAt p (j + 1) rest' = some later := by
  cases rest with
  | nil => cases h
  | cons a r =>
    unfold stagesAt at h
    cases ha : stageAt p j a with
    | none => rw [ha] at h; cases h
    | some c =>
      rw [ha] at h
      cases hr : stagesAt p (j + 1) r with
      | none => simp [hr] at h
      | some x =>
        simp [hr] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨a, r, rfl, ha, hr⟩

/-- The law on the stages, under the three propositions. -/
theorem later_law (X : Parts T12) (p : P12) (hF : FoldKeeps X p) (hS : SwitchKeeps X p)
    (hB : BaseGives X p) : ∀ {s : Sg} (c : Chain s) (q : GE × (s.cIn.J → GE)) (y : s.cIn.Word)
      (z : s.cFr.Word) (g : s.cIn.Word) (b : c.Bl) (j : Nat) (cur : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (l : Laid) (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs),
      JointK p c q y z g b j cur rest l t rs gs →
      (stagesFrom X p j cur rest l : Blk').decide t rs gs = .ok tE → c.Acc q y z g b := by
  intro s c
  induction c with
  | last s e dL dB fu fs εb =>
    intro q y z g b j cur rest l t tE rs gs hJ h
    have hrest : rest = [] := by
      obtain ⟨_, _, _, restI, _, _, h3, h4, _⟩ := hJ
      obtain ⟨rfl, _⟩ := h4
      exact stagesAt_nil h3
    subst hrest
    rw [stagesFrom_last] at h
    exact hB s e dL dB fu fs εb q y z g b j cur l t tE rs gs hJ h
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    intro q y z g b j cur rest l t tE rs gs hJ h
    obtain ⟨row, L, cu, restI, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hJ
    have hJ' : JointK p (Chain.step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next) q y z g b j cur
      rest l t rs gs := ⟨row, L, cu, restI, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    obtain ⟨nx, later, rfl, hP, _, _, _⟩ := h4
    obtain ⟨nxt, rest', rfl, _, _⟩ := stagesAt_cons h3
    have hk : cur.k = s.h + s.g := (stageAt_k h2).symm.trans hP.codes.k
    obtain ⟨t1, t2, t3, f1, f2, f3, f4, f5⟩ := (stagesFrom_ok X p j cur nxt rest' l t tE rs gs).1 h
    have hl : l.length = (1 + (s.h + s.g)) + (2 + next.rds.length) := by
      rw [h9]
      show (foldRds s dE dT ++ ([dS, dC] ++ next.rds)).length = _
      simp [foldRds]
      omega
    have nF : (foldAt X p j cur l : Blk').rounds.length = 1 + (s.h + s.g) := by
      simp [foldAt, Part.at, hk]
      omega
    have nS : (switchAt X p j cur nxt rest'.isEmpty l : Blk').rounds.length = 2 := by
      simp [switchAt, Part.at, hk]
      omega
    have lA : ((PQ.rvSL (ckP .two) (foldRds s dE dT) b.1).map noDigest).length
        = 1 + (s.h + s.g) := by
      rw [List.length_map, rvSL_length]
      simp [foldRds]
      omega
    have lB : ((PQ.rvSL (ckP .two) [dS, dC] b.2.1).map noDigest).length = 2 := by
      rw [List.length_map, rvSL_length]
      rfl
    have hrs : rs = (PQ.rvSL (ckP .two) (foldRds s dE dT) b.1).map noDigest ++
        ((PQ.rvSL (ckP .two) [dS, dC] b.2.1).map noDigest ++ (next.rvs b.2.2).map noDigest) := by
      rw [h8]
      show List.map noDigest (_ ++ (_ ++ _)) = _
      rw [List.map_append, List.map_append]
    have r1 : rs.take (foldAt X p j cur l : Blk').rounds.length =
        (PQ.rvSL (ckP .two) (foldRds s dE dT) b.1).map noDigest := by
      rw [nF, hrs, ← lA, List.take_left]
    have r2 : (rs.drop (foldAt X p j cur l : Blk').rounds.length).take
        (switchAt X p j cur nxt rest'.isEmpty l : Blk').rounds.length =
        (PQ.rvSL (ckP .two) [dS, dC] b.2.1).map noDigest := by
      rw [nF, nS, hrs, ← lA, List.drop_left, ← lB, List.take_left]
    have r3 : rs.drop ((foldAt X p j cur l : Blk').rounds.length +
        (switchAt X p j cur nxt rest'.isEmpty l : Blk').rounds.length) =
        (next.rvs b.2.2).map noDigest := by
      rw [nF, nS, hrs, ← List.drop_drop, ← lA, List.drop_left, ← lB, List.drop_left]
    rw [r1] at f1
    rw [r2] at f2
    rw [r3] at f5
    have k1 := hF hf n0 e dE dT dS dC fW fZ fG εf εc next q y z g b j cur nxt rest' l t t1 rs gs
      hJ' f1
    have k2 := hS hf n0 dE dT dS dC fW fZ fG next q y z b.1 b.2.1 b.2.2 j cur nxt rest' l t1 t2 t3
      gs k1 f2 f3 f4
    exact ih _ _ _ _ b.2.2 (j + 1) nxt rest' (l.drop (cur.k + 3)) t3 tE _ _ k2 f5

end H2K.JointK
