-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Honest/Shape/TestCore.lean: WHAT A PROXIMITY TEST WRITES, ON SHAPES: a function
with code, `testCore`, from the shape of statement, book and count of roots in front of a test
(`CoreSh`, Johnson/Desc/Ground/Shape/Core.lean), the plan of the place, the group's number and the
mask's number, to the shape behind the test; and the law that holds it against the description's
own sub-protocol (`proximityTestKind guardedProximityTestParts p`, Johnson/Desc/K12/JoinGuarded.lean): WHERE THE SUB-PROTOCOL ACCEPTS,
ON WHATEVER ROUNDS AND COLUMNS, `testCore` RETURNS THE SHAPE BEHIND. Both cases of the first fold's
mask (it has come; the fold receives it). No prover, no coin, no frame for an honest side.

The thin shape. Inside the test the structure `T12` is read as `ThinSh`: the core's shape, the
group's number, the mask's number, and of what passes from a part to the next only what the core's
changes hang on: behind a batching the layout; behind a fold the numbers of the messages that the
switch will ask for, and the new group's number.

Part by part (X_thin: where the part accepts, XThin at the thin shape in front returns the one
behind).
  `batThin`, `bat_thin`   the beginning of the test on the group.
  `foldThin`, `fold_thin`   the mask comes, if it has not (a receiving); it is spent; a new group.
  `switchThin`, `switch_thin`   a switch AND the batching behind it, as one step: a sending of the
      new message and the next mask; the sample is admitted; the ledger is shut; the message joins
      the new group; each tree that holds a message asked for is counted as opened once; the new
      group's test begins. The rows that the switch lays on the new group do not show: the
      beginning takes them off.
  `baseThin`, `base_thin`   the masking message is spent; the last tree is counted.
  `stagesThin`, `testThin`, `stages_thin`, `k12_thin`, `testCore`, `k12_core_sh`   the whole.

By what. The parts' accepts are opened as Johnson/Desc/K12/Law/Calls.lean opens them; the ground's
functions on shapes and their laws: Johnson/Desc/Ground/Shape/Ground.lean; the switch and the
batching behind it: the library's `switchUnfolds` (Johnson/Desc/K12/Law/SwUnfold.lean),
`switch_roots`, `behindJ_roots`, `readOld_inv`; the frame: `k12_ok`, `stagesFrom_ok`, `like_P5`.

Limits. ONE DIRECTION ALONE: from the sub-protocol's accept to the shape behind. `testCore` ASKS
FEWER GUARDS THAN THE SUB-PROTOCOL: that it returns says nothing on whether the sub-protocol
accepts: the front's clauses, the guards on the group's trees, on shapes of folds and switches, on
rows and on columns are not in it. Premises: the masks come early and a sample has one answer (the
sub-protocol's own test on the plan asks both). The two marks beside the shape
(Johnson/Desc/Ground/Shape/Marks.lean) are not carried here. Nothing on completeness, on soundness
or on what is hidden.


-/
import Johnson.Desc.K12.Honest.Shape.Test
import Johnson.Desc.Ground.Shape.More
import Johnson.Desc.K12.Law.Calls
import Johnson.Desc.K12.Law.SwUnfold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Out (dT DS beginRunP_at foldD_state like_P5)
open H2K.FoldLaw (bind_ok got_ok)
open H2K.JointK H2K.Sw

/-! ## 1 The thin shape -/

/-- Of what passes from a part to the next: what the core's changes hang on. -/
inductive ThinPass where
  | nothing
  | claim (lay : GroupLayout)
  | single (asked : List Nat) (next : Nat)
  | switched

structure ThinSh where
  core : CoreSh
  g : Nat
  pass : ThinPass
  mask : Option Nat

def thinPass : Passing → ThinPass
  | .nothing => .nothing
  | .claim _ L => .claim L
  | .single rows n => .single (singleRowsOracles rows).toList n
  | .switched _ _ _ => .switched

def thinSh (t : T12) : ThinSh := ⟨coreSh ⟨t.st, t.book, t.roots⟩, t.g, thinPass t.pass, t.mask⟩

/-! ## 2 The batching -/

def batThin (p : P12) (a : ThinSh) : Option ThinSh :=
  match a.pass, p.idx with
  | .nothing, _ :: _ =>
    (beginRunS a.core a.g).map fun x =>
      ⟨x.2, a.g, .claim x.1.1, if p.early then a.mask else none⟩
  | _, _ => none

theorem bat_thin (p : P12) (cut : List Fmt.DeclaredRound) (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (batJ p cut).decide t rs gs = .ok t1) :
    batThin p (thinSh t) = some (thinSh t1) := by
  unfold batJ at h
  dsimp only at h
  split at h
  · rename_i i is e1 e2
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨⟨row, L⟩, s1⟩, hx, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨rfl, _⟩ := back_ok h
    unfold H2K.batE at hx
    split at hx
    · obtain ⟨_, _, hx⟩ := bind_ok hx
      obtain ⟨⟨row', L', S'⟩, hb, hx⟩ := bind_ok hx
      cases hx
      have hb' := mapError_ok hb
      unfold First.Close.bat at hb'
      obtain ⟨_, _, hb'⟩ := bind_ok hb'
      obtain ⟨⟨input, d⟩, hbeg, hb'⟩ := bind_ok hb'
      obtain ⟨_, _, hb'⟩ := bind_ok hb'
      obtain ⟨_, _, hb'⟩ := bind_ok hb'
      obtain ⟨_, _, hb'⟩ := bind_ok hb'
      cases hb'
      have k := beginRunP_at (First.Close.onSt t.st) (dT t []) rfl (got_ok hbeg)
      have c := beginRun_carries (dT t []) _ t.g input k
      unfold batThin
      show (match thinPass t.pass, p.idx with
        | .nothing, _ :: _ => _
        | _, _ => none) = _
      rw [e1, e2]
      show (beginRunS (shD (dT t [])) t.g).map _ = _
      rw [c]
      rfl
    · cases hx
  · cases h

/-! ## 3 The fold -/

/-- What an accept of the plain fold leaves of the carried state, and which messages the single rows
that it returns name. (After `foldD_state`, Johnson/Desc/K12/Law/OutK.lean, with one clause more.)
-/
theorem foldD_asked (F : Nat) (d d' : DS) (Fs : FoldShape) (row : GroupRow) (mask : Option Nat)
    (es : List Fmt.Entry) (rs : List Fmt.RoundView) (out : SingleRows)
    (h : First.Close.foldD F d Fs row mask es rs = .ok (out, d')) :
    ∃ (id : Nat) (d1 : DS),
      ((mask = some id ∧ d1 = d) ∨ (mask = none ∧ ∃ ids,
        Ground.recvP F d #[foldMaskNotice Fs] = some (ids, d1) ∧ ids[0]? = some id)) ∧
      Ground.spendAsMaskP d1 id = some d' ∧
      singleRowsOracles out = Fs.layout.members.push id := by
  cases es with
  | nil => cases h
  | cons eE eR =>
    cases rs with
    | nil => cases h
    | cons rE rR =>
      rw [First.Close.foldD] at h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      have h1 : ∃ (id : Nat) (d1 : DS),
          ((mask = some id ∧ d1 = d) ∨ (mask = none ∧ ∃ ids,
            Ground.recvP F d #[foldMaskNotice Fs] = some (ids, d1) ∧ ids[0]? = some id)) ∧
          (do
            First.Close.need "K10.maskfits" (Own.foldMaskFits d1.st Fs id)
            First.Close.named (Ground.spendAsMaskL d1.st id)
            let d2 ← First.Close.got "K10.maskfits" (Ground.spendAsMaskP d1 id)
            match ← First.Close.heard "FOLD epsilon" 1 eE rE (d1.roots - d.roots) with
            | ([sum], eps) =>
              First.Close.need "K10.rowfits" (Own.foldRowFits d2.st Fs row)
              let (gamma, claim) ← First.Close.rounds eR rR (maddE sum eps row.target)
              pure (foldOutput d2.st Fs row id eps gamma claim, d2)
            | _ => .error "K10.items") = Except.ok (out, d') := by
        cases mask with
        | some o => exact ⟨o, d, .inl ⟨rfl, rfl⟩, h⟩
        | none =>
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨⟨ids, dd⟩, hr, h⟩ := bind_ok h
          obtain ⟨i0, hi, h⟩ := bind_ok h
          exact ⟨i0, dd, .inr ⟨rfl, ids, got_ok hr, got_ok hi⟩, h⟩
      obtain ⟨id, d1, hcase, h⟩ := h1
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨d2, hsp, h⟩ := bind_ok h
      obtain ⟨⟨xs, eps⟩, _, h⟩ := bind_ok h
      split at h
      · obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨⟨gamma, claim⟩, _, h⟩ := bind_ok h
        cases h
        exact ⟨id, d1, hcase, got_ok hsp, rfl⟩
      · cases h

/-- The mask's number and the core behind its coming. -/
def maskThin (p : P12) (F : FoldShape) (a : ThinSh) : Option (Nat × CoreSh) :=
  match a.mask with
  | some id => some (id, a.core)
  | none => (recvS p.nums.firstTree a.core #[foldMaskNotice F]).bind fun x =>
      (x.1[0]?).map fun id => (id, x.2)

def foldThin (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (a : ThinSh) : Option ThinSh :=
  match a.pass, stageAt p j cur, p.idx[j + 1]? with
  | .claim L, some c, some n =>
    (maskThin p (ioppFoldShape c L) a).bind fun y =>
      (spendS y.2 y.1).bind fun c2 => (newGroupS c2 n.1 n.2).map fun z =>
        ⟨z.2, a.g, .single ((ioppFoldShape c L).layout.members.push y.1).toList z.1, a.mask⟩
  | _, _, _ => none

theorem fold_thin (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (foldJ p j cur cut).decide t rs gs = .ok t1) :
    foldThin p j cur (thinSh t) = some (thinSh t1) := by
  simp only [foldJ] at h
  split at h
  · rename_i row L c n e1 e2 e3
    obtain ⟨⟨rows, s1⟩, hx, h⟩ := bind_ok h
    obtain ⟨⟨gp, s2⟩, hy, h⟩ := bind_ok h
    obtain ⟨rfl, _⟩ := back_ok h
    unfold H2K.foldE at hx
    obtain ⟨_, _, hx⟩ := bind_ok hx
    obtain ⟨_, _, hx⟩ := bind_ok hx
    obtain ⟨⟨rows', d'⟩, hf, hx⟩ := bind_ok hx
    cases hx
    obtain ⟨id, d1, hcase, hsp, hask⟩ := foldD_asked _ _ _ _ _ _ _ _ _ (mapError_ok hf)
    have hmask : maskThin p (ioppFoldShape c L) (thinSh t) = some (id, shD d1) := by
      unfold maskThin
      rcases hcase with ⟨hk, rfl⟩ | ⟨hk, ids, hr, hi⟩
      · show (match t.mask with
          | some id => some (id, (thinSh t).core)
          | none => _) = _
        rw [hk]
        rfl
      · have c1 := recv_carries p.nums.firstTree (lay p cut none t rs gs).d d1 _ ids hr
        show (match t.mask with
          | some id => some (id, (thinSh t).core)
          | none => (recvS p.nums.firstTree (shD (lay p cut none t rs gs).d)
              #[foldMaskNotice (ioppFoldShape c L)]).bind fun x =>
                (x.1[0]?).map fun id => (id, x.2)) = _
        rw [hk]
        show (recvS _ _ _).bind _ = _
        rw [c1, Option.bind_some]
        show (ids[0]?).map _ = _
        rw [hi]
        rfl
    have c2 := spend_carries d1 d' id hsp
    unfold H2K.newGroupE at hy
    cases hg : Ground.newGroupP d' n.1 n.2 with
    | none => simp [hg, H2K.opt, Except.map] at hy
    | some v =>
      simp only [hg, H2K.opt, Except.map] at hy
      cases hy
      have c3 := newGroup_carries d' v.2 n.1 n.2 v.1 hg
      unfold foldThin
      show (match thinPass t.pass, stageAt p j cur, p.idx[j + 1]? with
        | .claim L, some c, some n => _
        | _, _, _ => none) = _
      rw [e1, e2, e3]
      show (maskThin p (ioppFoldShape c L) (thinSh t)).bind _ = _
      rw [hmask, Option.bind_some]
      show (spendS (shD d1) id).bind _ = _
      rw [c2, Option.bind_some, c3, Option.map_some]
      show some (ThinSh.mk _ _ (.single _ _) _) = some (ThinSh.mk _ _ (.single _ _) _)
      rw [hask]
      rfl
  · cases h

/-! ## 4 The base case -/

def baseThin (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (a : ThinSh) : Option ThinSh :=
  match a.pass, stageAt p j cur with
  | .claim L, some _ =>
    (lastMember L).bind fun m => a.mask.bind fun star => (a.core.book.place[m]?).bind fun q =>
      (spendS a.core star).map fun c2 => ⟨countS c2 q.1, a.g, .nothing, none⟩
  | _, _ => none

theorem lastTree_place {P : Prox.BasePar} {B : TreeBook} {m star a : Nat}
    (h : lastTree P B m star = some a) : ∃ w, B.place[m]? = some (a, w) := by
  unfold lastTree at h
  split at h
  · rename_i a' b' e1 e2
    split at h
    · split at h
      · cases h
        exact ⟨0, e1⟩
      · cases h
    · cases h
  · cases h

theorem base_thin (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (baseJ5 p j cur cut).decide t rs gs = .ok tE) :
    baseThin p j cur (thinSh t) = some (thinSh tE) := by
  unfold baseJ5 at h
  dsimp only at h
  split at h
  · rename_i row L c d₁ d₂ e1 e2
    obtain ⟨cl, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨cl', _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨m, hmm, h⟩ := bind_ok h
    obtain ⟨star, hs, h⟩ := bind_ok h
    obtain ⟨_, hp, h⟩ := bind_ok h
    obtain ⟨a, ha, h⟩ := bind_ok h
    cases h
    have k1 := H2K.Out.lastPair_spend _ (dT t []) _ m star (H2K.FoldLaw.need_ok hp)
    have c1 := spend_carries (dT t []) _ star k1
    obtain ⟨w, hw⟩ := lastTree_place (H2K.Sw.named_ok ha)
    unfold baseThin
    show (match thinPass t.pass, stageAt p j cur with
      | .claim L, some _ => _
      | _, _ => none) = _
    rw [e1, e2]
    show (lastMember L).bind _ = _
    rw [H2K.Sw.named_ok hmm, Option.bind_some]
    show t.mask.bind _ = _
    rw [H2K.Sw.named_ok hs, Option.bind_some]
    show ((bookSh t.book).place[m]?).bind _ = _
    rw [place_get, hw, Option.bind_some]
    show (spendS (shD (dT t [])) star).map _ = _
    rw [c1, Option.map_some]
    show some (ThinSh.mk _ _ _ _) = some (ThinSh.mk (coreSh ⟨_, _, _⟩) _ _ _)
    rw [count_sh]
    rfl
  · cases h

/-! ## 5 The statements between, read -/

/-- a holds the statement's codes, oracle messages and groups. -/
def Bare (S : Statement) (a : StSh) : Prop :=
  S.codes = a.codes ∧ S.oracles.toList.map orcSh = a.oracles ∧ S.groups.toList.map grpSh = a.groups

theorem bare_self (S : Statement) : Bare S (stSh S) := ⟨rfl, rfl, rfl⟩

theorem stSh_of_bare {S : Statement} {a : StSh} (h : Bare S a) : stSh S = a :=
  stSh_eq h.1 h.2.1 h.2.2

def sentU (a : StSh) (sent : Array OracleNotice) : StSh :=
  { a with oracles := a.oracles ++ sent.toList.map freshOrc }

theorem bare_sent {S : Statement} {a : StSh} (h : Bare S a) (sent : Array OracleNotice) :
    Bare (stSent S sent) (sentU a sent) :=
  ⟨h.1, by rw [sent_oracles, h.2.1]; rfl, h.2.2⟩

def admitU (a : StSh) (o : Nat) (s : OracleShape) (places : List PadPlace) (n : Nat) : StSh :=
  { a with oracles := modAt a.oracles o fun y => { y with
      sampled := true, rows := n, pad := places.map fun p => (p.part, p.index)
      ledger := freshLedger a.codes s } }

theorem bare_admitted {S : Statement} {a : StSh} (h : Bare S a) (o : Nat) (s : OracleShape)
    (places : List PadPlace) (rows : Array Row) :
    Bare (admitted S o s places rows) (admitU a o s places rows.size) := by
  refine ⟨h.1, ?_, h.2.2⟩
  show (S.oracles.modify o _).toList.map orcSh = _
  rw [map_modify _ _ _ orcSh (fun y => { y with
      sampled := true, rows := rows.size, pad := places.map fun p => (p.part, p.index)
      ledger := freshLedger S.codes s }) fun _ => rfl, h.2.1, h.1]
  rfl

def shutU (a : StSh) (l : List Nat) : StSh :=
  { a with oracles := l.foldl (fun os o => modAt os o shutS) a.oracles }

theorem bare_shut {S : Statement} {a : StSh} (h : Bare S a) (l : List Nat) :
    Bare (closeLedgers S l) (shutU a l) :=
  ⟨(closeLedgers_codes l S).trans h.1, by rw [closeLedgers_sh, h.2.1]; rfl,
    by rw [closeLedgers_groups, h.2.2]; rfl⟩

def joinU (a : StSh) (g o : Nat) (kept : Bool) (G : GrpSh) : StSh :=
  { a with
    groups := modAt a.groups g fun G' => { G' with
      members := insAt G'.members (G.members.filter (· < o)).length o
      kept := insAt G'.kept (G.members.filter (· < o)).length kept }
    oracles := modAt a.oracles o fun x => { x with groups := x.groups ++ [g] } }

theorem bare_joined {S : Statement} {a : StSh} (h : Bare S a) (g o : Nat) (kept : Bool)
    (G : Group) : Bare (withMessageInGroup S g o kept G) (joinU a g o kept (grpSh G)) := by
  have efs : (G.members.filter (· < o)).size = (G.members.toList.filter (· < o)).length := by
    rw [← Array.length_toList, Array.toList_filter]
  refine ⟨h.1, ?_, ?_⟩
  · show (S.oracles.modify o _).toList.map orcSh = _
    rw [map_modify _ _ _ orcSh (fun x => { x with groups := x.groups ++ [g] }) fun _ => rfl,
      h.2.1]
    rfl
  · show (S.groups.modify g _).toList.map grpSh = _
    rw [map_modify _ _ _ grpSh (fun G' => { G' with
        members := insAt G'.members ((grpSh G).members.filter (· < o)).length o
        kept := insAt G'.kept ((grpSh G).members.filter (· < o)).length kept }) fun G' => by
          show grpSh _ = _
          unfold grpSh
          simp only [insAt_toList]
          rw [efs], h.2.2]
    rfl

/-- Rows laid on a group: the group's kinds grow; all else stays. -/
theorem bare_withRows (g : Nat) : ∀ (l : List Row) {S : Statement} {a : StSh}, Bare S a →
    Bare (withRows S g l) { a with
      groups := modAt a.groups g fun G => { G with kinds := G.kinds ++ l.map (·.kind) } }
  | [], S, a, h => by
    refine ⟨h.1, h.2.1, ?_⟩
    show S.groups.toList.map grpSh = modAt a.groups g fun G => { G with kinds := G.kinds ++ [] }
    rw [h.2.2]
    refine List.ext_getElem (by simp [modAt]) fun j j1 j2 => ?_
    simp only [modAt, List.getElem_map, List.getElem_zipIdx, Nat.zero_add, List.append_nil]
    split <;> rfl
  | r :: l, S, a, h => by
    have h1 : Bare (withRow S g r) { a with
        groups := modAt a.groups g fun G => { G with kinds := G.kinds ++ [r.kind] } } := by
      refine ⟨h.1, h.2.1, ?_⟩
      show (S.groups.modify g _).toList.map grpSh = _
      rw [map_modify _ _ _ grpSh (fun G => { G with kinds := G.kinds ++ [r.kind] }) fun G => by
        show grpSh _ = _
        unfold grpSh
        simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil], h.2.2]
    have h2 := bare_withRows g l h1
    refine ⟨h2.1, h2.2.1, ?_⟩
    rw [show withRows S g (r :: l) = withRows (withRow S g r) g l from rfl, h2.2.2]
    dsimp only
    rw [modAt_modAt]
    simp only [List.append_assoc, List.singleton_append, List.map_cons]

theorem bare_begun {S : Statement} {a : StSh} (h : Bare S a) (g : Nat) (G : Group) :
    Bare (begun S g G) (begunS a g (grpSh G)) := by
  have h1 := bare_shut h G.members.toList
  refine ⟨h1.1, h1.2.1, ?_⟩
  show ((closeLedgers S G.members.toList).groups.modify g _).toList.map grpSh = _
  rw [map_modify _ _ _ grpSh (fun G => { G with inRun := true, kinds := [] }) fun _ => rfl,
    h1.2.2]
  rfl

theorem layoutS_bare {S : Statement} {a : StSh} (h : Bare S a) (G : Group) :
    layoutS a (grpSh G) = Own.layoutOf S G := by
  rw [← layoutS_eq]
  obtain ⟨h1, h2, h3⟩ := h
  cases a
  subst h1 h2 h3
  rfl

/-! ## 6 The book: a sending; the counting of openings -/

/-- The book behind a sending, on shapes. n0: the number of the first new message. -/
def sentBookS (first n0 roots : Nat) (b : BookSh) (sent : Array OracleNotice) (lay : TreeLay) :
    BookSh :=
  { trees := (List.range sent.size).foldl (fun t i =>
      modAt t (b.trees.length + lay.tree.getD i 0) fun x => { x with
        parts := x.parts ++ [n0 + i]
        oneList := x.oneList || (sent.getD i default).shape.answers == 0 })
      (treesSentS first lay.shapes.toList roots b.trees)
    place := b.place ++ (List.range sent.size).map fun i =>
      (b.trees.length + lay.tree.getD i 0, lay.part.getD i 0) }

theorem sentBook_sh (first roots : Nat) (S : Statement) (B : TreeBook)
    (sent : Array OracleNotice) (lay : TreeLay) :
    bookSh (bookSentP first roots S B sent lay) =
      sentBookS first S.oracles.size roots (bookSh B) sent lay :=
  recv_book first B S.oracles.size roots sent lay

theorem openOne_book (S : Statement) (ft : Nat) (pos : Positions) (B0 : TreeBook) (t : Nat)
    (s s' : TreeBook × List Tw.L9.Col × Array (Nat × Array Nat × Array (Array F)))
    (h : Tw.L9.openOne S ft pos B0 t s = .ok s') : bookSh s'.1 = countB (bookSh s.1) t := by
  unfold Tw.L9.openOne at h
  split at h
  · dsimp only at h
    repeat' split at h
    all_goals first
      | (cases h; exact countB_sh _ _)
      | cases h
  · cases h

theorem opened_book (S : Statement) (ft : Nat) (pos : Positions) (B0 : TreeBook) :
    ∀ (l : List Nat) (s s' : TreeBook × List Tw.L9.Col × Array (Nat × Array Nat × Array (Array F))),
      l.foldlM (fun s t => Tw.L9.openOne S ft pos B0 t s) s = .ok s' →
      bookSh s'.1 = l.foldl countB (bookSh s.1)
  | [], s, s', h => by cases h; rfl
  | t :: l, s, s', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h2⟩ := bind_ok h
    rw [opened_book S ft pos B0 l s1 s' h2, openOne_book S ft pos B0 t s s1 h1]
    rfl

/-- **The book behind the reading of the old rows**: each tree that holds a message asked for is
counted once. -/
theorem readOld_book (i : Tw.L9.SwIn) (pos : Positions) (B : TreeBook) (left : List Tw.L9.Col)
    (ys : Array E) (h : Tw.L9.readOld i pos = .ok (B, left, ys)) :
    ∃ ps : List (Nat × Nat),
      ((singleRowsOracles i.old).toList.mapM fun o => (bookSh i.book).place[o]?) = some ps ∧
      bookSh B = (Fmt.listOf (ps.map (·.1))).foldl countB (bookSh i.book) := by
  obtain ⟨places, cols, opened, h1, h3, _, _⟩ := readOld_inv i pos B left ys h
  refine ⟨places.toList, ?_, ?_⟩
  · rw [Array.mapM_eq_mapM_toList] at h1
    obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 h1
    simp only [place_get]
    exact hl
  · rw [OnBytes.listOfT_eq] at h3
    have := opened_book _ _ _ _ _ _ _ h3
    rw [this, Array.toList_map]

/-! ## 7 A switch and the batching behind it, as one step -/

/-- The group with its new member. -/
def grownS (G : GrpSh) (id : Nat) : GrpSh :=
  { G with
    members := insAt G.members (G.members.filter (· < id)).length id
    kept := insAt G.kept (G.members.filter (· < id)).length false }

/-- The step's body. id: the new message's number. -/
def switchBody (p : P12) (last : Bool) (nx : IoppStage) (asked : List Nat) (gp : Nat) (a : ThinSh)
    (id : Nat) : Option ThinSh :=
  (layTrees a.core.st.codes (Slice.sentOf (switchTargetStage nx.code nx.maskCode nx.k nx.h 1)
    (othersOf last nx))).bind fun lay =>
  (Send.pad a.core.st.codes (switchTargetStage nx.code nx.maskCode nx.k nx.h 1).shape).bind
    fun places =>
  ((if 0 < (switchTargetStage nx.code nx.maskCode nx.k nx.h 1).shape.maskRows then
      shutU (admitU (sentU a.core.st (Slice.sentOf (switchTargetStage nx.code nx.maskCode nx.k nx.h
        1) (othersOf last nx))) id (switchTargetStage nx.code nx.maskCode nx.k nx.h 1).shape places
        1) [id]
    else admitU (sentU a.core.st (Slice.sentOf (switchTargetStage nx.code nx.maskCode nx.k nx.h 1)
      (othersOf last nx))) id (switchTargetStage nx.code nx.maskCode nx.k nx.h 1).shape places
      1).groups[gp]?).bind fun G =>
  (asked.mapM fun o => (sentBookS p.nums.firstTree id a.core.roots a.core.book
    (Slice.sentOf (switchTargetStage nx.code nx.maskCode nx.k nx.h 1) (othersOf last nx))
    lay).place[o]?).map fun ps =>
    ⟨⟨begunS (joinU (if 0 < (switchTargetStage nx.code nx.maskCode nx.k nx.h 1).shape.maskRows then
            shutU (admitU (sentU a.core.st (Slice.sentOf (switchTargetStage nx.code nx.maskCode nx.k
              nx.h 1) (othersOf last nx))) id (switchTargetStage nx.code nx.maskCode nx.k nx.h
              1).shape places 1) [id]
          else admitU (sentU a.core.st (Slice.sentOf (switchTargetStage nx.code nx.maskCode nx.k
            nx.h 1) (othersOf last nx))) id (switchTargetStage nx.code nx.maskCode nx.k nx.h
            1).shape places 1) gp id false G) gp (grownS G id),
        (Fmt.listOf (ps.map (·.1))).foldl countB (sentBookS p.nums.firstTree id a.core.roots
          a.core.book (Slice.sentOf (switchTargetStage nx.code nx.maskCode nx.k nx.h 1)
          (othersOf last nx)) lay), a.core.roots + lay.shapes.size⟩,
      a.g, .claim (layoutS (joinU (if 0 < (switchTargetStage nx.code nx.maskCode nx.k nx.h
            1).shape.maskRows then
            shutU (admitU (sentU a.core.st (Slice.sentOf (switchTargetStage nx.code nx.maskCode nx.k
              nx.h 1) (othersOf last nx))) id (switchTargetStage nx.code nx.maskCode nx.k nx.h
              1).shape places 1) [id]
          else admitU (sentU a.core.st (Slice.sentOf (switchTargetStage nx.code nx.maskCode nx.k
            nx.h 1) (othersOf last nx))) id (switchTargetStage nx.code nx.maskCode nx.k nx.h
            1).shape places 1) gp id false G) (grownS G id)),
      ((Array.range (othersOf last nx).size).map (· + (id + 1)))[0]?⟩

def switchThin (p : P12) (j : Nat) (nxt : Fmt.M1.Stage) (last : Bool) (a : ThinSh) :
    Option ThinSh :=
  match a.pass, stageAt p (j + 1) nxt with
  | .single asked gp, some nx => switchBody p last nx asked gp a a.core.st.oracles.length
  | _, _ => none

/-- Rows that were laid on the group do not show behind the beginning of its test. -/
theorem begunS_rows (a : StSh) (g : Nat) (k : List RowKind) (G1 G2 : GrpSh)
    (h : G1.members = G2.members) :
    begunS { a with groups := modAt a.groups g fun G => { G with kinds := G.kinds ++ k } } g G1 =
      begunS a g G2 := by
  unfold begunS
  dsimp only
  rw [modAt_modAt, h]

theorem grpSh_grown (D : Taken) (S : Statement) :
    { grpSh (D.grown S) with kinds := (grpSh D.G).kinds } = grownS (grpSh D.G) S.oracles.size := by
  have efs : (D.G.members.filter (· < S.oracles.size)).size =
      (D.G.members.toList.filter (· < S.oracles.size)).length := by
    rw [← Array.length_toList, Array.toList_filter]
  unfold grownS grpSh Taken.grown
  simp only [insAt_toList]
  rw [efs]

theorem switch_thin (p : P12) (he : p.early = true) (ha : p.answers = 1) (j : Nat)
    (cur nxt : Fmt.M1.Stage) (last : Bool) (cut : List Fmt.DeclaredRound) (t1 t2 t3 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (hlen : rs.length ≤ 2)
    (h1 : (switchJ p j cur nxt last cut).decide t1 rs gs = .ok t2)
    (h2 : (behindJ p (j + 1) nxt cut).decide t2 [] [] = .ok t3)
    : switchThin p j nxt last (thinSh t1) = some (thinSh t3) := by
  have h1' := h1
  simp only [switchJ] at h1'
  split at h1'
  · rename_i rows gp nx e1 e2
    obtain ⟨⟨⟨out0, theta0⟩, s'⟩, hx, h1''⟩ := bind_ok h1'
    obtain ⟨ht2, _⟩ := back_ok h1''
    obtain ⟨r1, r2, rest, hr⟩ := H2K.Out.switchE_two hx
    have hr' : rs = r1 :: r2 :: rest := hr
    have hrest : rest = [] := by
      rw [hr'] at hlen
      simp only [List.length_cons] at hlen
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hrest
    subst hr'
    obtain ⟨out, row, L, th, D, _, _, hd, hpass, hmask⟩ :=
      switchUnfolds p j cur nxt last cut t1 t2 t3 r1 r2 gs rows gp nx he ha e1 e2 h1 h2
    obtain ⟨nx', lay, e2', hlay, hroots⟩ :=
      H2K.Out.switch_roots p he ha j cur nxt last cut t1 t2 _ gs h1
    obtain rfl : nx = nx' := Option.some.inj (e2.symm.trans e2')
    obtain rfl : D.lay = lay := Option.some.inj (hd.trees.symm.trans hlay)
    have h3 := H2K.Out.behindJ_roots p (j + 1) nxt cut t2 t3 h2
    have hg : t3.g = t1.g := by
      have h2' := h2
      rw [ht2] at h2'
      simp only [behindJ] at h2'
      obtain ⟨x, _, h2'⟩ := bind_ok h2'
      obtain ⟨rfl, _⟩ := back_ok h2'
      rfl
    obtain ⟨i, left, hist, hib, _, _, hio, hread⟩ := hd.read
    obtain ⟨ps, hps, hbook⟩ := readOld_book i _ _ _ _ hread
    rw [hib, sentBook_sh, hio] at hps
    rw [hib, sentBook_sh] at hbook
    -- the statements between
    let T := switchTargetStage nx.code nx.maskCode nx.k nx.h 1
    let others := othersOf last nx
    have bA : Bare (D.stA T others t1.st)
        (admitU (sentU (stSh t1.st) (Slice.sentOf T others)) t1.st.oracles.size T.shape D.places
          1) :=
      bare_admitted (bare_sent (bare_self t1.st) _) _ _ _ #[D.sample]
    have bL : Bare (ledgerShut (D.stA T others t1.st) T t1.st.oracles.size)
        (if 0 < T.shape.maskRows then
          shutU (admitU (sentU (stSh t1.st) (Slice.sentOf T others)) t1.st.oracles.size T.shape
            D.places 1) [t1.st.oracles.size]
        else admitU (sentU (stSh t1.st) (Slice.sentOf T others)) t1.st.oracles.size T.shape
          D.places 1) := by
      unfold ledgerShut
      split
      · exact bare_shut bA _
      · exact bA
    have bJ := bare_joined bL gp t1.st.oracles.size false D.G
    have bR := bare_withRows gp D.rows bJ
    have b3 := bare_begun bR gp (D.grown t1.st)
    have hG : (if 0 < T.shape.maskRows then
          shutU (admitU (sentU (stSh t1.st) (Slice.sentOf T others)) t1.st.oracles.size T.shape
            D.places 1) [t1.st.oracles.size]
        else admitU (sentU (stSh t1.st) (Slice.sentOf T others)) t1.st.oracles.size T.shape
          D.places 1).groups[gp]? = some (grpSh D.G) := by
      rw [← bL.2.2, map_get, hd.group]
      rfl
    have hmem : (grpSh (D.grown t1.st)).members =
        (grownS (grpSh D.G) t1.st.oracles.size).members := by
      have e := congrArg GrpSh.members (grpSh_grown D t1.st)
      exact e
    have hst : stSh t3.st = begunS (joinU (if 0 < T.shape.maskRows then
          shutU (admitU (sentU (stSh t1.st) (Slice.sentOf T others)) t1.st.oracles.size T.shape
            D.places 1) [t1.st.oracles.size]
        else admitU (sentU (stSh t1.st) (Slice.sentOf T others)) t1.st.oracles.size T.shape
          D.places 1) gp t1.st.oracles.size false (grpSh D.G)) gp
        (grownS (grpSh D.G) t1.st.oracles.size) := by
      have e := stSh_of_bare b3
      rw [begunS_rows _ gp _ _ _ hmem] at e
      rw [hd.st]
      exact e
    have hlayout : L = layoutS (joinU (if 0 < T.shape.maskRows then
          shutU (admitU (sentU (stSh t1.st) (Slice.sentOf T others)) t1.st.oracles.size T.shape
            D.places 1) [t1.st.oracles.size]
        else admitU (sentU (stSh t1.st) (Slice.sentOf T others)) t1.st.oracles.size T.shape
          D.places 1) gp t1.st.oracles.size false (grpSh D.G))
        (grownS (grpSh D.G) t1.st.oracles.size) := by
      have e := hd.layout
      rw [← Own.layoutMade_eq] at e
      obtain ⟨G', hG', rfl⟩ := Option.map_eq_some_iff.1 e
      refine (layoutS_bare bR G').symm.trans ?_
      have e3 : (joinU (if 0 < T.shape.maskRows then
          shutU (admitU (sentU (stSh t1.st) (Slice.sentOf T others)) t1.st.oracles.size T.shape
            D.places 1) [t1.st.oracles.size]
        else admitU (sentU (stSh t1.st) (Slice.sentOf T others)) t1.st.oracles.size T.shape
          D.places 1) gp t1.st.oracles.size false (grpSh D.G)).groups[gp]? =
          some (grownS (grpSh D.G) t1.st.oracles.size) := by
        unfold joinU
        dsimp only
        rw [modAt_get, hG]
        rfl
      have e4 := congrArg (Option.map grpSh) hG'
      rw [← map_get] at e4
      have e5 : (D.stR T gp others t1.st).groups.toList.map grpSh = _ := bR.2.2
      rw [e5] at e4
      dsimp only at e4
      rw [modAt_get, e3] at e4
      rw [← Option.some.inj e4]
      rfl
    unfold switchThin
    show (match thinPass t1.pass, stageAt p (j + 1) nxt with
      | .single asked gp, some nx =>
        switchBody p last nx asked gp (thinSh t1) (thinSh t1).core.st.oracles.length
      | _, _ => none) = _
    rw [e1, e2]
    show switchBody p last nx (singleRowsOracles rows).toList gp (thinSh t1)
      (stSh t1.st).oracles.length = _
    rw [orc_size]
    unfold switchBody
    show (layTrees t1.st.codes (Slice.sentOf T others)).bind _ = _
    rw [hlay, Option.bind_some]
    show (Send.pad t1.st.codes T.shape).bind _ = _
    rw [hd.pad, Option.bind_some]
    show (Option.bind ((if 0 < T.shape.maskRows then
          shutU (admitU (sentU (stSh t1.st) (Slice.sentOf T others)) t1.st.oracles.size T.shape
            D.places 1) [t1.st.oracles.size]
        else admitU (sentU (stSh t1.st) (Slice.sentOf T others)) t1.st.oracles.size T.shape
          D.places 1).groups[gp]?) _) = _
    rw [hG, Option.bind_some]
    show (Option.map _ ((singleRowsOracles rows).toList.mapM fun o =>
      (sentBookS p.nums.firstTree t1.st.oracles.size t1.roots (bookSh t1.book)
        (Slice.sentOf T others) D.lay).place[o]?)) = _
    rw [hps, Option.map_some]
    show some (ThinSh.mk (CoreSh.mk _ _ _) _ _ _) =
      some (ThinSh.mk (CoreSh.mk (stSh t3.st) (bookSh t3.book) t3.roots) t3.g (thinPass t3.pass)
        t3.mask)
    rw [hst, hbook, h3, hroots, hg, hpass, hmask, hd.riders, hlayout]
    rfl
  · cases h1'

/-! ## 8 The stages; the whole test -/

def stagesThin (p : P12) : List Fmt.M1.Stage → Nat → Fmt.M1.Stage → ThinSh → Option ThinSh
  | [], j, cur, a => baseThin p j cur a
  | nxt :: rest, j, cur, a =>
    (foldThin p j cur a).bind fun a1 => (switchThin p j nxt rest.isEmpty a1).bind fun a3 =>
      stagesThin p rest (j + 1) nxt a3

/-- **The proximity test on the thin shape.** -/
def testThin (p : P12) (a : ThinSh) : Option ThinSh :=
  match p.nums.stages with
  | first :: rest => (batThin p a).bind fun a1 => stagesThin p rest 0 first a1
  | [] => none

theorem stages_thin (p : P12) (he : p.early = true) (ha : p.answers = 1) :
    ∀ (rest : List Fmt.M1.Stage) (j : Nat) (cur : Fmt.M1.Stage) (la : Laid) (t tE : T12)
      (rs : List Fmt.RoundView) (gs : Gs),
      (stagesFrom guardedProximityTestParts p j cur rest la : Blk').decide t rs gs = .ok tE →
      stagesThin p rest j cur (thinSh t) = some (thinSh tE)
  | [], j, cur, la, t, tE, rs, gs, h => by
    rw [stagesFrom_last] at h
    exact base_thin p _ _ _ _ _ _ _ (ranged_ok _ _ _ _ _ _ h).1
  | nxt :: rest, j, cur, la, t, tE, rs, gs, h => by
    obtain ⟨t1, t2, t3, f1, f2, f3, _, f5⟩ :=
      (stagesFrom_ok guardedProximityTestParts p j cur nxt rest la t tE rs gs).1 h
    have k1 := fold_thin p j cur _ t t1 _ _ ((like_P5 p).fold _ _ _ _ _ _ _ f1)
    have hlen : ((rs.drop (foldAt guardedProximityTestParts p j cur la : Blk').rounds.length).take
        (switchAt guardedProximityTestParts p j cur nxt rest.isEmpty la : Blk').rounds.length).length ≤
        2 := by
      refine (List.length_take_le _ _).trans ?_
      show (((la.drop (1 + cur.k)).take 2).map (·.1)).length ≤ 2
      rw [List.length_map]
      exact List.length_take_le _ _
    have k2 := switch_thin p he ha j cur nxt rest.isEmpty _ t1 t2 t3 _ _ hlen
      ((like_P5 p).switch _ _ _ _ _ _ _ _ _ f2) ((like_P5 p).behind _ _ _ _ _ f3)
    have k4 := stages_thin p he ha rest (j + 1) nxt _ t3 tE _ _ f5
    show (foldThin p j cur (thinSh t)).bind _ = _
    rw [k1, Option.bind_some, k2, Option.bind_some]
    exact k4

/-- **Where the test's sub-protocol accepts, the test on the thin shape returns the shape behind.**
-/
theorem k12_thin (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    testThin p (thinSh t0) = some (thinSh tE) := by
  obtain ⟨first, rest, ds, tF, t1, hs, hr, hfr, hbat, _, hst⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  have hF : tF = t0 := by
    have hfr' := (like_P5 p).front _ _ hfr
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  unfold testThin
  rw [hs]
  show (batThin p (thinSh tF)).bind _ = _
  rw [bat_thin p _ _ _ _ _ ((like_P5 p).bat _ _ _ _ _ hbat), Option.bind_some]
  exact stages_thin p he ha rest 0 first _ _ tE _ _ hst

/-- Where the test's sub-protocol accepts, nothing passed in front of it. -/
theorem k12_nothing (p : P12) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) : t0.pass = .nothing := by
  obtain ⟨first, rest, ds, tF, t1, hs, hr, hfr, hbat, _, hst⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  have hfr' := (like_P5 p).front _ _ hfr
  unfold frontJ at hfr'
  dsimp only at hfr'
  split at hfr'
  · assumption
  · cases hfr'

/-- **The proximity test on the core's shape alone.** g: the group under test. mask: the number of
the message that holds the first stage's mask, if it has come. -/
def testCore (p : P12) (c : CoreSh) (g : Nat) (mask : Option Nat) : Option CoreSh :=
  (testThin p ⟨c, g, .nothing, mask⟩).map (·.core)

/-- **Where the test's sub-protocol accepts, the test on the core's shape returns the core's shape
behind.** -/
theorem k12_core_sh (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    testCore p (coreSh ⟨t0.st, t0.book, t0.roots⟩) t0.g t0.mask =
      some (coreSh ⟨tE.st, tE.book, tE.roots⟩) := by
  have k := k12_thin p he ha t0 tE rs gs h
  unfold testCore
  have e : (⟨coreSh ⟨t0.st, t0.book, t0.roots⟩, t0.g, .nothing, t0.mask⟩ : ThinSh) = thinSh t0 := by
    unfold thinSh
    rw [k12_nothing p t0 tE rs gs h]
    rfl
  rw [e, k]
  rfl

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.bat_thin
#print axioms ProofFile.Honest.Sh.foldD_asked
#print axioms ProofFile.Honest.Sh.fold_thin
#print axioms ProofFile.Honest.Sh.lastTree_place
#print axioms ProofFile.Honest.Sh.base_thin
#print axioms ProofFile.Honest.Sh.bare_self
#print axioms ProofFile.Honest.Sh.stSh_of_bare
#print axioms ProofFile.Honest.Sh.bare_sent
#print axioms ProofFile.Honest.Sh.bare_admitted
#print axioms ProofFile.Honest.Sh.bare_shut
#print axioms ProofFile.Honest.Sh.bare_joined
#print axioms ProofFile.Honest.Sh.bare_withRows
#print axioms ProofFile.Honest.Sh.bare_begun
#print axioms ProofFile.Honest.Sh.layoutS_bare
#print axioms ProofFile.Honest.Sh.sentBook_sh
#print axioms ProofFile.Honest.Sh.openOne_book
#print axioms ProofFile.Honest.Sh.opened_book
#print axioms ProofFile.Honest.Sh.readOld_book
#print axioms ProofFile.Honest.Sh.begunS_rows
#print axioms ProofFile.Honest.Sh.grpSh_grown
#print axioms ProofFile.Honest.Sh.switch_thin
#print axioms ProofFile.Honest.Sh.stages_thin
#print axioms ProofFile.Honest.Sh.k12_thin
#print axioms ProofFile.Honest.Sh.k12_nothing
#print axioms ProofFile.Honest.Sh.k12_core_sh
