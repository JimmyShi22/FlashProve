-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestKeeps.lean: what a proximity test keeps. One proposition on the
verifier's structure before a proximity test and after it, `K12Keeps p t t'`, is defined. It is
proved, under two hypotheses on the plan p, wherever the test's own block accepts, on whatever
rounds and columns (`k12_keeps`). The block is `proximityTestKind guardedProximityTestParts p` (`proximityTestKind`:
Johnson/Desc/K12/Frame.lean; `guardedProximityTestParts`: Johnson/Desc/K12/JoinGuarded.lean). General in p, t, t', rounds
and columns. The verifier's structure alone: no prover, no coin, no frame for an honest side.

How the proposition is built. Statement, book and count of roots consist of their shape (`CoreSh`,
Johnson/Desc/Ground/Shape/Core.lean) and of three sorts of values that the shape leaves out: the
summands and targets of the groups' open rows; those of the messages' sample rows; a given tree's
root and start. So the proposition is one equation on shapes and three clauses that say that these
values stay.

Terms. The structure inside a test is `T12` (Johnson/Desc/K12/Join.lean): the statement `st`
(`Statement`, OnBytes/Iop/Ground.lean: codes, oracle messages, groups); the book of trees `book`
(`TreeBook`: the trees, and each oracle message's place: its tree and its part there); the count of
roots; the number `g` of the group under test; what passes from a part of the test to the next
(`pass`); and `mask`, the number of the oracle message that holds the present stage's mask, if it
has come. t is the structure before the test ("in front"), t' the one after it ("behind"). "Older"
is what t has: a message, group, tree or place at a number below the size in t. "Stands to the
letter" means: t' has the equal value at the same number, field elements included; such a message
"rides past" the test. "Not the first fold's mask" is, in Lean, `t.mask ≠ some o`. "The sentence" is
`K12Keeps`, and its "payer" is the theorem that proves it, `k12_keeps`. The plan p (`P12`,
Johnson/Desc/K12/Frame.lean) holds the numbers of the place of the test. A block (`Block`,
Johnson/Desc/Block.lean) accepts where its `decide` returns `.ok` with the next structure. The frame
for an honest side is Johnson/Desc/ProofFile/Honest/Frame.lean.

  `k12_keeps`: where `p.early = true`, `p.answers = 1` and `(proximityTestKind guardedProximityTestParts p).decide t rs gs`
    returns `.ok t'`: `K12Keeps p t t'` holds
  `K12Keeps p t t'`: a structure of seven propositions: the fields `shape`, `groupsElse`,
    `samples`, `srcs`, `ends`, `rest` and `place`, which the next six entries describe
  `shape`: `testCore p` (Johnson/Desc/K12/Honest/Shape/TestCore.lean) at the shape of t, `t.g` and
    `t.mask` returns the shape of t'. In words: the codes stay. An older message keeps shape,
    sampled, number of sample rows, pad and groups; its ledger is shut if it is a member of the
    group under test; at most one older message is marked as spent: the first fold's mask, if it
    had come. The group under test keeps codes, members and kept marks; its test has begun; its
    open rows are gone. An older tree keeps shape, number, the kind of its source, parts and the
    mark "opened at one list only"; its count of openings rises by one exactly if it holds a member
    of the group or the first fold's mask. Older places stay. Added behind: messages, trees,
    places, groups, by the plan; each mask that the test itself brings is marked as spent, the last
    stage's among them; each tree that it brings is counted as opened once, the last one (which
    holds the last stage's message and its mask) by the last part; the count of roots rises by the
    number of new trees.
  `groupsElse`: every other group of t is unchanged in t', its open rows with their values
  `samples`: every message of t is there in t' with the same sample rows, values included
  `srcs`: every tree of t is there in t' with the same source (`src`), values included
  `ends`: the group's number stays; nothing passes; no mask is named. In Lean: `t'.g = t.g`,
    `t'.pass = .nothing`, `t'.mask = none`
  `rest`, `place`: an older message that is no member of the group under test and not the first
    fold's mask stands to the letter; every older place stands. (They are fields of their own, for
    a caller that has `K12Keeps` and no accept: no lemma here derives them from the other clauses.)
  `K12Keeps.rides_past`: from the sentence alone, with no accept in hand: an older message that is
    no member of the group under test and not the first fold's mask stands behind the test to the
    letter, at its place. In Lean: from `t.st.groups[t.g]? = some G`, `t.st.oracles[o]? = some x`,
    `o ∉ G.members.toList` and `t.mask ≠ some o`: `t'.st.oracles[o]? = some x`, and a place that
    `t.book` has for o is the place that `t'.book` has for o
  `K12KeepsAt p enter leave s s'`: a definition: the same proposition at a chain's state, of any
    type S: there are t and t' such that `enter s` returns t, `K12Keeps p t t'` holds and
    `leave s t'` returns s'
  `k12_keeps_at`: under the same two hypotheses on p, where the block
    `(proximityTestKind guardedProximityTestParts p).inside enter leave` (`Block.inside`, Johnson/Desc/Block.lean) accepts at s
    and returns s': `K12KeepsAt p enter leave s s'` holds
  `K12KeepsAt.rides_past`: the conclusion of `K12Keeps.rides_past` at a chain's state, from
    `K12KeepsAt` and the hypotheses hin and hout below: there is a t that `enter s` returns such
    that it holds with `st s`, `book s` for the statement and book of t, and `st s'`, `book s'` for
    those of t'; `t.g` and `t.mask` are read at this t
  `StayV t t'`: a structure of four propositions, for two structures inside one test: every message
    of t has the same sample rows in t' (`samples`); every tree of t has the same source in t'
    (`srcs`); t' has no fewer messages (`osize`) and no fewer trees (`tsize`) than t
  `StayV.trans`: `StayV` is transitive
  `k12_stay`, `stages_stay`: under the two hypotheses on p, `StayV` holds from the structure before
    to the one after, where the whole block accepts; the same for the stages from any stage on
    (`stagesFrom guardedProximityTestParts`, Johnson/Desc/K12/Frame.lean)
  `bat_stay`, `fold_stay`, `base_stay`: the same where the batching (`batJ`) or a fold (`foldJ`,
    both Johnson/Desc/K12/Join.lean) or the base case (`baseJ5`, JoinGuarded.lean) accepts, with no
    hypothesis on p
  `switch_stay`: the same for a switch (`switchJ`) and the batching after it (`behindJ`, both
    Join.lean), taken as one step, under the two hypotheses on p and `rs.length ≤ 2`;
    `stages_stay` proves that bound: `stagesFrom` deals a switch two rounds at most
  `bat_form`: where the batching accepts at t, the structure after it is t with
    `begun t.st t.g G` as the statement, at the group G number `t.g`, with `.claim row L` in `pass`
    and some value in `mask`
  `openOne_src`, `opened_src`, `readOld_src`: where the switch's reading of the old rows returns
    `.ok`, every tree has the source that it had: at one tree (`Tw.L9.openOne`), along a list of
    trees, and for the whole reading (`Tw.L9.readOld`, Johnson/Top/H0/Tw/L9/Switch.lean)
  `bookSent_old`, `bookSent_size`: the book after a prover's message with oracle messages
    (`bookSentP`, Johnson/Desc/K12/Law/SwDid.lean) has every tree of the book before it unchanged,
    and no fewer trees
  `begun_rows`, `begun_osize`: `begun S g G` (OnBytes/Slice/BlkBegin.lean), the statement after the
    beginning of a test, has the messages' sample rows and the number of messages of S
  `modify_rows`, `modify_src`: `Array.modify` by a function that keeps the sample rows, or the
    source, keeps them at every number; `modify_other`: it changes no other element
  `foldl_modify_size`, `treesSent_size`: a fold of `Array.modify` keeps the size; `treesSent`
    (OnBytes/Slice/BlkSendRun.lean) does not shorten the array of trees

By what. `shape`: `k12_core_sh` (TestCore.lean). `groupsElse`, `ends`, `rest`, `place`: the
library's own `k12_out` and `k12_out2` (Johnson/Desc/K12/Law/OutK.lean, OutK2.lean): they are
called, not stated anew. `samples`, `srcs`: `k12_stay`, proved here part by part over the library's
`foldJ_form`, `spendP_form` (OutK2.lean), `recvP_ok`, `switchUnfolds`
(Johnson/Desc/K12/Law/SwUnfold.lean), `readOld_inv` (Johnson/Desc/K12/Law/SwRead.lean),
`treesSent_old` and `partsLaid_old` (OnBytes/Slice/BlkSentSeat.lean). The block's accept is cut into
its parts' accepts by `k12_ok`, `stagesFrom_ok` (Johnson/Desc/K12/FrameLaws.lean) and `like_P5`
(OutK.lean). `k12_keeps_at`: `Seat.inside_ok` (Johnson/Desc/K12/SeatLaws.lean).

Hypotheses. Of `k12_keeps` and `k12_keeps_at`: he: `p.early = true`; ha: `p.answers = 1`; h: the
accept. Of `K12KeepsAt.rides_past`, both at the given s and s' only: hin: what `enter s` returns has
`st s` and `book s` as its statement and book; hout: a t' that `leave s` takes to s' has `st s'` and
`book s'` as its statement and book.

Limits.
- Premises of the payer: the masks come early and a sample has one answer (the block's own test on
  the plan asks both).
- One direction only: from an accept to `K12Keeps`. Nothing is stated from `K12Keeps` to an accept.
- Of what t has, the seven fields fix every value: unchanged, but for the changes named under
  `shape` (by reading the fields: no theorem here says so). Of what the test adds they fix the shape
  only: the values in the sample rows that are admitted on the new messages are left free.
- The words under `shape` are a reading of the text of `testCore`: no theorem states them one by
  one. Where they say that the last tree holds the last stage's message and its mask, they lean on
  a test that the block makes and `testCore` does not (`lastTree`, JoinGuarded.lean): the last step of
  `testCore` (`baseThin`) counts only the tree in which the book places the last group's one
  member. At a plan of one stage there is no fold and no switch, and that step acts on what t has:
  it marks the message number `t.mask` as spent and counts that member's tree. The words on an older
  tree's count of openings are then right only where that tree holds both messages.
- `shape` does not read `t.pass`: `testCore` starts from `.nothing`. No field says what `t.pass` is.
- `rest` is vacuous where t has no group number `t.g`. By reading, `shape` cannot hold there:
  `beginRunS` (Johnson/Desc/Ground/Shape/Ground.lean) returns nothing.
- `rides_past` states nothing of the message's tree beyond what `shape` and `srcs` give.
- What `leave` writes into a chain's state is a parameter: `K12KeepsAt` names it and states nothing
  of it, and t' need not be the only structure that `leave s` takes to s'. This file applies
  `K12KeepsAt` to no `enter` and `leave` of the library.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.TestCore
import Johnson.Desc.K12.Law.OutK2
import Johnson.Desc.K12.Law.SwClaim
import Johnson.Desc.K12.SeatLaws
import OnBytes.Slice.BlkSentSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Out (dT DS beginRunP_at like_P5 foldJ_form spendP_form)
open H2K.FoldLaw (bind_ok got_ok)
open H2K.JointK H2K.Sw

/-! ## 1 The values that stay, part by part -/

/-- What is kept between two structures t and t' inside one test: every message of t keeps its
sample rows, every tree of t keeps its source, and neither array gets shorter. -/
structure StayV (t t' : T12) : Prop where
  samples : ∀ o, o < t.st.oracles.size →
    (t'.st.oracles[o]?).map (·.sampleRows) = (t.st.oracles[o]?).map (·.sampleRows)
  srcs : ∀ k, k < t.book.trees.size →
    (t'.book.trees[k]?).map (·.src) = (t.book.trees[k]?).map (·.src)
  osize : t.st.oracles.size ≤ t'.st.oracles.size
  tsize : t.book.trees.size ≤ t'.book.trees.size

theorem StayV.trans {a b c : T12} (h1 : StayV a b) (h2 : StayV b c) : StayV a c :=
  ⟨fun o ho => (h2.samples o (Nat.lt_of_lt_of_le ho h1.osize)).trans (h1.samples o ho),
    fun k hk => (h2.srcs k (Nat.lt_of_lt_of_le hk h1.tsize)).trans (h1.srcs k hk),
    Nat.le_trans h1.osize h2.osize, Nat.le_trans h1.tsize h2.tsize⟩

theorem modify_rows (a : Array OnBytes.Oracle) (i o : Nat) (f : OnBytes.Oracle → OnBytes.Oracle)
    (hf : ∀ x, (f x).sampleRows = x.sampleRows) :
    ((a.modify i f)[o]?).map (·.sampleRows) = (a[o]?).map (·.sampleRows) := by
  rw [Array.getElem?_modify]
  split
  · cases a[o]? with
    | none => rfl
    | some x => exact congrArg some (hf x)
  · rfl

theorem modify_src (a : Array Tree) (i k : Nat) (f : Tree → Tree) (hf : ∀ x, (f x).src = x.src) :
    ((a.modify i f)[k]?).map (·.src) = (a[k]?).map (·.src) := by
  rw [Array.getElem?_modify]
  split
  · cases a[k]? with
    | none => rfl
    | some x => exact congrArg some (hf x)
  · rfl

theorem modify_other {α : Type} (a : Array α) (i q : Nat) (f : α → α) (h : q ≠ i) :
    (a.modify i f)[q]? = a[q]? := by
  rw [Array.getElem?_modify, if_neg fun e => h e.symm]

theorem begun_rows (S : Statement) (g o : Nat) (G : Group) :
    ((begun S g G).oracles[o]?).map (·.sampleRows) = (S.oracles[o]?).map (·.sampleRows) :=
  closeLedgers_sampleRows G.members.toList S o

theorem begun_osize (S : Statement) (g : Nat) (G : Group) :
    (begun S g G).oracles.size = S.oracles.size :=
  ProxRun.closeLedgers_size G.members.toList S

theorem treesSent_size (first : Nat) : ∀ (l : List TreeShape) (roots : Nat) (A : Array Tree),
    A.size ≤ (treesSent first l roots A).size
  | [], _, _ => Nat.le_refl _
  | s :: l, roots, A => by
    show _ ≤ (treesSent first l (roots + 1) (A.push _)).size
    refine Nat.le_trans ?_ (treesSent_size first l _ _)
    rw [Array.size_push]
    omega

theorem foldl_modify_size {α ι : Type} (kf : ι → Nat) (f : ι → α → α) : ∀ (l : List ι)
    (A : Array α), (l.foldl (fun t i => t.modify (kf i) (f i)) A).size = A.size
  | [], _ => rfl
  | i :: l, A => by
    rw [List.foldl_cons, foldl_modify_size kf f l, Array.size_modify]

/-- A tree that the book B has is unchanged in the book after a prover's message with oracle
messages. -/
theorem bookSent_old (first roots : Nat) (S : Statement) (B : TreeBook)
    (sent : Array OracleNotice) (lay : TreeLay) (k : Nat) (hk : k < B.trees.size) :
    (bookSentP first roots S B sent lay).trees[k]? = B.trees[k]? := by
  show (partsLaid sent lay S.oracles.size B.trees.size
    (treesSent first lay.shapes.toList roots B.trees))[k]? = _
  rw [partsLaid_old _ _ _ _ _ k hk, treesSent_old first _ _ _ k hk]

theorem bookSent_size (first roots : Nat) (S : Statement) (B : TreeBook)
    (sent : Array OracleNotice) (lay : TreeLay) :
    B.trees.size ≤ (bookSentP first roots S B sent lay).trees.size := by
  unfold bookSentP partsLaid
  dsimp only
  rw [foldl_modify_size]
  exact treesSent_size first _ _ _

/-! ## 2 The batching -/

theorem bat_form (p : P12) (cut : List Fmt.DeclaredRound) (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (batJ p cut).decide t rs gs = .ok t1) :
    ∃ (G : Group) (row : GroupRow) (L : GroupLayout) (m : Option Nat),
      t.st.groups[t.g]? = some G ∧
      t1 = { t with st := begun t.st t.g G, pass := .claim row L, mask := m } := by
  unfold batJ at h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bind_ok h
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
      obtain ⟨G, lay', hG, _, _, hd⟩ := beginRunP_ok (got_ok hbeg)
      have hst : d.st = begun t.st t.g G := congrArg (·.st) hd
      refine ⟨G, row', input.layout, if p.early then t.mask else none, hG, ?_⟩
      show T12.mk d.st t.book t.roots t.g (.claim row' input.layout)
        (if p.early then t.mask else none) = _
      rw [hst]
    · cases hx
  · cases h

theorem bat_stay (p : P12) (cut : List Fmt.DeclaredRound) (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (batJ p cut).decide t rs gs = .ok t1) : StayV t t1 := by
  obtain ⟨G, row, L, m, _, rfl⟩ := bat_form p cut t t1 rs gs h
  exact ⟨fun o _ => begun_rows t.st t.g o G, fun _ _ => rfl,
    Nat.le_of_eq (begun_osize t.st t.g G).symm, Nat.le_refl _⟩

/-! ## 3 The fold -/

theorem fold_stay (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (foldJ p j cur cut).decide t rs gs = .ok t1) :
    StayV t t1 := by
  obtain ⟨row, L, c, nn, id, d1, d', rows, _, _, hcase, hsp, rfl⟩ :=
    foldJ_form p j cur cut t t1 rs gs h
  have hd' := spendP_form hsp
  subst hd'
  rcases hcase with ⟨_, rfl⟩ | ⟨_, ids, hr, _⟩
  · refine ⟨fun o _ => modify_rows _ _ _ _ fun _ => rfl, fun _ _ => rfl, ?_, Nat.le_refl _⟩
    show _ ≤ (t.st.oracles.modify _ _).size
    rw [Array.size_modify]
  · obtain ⟨lay, _, _, _, rfl⟩ := recvP_ok hr
    refine ⟨fun o ho => ?_, fun k hk => congrArg _ (bookSent_old _ _ _ _ _ _ k hk), ?_,
      bookSent_size _ _ _ _ _ _⟩
    · show (((stSent t.st _).oracles.modify _ _)[o]?).map _ = _
      refine Eq.trans (modify_rows _ _ _ _ ?_) ?_
      · exact fun _ => rfl
      · rw [stSent_old _ _ _ ho]
    · show _ ≤ ((stSent t.st _).oracles.modify _ _).size
      rw [Array.size_modify]
      show _ ≤ (t.st.oracles ++ _).size
      rw [Array.size_append]
      omega

/-! ## 4 The base case -/

theorem base_stay (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (baseJ5 p j cur cut).decide t rs gs = .ok tE)
    : StayV t tE := by
  unfold baseJ5 at h
  dsimp only at h
  split at h
  · obtain ⟨cl, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨cl', _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨m, _, h⟩ := bind_ok h
    obtain ⟨star, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨a, _, h⟩ := bind_ok h
    cases h
    refine ⟨fun o _ => modify_rows _ _ _ _ fun _ => rfl,
      fun k _ => modify_src _ _ _ _ fun _ => rfl, ?_, ?_⟩
    · show _ ≤ (t.st.oracles.modify _ _).size
      rw [Array.size_modify]
    · show _ ≤ (t.book.trees.modify _ _).size
      rw [Array.size_modify]
  · cases h

/-! ## 5 A switch and the batching after it -/

theorem openOne_src (S : Statement) (ft : Nat) (pos : Positions) (B0 : TreeBook) (t : Nat)
    (s s' : TreeBook × List Tw.L9.Col × Array (Nat × Array Nat × Array (Array F)))
    (h : Tw.L9.openOne S ft pos B0 t s = .ok s') (k : Nat) :
    (s'.1.trees[k]?).map (·.src) = (s.1.trees[k]?).map (·.src) := by
  unfold Tw.L9.openOne at h
  split at h
  · dsimp only at h
    repeat' split at h
    all_goals first
      | (cases h; exact modify_src _ _ _ _ fun _ => rfl)
      | cases h
  · cases h

theorem opened_src (S : Statement) (ft : Nat) (pos : Positions) (B0 : TreeBook) (k : Nat) :
    ∀ (l : List Nat) (s s' : TreeBook × List Tw.L9.Col × Array (Nat × Array Nat × Array (Array F))),
      l.foldlM (fun s t => Tw.L9.openOne S ft pos B0 t s) s = .ok s' →
      (s'.1.trees[k]?).map (·.src) = (s.1.trees[k]?).map (·.src)
  | [], s, s', h => by cases h; rfl
  | t :: l, s, s', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h2⟩ := bind_ok h
    rw [opened_src S ft pos B0 k l s1 s' h2, openOne_src S ft pos B0 t s s1 h1]

theorem readOld_src (i : Tw.L9.SwIn) (pos : Positions) (B : TreeBook) (left : List Tw.L9.Col)
    (ys : Array E) (h : Tw.L9.readOld i pos = .ok (B, left, ys)) (k : Nat) :
    (B.trees[k]?).map (·.src) = (i.book.trees[k]?).map (·.src) := by
  obtain ⟨places, cols, opened, _, h3, _, _⟩ := readOld_inv i pos B left ys h
  exact opened_src _ _ _ _ k _ _ _ h3

theorem switch_stay (p : P12) (he : p.early = true) (ha : p.answers = 1) (j : Nat)
    (cur nxt : Fmt.M1.Stage) (last : Bool) (cut : List Fmt.DeclaredRound) (t1 t2 t3 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (hlen : rs.length ≤ 2)
    (h1 : (switchJ p j cur nxt last cut).decide t1 rs gs = .ok t2)
    (h2 : (behindJ p (j + 1) nxt cut).decide t2 [] [] = .ok t3) : StayV t1 t3 := by
  have h1' := h1
  simp only [switchJ] at h1'
  split at h1'
  · rename_i rows gp nx e1 e2
    obtain ⟨⟨⟨out0, theta0⟩, s'⟩, hx, h1''⟩ := bind_ok h1'
    obtain ⟨r1, r2, rest, hr⟩ := H2K.Out.switchE_two hx
    have hr' : rs = r1 :: r2 :: rest := hr
    have hrest : rest = [] := by
      rw [hr'] at hlen
      simp only [List.length_cons] at hlen
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hrest
    subst hr'
    obtain ⟨out, row, L, th, D, _, _, hd, _, _⟩ :=
      switchUnfolds p j cur nxt last cut t1 t2 t3 r1 r2 gs rows gp nx he ha e1 e2 h1 h2
    obtain ⟨i, left, _, hib, _, _, _, hread⟩ := hd.read
    have hsame := H2K.Out.readOld_same i _ _ _ _ hread
    refine ⟨fun o ho => ?_, fun k hk => ?_, ?_, ?_⟩
    · rw [hd.st, begun_rows]
      unfold Taken.stR Taken.stJ Taken.stA
      rw [(withRows_oracles gp D.rows _).1, joined_sampleRows, ledgerShut_sampleRows]
      show (((stSent t1.st _).oracles.modify t1.st.oracles.size _)[o]?).map _ = _
      rw [modify_other _ _ _ _ (by omega), stSent_old _ _ _ ho]
    · rw [readOld_src i _ _ _ _ hread k, hib, bookSent_old _ _ _ _ _ _ k hk]
    · rw [hd.st, begun_osize]
      unfold Taken.stR Taken.stJ Taken.stA
      rw [(withRows_oracles gp D.rows _).1]
      show _ ≤ ((ledgerShut _ _ _).oracles.modify _ _).size
      rw [Array.size_modify]
      have e : ∀ (S : Statement) (T : SwitchTarget) (o : Nat),
          (ledgerShut S T o).oracles.size = S.oracles.size := fun S T o => by
        unfold ledgerShut
        split
        · exact ProxRun.closeLedgers_size _ _
        · rfl
      rw [e]
      show _ ≤ ((stSent t1.st _).oracles.modify _ _).size
      rw [Array.size_modify]
      show _ ≤ (t1.st.oracles ++ _).size
      rw [Array.size_append]
      omega
    · rw [hsame.1, hib]
      exact bookSent_size _ _ _ _ _ _
  · cases h1'

/-! ## 6 The whole test -/

theorem stages_stay (p : P12) (he : p.early = true) (ha : p.answers = 1) :
    ∀ (rest : List Fmt.M1.Stage) (j : Nat) (cur : Fmt.M1.Stage) (la : Laid) (t tE : T12)
      (rs : List Fmt.RoundView) (gs : Gs),
      (stagesFrom guardedProximityTestParts p j cur rest la : Blk').decide t rs gs = .ok tE → StayV t tE
  | [], j, cur, la, t, tE, rs, gs, h => by
    rw [stagesFrom_last] at h
    exact base_stay p _ _ _ _ _ _ _ (ranged_ok _ _ _ _ _ _ h).1
  | nxt :: rest, j, cur, la, t, tE, rs, gs, h => by
    obtain ⟨t1, t2, t3, f1, f2, f3, _, f5⟩ :=
      (stagesFrom_ok guardedProximityTestParts p j cur nxt rest la t tE rs gs).1 h
    have k1 := fold_stay p j cur _ t t1 _ _ ((like_P5 p).fold _ _ _ _ _ _ _ f1)
    have hlen : ((rs.drop (foldAt guardedProximityTestParts p j cur la : Blk').rounds.length).take
        (switchAt guardedProximityTestParts p j cur nxt rest.isEmpty la : Blk').rounds.length).length ≤ 2 := by
      refine (List.length_take_le _ _).trans ?_
      show (((la.drop (1 + cur.k)).take 2).map (·.1)).length ≤ 2
      rw [List.length_map]
      exact List.length_take_le _ _
    have k2 := switch_stay p he ha j cur nxt rest.isEmpty _ t1 t2 t3 _ _ hlen
      ((like_P5 p).switch _ _ _ _ _ _ _ _ _ f2) ((like_P5 p).behind _ _ _ _ _ f3)
    exact (k1.trans k2).trans (stages_stay p he ha rest (j + 1) nxt _ t3 tE _ _ f5)

theorem k12_stay (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    StayV t0 tE := by
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
  exact (bat_stay p _ _ _ _ _ ((like_P5 p).bat _ _ _ _ _ hbat)).trans
    (stages_stay p he ha rest 0 first _ _ tE _ _ hst)

/-! ## 7 What a proximity test keeps -/

/-- What a proximity test leaves as it was, and how what it changes may have changed. t: the
structure before the test; t': the structure after it. -/
structure K12Keeps (p : P12) (t t' : T12) : Prop where
  /-- every number, flag and list of statement, book and count of roots: as the function on shapes
  returns them -/
  shape : testCore p (coreSh ⟨t.st, t.book, t.roots⟩) t.g t.mask =
    some (coreSh ⟨t'.st, t'.book, t'.roots⟩)
  /-- every other group of t is unchanged, its open rows with their values -/
  groupsElse : ∀ (q : Nat) (G : Group), q ≠ t.g → t.st.groups[q]? = some G →
    t'.st.groups[q]? = some G
  /-- every message of t keeps its sample rows, with their values -/
  samples : ∀ (o : Nat) (x : OnBytes.Oracle), t.st.oracles[o]? = some x →
    ∃ x' : OnBytes.Oracle, t'.st.oracles[o]? = some x' ∧ x'.sampleRows = x.sampleRows
  /-- every tree of t keeps its source, with its values -/
  srcs : ∀ (k : Nat) (T : Tree), t.book.trees[k]? = some T →
    ∃ T' : Tree, t'.book.trees[k]? = some T' ∧ T'.src = T.src
  ends : t'.g = t.g ∧ t'.pass = .nothing ∧ t'.mask = none
  /-- an older message that is no member of the group under test and not the first fold's mask: to
  the letter -/
  rest : ∀ (G : Group) (o : Nat), t.st.groups[t.g]? = some G → o < t.st.oracles.size →
    o ∉ G.members.toList → t.mask ≠ some o → t'.st.oracles[o]? = t.st.oracles[o]?
  /-- every place that the book of t has, the book of t' has -/
  place : ∀ (o : Nat) (q : Nat × Nat), t.book.place[o]? = some q → t'.book.place[o]? = some q

/-- **Where the test's own block accepts, `K12Keeps` holds.** -/
theorem k12_keeps (p : P12) (he : p.early = true) (ha : p.answers = 1) (t t' : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t rs gs = .ok t') :
    K12Keeps p t t' := by
  have o1 := H2K.Out.k12_out p he ha t t' rs gs h
  obtain ⟨G, o2⟩ := H2K.Out.k12_out2 p he ha t t' rs gs h
  have s := k12_stay p he ha t t' rs gs h
  refine ⟨k12_core_sh p he ha t t' rs gs h, fun q G' hq hG' => ?_, fun o x hx => ?_,
    fun k T hT => ?_, ⟨o1.g, o1.pass, o1.mask⟩, fun G' o hG' hlt hno hmask => ?_, o1.book.place⟩
  · have hlt : q < t.st.groups.size := (Array.getElem?_eq_some_iff.1 hG').1
    rw [o2.others q hlt hq]
    exact hG'
  · have hlt : o < t.st.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
    have e := s.samples o hlt
    rw [hx] at e
    obtain ⟨x', hx', ex⟩ := Option.map_eq_some_iff.1 e
    exact ⟨x', hx', ex⟩
  · have hlt : k < t.book.trees.size := (Array.getElem?_eq_some_iff.1 hT).1
    have e := s.srcs k hlt
    rw [hT] at e
    obtain ⟨T', hT', eT⟩ := Option.map_eq_some_iff.1 e
    exact ⟨T', hT', eT⟩
  · obtain rfl : G' = G := Option.some.inj (hG'.symm.trans o2.was)
    exact o2.rest o hlt hno hmask

/-- **What rides past, from `K12Keeps` alone**: an older message that is no member of the group
under test and not the first fold's mask stands behind the test to the letter, at its place in the
book. -/
theorem K12Keeps.rides_past {p : P12} {t t' : T12} (K : K12Keeps p t t') {G : Group}
    (hG : t.st.groups[t.g]? = some G) {o : Nat} {x : OnBytes.Oracle}
    (hx : t.st.oracles[o]? = some x) (hno : o ∉ G.members.toList) (hmask : t.mask ≠ some o) :
    t'.st.oracles[o]? = some x ∧ ∀ q, t.book.place[o]? = some q → t'.book.place[o]? = some q :=
  ⟨(K.rest G o hG (Array.getElem?_eq_some_iff.1 hx).1 hno hmask).trans hx, K.place o⟩

/-- The same at a chain's state, for a test that is placed in a chain by a way in, `enter`, and a
way out, `leave` (`Block.inside`, Johnson/Desc/Block.lean). s: the chain's state before the test;
s': after it. -/
def K12KeepsAt {S : Type} (p : P12) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (s s' : S) : Prop :=
  ∃ t t', enter s = .ok t ∧ K12Keeps p t t' ∧ leave s t' = .ok s'

/-- **Where the block that is placed by `enter` and `leave` accepts, `K12KeepsAt` holds.** -/
theorem k12_keeps_at {S : Type} (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (enter : S → Except String T12) (leave : S → T12 → Except String S) (s s' : S)
    (rs : List Fmt.RoundView) (gs : Gs)
    (h : ((proximityTestKind guardedProximityTestParts p : Blk').inside enter leave).decide s rs gs = .ok s') :
    K12KeepsAt p enter leave s s' := by
  obtain ⟨t, t', h1, h2, h3⟩ :=
    (VerifiableInference.Desc.K12.Seat.inside_ok enter _ leave s s' rs gs).1 h
  exact ⟨t, t', h1, k12_keeps p he ha t t' rs gs h2, h3⟩

/-- **What rides past, at a chain's state, from `K12KeepsAt` only.** st, book: how the chain's state
holds statement and book. Hypotheses, at the given s and s': `enter` hands the two on as they are
(hin); `leave` puts the test's own two back (hout). -/
theorem K12KeepsAt.rides_past {S : Type} {p : P12} {enter : S → Except String T12}
    {leave : S → T12 → Except String S} {s s' : S} (K : K12KeepsAt p enter leave s s')
    (st : S → Statement) (book : S → TreeBook)
    (hin : ∀ t, enter s = .ok t → t.st = st s ∧ t.book = book s)
    (hout : ∀ t', leave s t' = .ok s' → st s' = t'.st ∧ book s' = t'.book) :
    ∃ t, enter s = .ok t ∧ ∀ (G : Group) (o : Nat) (x : OnBytes.Oracle),
      (st s).groups[t.g]? = some G → (st s).oracles[o]? = some x → o ∉ G.members.toList →
      t.mask ≠ some o →
      (st s').oracles[o]? = some x ∧
        ∀ q, (book s).place[o]? = some q → (book s').place[o]? = some q := by
  obtain ⟨t, t', h1, h2, h3⟩ := K
  obtain ⟨e1, e2⟩ := hin t h1
  obtain ⟨e3, e4⟩ := hout t' h3
  refine ⟨t, h1, fun G o x hG hx hno hmask => ?_⟩
  rw [e3, e4, ← e2]
  rw [← e1] at hG hx
  exact h2.rides_past hG hx hno hmask

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.StayV.trans
#print axioms ProofFile.Honest.Sh.modify_rows
#print axioms ProofFile.Honest.Sh.modify_src
#print axioms ProofFile.Honest.Sh.modify_other
#print axioms ProofFile.Honest.Sh.begun_rows
#print axioms ProofFile.Honest.Sh.begun_osize
#print axioms ProofFile.Honest.Sh.treesSent_size
#print axioms ProofFile.Honest.Sh.foldl_modify_size
#print axioms ProofFile.Honest.Sh.bookSent_old
#print axioms ProofFile.Honest.Sh.bookSent_size
#print axioms ProofFile.Honest.Sh.bat_form
#print axioms ProofFile.Honest.Sh.bat_stay
#print axioms ProofFile.Honest.Sh.fold_stay
#print axioms ProofFile.Honest.Sh.base_stay
#print axioms ProofFile.Honest.Sh.openOne_src
#print axioms ProofFile.Honest.Sh.opened_src
#print axioms ProofFile.Honest.Sh.readOld_src
#print axioms ProofFile.Honest.Sh.switch_stay
#print axioms ProofFile.Honest.Sh.stages_stay
#print axioms ProofFile.Honest.Sh.k12_stay
#print axioms ProofFile.Honest.Sh.k12_keeps
#print axioms ProofFile.Honest.Sh.K12Keeps.rides_past
#print axioms ProofFile.Honest.Sh.k12_keeps_at
#print axioms ProofFile.Honest.Sh.K12KeepsAt.rides_past
#print axioms ProofFile.Honest.Sh.StayV
#print axioms ProofFile.Honest.Sh.K12Keeps
#print axioms ProofFile.Honest.Sh.K12KeepsAt
