-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Blind/DoorL.lean

The state on entry of the first chain's proximity test, as a function of the input and of the rounds
shown alone: the description's own fold over the blocks in front, at made-up columns (`zeroCols`,
the kind K10's authors' filler), then the way in, then every row's target set to zero. And its tie
to the state that the description's own fold reaches at a run's own columns. Seven definitions;
eleven theorems.

  `doorTryZ`, `atHandZ`, `doorZ`: one text that may refuse, and two readings of it: the test "it
      returns", and its value or a default. General in the chain's state and in the way in.
  `doorTryL`, `atHandL`, `doorL`: these at the first chain's state (`Desc.First.S`) and
      `enterFinish` (Johnson/Desc/K12/AtFinish.lean).
  `KeepsInFront`: the premise, by name: every block in front keeps the wiping `wipeS`.
  `takeWhile_cut`, `any_cut`, `apart_of_nodup`: on lists of blocks.
  `doorZ_doorBy`: `doorZ` is `doorBy` (DoorByAtFirst.lean) at a reader that makes up the columns: so
      it is no further text of a fold.
  `enterFinish_alike`: at two states that are one once wiped the way in refuses with one word, or
      returns records that agree but for targets.
  `doorTryZ_of_fold`: the heart; no frame in it: where the description's own fold over the blocks in
      front returns a state at the rounds shown and at any columns, `doorTryZ` is the way in at that
      state, wiped.
  `atHandZ_of_try`, `doorZ_agree`: from that equation: at hand just where the way in returns; and
      then the value agrees with what it returns, but for targets.
  `door_zero_at_first`: at a called part of the first chain, at a run of the frame's walking prover:
      over `called_at_first` (CalledAtFirst.lean), whose eight clauses it carries. General in the
      description.
  `say_zero_at_first`: under `Steps` (Top.lean) by name: at such a run each move of a part whose
      state on entry is `doorZ` says what it says at the record that the way in returns.
  `doorL_at_first`: `door_zero_at_first` at the seated description's own term (`P5J.F0T`), `wipeS`
      and `enterFinish`, under `KeepsInFront`.

Over what it stands. Files of the kind K10's authors, rows of the sealed library
(Johnson/Desc/ProofFile/Honest/K10/: BatWipe, StAtZero, WipeFold, WipeS, Wipe/Alike, Wipe/KeepK10,
Wipe/WipeGround, Wipe/WipeLaws), and this folder's Wipe.lean, Fold.lean, Readers.lean and Top.lean.

How it may be spoken of. What may be said here on hiding, and no more (a rule of use for whoever
builds on this file; no theorem), in the words of the library's makers' own review of hiding,
whole, a working name replaced in the first pair of square brackets (the second pair is the words'
own): «the sentence that could stand, if [the kind K10's authors'] Keeps in front, yours and a named
test «the fold and the way in return» stand: «at a state on entry that agrees with the verifier's
but for the rows' targets; what the two parts send does not hang on these [theorems]»: NEVER «the
verifier's»». These words name no lemma. As we read the three: `open_front2` (the kind K10's
authors'); `keeps_finish` (KeepsAtFinish.lean); `atHandL` (here), which AtHandAtFinish.lean shows to
be true at the stands of which it speaks. That word was given of the stand that `midAt` returns, at
which this file's laws then stood. Of the stand that `midAtW` returns, at which they stand now, the
same review has said: «MY SENTENCE AT L … CARRIES TO midAtW's STAND: the doors read the rounds
alone, to the sign, and the new stand is tied to the first view by the same clause.» Whether the
sentence may now be said is the review's to say, not this file's.

Limits.
- That `enterFinish` returns at the state in front of the test is a hypothesis in this file's laws.
  AtHandAtFinish.lean in this folder pays it, in the goals' scope, at an opening at the library's
  older hash: the state in front is what the last code switch's place has returned.
- `doorZ` HAS A SILENT DEFAULT (`fall`); `atHandZ` is the test that says whether it was taken. The
  kind K10's filler, over which this file stands, is swallowed by a like default, and on it holds
  (Honest/K10/StAtZero.lean's head): «INTO A LOT OF A FILLING AT
  WHICH ANYTHING ON HIDING IS SAID OR COUNTED: «NOT BEFORE (L0) · (L1) · (L2) ARE THEOREMS»»; «NEVER
  A LAW ON HIDING COUNTED AT A CLOSING, NOR "the honest prover's closing", WITHOUT closeAtHand … =
  true BY NAME AT THE STANDS SPOKEN OF». What that asks at this place is the review's to say. On
  hiding this file says nothing of its own.
- `KeepsInFront` is a premise here. KeepsAtFinish.lean in this folder pays it at the test's place,
  in the goals' scope, at an opening at the library's older hash (`keepsInFront_L`).
- `Steps` is a premise here. All.lean in this folder pays it (`theSteps`).
- bs, start, a and fall are letters: at a laying they are to be named. A value laid for start may
  close over anything.
- General in the chain's state, not in the number of the first tree (0, as in the first and the
  shared chain) nor in the front's form: in the last chain the rounds shown begin with both earlier
  chains'.
- `frontState` drops what the fold leaves over: at a front that shows more rounds `doorTryZ` may
  return too; the laws here speak of fronts that show just the rounds of the blocks in front.
- Of the walk (`runC`) and of `midAtW`'s stand, as `called_at_first` is. Nothing on whether `ready`
  or `runC` returns or a part is called.
- The stand is the state that `midAtW` (Honest/MidW.lean) returns. That `runC`'s own walk goes
  through that state is not said here.
- No property of a prover or a protocol: nothing on completeness, soundness, binding or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K10.WipeS
import Johnson.Desc.ProofFile.Honest.K10.Wipe.Alike
import Johnson.Desc.ProofFile.Honest.K12.Blind.Top
import Johnson.Desc.ProofFile.Honest.K12.DoorByAtFirst
import Johnson.Desc.ProofFile.Honest.Law.Cuts
import Johnson.Desc.K12.AtFinish
import Johnson.P5J.AtTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Blind
open VerifiableInference.Desc (Block Place OpenedColumn FileDescription foldBlocks)
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.First (S Here FinOwn)
open ProofFile.Honest
open ProofFile.Honest.K10 (frontState zeroCols Keeps AlikeE wipeS wipeSt wipeHere fold_zero)

/-! ## 1 The definitions -/

/-- **The state on entry, tried**: the description's own fold over the blocks of bs in front of the
place a (`frontState`), from `start w`, at the rounds shown and at made-up columns (`zeroCols`);
then the way in, `enter`; then every target set to zero (`wipeT`). A refusal where no block stands
at a, where the fold refuses, and where the way in refuses. General in the chain's state σ. With
code. It reads the input through start alone, and of the front the rounds shown alone. -/
def doorTryZ {σ Cl W X : Type} (enter : σ → Except String T12) (bs : List (Block σ Cl))
    (start : W → σ) (a : Place) (w : W) (fr : Front X) : Except String T12 :=
  ((frontState 0 bs (start w) a fr.seen.rounds
    (zeroCols 0 (bs.takeWhile (·.place != a)) fr.seen.rounds)).bind enter).map wipeT

/-- **The state on entry is at hand**: the fold and the way in return. A test with code. -/
def atHandZ {σ Cl W X : Type} (enter : σ → Except String T12) (bs : List (Block σ Cl))
    (start : W → σ) (a : Place) (w : W) (fr : Front X) : Bool :=
  (doorTryZ enter bs start a w fr).toOption.isSome

/-- **The state on entry**, of the type of `TestJob.rec₀`: what `doorTryZ` returns; `fall` where it
refuses: A SILENT DEFAULT: `atHandZ` is the test that says whether it was taken. -/
def doorZ {σ Cl W X : Type} (enter : σ → Except String T12) (bs : List (Block σ Cl))
    (start : W → σ) (a : Place) (fall : T12) (w : W) (fr : Front X) : T12 :=
  (doorTryZ enter bs start a w fr).toOption.getD fall

/-- The three at the first chain's state and the way into the test at the finish (`enterFinish`,
Johnson/Desc/K12/AtFinish.lean). bs, start, a and fall are letters: at a laying they are to be
named.
-/
def doorTryL {Cl W X : Type} (bs : List (Block S Cl)) (start : W → S) (a : Place) :
    W → Front X → Except String T12 := doorTryZ enterFinish bs start a

def atHandL {Cl W X : Type} (bs : List (Block S Cl)) (start : W → S) (a : Place) :
    W → Front X → Bool := atHandZ enterFinish bs start a

def doorL {Cl W X : Type} (bs : List (Block S Cl)) (start : W → S) (a : Place) (fall : T12) :
    W → Front X → T12 := doorZ enterFinish bs start a fall

/-- **The premise, by name**: every block of bs in front of the place a keeps the wiping of the
first chain's state (`Keeps wipeS 0`, the kind K10's authors' Honest/K10/WipeFold.lean, WipeS.lean).
-/
def KeepsInFront {Cl : Type} (bs : List (Block S Cl)) (a : Place) : Prop :=
  ∀ b ∈ bs.takeWhile (·.place != a), Keeps wipeS 0 b

/-! ## 2 On lists of blocks -/

/-- The blocks in front of a place, where the list is cut at a block of that place and no block in
front bears it. -/
theorem takeWhile_cut {σ Cl : Type} (pre t : List (Block σ Cl)) (b : Block σ Cl)
    (h : ∀ y ∈ pre, y.place ≠ b.place) :
    (pre ++ b :: t).takeWhile (·.place != b.place) = pre := by
  induction pre with
  | nil =>
    have hx : (b.place != b.place) = false := bne_self_eq_false _
    rw [List.nil_append, List.takeWhile_cons, hx]
    rfl
  | cons y l ih =>
    have hy : (y.place != b.place) = true := bne_iff_ne.2 (h y (List.mem_cons_self ..))
    rw [List.cons_append, List.takeWhile_cons, hy, ih fun z hz => h z (List.mem_cons_of_mem _ hz)]
    rfl

theorem any_cut {σ Cl : Type} (pre t : List (Block σ Cl)) (b : Block σ Cl) :
    (pre ++ b :: t).any (·.place == b.place) = true :=
  List.any_eq_true.2 ⟨b, List.mem_append_right _ (List.mem_cons_self ..), beq_self_eq_true _⟩

/-- Where the places of a list are apart, no block in front of a cut bears the place at the cut. -/
theorem apart_of_nodup {σ Cl : Type} {pre t : List (Block σ Cl)} {b : Block σ Cl}
    (h : ((pre ++ b :: t).map (·.place)).Nodup) : ∀ y ∈ pre, y.place ≠ b.place := by
  intro y hy e
  rw [List.map_append, List.map_cons] at h
  exact (List.nodup_append.1 h).2.2 y.place (List.mem_map.2 ⟨y, hy, rfl⟩) b.place
    (List.mem_cons_self ..) e

/-! ## 3 The text, the way in, the heart -/

/-- `doorZ` is `doorBy` (DoorByAtFirst.lean) at the blocks in front of a, the reader that makes up
the columns, and the way in followed by the wiping, where a block of bs stands at a. -/
theorem doorZ_doorBy {σ Cl W X : Type} (enter : σ → Except String T12) (bs : List (Block σ Cl))
    (start : W → σ) (a : Place) (fall : T12) (ha : bs.any (·.place == a) = true) :
    (doorZ enter bs start a fall : W → Front X → T12) =
      Light.doorBy (bs.takeWhile (·.place != a)) start (fun s => (enter s).map wipeT)
        (fun _ fr => zeroCols 0 (bs.takeWhile (·.place != a)) fr.seen.rounds) fall := by
  funext w fr
  unfold doorZ doorTryZ frontState Light.doorBy
  rw [ha]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  cases foldBlocks 0 (bs.takeWhile (·.place != a)) (start w) fr.seen.rounds
    (zeroCols 0 (bs.takeWhile (·.place != a)) fr.seen.rounds) <;> rfl

/-- **The way in at two states that are one once wiped**: it refuses with one word, or returns two
records that agree but for targets. -/
theorem enterFinish_alike (s s' : S) (h : wipeS s = wipeS s') :
    AlikeE wipeT (enterFinish s) (enterFinish s') := by
  have h1 : wipeSt s.st = wipeSt s'.st := congrArg (fun z : S => z.st) h
  have h2 : s.book = s'.book := by
    have e := congrArg (fun z : S => z.book) h
    exact e
  have h3 : s.roots = s'.roots := by
    have e := congrArg (fun z : S => z.roots) h
    exact e
  have h4 : s.rowsOwed = s'.rowsOwed := by
    have e := congrArg (fun z : S => z.rowsOwed) h
    exact e
  have h5 : s.failed = s'.failed := by
    have e := congrArg (fun z : S => z.failed) h
    exact e
  have h6 : wipeHere s.here = wipeHere s'.here := congrArg (fun z : S => z.here) h
  have h7 : s.noneWaits = s'.noneWaits := by
    unfold S.noneWaits
    rw [h4]
  unfold enterFinish
  rw [h7, h5]
  generalize s.here = x at h6 ⊢
  generalize s'.here = y at h6 ⊢
  cases x <;> cases y
  case fin.fin o o' =>
    have h8 := Here.fin.inj h6
    have g : o.fr.group = o'.fr.group := by
      have e := congrArg (fun z : FinOwn => z.fr.group) h8
      exact e
    have k : o.mask = o'.mask := by
      have e := congrArg (fun z : FinOwn => z.mask) h8
      exact e
    refine AlikeE.head_ok' fun _ _ => AlikeE.head_ok' fun _ _ => AlikeE.ok ?_
    unfold wipeT
    dsimp only
    rw [h1, h2, h3, g, k]
  all_goals first
    | exact AlikeE.error _
    | simp [wipeHere] at h6

/-- **The heart, with no frame in it.** The list is cut at a block b whose place no block in front
bears; every block in front keeps `wipe`; the way in is alike at states that are one under `wipe`.
Where the description's own fold over the blocks in front returns s, at the rounds shown and at ANY
columns, `doorTryZ` is the way in at s, wiped. -/
theorem doorTryZ_of_fold {σ Cl W X : Type} (wipe : σ → σ) (enter : σ → Except String T12)
    (pre t : List (Block σ Cl)) (b : Block σ Cl) (hp : ∀ y ∈ pre, y.place ≠ b.place)
    (hk : ∀ y ∈ pre, Keeps wipe 0 y)
    (hE : ∀ s s', wipe s = wipe s' → AlikeE wipeT (enter s) (enter s')) (start : W → σ) (w : W)
    (fr : Front X) {cs : List OpenedColumn} {r : σ × List Fmt.RoundView × List OpenedColumn}
    (h : foldBlocks 0 pre (start w) fr.seen.rounds cs = .ok r) :
    doorTryZ enter (pre ++ b :: t) start b.place w fr = (enter r.1).map wipeT := by
  obtain ⟨t0, z1, z2⟩ := fold_zero wipe 0 pre hk h
  unfold doorTryZ frontState
  rw [any_cut, takeWhile_cut pre t b hp]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  rw [z1]
  exact hE t0 r.1 z2

/-- From that equation: the state on entry is at hand just where the way in returns at s. -/
theorem atHandZ_of_try {σ Cl W X : Type} {enter : σ → Except String T12} {bs : List (Block σ Cl)}
    {start : W → σ} {a : Place} {w : W} {fr : Front X} {s : σ}
    (h : doorTryZ enter bs start a w fr = (enter s).map wipeT) :
    atHandZ enter bs start a w fr = (enter s).toOption.isSome := by
  unfold atHandZ
  rw [h]
  cases enter s <;> rfl

/-- And where the way in returns T at s, the state on entry agrees with T but for targets. -/
theorem doorZ_agree {σ Cl W X : Type} {enter : σ → Except String T12} {bs : List (Block σ Cl)}
    {start : W → σ} {a : Place} {w : W} {fr : Front X} {s : σ} {T : T12} (fall : T12)
    (h : doorTryZ enter bs start a w fr = (enter s).map wipeT) (hT : enter s = .ok T) :
    Agree (doorZ enter bs start a fall w fr) T := by
  unfold doorZ Agree
  rw [h, hT]
  exact wipeT_wipeT T

/-! ## 4 At a run -/

/-- **At a called part of the first chain, at a run of the frame's walking prover.** General in the
description. All eight clauses of `called_at_first` (CalledAtFirst.lean), to the letter (the stand
m; the state s that the description's own fold over the blocks in front returns at the run's own
rounds and at cs; cs tied to the first view's columns and to the filling); and, of the same m, s and
cs: at m's input, at every front that shows just the rounds of the blocks in front, and at every
start that is the description's own there, `doorTryZ` at the chain's own list and the side's place
is the way in at s, wiped. hk: the premise on the blocks in front. hE: on the way in. -/
theorem door_zero_at_first {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R)
    (σ : Side F.S₁ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₁ F.Cl)) (i : ℕ) (St : StandsAt F.first.blocksInOrder R.first σ u pre t i)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (wipe : F.S₁ → F.S₁) (enter : F.S₁ → Except String T12) (hk : ∀ y ∈ pre, Keeps wipe 0 y)
    (hE : ∀ s s', wipe s = wipe s' → AlikeE wipeT (enter s) (enter s')) :
    ∃ (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y) (s : F.S₁) (cs more : List OpenedColumn)
      (rest : List Fmt.RoundView) (tr : Tr),
      midAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      P.trace w₀ x = some tr ∧ m.st.input = ⟨w₀, rc, x, tr⟩ ∧
      r.run.views.1.rounds = m.seen ++ rest ∧
      m.seen.length = (pre.flatMap (·.rounds)).length + i ∧
      r.run.views.1.opened = cs ++ more ∧
      foldBlocks 0 pre (F.start₁ (F.pub x)) (m.seen.take (pre.flatMap (·.rounds)).length) cs =
        .ok (s, [], []) ∧
      fillCols (readsOf 0 0 (P.storedWords w₀ rc)
        (treeOwn (r.run.played.1.take (pre.flatMap (·.rounds)).length))
        (pre.flatMap (·.rounds))
        ((m.seen.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cs ∧
      ∀ (start : Local W₀ Rc Xi Tr → F.S₁) (fr : Front Y),
        start m.st.input = F.start₁ (F.pub x) →
        fr.seen.rounds = m.seen.take (pre.flatMap (·.rounds)).length →
        doorTryZ enter F.first.blocksInOrder start σ.block.place m.st.input fr = (enter s).map wipeT := by
  obtain ⟨m, s, cs, more, rest, tr, a1, a2, a3, a4, a5, a6, a7, a8⟩ :=
    Light.called_at_first hpl hR σ u pre t i St hrun hc
  refine ⟨m, s, cs, more, rest, tr, a1, a2, a3, a4, a5, a6, a7, a8, fun start fr hs hf => ?_⟩
  have hn := (places_nodup ((F.planOk_ok).1 hpl).places).1
  rw [St.cut] at hn
  rw [St.cut]
  refine doorTryZ_of_fold wipe enter pre t σ.block (apart_of_nodup hn) hk hE start m.st.input fr
    (cs := cs) (r := (s, [], [])) ?_
  rw [hs, hf]
  exact a7

/-- **At such a run what a part at `doorZ` says is what it says at the record that the way in
returns at s.** Under the five equations `Steps` (Top.lean), by name. `doorZ`'s value is not that
record: it agrees with it but for the rows' targets. With all eight clauses of `called_at_first` on
m, s and cs: where the way in returns T at s: for every job J whose state on entry is `doorZ` at the
chain's own list, the side's place and a start that is the description's own at m's input: the move
of the test's round number j says, at m's input and at what is shown, the same as the move of the
job that is handed T; for every j, where what is shown begins with the rounds of the blocks in front
and has j rounds more, at every value of the columns handed. -/
theorem say_zero_at_first (s5 : Steps) {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk :
           ProverCoinCounts} {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R)
    (σ : Side F.S₁ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₁ F.Cl)) (i : ℕ) (St : StandsAt F.first.blocksInOrder R.first σ u pre t i)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (wipe : F.S₁ → F.S₁) (enter : F.S₁ → Except String T12) (hk : ∀ y ∈ pre, Keeps wipe 0 y)
    (hE : ∀ s s', wipe s = wipe s' → AlikeE wipeT (enter s) (enter s')) :
    ∃ (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y) (s : F.S₁) (cs more : List OpenedColumn)
      (rest : List Fmt.RoundView) (tr : Tr),
      midAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      P.trace w₀ x = some tr ∧ m.st.input = ⟨w₀, rc, x, tr⟩ ∧
      r.run.views.1.rounds = m.seen ++ rest ∧
      m.seen.length = (pre.flatMap (·.rounds)).length + i ∧
      r.run.views.1.opened = cs ++ more ∧
      foldBlocks 0 pre (F.start₁ (F.pub x)) (m.seen.take (pre.flatMap (·.rounds)).length) cs =
        .ok (s, [], []) ∧
      fillCols (readsOf 0 0 (P.storedWords w₀ rc)
        (treeOwn (r.run.played.1.take (pre.flatMap (·.rounds)).length))
        (pre.flatMap (·.rounds))
        ((m.seen.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cs ∧
      ∀ (T : T12), enter s = .ok T →
      ∀ (start : Local W₀ Rc Xi Tr → F.S₁) (fall : T12) (J : TestJob (Local W₀ Rc Xi Tr) Y),
        start m.st.input = F.start₁ (F.pub x) →
        J.rec₀ = doorZ enter F.first.blocksInOrder start σ.block.place fall →
      ∀ (C : Type) (rd : C → TestCoins) (j : ℕ) (c : C) (sn : Seen)
        (st : State (Local W₀ Rc Xi Tr) Y), st.input = m.st.input →
        sn.rounds.length = (pre.flatMap (·.rounds)).length + j →
        sn.rounds.take (pre.flatMap (·.rounds)).length =
          m.seen.take (pre.flatMap (·.rounds)).length →
        (moveAt J rd j).say c sn st =
          (moveAt { J with rec₀ := fun _ _ => T } rd j).say c sn st := by
  obtain ⟨m, s, cs, more, rest, tr, a1, a2, a3, a4, a5, a6, a7, a8, b7⟩ :=
    door_zero_at_first hpl hR σ u pre t i St hrun hc wipe enter hk hE
  refine ⟨m, s, cs, more, rest, tr, a1, a2, a3, a4, a5, a6, a7, a8,
    fun T hT start fall J hs hJ C rd j c sn st h1 h2 h3 => ?_⟩
  have hfr : sn.rounds.take (sn.rounds.length - j) =
      m.seen.take (pre.flatMap (·.rounds)).length := by
    rw [h2, Nat.add_sub_cancel, h3]
  have hA : Agree
      (J.rec₀ st.input ⟨st.heard.take (st.heard.length - j), st.own,
        sn.front j⟩) T := by
    rw [hJ, h1]
    exact doorZ_agree fall (b7 start _ hs hfr) hT
  show Except.ok (msgAt J st.input _ (rd c) _ j) =
    Except.ok (msgAt { J with rec₀ := fun _ _ => T } st.input _ (rd c) _ j)
  rw [msgAt_agree s5 J (fun _ _ => T) st.input _ hA (rd c) _ j]

/-- **The door at the first chain's proximity test, at the seated description's own term**
(`P5J.F0T`, Johnson/P5J/AtTerm.lean), under `KeepsInFront` by name: `door_zero_at_first` at `wipeS`
and `enterFinish`. So `atHandL` there is "the way in returns at s", and where it returns T, `doorL`
agrees with T but for targets. -/
theorem doorL_at_first {o : ProofFile.SecondHashFunctionArgument} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain S ProofFile.Cl} {W₀ Rc Ky Tr X₀ Y V Pb : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {r : RunC (P5J.F0T o Zp Np cF)}
    (hpl : (P5J.F0T o Zp Np cF).planOk = true)
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side S ProofFile.Cl V (Local W₀ Rc ProofFile.Inst Tr) Y Pb)
    (u : Member V (Local W₀ Rc ProofFile.Inst Tr) Y Pb) (pre t : List (Block S ProofFile.Cl)) (i : ℕ)
    (St : StandsAt cF.blocksInOrder R.first σ u pre t i)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (hk : KeepsInFront cF.blocksInOrder σ.block.place) :
    ∃ (m : ProofFile.Honest.Mid (Local W₀ Rc ProofFile.Inst Tr) Y) (s : S) (cs more : List OpenedColumn)
      (rest : List Fmt.RoundView) (tr : Tr),
      midAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      P.trace w₀ x = some tr ∧ m.st.input = ⟨w₀, rc, x, tr⟩ ∧
      r.run.views.1.rounds = m.seen ++ rest ∧
      m.seen.length = (pre.flatMap (·.rounds)).length + i ∧
      r.run.views.1.opened = cs ++ more ∧
      foldBlocks 0 pre
        ((P5J.F0T o Zp Np cF).start₁ ((P5J.F0T o Zp Np cF).pub x))
        (m.seen.take (pre.flatMap (·.rounds)).length) cs = .ok (s, [], []) ∧
      fillCols (readsOf 0 0 (P.storedWords w₀ rc)
        (treeOwn (r.run.played.1.take (pre.flatMap (·.rounds)).length))
        (pre.flatMap (·.rounds))
        ((m.seen.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cs ∧
      ∀ (start : Local W₀ Rc ProofFile.Inst Tr → S) (fr : Front Y),
        start m.st.input =
          (P5J.F0T o Zp Np cF).start₁ ((P5J.F0T o Zp Np cF).pub x) →
        fr.seen.rounds = m.seen.take (pre.flatMap (·.rounds)).length →
        doorTryL cF.blocksInOrder start σ.block.place m.st.input fr = (enterFinish s).map wipeT ∧
        atHandL cF.blocksInOrder start σ.block.place m.st.input fr = (enterFinish s).toOption.isSome ∧
        ∀ (T fall : T12), enterFinish s = .ok T →
          Agree (doorL cF.blocksInOrder start σ.block.place fall m.st.input fr) T := by
  have hn := (places_nodup (((P5J.F0T o Zp Np cF).planOk_ok).1 hpl).places).1
  have hcut : cF.blocksInOrder = pre ++ σ.block :: t := St.cut
  have hn' : ((pre ++ σ.block :: t).map (·.place)).Nodup := hcut ▸ hn
  have hk' : ∀ y ∈ pre, Keeps wipeS 0 y := by
    unfold KeepsInFront at hk
    rw [hcut, takeWhile_cut pre t σ.block (apart_of_nodup hn')] at hk
    exact hk
  obtain ⟨m, s, cs, more, rest, tr, a1, a2, a3, a4, a5, a6, a7, a8, b7⟩ :=
    door_zero_at_first (F := (P5J.F0T o Zp Np cF)) hpl hR σ u pre t i St hrun hc wipeS
      enterFinish hk' enterFinish_alike
  refine ⟨m, s, cs, more, rest, tr, a1, a2, a3, a4, a5, a6, a7, a8, fun start fr hs hf => ?_⟩
  have e := b7 start fr hs hf
  exact ⟨e, atHandZ_of_try e, fun T fall hT => doorZ_agree fall e hT⟩

end ProofFile.Honest.K12.Blind

#print axioms ProofFile.Honest.K12.Blind.doorTryZ
#print axioms ProofFile.Honest.K12.Blind.atHandZ
#print axioms ProofFile.Honest.K12.Blind.doorZ
#print axioms ProofFile.Honest.K12.Blind.doorTryL
#print axioms ProofFile.Honest.K12.Blind.atHandL
#print axioms ProofFile.Honest.K12.Blind.doorL
#print axioms ProofFile.Honest.K12.Blind.KeepsInFront
#print axioms ProofFile.Honest.K12.Blind.takeWhile_cut
#print axioms ProofFile.Honest.K12.Blind.any_cut
#print axioms ProofFile.Honest.K12.Blind.apart_of_nodup
#print axioms ProofFile.Honest.K12.Blind.doorZ_doorBy
#print axioms ProofFile.Honest.K12.Blind.enterFinish_alike
#print axioms ProofFile.Honest.K12.Blind.doorTryZ_of_fold
#print axioms ProofFile.Honest.K12.Blind.atHandZ_of_try
#print axioms ProofFile.Honest.K12.Blind.doorZ_agree
#print axioms ProofFile.Honest.K12.Blind.door_zero_at_first
#print axioms ProofFile.Honest.K12.Blind.say_zero_at_first
#print axioms ProofFile.Honest.K12.Blind.doorL_at_first
