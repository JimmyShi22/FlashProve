-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Keep/Bridge.lean: from the parts of a row that passes its
tables on (Honest/K3/RowKeep.lean) to the parts of a row that passes nothing on
(Honest/K3/Row.lean): each sort of part, played alone, shows the rounds of its counterpart there.
The theorems on `keepPart` are conditional on `KeepJob.FaithfulOn`. One definition that the
statements need, and theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: a part played alone is `alone`
(Honest/SumLaw/Terms.lean); the state behind moves is `endFrom` (Honest/K3/Law/PlayPart.lean);
`PairSame` is the list of hypotheses on a pair of parts in Honest/K3/Law/Keep/RowTwin.lean.

What is defined.
  `pullJob get B`: a job for the masked sumcheck that is typed at Y, as a job at X: each of its
    functions is given what is passed on through get. It is no part of a prover: `jobOfAt` is such a
    job by `rfl`, and the theorems are stated once, at `pullJob`.

What is shown.
  1 `endFrom_eq_stateFrom`: `endFrom` is `stateFrom` (Honest/SumLaw/Plays.lean), at all lists.
  2 `alone_quietLay`, `alone_quietLay_quiet`, `alone_quietAt`, `endFrom_quietLay`,
    `endFrom_quietAt`, `pairSame_quietLay`: whatever g lays, the one round of `quietLay g` is that
    of `quiet`; behind it the state holds what g lays.
  3 `jobOfAt_pull`, `sumGs_pull`, `aloneFrom_pull`, `alone_pull`, `alone_jobOfAt`: `sumPart` at
    `pullJob get B` shows the rounds of `sumPart` at B, at the state read through get.
  4 `sumPart_length`, `withPass_length`, `keepPart_length`, `endFrom_sumPart`, `endFrom_keepPart`,
    `scalarsOf_pos`, `keepPart_ne_nil`: the numbers of moves; `sumPart` leaves what is passed on as
    it is; `keepPart` does so from a state without a kept state.
  5 `aloneFrom_cons`, `aloneFrom_one`, `aloneFrom_tail`, `aloneFrom_lastHand`, `alone_lastHand`,
    `lastHandMoves_length`, `lastHand_length`, `endFrom_lastHandMoves`, `endFrom_lastHand`,
    `endFrom_lastHand_const`, `PairSame.lastHand`: `Part.lastHand` turns no round; behind the part
    the state holds what g lays.
  6 `keep_pull`, `keep_same`, `pairSame_keep`, `pairSame_keepAt`: **`keepPart` at a job whose
    earlier job is `pullJob get B` shows the rounds of `sumPart` at B.** Conditional on
    `KeepJob.FaithfulOn J Ok` and on Ok at the state in front.

Hypotheses that remain.
  `hJ : J.FaithfulOn Ok` and `hOk : Ok w h x` in 6: for whoever supplies the job and the row to
    show.
  `hb`: (in 6) the job's earlier job is `pullJob get B`, or `jobOfAt`.
  `h1`, `h2` in 6: the two parts' coins are read alike. No coin is moved from one type to the other,
    and nothing here says that for coins of the one part there are such coins of the other: a
    relation that is general in the parts, and that it has members, is shown in
    Honest/K3/Law/Keep/RowKeepLaw.lean (`SpentSame`, `spentSame_total`).
  In the makers of `PairSame`: that the invariant is carried on is a hypothesis of each (`hg`; `hI`,
    `hI'`); `hRel`: coins in the relation are read alike; `H`: (in `PairSame.lastHand`) `PairSame`
    of the part.
  `hl`, `hne`: as many challenges as moves; the part has a move. `hs`, `h`: (in `aloneFrom_one`,
    `aloneFrom_tail`) two moves say the same; two lists of moves, played alone, yield the same, at
    every state, at all that can be shown (every value of the columns opened too) and at all
    challenges.

Imported: Honest/SumKeepLaw.lean, Honest/SumKeep.lean, Honest/SumLaw/Said.lean and
Honest/SumLaw/Plays.lean (for `stateFrom`).

Users. Honest/K3/Law/Keep/RowKeepLaw.lean, Honest/K3/Law/Keep/LiftLens.lean,
Honest/K3/Law/Keep/LotInstKeepLaw.lean [not in this library] and Honest/K3/Law/Keep/RowTwinToy.lean
[not in this library] import this file.

Limits. `keep_pull` and what follows from it start at a state without a kept state, as
`alone_keep_on` does. g in `Part.lastHand` stands in the stead of the last move's own second half,
which is not called; g is given what the move in front of the last passed on. Nothing is said on
stops or on the shapes of messages, nor on how long a move takes.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.SumKeepLaw
import Johnson.Desc.ProofFile.Honest.K3.JobsKeepKey
import Johnson.Desc.ProofFile.Honest.K3.RowKeepParts
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.RowTwin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE)
open VerifiableInference.Desc.Part.MaskedSum (Call)
open ProofFile.Honest.SumLaw (alone aloneFrom stateFrom SumCoins sumGs mvOf rvSaid askG saidFirst saidVar
  saidY saidEnds sumPart_moves stateFrom_mvOf)

variable {V W X Y K C : Type}

/-! ## 1 The two names of the state behind moves -/

/-- `endFrom` is `stateFrom` (Honest/SumLaw/Plays.lean): at all lists. -/
theorem endFrom_eq_stateFrom : ∀ (ms : List (Move C W X)) (t : State W X) (ds : List Fmt.Drawn),
    endFrom ms t ds = stateFrom ms t ds
  | [], _, _ => rfl
  | _ :: _, _, [] => rfl
  | mv :: ms, t, d :: ds =>
    endFrom_eq_stateFrom ms { t.hears d with own := mv.hand (t.hears d) } ds

/-! ## 2 A part that sends nothing -/

/-- Whatever g lays: one round, in which nothing is shown. -/
theorem alone_quietLay (g : State W X → X) (c : (quietLay (V := V) g).Coins) (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn) :
    alone (quietLay g) c t seen ds = (match ds with
      | [d] => some [⟨[], d⟩]
      | _ => none) := by
  cases ds with
  | nil => rfl
  | cons d ds => cases ds <;> rfl

/-- Whatever g lays, the round is that of `quiet`: at all coins and states. -/
theorem alone_quietLay_quiet (g : State W X → X) (c : (quietLay (V := V) g).Coins)
    (c' : (quiet : Part V W Unit).Coins) (t : State W X) (u : State W Unit) (seen : Seen)
    (ds : List Fmt.Drawn) : alone (quietLay g) c t seen ds = alone quiet c' u seen ds := by
  cases ds with
  | nil => rfl
  | cons d ds => cases ds <;> rfl

/-- The case in which what was passed on stays. -/
theorem alone_quietAt (c : (quietAt : Part V W X).Coins) (w : W) (h : List Fmt.Drawn) (x : X)
    (seen : Seen) (ds : List Fmt.Drawn) :
    alone (quietAt : Part V W X) c ⟨w, h, x⟩ seen ds =
      alone (quiet : Part V W Unit) c ⟨w, h, ()⟩ seen ds :=
  alone_quietLay_quiet _ c c _ _ seen ds

/-- Behind the one move the state holds what g lays. g is given the state that has heard the round's
challenge. -/
theorem endFrom_quietLay (g : State W X → X) (t : State W X) (d : Fmt.Drawn) :
    endFrom (quietLay (V := V) g).moves t [d] =
      ⟨t.input, t.heard ++ [d], g ⟨t.input, t.heard ++ [d], t.own⟩⟩ := rfl

/-- What was passed on stays. -/
theorem endFrom_quietAt (t : State W X) (d : Fmt.Drawn) :
    endFrom (quietAt : Part V W X).moves t [d] = ⟨t.input, t.heard ++ [d], t.own⟩ := rfl

/-- **`PairSame` of `quietLay g` and `quiet`**, at every relation on coins. The hypothesis: what g
lays satisfies the invariant behind the pair. -/
theorem pairSame_quietLay (w : W) (I I' : List Fmt.Drawn → X → Prop) (g : State W X → X)
    (Rel : (quietLay (V := V) g).Coins → (quiet : Part V W Unit).Coins → Prop)
    (hg : ∀ (h : List Fmt.Drawn) (x : X) (d : Fmt.Drawn), I h x →
      I' (h ++ [d]) (g ⟨w, h ++ [d], x⟩)) :
    PairSame w I I' (quietLay (V := V) g) quiet Rel where
  len := rfl
  rounds := fun c c' _ _ seen ds _ _ => alone_quietLay_quiet g c c' _ _ seen ds
  stays := fun h x ds hI hl => by
    have hl' : ds.length = 1 := hl
    cases ds with
    | nil => simp only [List.length_nil] at hl'; omega
    | cons d ds =>
      cases ds with
      | nil => exact hg h x d hI
      | cons d' ds => simp only [List.length_cons] at hl'; omega

/-! ## 3 A job that is read through get -/

/-- A job that is typed at Y, as a job at X: each function is given what is passed on through get.
-/
def pullJob (get : X → Y) (B : SumJob W Y) : SumJob W X :=
  { shape := B.shape
    points := fun w f => B.points w ⟨f.heard, get f.own, f.seen⟩
    lead := fun w f => B.lead w ⟨f.heard, get f.own, f.seen⟩
    round := fun w f rs => B.round w ⟨f.heard, get f.own, f.seen⟩ rs
    inY := fun w f rs m => B.inY w ⟨f.heard, get f.own, f.seen⟩ rs m
    ends := fun w f rs => B.ends w ⟨f.heard, get f.own, f.seen⟩ rs }

/-- `jobOfAt` is `jobOf`, read through the one function to `Unit`. -/
theorem jobOfAt_pull (R : Reads) (J : LookJobs W) (a : At) (s : Stage) (k : Call) :
    jobOfAt (X := X) R J a s k = pullJob (fun _ => ()) (jobOf R J a s k) := rfl

/-- What the moves of `sumPart` at `pullJob get B` say: what those at B say at the narrowed state. -/
theorem sumGs_pull (n e : String) (get : X → Y) (B : SumJob W Y) :
    sumGs n e (pullJob get B) =
      (sumGs n e B).map fun g c s (t : State W X) => g c s (t.narrow id get) := by
  show [askG n e (pullJob get B) (saidFirst (pullJob get B)) 0] ++
      ((List.range B.shape.vs.length).map fun i =>
        askG n e (pullJob get B) (saidVar (pullJob get B) i) (i + 1)) ++
      ((B.shape.ends.map fun en =>
        [askG n e (pullJob get B) (saidY (pullJob get B) en) (B.shape.vs.length + 1),
          askG n e (pullJob get B) (saidEnds (pullJob get B) en) (B.shape.vs.length + 2)]).getD
        []) =
    ([askG n e B (saidFirst B) 0] ++
      ((List.range B.shape.vs.length).map fun i => askG n e B (saidVar B i) (i + 1)) ++
      ((B.shape.ends.map fun en =>
        [askG n e B (saidY B en) (B.shape.vs.length + 1),
          askG n e B (saidEnds B en) (B.shape.vs.length + 2)]).getD [])).map
      fun g c s (t : State W X) => g c s (t.narrow id get)
  rw [List.map_append, List.map_append, List.map_map]
  cases B.shape.ends with
  | none => rfl
  | some en => rfl

/-- Moves that say scalars, each read at the narrowed state, played alone. -/
theorem aloneFrom_pull (get : X → Y) (c : C) :
    ∀ (gs : List (C → Seen → State W Y → List E)) (t : State W X) (seen : Seen)
      (ds : List Fmt.Drawn),
      aloneFrom c ((gs.map fun g c s (t : State W X) => g c s (t.narrow id get)).map mvOf) t seen
          ds =
        aloneFrom c (gs.map mvOf) (t.narrow id get) seen ds
  | [], _, _, [] => rfl
  | [], _, _, _ :: _ => rfl
  | _ :: _, _, _, [] => rfl
  | g :: gs, t, seen, d :: ds => by
    show (aloneFrom c ((gs.map fun g c s (t : State W X) => g c s (t.narrow id get)).map mvOf)
        (t.hears d) (seen.plus [rvSaid (g c seen (t.narrow id get)) d]) ds).map
          (rvSaid (g c seen (t.narrow id get)) d :: ·) =
      (aloneFrom c (gs.map mvOf) ((t.hears d).narrow id get)
        (seen.plus [rvSaid (g c seen (t.narrow id get)) d]) ds).map
          (rvSaid (g c seen (t.narrow id get)) d :: ·)
    rw [aloneFrom_pull get c gs (t.hears d)]

/-- **`sumPart` at `pullJob get B` shows the rounds of `sumPart` at B**, at the state read through
get. -/
theorem alone_pull (n e : String) (get : X → Y) (B : SumJob W Y) (c : SumCoins n e B) (w : W)
    (h : List Fmt.Drawn) (x : X) (seen : Seen) (ds : List Fmt.Drawn) :
    alone (sumPart (V := V) n e (pullJob get B)) c ⟨w, h, x⟩ seen ds =
      alone (sumPart (V := V) n e B) c ⟨w, h, get x⟩ seen ds := by
  show aloneFrom (C := SumCoins n e B) c (sumPart (V := V) n e (pullJob get B)).moves ⟨w, h, x⟩ seen
      ds =
    aloneFrom (C := SumCoins n e B) c (sumPart (V := V) n e B).moves ⟨w, h, get x⟩ seen ds
  rw [sumPart_moves, sumPart_moves, sumGs_pull]
  exact aloneFrom_pull get c (sumGs n e B) ⟨w, h, x⟩ seen ds

/-- **`sumPart` at `jobOfAt` shows the rounds of `sumPart` at `jobOf`.** -/
theorem alone_jobOfAt (n e : String) (R : Reads) (J : LookJobs W) (a : At) (s : Stage) (k : Call)
    (c : SumCoins n e (jobOf R J a s k)) (w : W) (h : List Fmt.Drawn) (x : X)
    (seen : Seen) (ds : List Fmt.Drawn) :
    alone (sumPart (V := V) n e (jobOfAt (X := X) R J a s k)) c ⟨w, h, x⟩ seen ds =
      alone (sumPart (V := V) n e (jobOf R J a s k)) c ⟨w, h, ()⟩ seen ds :=
  alone_pull n e (fun _ => ()) (jobOf R J a s k) c w h x seen ds

/-! ## 4 Numbers of moves; what is passed on stays -/

theorem sumPart_length (n e : String) (J : SumJob W X) :
    (sumPart (V := V) n e J).moves.length = (scalarsOf J.shape).length := by
  have hg : ((sumGs n e J).map mvOf).length = (scalarsOf J.shape).length := by
    rw [List.length_map]
    exact Keep.sumGs_rounds n e J
  exact (congrArg List.length (sumPart_moves (V := V) n e J)).trans hg

theorem withPass_length (pass : Nat → State W Y → Y) :
    ∀ (n : Nat) (l : List (Move C W Y)), (withPass pass n l).length = l.length
  | _, [] => rfl
  | n, _ :: l => congrArg (· + 1) (withPass_length pass (n + 1) l)

theorem keepPart_length (n e : String) (J : KeepJob W X K) :
    (keepPart (V := V) n e J).moves.length = (scalarsOf J.base.shape).length := by
  have hg : ((sumGs n e J.job).map mvOf).length = (scalarsOf J.base.shape).length := by
    rw [List.length_map]
    exact Keep.sumGs_rounds n e J.job
  exact (congrArg List.length (Keep.keepPart_moves (V := V) n e J)).trans
    ((withPass_length J.pass 0 _).trans hg)

/-- A call has at least one round. -/
theorem scalarsOf_pos (k : Call) : 0 < (scalarsOf k).length := by
  unfold scalarsOf
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- So `keepPart` has a move. -/
theorem keepPart_ne_nil (n e : String) (J : KeepJob W X K) :
    (keepPart (V := V) n e J).moves ≠ [] := by
  intro h
  have e1 := keepPart_length (V := V) n e J
  rw [h] at e1
  exact absurd e1 (Nat.ne_of_lt (scalarsOf_pos J.base.shape))

/-- The moves of `sumPart` leave what is passed on as it is. -/
theorem endFrom_sumPart (n e : String) (J : SumJob W X) (t : State W X) (ds : List Fmt.Drawn)
    (hl : ds.length = (scalarsOf J.shape).length) :
    endFrom (sumPart (V := V) n e J).moves t ds = ⟨t.input, t.heard ++ ds, t.own⟩ := by
  rw [endFrom_eq_stateFrom, sumPart_moves]
  exact stateFrom_mvOf _ t ds ((Keep.sumGs_rounds n e J).trans hl.symm)

/-- `state_keep` (Honest/SumKeepLaw.lean) over `endFrom`. -/
theorem endFrom_keepPart (n e : String) (J : KeepJob W X K) (w : W) (h : List Fmt.Drawn) (x : X)
    (ds : List Fmt.Drawn) (hl : ds.length = (scalarsOf J.base.shape).length) :
    endFrom (keepPart (V := V) n e J).moves ⟨w, h, (x, none)⟩ ds = ⟨w, h ++ ds, (x, none)⟩ := by
  rw [endFrom_eq_stateFrom]
  exact Keep.state_keep n e J w h x ds hl

/-! ## 5 A part whose last move passes on something else -/

/-- The text of `aloneFrom` at a move and a challenge. -/
theorem aloneFrom_cons (c : C) (mv : Move C W X) (ms : List (Move C W X)) (t : State W X)
    (seen : Seen) (d : Fmt.Drawn) (ds : List Fmt.Drawn) :
    aloneFrom c (mv :: ms) t seen (d :: ds) =
      (match mv.say c seen t with
       | .ok x =>
         (aloneFrom c ms { t.hears d with own := mv.hand (t.hears d) }
           (seen.plus [⟨x.vals.map Said.got, d⟩]) ds).map (⟨x.vals.map Said.got, d⟩ :: ·)
       | .error _ => none) := rfl

/-- One move, played alone: what it passes on is not read. -/
theorem aloneFrom_one (c : C) (mv mv' : Move C W X) (hs : mv.say = mv'.say) (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn) :
    aloneFrom c [mv] t seen ds = aloneFrom c [mv'] t seen ds := by
  cases ds with
  | nil => rfl
  | cons d ds =>
    rw [aloneFrom_cons, aloneFrom_cons, hs]
    cases mv'.say c seen t with
    | error _ => rfl
    | ok y => cases ds <;> rfl

/-- The same move in front of two lists that show the same. -/
theorem aloneFrom_tail (c : C) (mv : Move C W X) (l l' : List (Move C W X))
    (h : ∀ t seen ds, aloneFrom c l t seen ds = aloneFrom c l' t seen ds) (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn) :
    aloneFrom c (mv :: l) t seen ds = aloneFrom c (mv :: l') t seen ds := by
  cases ds with
  | nil => rfl
  | cons d ds =>
    rw [aloneFrom_cons, aloneFrom_cons]
    cases mv.say c seen t with
    | error _ => rfl
    | ok y =>
      show (aloneFrom c l _ _ ds).map _ = (aloneFrom c l' _ _ ds).map _
      rw [h]

theorem aloneFrom_lastHand (g : State W X → X) (c : C) :
    ∀ (ms : List (Move C W X)) (t : State W X) (seen : Seen) (ds : List Fmt.Drawn),
      aloneFrom c (lastHandMoves g ms) t seen ds = aloneFrom c ms t seen ds
  | [], _, _, _ => rfl
  | [mv], t, seen, ds => aloneFrom_one c ⟨mv.say, g⟩ mv rfl t seen ds
  | mv :: mv' :: l, t, seen, ds =>
    aloneFrom_tail c mv _ _ (aloneFrom_lastHand g c (mv' :: l)) t seen ds

/-- **`Part.lastHand` turns no round**: no move reads what the last move passes on. -/
theorem alone_lastHand (p : Part V W X) (g : State W X → X) (c : p.Coins) (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn) :
    alone (p.lastHand g) c t seen ds = alone p c t seen ds :=
  aloneFrom_lastHand g c p.moves t seen ds

theorem lastHandMoves_length (g : State W X → X) :
    ∀ (ms : List (Move C W X)), (lastHandMoves g ms).length = ms.length
  | [] => rfl
  | [_] => rfl
  | _ :: mv' :: l => congrArg (· + 1) (lastHandMoves_length g (mv' :: l))

theorem lastHand_length (p : Part V W X) (g : State W X → X) :
    (p.lastHand g).moves.length = p.moves.length :=
  lastHandMoves_length g p.moves

/-- Behind the moves the state holds what g lays. g is given the state that has heard all
challenges and that holds what the moves in front of the last passed on. -/
theorem endFrom_lastHandMoves (g : State W X → X) :
    ∀ (ms : List (Move C W X)) (t : State W X) (ds : List Fmt.Drawn), ds.length = ms.length →
      ms ≠ [] →
      (endFrom (lastHandMoves g ms) t ds).own =
        g ⟨t.input, t.heard ++ ds, (endFrom ms.dropLast t ds.dropLast).own⟩
  | [], _, _, _, h => absurd rfl h
  | [_], _, [_], _, _ => rfl
  | [_], _, [], h, _ => by simp only [List.length_cons, List.length_nil] at h; omega
  | [_], _, _ :: _ :: _, h, _ => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ :: _ :: _, _, [], h, _ => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ :: _ :: _, _, [_], h, _ => by simp only [List.length_cons, List.length_nil] at h; omega
  | mv :: mv' :: l, t, d :: d' :: ds, h, _ => by
    have ih := endFrom_lastHandMoves g (mv' :: l) { t.hears d with own := mv.hand (t.hears d) }
      (d' :: ds) (by simp only [List.length_cons] at h ⊢; omega) (List.cons_ne_nil _ _)
    show (endFrom (lastHandMoves g (mv' :: l)) { t.hears d with own := mv.hand (t.hears d) }
        (d' :: ds)).own =
      g ⟨t.input, t.heard ++ d :: d' :: ds,
        (endFrom (mv' :: l).dropLast { t.hears d with own := mv.hand (t.hears d) }
          (d' :: ds).dropLast).own⟩
    rw [ih]
    show g ⟨t.input, (t.heard ++ [d]) ++ d' :: ds, _⟩ = _
    rw [List.append_assoc]
    rfl

/-- The same of a part, as one equation. -/
theorem endFrom_lastHand (p : Part V W X) (g : State W X → X) (t : State W X)
    (ds : List Fmt.Drawn) (hl : ds.length = p.moves.length) (hne : p.moves ≠ []) :
    endFrom (p.lastHand g).moves t ds =
      ⟨t.input, t.heard ++ ds,
        g ⟨t.input, t.heard ++ ds, (endFrom p.moves.dropLast t ds.dropLast).own⟩⟩ :=
  (endFrom_eq _ t ds (hl.trans (lastHand_length p g).symm)).trans
    (congrArg (fun z => (⟨t.input, t.heard ++ ds, z⟩ : State W X))
      (endFrom_lastHandMoves g p.moves t ds hl hne))

/-- The case in which g lays one value. -/
theorem endFrom_lastHand_const (p : Part V W X) (y : X) (t : State W X) (ds : List Fmt.Drawn)
    (hl : ds.length = p.moves.length) (hne : p.moves ≠ []) :
    endFrom (p.lastHand fun _ => y).moves t ds = ⟨t.input, t.heard ++ ds, y⟩ :=
  endFrom_lastHand p (fun _ => y) t ds hl hne

/-- **`PairSame` of `p.lastHand g`, of `PairSame` of p.** The hypothesis: whatever the moves in
front of the last passed on, what g lays satisfies the invariant behind the pair. Of H its `len` and
its `rounds` are used; its invariant behind the pair, I'', and its `stays` are not. -/
theorem PairSame.lastHand {w : W} {I I' I'' : List Fmt.Drawn → X → Prop} {p : Part V W X}
    {q : Part V W Unit} {Rel : p.Coins → q.Coins → Prop} (H : PairSame w I I'' p q Rel)
    (g : State W X → X) (hne : p.moves ≠ [])
    (hg : ∀ (h : List Fmt.Drawn) (x z : X) (ds : List Fmt.Drawn), I h x →
      ds.length = p.moves.length → I' (h ++ ds) (g ⟨w, h ++ ds, z⟩)) :
    PairSame w I I' (p.lastHand g) q Rel where
  len := (lastHand_length p g).trans H.len
  rounds := fun c c' h x seen ds hr hI =>
    (alone_lastHand p g c _ seen ds).trans (H.rounds c c' h x seen ds hr hI)
  stays := fun h x ds hI hl => by
    have hl' : ds.length = p.moves.length := hl.trans (lastHand_length p g)
    rw [endFrom_lastHand p g ⟨w, h, x⟩ ds hl' hne]
    exact hg h x _ ds hI hl'

/-! ## 6 The part with a kept state -/

/-- **`keepPart` at a job whose earlier job is `pullJob get B` shows the rounds of `sumPart` at B.**
Conditional on `KeepJob.FaithfulOn J Ok` and on Ok at the state in front. h1, h2: the two parts'
coins are read alike. -/
theorem keep_pull (n e : String) (J : KeepJob W X K) (B : SumJob W Y) (get : X → Y)
    (hb : J.base = pullJob get B) (Ok : W → List Fmt.Drawn → X → Prop) (hJ : J.FaithfulOn Ok)
    (c : SumCoins n e J.base) (c' : SumCoins n e B) (h1 : coinsE c.2.1.1 = coinsE c'.2.1.1)
    (h2 : endCoins e J.base.shape.ends c.2.1.2 = endCoins e B.shape.ends c'.2.1.2) (w : W)
    (h : List Fmt.Drawn) (x : X) (hOk : Ok w h x) (seen : Seen) (ds : List Fmt.Drawn) :
    alone (keepPart (V := V) n e J) c ⟨w, h, (x, none)⟩ seen ds =
      alone (sumPart (V := V) n e B) c' ⟨w, h, get x⟩ seen ds :=
  (Keep.alone_keep_on n e J Ok hJ c w h x hOk seen ds).trans
    ((sumPart_alone_congr n e n e J.base (pullJob get B) hb c c' h1 h2 ⟨w, h, x⟩ seen ds).trans
      (alone_pull n e get B c' w h x seen ds))

/-- **The same at `jobOfAt` and `jobOf`.** Conditional on `KeepJob.FaithfulOn J Ok` and on Ok at the
state in front. -/
theorem keep_same (n e : String) (J : KeepJob W X K) (R : Reads) (Jf : LookJobs W) (a : At)
    (s : Stage) (k : Call) (hb : J.base = jobOfAt R Jf a s k)
    (Ok : W → List Fmt.Drawn → X → Prop) (hJ : J.FaithfulOn Ok) (c : SumCoins n e J.base)
    (c' : SumCoins n e (jobOf R Jf a s k)) (h1 : coinsE c.2.1.1 = coinsE c'.2.1.1)
    (h2 : endCoins e J.base.shape.ends c.2.1.2 = endCoins e k.ends c'.2.1.2) (w : W)
    (h : List Fmt.Drawn) (x : X) (hOk : Ok w h x) (seen : Seen) (ds : List Fmt.Drawn) :
    alone (keepPart (V := V) n e J) c ⟨w, h, (x, none)⟩ seen ds =
      alone (sumPart (V := V) n e (jobOf R Jf a s k)) c' ⟨w, h, ()⟩ seen ds :=
  keep_pull n e J (jobOf R Jf a s k) (fun _ => ()) hb Ok hJ c c' h1 h2 w h x hOk seen ds

/-- **`PairSame` of `keepPart` and `sumPart`.** Conditional on `KeepJob.FaithfulOn J Ok`. The
hypotheses: coins in the relation are read alike; the invariant in front says that there is no kept
state and that Ok holds; the invariant behind follows as the part's challenges are heard. -/
theorem pairSame_keep (n e : String) (J : KeepJob W X K) (B : SumJob W Unit)
    (hb : J.base = pullJob (fun _ => ()) B) (Ok : W → List Fmt.Drawn → X → Prop)
    (hJ : J.FaithfulOn Ok) (w : W) (I I' : List Fmt.Drawn → X × Option K → Prop)
    (Rel : SumCoins n e J.base → SumCoins n e B → Prop)
    (hRel : ∀ c c', Rel c c' → coinsE c.2.1.1 = coinsE c'.2.1.1 ∧
      endCoins e J.base.shape.ends c.2.1.2 = endCoins e B.shape.ends c'.2.1.2)
    (hI : ∀ h y, I h y → y.2 = none ∧ Ok w h y.1)
    (hI' : ∀ h y (ds : List Fmt.Drawn), I h y → ds.length = (scalarsOf J.base.shape).length →
      I' (h ++ ds) y) :
    PairSame w I I' (keepPart (V := V) n e J) (sumPart (V := V) n e B) Rel where
  len := by
    rw [keepPart_length, sumPart_length, hb]
    rfl
  rounds := fun c c' h y seen ds hr hi => by
    obtain ⟨x, k⟩ := y
    obtain ⟨hk, hok⟩ := hI h (x, k) hi
    have hk' : k = none := hk
    subst hk'
    exact keep_pull n e J B (fun _ => ()) hb Ok hJ c c' (hRel c c' hr).1 (hRel c c' hr).2 w h x hok
      seen ds
  stays := fun h y ds hi hl => by
    obtain ⟨x, k⟩ := y
    have hk' : k = none := (hI h (x, k) hi).1
    subst hk'
    have hl' : ds.length = (scalarsOf J.base.shape).length := hl.trans (keepPart_length n e J)
    rw [endFrom_keepPart n e J w h x ds hl']
    exact hI' h (x, none) ds hi hl'

/-- **The same at `jobOfAt` and `jobOf`.** Conditional on `KeepJob.FaithfulOn J Ok`. -/
theorem pairSame_keepAt (n e : String) (J : KeepJob W X K) (R : Reads) (Jf : LookJobs W) (a : At)
    (s : Stage) (k : Call) (hb : J.base = jobOfAt R Jf a s k)
    (Ok : W → List Fmt.Drawn → X → Prop) (hJ : J.FaithfulOn Ok) (w : W)
    (I I' : List Fmt.Drawn → X × Option K → Prop)
    (Rel : SumCoins n e J.base → SumCoins n e (jobOf R Jf a s k) → Prop)
    (hRel : ∀ c c', Rel c c' → coinsE c.2.1.1 = coinsE c'.2.1.1 ∧
      endCoins e J.base.shape.ends c.2.1.2 = endCoins e k.ends c'.2.1.2)
    (hI : ∀ h y, I h y → y.2 = none ∧ Ok w h y.1)
    (hI' : ∀ h y (ds : List Fmt.Drawn), I h y → ds.length = (scalarsOf J.base.shape).length →
      I' (h ++ ds) y) :
    PairSame w I I' (keepPart (V := V) n e J) (sumPart (V := V) n e (jobOf R Jf a s k)) Rel :=
  pairSame_keep n e J (jobOf R Jf a s k) hb Ok hJ w I I' Rel hRel hI hI'

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.endFrom_eq_stateFrom
#print axioms ProofFile.Honest.K3.Law.alone_quietLay
#print axioms ProofFile.Honest.K3.Law.alone_quietLay_quiet
#print axioms ProofFile.Honest.K3.Law.alone_quietAt
#print axioms ProofFile.Honest.K3.Law.endFrom_quietLay
#print axioms ProofFile.Honest.K3.Law.endFrom_quietAt
#print axioms ProofFile.Honest.K3.Law.pairSame_quietLay
#print axioms ProofFile.Honest.K3.Law.jobOfAt_pull
#print axioms ProofFile.Honest.K3.Law.sumGs_pull
#print axioms ProofFile.Honest.K3.Law.aloneFrom_pull
#print axioms ProofFile.Honest.K3.Law.alone_pull
#print axioms ProofFile.Honest.K3.Law.alone_jobOfAt
#print axioms ProofFile.Honest.K3.Law.sumPart_length
#print axioms ProofFile.Honest.K3.Law.withPass_length
#print axioms ProofFile.Honest.K3.Law.keepPart_length
#print axioms ProofFile.Honest.K3.Law.scalarsOf_pos
#print axioms ProofFile.Honest.K3.Law.keepPart_ne_nil
#print axioms ProofFile.Honest.K3.Law.endFrom_sumPart
#print axioms ProofFile.Honest.K3.Law.endFrom_keepPart
#print axioms ProofFile.Honest.K3.Law.aloneFrom_cons
#print axioms ProofFile.Honest.K3.Law.aloneFrom_one
#print axioms ProofFile.Honest.K3.Law.aloneFrom_tail
#print axioms ProofFile.Honest.K3.Law.aloneFrom_lastHand
#print axioms ProofFile.Honest.K3.Law.alone_lastHand
#print axioms ProofFile.Honest.K3.Law.lastHandMoves_length
#print axioms ProofFile.Honest.K3.Law.lastHand_length
#print axioms ProofFile.Honest.K3.Law.endFrom_lastHandMoves
#print axioms ProofFile.Honest.K3.Law.endFrom_lastHand
#print axioms ProofFile.Honest.K3.Law.endFrom_lastHand_const
#print axioms ProofFile.Honest.K3.Law.PairSame.lastHand
#print axioms ProofFile.Honest.K3.Law.keep_pull
#print axioms ProofFile.Honest.K3.Law.keep_same
#print axioms ProofFile.Honest.K3.Law.pairSame_keep
#print axioms ProofFile.Honest.K3.Law.pairSame_keepAt
