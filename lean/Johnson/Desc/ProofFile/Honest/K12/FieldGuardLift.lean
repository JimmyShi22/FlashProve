-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FieldGuardLift.lean

THE GUARD's LIFT. Where the field `opened` is some, a chain's rounds behind the guard
(K12/FieldGuard.lean) play as the plain ones do, general in the list of parts. So what is proved of a
plain half at a place carries to that half behind the guard, under the premise that the field is
some. The first caller of `needsField_some`.

  `Step.guarded`       a step with its move, if any, behind the guard
  `tell_guarded`, `hear_guarded`, `play_guarded`   at a field that is some, `play` over guarded steps
                       is `play` over the plain ones: the same rounds played and the same end state
  `guardCoins`         the coins of a list of parts, as coins of the list behind the guard
  `partSteps_guarded`, `rowSteps_guarded`, `placedSteps_guarded`   a half's steps behind the guard
                       are its plain steps, each guarded
  `lendPart_guarded`, `lendRow_guarded`   `lendPart`, `lendRow` behind the guard are the plain ones,
                       the coins carried over
  `chainSteps_guarded`, `chainStop_guarded`   the same at one sub-protocol, stops included
  `playsOn_guarded`, `saysYes_guarded`   `PlaysOn` and `SaysYes` carry from the plain half to the
                       guarded one, under hopen: wherever A holds, the field is some
  `tell_guarded_none`, `play_guarded_none`   at a field that is none and a head step with a move,
                       `play` over guarded steps does not return
  `GuardToy`           one step at which the plain play returns and the guarded errs at none

Limits.
- NOT CLAIMED: that any A meets hopen. That is what the thread's letter has to give; this file gives
  none, and `PlayedTo` keeps the field at none.
- NOT CLAIMED: that `Plays` holds at any guarded half. `Plays` asks a return at the field none
  (`plays_at_none`, Thread/OwesAtNone.lean), and `play_guarded_none` says that this cannot be had
  where the member's first step has a move.
- NOT CLAIMED: anything of `Accepted`, of what the field holds, or of the door at the test on G_omega.
- NOT IN FRONT OF A LAW OVER COINS: `playsOn_guarded`, `saysYes_guarded` bear this label; the rule
  is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: the letter A,
  as a free premise, `PlaysOn` and `SaysYes` as ends. None: the bar is flat.
  The guard tests that the field is there; nothing here reads what it holds.
- `chainSteps_guarded` and its callers are at a list of one sub-protocol.
- Nothing on completeness, on soundness or on what is
  hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.FieldGuard
import Johnson.Desc.ProofFile.Honest.Law.ThreadC
import Johnson.Desc.ProofFile.Honest.Rule
import Johnson.Desc.ProofFile.Honest.WalkOpened

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn Oracle)

variable {S Cl V W X Pb : Type}

/-! ## 1 Play -/

/-- **A step with its move, if any, behind the guard.** -/
def Step.guarded (s : Step W X) : Step W X := { s with move := s.move.map Move.needsField }

/-- At a field that is some, a guarded step tells what the step tells. -/
theorem tell_guarded (s : Step W X) (back : Option Fmt.RoundView) (m : Mid W X) (cs : List OpenedColumn)
    (h : m.opened = some cs) : s.guarded.tell back m = s.tell back m := by
  rcases s with ⟨name, addr, decl, oracles, bad, hid, nth, last, move⟩
  cases move with
  | none => rfl
  | some mv =>
    have e : mv.needsField.say () m.shown m.st = mv.say () m.shown m.st :=
      needsField_some mv () m.shown m.st cs h
    simp only [Step.guarded, Option.map_some, Step.tell, Step.stop, e]

/-- A guarded step hears as the step does. -/
theorem hear_guarded (s : Step W X) (x : Told) (d : Fmt.Drawn) (m : Mid W X) :
    s.guarded.hear x d m = s.hear x d m := by
  rcases s with ⟨name, addr, decl, oracles, bad, hid, nth, last, move⟩
  cases move <;> rfl

/-- **At a field that is some, `play` over guarded steps is `play` over the steps.** -/
theorem play_guarded : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (m : Mid W X) (cs : List OpenedColumn), m.opened = some cs →
    play (ss.map Step.guarded) ds back m = play ss ds back m
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _ => by simp [play]
  | s :: ss, [], _, _, _, _ => by
    rw [List.map_cons]
    simp [play]
  | s :: ss, d :: ds, back, m, cs, h => by
    rw [List.map_cons, play, play, tell_guarded s _ m cs h]
    cases ht : s.tell back.head? m with
    | error e => rfl
    | ok x =>
      show (s.guarded.hear x d m).bind _ = (s.hear x d m).bind _
      rw [hear_guarded]
      cases hh : s.hear x d m with
      | error e => rfl
      | ok m' =>
        show Except.map _ (play (ss.map Step.guarded) ds back.tail m') =
          Except.map _ (play ss ds back.tail m')
        rw [play_guarded ss ds back.tail m' cs ((hear_opened hh).trans h)] <;> rfl

/-- At a field that is none, a guarded step with a move does not tell. -/
theorem tell_guarded_none (s : Step W X) (mv : Move Unit W X) (hm : s.move = some mv)
    (back : Option Fmt.RoundView) (m : Mid W X) (hn : m.opened = none) (x : Told) :
    s.guarded.tell back m ≠ .ok x := by
  intro h
  have e : mv.needsField.say () m.shown m.st = .error fieldWord :=
    needsField_none mv () m.shown m.st hn
  have hg : s.guarded.move = some mv.needsField := by
    show s.move.map Move.needsField = _
    rw [hm]
    rfl
  unfold Step.tell at h
  rw [hg] at h
  cases hstop : s.guarded.stop m.loc s.guarded.nth with
  | some r => simp only [hstop] at h <;> cases h
  | none => simp only [hstop, e] at h <;> cases h

/-- **At a field that is none and a head step with a move, `play` over guarded steps does not
return.** -/
theorem play_guarded_none (s : Step W X) (mv : Move Unit W X) (hm : s.move = some mv)
    (ss : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (m : Mid W X)
    (y : List Played × Mid W X) :
    play ((s :: ss).map Step.guarded) ds back { m with opened := none } ≠ .ok y := by
  intro h
  rw [List.map_cons] at h
  cases ds with
  | nil => simp [play] at h
  | cons d ds =>
    rw [play] at h
    obtain ⟨x, hx, -⟩ := of_bind_ok h
    exact tell_guarded_none s mv hm _ _ rfl x hx

/-! ## 2 A half's steps -/

/-- Mapping the second list of a zip, in a list with its numbers. -/
theorem map_zipIdx_zip_map {A B B' C : Type} (f : B → B') (F : (A × B') × Nat → C)
    (G : (A × B) × Nat → C) (hFG : ∀ a b n, F ((a, f b), n) = G ((a, b), n)) :
    ∀ (rs : List A) (ms : List B) (k : Nat),
      ((rs.zip (ms.map f)).zipIdx k).map F = ((rs.zip ms).zipIdx k).map G
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | r :: rs, m :: ms, k => by
    have ih := map_zipIdx_zip_map f F G hFG rs ms (k + 1)
    show F ((r, f m), k) :: ((rs.zip (ms.map f)).zipIdx (k + 1)).map F =
      G ((r, m), k) :: ((rs.zip ms).zipIdx (k + 1)).map G
    rw [hFG, ih]

/-- A part's steps behind the guard are its steps, each guarded. -/
theorem partSteps_guarded (p : Part V W X) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins) :
    p.needsField.steps name a rs v c = (p.steps name a rs v c).map Step.guarded := by
  have hl := needsField_length p
  unfold Part.steps
  rw [hl, List.map_map]
  refine map_zipIdx_zip_map Move.needsField _ _ ?_ rs p.moves 0
  intro r mv n
  rfl

/-- **The coins of a list of parts, as coins of the list behind the guard.** -/
def guardCoins : (ps : List (Part V W X)) → RowCoins ps → RowCoins (ps.map Part.needsField)
  | [], _ => ()
  | _ :: ps, c => (c.1, guardCoins ps c.2)

/-- A list's steps behind the guard are its steps, each guarded. -/
theorem rowSteps_guarded (name : String) (a : Place) (v : Option V) :
    ∀ (ps : List (Part V W X)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
      (c : RowCoins ps),
      rowSteps name a v (ps.map Part.needsField) j rs (guardCoins ps c) =
        (rowSteps name a v ps j rs c).map Step.guarded
  | [], _, _, _ => rfl
  | p :: ps, j, rs, c => by
    have e : rowSteps name a v ((p :: ps).map Part.needsField) j rs (guardCoins (p :: ps) c) =
        p.needsField.steps name ⟨a, j⟩ (rs.take p.needsField.moves.length) v c.1 ++
          rowSteps name a v (ps.map Part.needsField) (j + 1)
            (rs.drop p.needsField.moves.length) (guardCoins ps c.2) := rfl
    have e' : rowSteps name a v (p :: ps) j rs c =
        p.steps name ⟨a, j⟩ (rs.take p.moves.length) v c.1 ++
          rowSteps name a v ps (j + 1) (rs.drop p.moves.length) c.2 := rfl
    rw [e, e', needsField_length, List.map_append, partSteps_guarded,
      rowSteps_guarded name a v ps]

/-- A half's steps behind the guard are its steps, each guarded. -/
theorem placedSteps_guarded (h : Placed V W X) (b : Block S Cl) (v : Option V)
    (c : RowCoins h.parts) :
    h.needsField.steps b v (guardCoins h.parts c) = (h.steps b v c).map Step.guarded :=
  rowSteps_guarded b.name b.place v h.parts 0 (b.rounds.zip b.oracles) c

/-! ## 3 The book -/

/-- `lendPart` reads no move: behind the guard it is the plain one. -/
theorem lendPart_guarded (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (a : Addr) (p : Part V W X) :
    lendPart B rows look a p.needsField =
      (lendPart B rows look a p : Except String p.needsField.Coins) := by
  cases p with
  | mk t s c b h o1 o2 m =>
    dsimp only [Part.needsField, lendPart]
    by_cases hd : (t != dueAt rows a) = true
    · simp only [if_pos hd] <;> rfl
    · simp only [if_neg hd]
      cases (look a).2.cut ⟨0, 0⟩ t <;> rfl

/-- **`lendRow` behind the guard is the plain one, the coins carried over.** -/
theorem lendRow_guarded (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (a : Place) : ∀ (ps : List (Part V W X)) (j : Nat),
    lendRow B rows look a (ps.map Part.needsField) j =
      (lendRow B rows look a ps j).map (guardCoins ps)
  | [], _ => rfl
  | p :: ps, j => by
    have e : lendRow B rows look a ((p :: ps).map Part.needsField) j =
        ((lendPart B rows look ⟨a, j⟩ p.needsField).mapError
          fun e => "part " ++ toString j ++ ": " ++ e).bind
          fun c => (lendRow B rows look a (ps.map Part.needsField) (j + 1)).map
            fun r => ((c, r) : RowCoins (p.needsField :: ps.map Part.needsField)) := rfl
    have e' : lendRow B rows look a (p :: ps) j =
        ((lendPart B rows look ⟨a, j⟩ p).mapError
          fun e => "part " ++ toString j ++ ": " ++ e).bind
          fun c => (lendRow B rows look a ps (j + 1)).map
            fun r => ((c, r) : RowCoins (p :: ps)) := rfl
    rw [e, e', lendPart_guarded, lendRow_guarded B rows look a ps (j + 1)]
    cases lendPart B rows look ⟨a, j⟩ p with
    | error _ => rfl
    | ok c =>
      cases lendRow B rows look a ps (j + 1) with
      | error _ => rfl
      | ok r => rfl

/-- The same at a half's parts. -/
theorem lendRow_placed (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (a : Place) (h : Placed V W X) (j : Nat) :
    lendRow B rows look a h.needsField.parts j =
      (lendRow B rows look a h.parts j).map (guardCoins h.parts) :=
  lendRow_guarded B rows look a h.parts j

theorem needsField_rounds (h : Placed V W X) : h.needsField.rounds = h.rounds := by
  have e : ∀ (ps : List (Part V W X)) (n : Nat),
      (ps.map Part.needsField).foldl (fun n p => n + p.moves.length) n =
        ps.foldl (fun n p => n + p.moves.length) n := by
    intro ps
    induction ps with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro n
      show (ps.map Part.needsField).foldl _ (n + p.needsField.moves.length) =
        ps.foldl _ (n + p.moves.length)
      rw [needsField_length, ih]
  exact e h.parts 0

theorem needsField_cut (h : Placed V W X) :
    h.needsField.parts.map (·.moves.length) = h.parts.map (·.moves.length) := by
  show (h.parts.map Part.needsField).map _ = _
  rw [List.map_map]
  exact List.map_congr_left fun p _ => needsField_length p

theorem needsField_parts_length (h : Placed V W X) :
    h.needsField.parts.length = h.parts.length := List.length_map _

/-! ## 4 One sub-protocol -/

/-- **`chainSteps` behind the guard, at one sub-protocol.** hs has at b's place the half h behind the
guard, hs' the half h. Every error of the one is the other's; where both return, the steps of the
one are those of the other, each guarded. -/
theorem chainSteps_guarded (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (b : Block S Cl) (hs hs' : List (Placed V W X)) (h : Placed V W X)
    (hf : (hs.find? fun g => g.place == b.place) = some h.needsField)
    (hf' : (hs'.find? fun g => g.place == b.place) = some h) :
    chainSteps B rows look v [b] hs =
      (chainSteps B rows look v [b] hs').map (·.map Step.guarded) := by
  simp only [chainSteps, hf, hf', needsField_rounds, needsField_cut, needsField_parts_length]
  by_cases c1 : (b.oracles.length != b.rounds.length) = true
  · simp only [if_pos c1] <;> rfl
  by_cases c2 : (h.rounds != b.rounds.length) = true
  · simp only [if_neg c1, if_pos c2] <;> rfl
  by_cases c3 : (B.cuts.lookup b.place != some (h.parts.map (·.moves.length))) = true
  · simp only [if_neg c1, if_neg c2, if_pos c3] <;> rfl
  by_cases c4 : (rows.any fun r =>
      r.1.place == b.place && decide (h.parts.length ≤ r.1.part)) = true
  · simp only [if_neg c1, if_neg c2, if_neg c3, if_pos c4] <;> rfl
  by_cases c5 : (B.ahead.any fun e =>
      e.spender.place == b.place && decide (h.parts.length ≤ e.spender.part)) = true
  · simp only [if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_pos c5] <;> rfl
  simp only [if_neg c1, if_neg c2, if_neg c3, if_neg c4, if_neg c5, lendRow_placed]
  cases hl : lendRow B rows look b.place h.parts 0 with
  | error e => rfl
  | ok c =>
    show Except.ok (h.needsField.steps b v (guardCoins h.parts c) ++ []) =
      Except.ok ((h.steps b v c ++ []).map Step.guarded)
    rw [placedSteps_guarded, List.append_nil, List.append_nil]

theorem partStop_guarded (p : Part V W X) (v : Option V) (loc ds : List Fmt.Drawn) :
    p.needsField.stopAt v loc ds = p.stopAt v loc ds := by
  unfold Part.stopAt
  rw [needsField_length] <;> rfl

theorem rowStop_guarded (v : Option V) : ∀ (ps : List (Part V W X)) (loc ds : List Fmt.Drawn),
    rowStopAt v (ps.map Part.needsField) loc ds = rowStopAt v ps loc ds
  | [], _, _ => rfl
  | p :: ps, loc, ds => by
    show (p.needsField.stopAt v loc (ds.take p.needsField.moves.length)).or
        (rowStopAt v (ps.map Part.needsField) (loc ++ ds.take p.needsField.moves.length)
          (ds.drop p.needsField.moves.length)) =
      (p.stopAt v loc (ds.take p.moves.length)).or
        (rowStopAt v ps (loc ++ ds.take p.moves.length) (ds.drop p.moves.length))
    rw [needsField_length, partStop_guarded, rowStop_guarded v ps]

/-- The stops read nothing of the guard. -/
theorem chainStop_guarded (v : Option V) (b : Block S Cl) (hs hs' : List (Placed V W X))
    (h : Placed V W X) (hf : (hs.find? fun g => g.place == b.place) = some h.needsField)
    (hf' : (hs'.find? fun g => g.place == b.place) = some h) (loc ds : List Fmt.Drawn) :
    chainStopAt v [b] hs loc ds = chainStopAt v [b] hs' loc ds := by
  have e : rowStopAt v h.needsField.parts loc (ds.take b.rounds.length) =
      rowStopAt v h.parts loc (ds.take b.rounds.length) := rowStop_guarded v h.parts _ _
  show ((hs.find? fun g => g.place == b.place).bind
        fun g => rowStopAt v g.parts loc (ds.take b.rounds.length)).or
      (chainStopAt v [] hs (loc ++ ds.take b.rounds.length) (ds.drop b.rounds.length)) =
    ((hs'.find? fun g => g.place == b.place).bind
        fun g => rowStopAt v g.parts loc (ds.take b.rounds.length)).or
      (chainStopAt v [] hs' (loc ++ ds.take b.rounds.length) (ds.drop b.rounds.length))
  rw [hf, hf']
  exact congrArg (fun o => Option.or o none) e

/-- **`PlaysOn` carries from the plain half to the guarded one**, wherever A holds the field being
some (hopen). 
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem playsOn_guarded {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain ft : Nat}
    {hs hs' : List (Placed V W X)} {b : Block S Cl} {A B : Coins Bk → S → Mid W X → Env → Prop}
    (h : Placed V W X) (hf : (hs.find? fun g => g.place == b.place) = some h.needsField)
    (hf' : (hs'.find? fun g => g.place == b.place) = some h)
    (hopen : ∀ k s m E, A k s m E → m.opened.isSome = true)
    (hP : PlaysOn φ Bk chain ft hs' b A B) : PlaysOn φ Bk chain ft hs b A B := by
  intro k s m E ds l hA hd hst hl
  rw [chainSteps_guarded _ _ _ _ b hs hs' h hf hf'] at hl
  obtain ⟨l₀, hl₀, rfl⟩ := map_ok hl
  obtain ⟨cs, hcs⟩ := Option.isSome_iff_exists.1 (hopen k s m E hA)
  obtain ⟨y, cols, h1, h2, h3⟩ := hP k s m E ds l₀ hA hd
    ((chainStop_guarded _ b hs hs' h hf hf' _ _).symm.trans hst) hl₀
  exact ⟨y, cols, (play_guarded l₀ ds [] m cs hcs).trans h1, h2, h3⟩

/-- **`SaysYes` carries from the plain half to the guarded one**, under the same premise. -/
theorem saysYes_guarded {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain ft : Nat}
    {hs hs' : List (Placed V W X)} {b : Block S Cl} {fall : S → List Fmt.Drawn → Option String}
    {A : Coins Bk → S → Mid W X → Env → Prop}
    (h : Placed V W X) (hf : (hs.find? fun g => g.place == b.place) = some h.needsField)
    (hf' : (hs'.find? fun g => g.place == b.place) = some h)
    (hopen : ∀ k s m E, A k s m E → m.opened.isSome = true)
    (hP : SaysYes φ Bk chain ft hs' b fall A) : SaysYes φ Bk chain ft hs b fall A := by
  intro k s m E ds l y cols hA hd hst hfall hl hpl hcols
  rw [chainSteps_guarded _ _ _ _ b hs hs' h hf hf'] at hl
  obtain ⟨l₀, hl₀, rfl⟩ := map_ok hl
  obtain ⟨cs, hcs⟩ := Option.isSome_iff_exists.1 (hopen k s m E hA)
  exact hP k s m E ds l₀ y cols hA hd
    ((chainStop_guarded _ b hs hs' h hf hf' _ _).symm.trans hst) hfall hl₀
    ((play_guarded l₀ ds [] m cs hcs).symm.trans hpl) hcols

/-! ## 5 The premise cannot be dropped: one step -/

namespace GuardToy

/-- One step that says an empty message. -/
def toyStep : Step Unit Unit :=
  ⟨"toy", ⟨⟨1, none, 1, .K12⟩, 0⟩, ⟨{ name := "toy" }, [], []⟩, [], fun _ _ => none,
    fun _ _ => none, 0, false, some ⟨fun _ _ _ => .ok ⟨[], []⟩, fun _ => ()⟩⟩

/-- A challenge with nothing in it. -/
def toyDrawn : Fmt.Drawn := ⟨[], [], [], none⟩

/-- The start, at a field. -/
def toyMid (f : Option (List OpenedColumn)) : Mid Unit Unit := ⟨⟨(), [], ()⟩, [], [], f⟩

/-- It returned. -/
def okB {α β : Type} : Except α β → Bool
  | .ok _ => true
  | .error _ => false

/-- At none the plain step returns. -/
theorem toy_plain : okB (play [toyStep] [toyDrawn] [] (toyMid none)) = true := by decide +kernel

/-- At none the guarded step does not. -/
theorem toy_guarded_none :
    okB (play ([toyStep].map Step.guarded) [toyDrawn] [] (toyMid none)) = false := by
  decide +kernel

/-- At some the guarded step returns. -/
theorem toy_guarded_some :
    okB (play ([toyStep].map Step.guarded) [toyDrawn] [] (toyMid (some []))) = true := by
  decide +kernel

end GuardToy

end ProofFile.Honest

#print axioms ProofFile.Honest.Step.guarded
#print axioms ProofFile.Honest.tell_guarded
#print axioms ProofFile.Honest.hear_guarded
#print axioms ProofFile.Honest.play_guarded
#print axioms ProofFile.Honest.tell_guarded_none
#print axioms ProofFile.Honest.play_guarded_none
#print axioms ProofFile.Honest.map_zipIdx_zip_map
#print axioms ProofFile.Honest.partSteps_guarded
#print axioms ProofFile.Honest.guardCoins
#print axioms ProofFile.Honest.rowSteps_guarded
#print axioms ProofFile.Honest.placedSteps_guarded
#print axioms ProofFile.Honest.lendPart_guarded
#print axioms ProofFile.Honest.lendRow_guarded
#print axioms ProofFile.Honest.lendRow_placed
#print axioms ProofFile.Honest.needsField_rounds
#print axioms ProofFile.Honest.needsField_cut
#print axioms ProofFile.Honest.needsField_parts_length
#print axioms ProofFile.Honest.chainSteps_guarded
#print axioms ProofFile.Honest.partStop_guarded
#print axioms ProofFile.Honest.rowStop_guarded
#print axioms ProofFile.Honest.chainStop_guarded
#print axioms ProofFile.Honest.playsOn_guarded
#print axioms ProofFile.Honest.saysYes_guarded
#print axioms ProofFile.Honest.GuardToy.toyStep
#print axioms ProofFile.Honest.GuardToy.toyDrawn
#print axioms ProofFile.Honest.GuardToy.toyMid
#print axioms ProofFile.Honest.GuardToy.okB
#print axioms ProofFile.Honest.GuardToy.toy_plain
#print axioms ProofFile.Honest.GuardToy.toy_guarded_none
#print axioms ProofFile.Honest.GuardToy.toy_guarded_some
