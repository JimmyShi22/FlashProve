-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineTestAsksGuarded.lean: the bridge of E2E/OfflineTestAsks.lean where the test's half stands behind the guard
on the field (`Placed.needsField`, Johnson/Desc/ProofFile/Honest/K12/FieldGuard.lean). General in the job, the
chain, the book, the list of halves, the face and the invariant.

  `behind_first_guarded`     what `InsideOf` (Honest/Law/Inside.lean) gives behind the guarded first part's rounds,
                           wherever the invariant holds the field being some: the row of the two PLAIN parts
                           is lent the same coins; the input and the front cut back are those in front of the
                           test; the challenges heard fit
  `left_of_inside_guarded`   **the bridge behind the guard**

It imports of the guard its definitions alone. The four small laws that it needs on a guarded step, a guarded
part's steps and the lending are proved here under private names, so that this file can be imported beside any
other file that states them.

Limits. Those of E2E/OfflineTestAsks.lean. Nothing on any property.
-/
import E2E.OfflineTestAsks
import Johnson.Desc.ProofFile.Honest.K12.FieldGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Block OpenedColumn)

variable {V W X : Type}

/-- A step with its move, if any, behind the guard. -/
private def guardStep (s : Step W X) : Step W X := { s with move := s.move.map Move.needsField }

private theorem tell_guardStep (s : Step W X) (back : Option Fmt.RoundView) (m : Mid W X) (cs : List OpenedColumn)
    (h : m.opened = some cs) : (guardStep s).tell back m = s.tell back m := by
  rcases s with ⟨name, addr, decl, oracles, bad, hid, nth, last, move⟩
  cases move with
  | none => rfl
  | some mv =>
    have e : mv.needsField.say () m.shown m.st = mv.say () m.shown m.st :=
      needsField_some mv () m.shown m.st cs h
    simp only [guardStep, Option.map_some, Step.tell, Step.stop, e]

private theorem hear_guardStep (s : Step W X) (x : Told) (d : Fmt.Drawn) (m : Mid W X) :
    (guardStep s).hear x d m = s.hear x d m := by
  rcases s with ⟨name, addr, decl, oracles, bad, hid, nth, last, move⟩
  cases move <;> rfl

private theorem play_guardStep : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (m : Mid W X) (cs : List OpenedColumn), m.opened = some cs →
    play (ss.map guardStep) ds back m = play ss ds back m
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _ => by simp [play]
  | s :: ss, [], _, _, _, _ => by
    rw [List.map_cons]
    simp [play]
  | s :: ss, d :: ds, back, m, cs, h => by
    rw [List.map_cons, play, play, tell_guardStep s _ m cs h]
    cases ht : s.tell back.head? m with
    | error e => rfl
    | ok x =>
      show ((guardStep s).hear x d m).bind _ = (s.hear x d m).bind _
      rw [hear_guardStep]
      cases hh : s.hear x d m with
      | error e => rfl
      | ok m' =>
        show Except.map _ (play (ss.map guardStep) ds back.tail m') =
          Except.map _ (play ss ds back.tail m')
        rw [play_guardStep ss ds back.tail m' cs ((hear_opened hh).trans h)] <;> rfl

private theorem map_zip_numbers {A B B' C : Type} (f : B → B') (F : (A × B') × Nat → C)
    (G : (A × B) × Nat → C) (hFG : ∀ a b n, F ((a, f b), n) = G ((a, b), n)) :
    ∀ (rs : List A) (ms : List B) (k : Nat),
      ((rs.zip (ms.map f)).zipIdx k).map F = ((rs.zip ms).zipIdx k).map G
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | r :: rs, m :: ms, k => by
    have ih := map_zip_numbers f F G hFG rs ms (k + 1)
    show F ((r, f m), k) :: ((rs.zip (ms.map f)).zipIdx (k + 1)).map F =
      G ((r, m), k) :: ((rs.zip ms).zipIdx (k + 1)).map G
    rw [hFG, ih]

private theorem steps_guardStep (p : Part V W X) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle)) (v : Option V) (c : p.Coins) :
    p.needsField.steps name a rs v c = (p.steps name a rs v c).map guardStep := by
  have hl := needsField_length p
  unfold Part.steps
  rw [hl, List.map_map]
  refine map_zip_numbers Move.needsField _ _ ?_ rs p.moves 0
  intro r mv n
  rfl

private theorem lendPart_behind (B : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (a : Addr) (p : Part V W X) :
    lendPart B rows look a p.needsField =
      (lendPart B rows look a p : Except String p.needsField.Coins) := by
  cases p with
  | mk t s c b h o1 o2 m =>
    dsimp only [Part.needsField, lendPart]
    by_cases hd : (t != dueAt rows a) = true
    · simp only [if_pos hd]
    · simp only [if_neg hd]
      cases (look a).2.cut ⟨0, 0⟩ t <;> rfl

private theorem lendRow_behind (B : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (a : VerifiableInference.Desc.Place) (p q : Part V W X) :
    lendRow B rows look a [p.needsField, q.needsField] 0 =
      (lendRow B rows look a [p, q] 0 : Except String (RowCoins [p.needsField, q.needsField])) := by
  simp only [lendRow]
  rw [lendPart_behind, lendPart_behind]
  rfl

/-- **Behind the guarded first part's rounds.** hopen: wherever A holds the field is some. -/
theorem behind_first_guarded {S Cl Pb : Type} {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain : ℕ}
    {hs : List (Placed V W X)} {b : Block S Cl} (J : TestJob W X) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (P : FirstPartPublic J s next rest)
    (hlaid : b.rounds.zip b.oracles = J.laid) (hor : b.oracles.length = b.rounds.length)
    (hhalf : (hs.find? fun g => g.place == b.place) = some (proverSideOfProximityTest J).needsField)
    {A : Coins Bk → S → Mid W X → Env → Prop}
    (hopen : ∀ k s m E, A k s m E → m.opened.isSome = true) {k : Coins Bk} {m : Mid W X} {E : Env}
    (hin : InsideOf φ Bk chain hs b A (firstLen J.p.nums.stages) k m E) :
    ∃ st m₀ E₀, ∃ c : RowCoins [(firstPart J : Part V W X), restPart J], A k st m₀ E₀ ∧
      lendRow Bk (Bk.rowsOf chain) (k.look chain) b.place
        [(firstPart J : Part V W X), restPart J] 0 = .ok c ∧
      m.st.input = m₀.st.input ∧ restFront J m = frontOf m₀ ∧
      drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
        (m.st.lately (firstLen J.p.nums.stages)) = true := by
  obtain ⟨st, m₀, E₀, l, ds, y, hA, hl, hd, hy, rfl, -⟩ := hin
  obtain ⟨c, hc, rfl⟩ := steps_one_half hhalf hl
  obtain ⟨cs, hcs⟩ := Option.isSome_iff_exists.1 (hopen k st m₀ E₀ hA)
  have hc' : lendRow Bk (Bk.rowsOf chain) (k.look chain) b.place
      [(firstPart J : Part V W X).needsField, (restPart J : Part V W X).needsField] 0 = .ok c := hc
  rw [lendRow_behind] at hc'
  have l1 : (firstPart J : Part V W X).moves.length = firstLen J.p.nums.stages :=
    Light.first_moves_len J
  have hrs : (J.laid.take (firstLen J.p.nums.stages)).length = firstLen J.p.nums.stages := by
    rw [List.length_take]
    exact Nat.min_eq_left P.enough
  have hsl := (steps_at J (firstPart J : Part V W X) (firstRd J) 0 (firstLen J.p.nums.stages)
    (first_moves J) b.name ⟨b.place, 0⟩ (J.laid.take (firstLen J.p.nums.stages)) hrs
    (φ.sees m₀.st.input) c.1).1
  have htake : ((proverSideOfProximityTest J : Placed V W X).needsField.steps b (φ.sees m₀.st.input) c).take
      (firstLen J.p.nums.stages) =
      ((firstPart J : Part V W X).steps b.name ⟨b.place, 0⟩
        (J.laid.take (firstLen J.p.nums.stages)) (φ.sees m₀.st.input) c.1).map guardStep := by
    show ((firstPart J : Part V W X).needsField.steps b.name ⟨b.place, 0⟩
      ((b.rounds.zip b.oracles).take (firstPart J : Part V W X).needsField.moves.length)
      (φ.sees m₀.st.input) c.1 ++ _).take _ = _
    rw [hlaid, needsField_length, l1, steps_guardStep]
    exact List.take_left' (by rw [List.length_map]; exact hsl)
  rw [htake, play_guardStep _ _ _ _ cs hcs] at hy
  obtain ⟨h1, h2, h3⟩ := behind_first_steps J s next rest P hlaid hor _ c.1 m₀ ds y hd hy
  exact ⟨st, m₀, E₀, c, hA, hc', h1, h2, h3⟩

/-- **THE BRIDGE, where the test's half stands behind the guard on the field.** The carried blocks are those of
the guarded second part: the guard reads no coin. -/
theorem left_of_inside_guarded {S Cl Pb : Type} {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain : ℕ}
    {hs : List (Placed V W X)} {b : Block S Cl} (J : TestJob W X) (K : Codes) (n : ℕ)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (P : FirstPartPublic J s next rest)
    (hF : formPubB J.p = true) (hlaid : b.rounds.zip b.oracles = J.laid)
    (hor : b.oracles.length = b.rounds.length)
    (hhalf : (hs.find? fun g => g.place == b.place) = some (proverSideOfProximityTest J).needsField)
    {A : Coins Bk → S → Mid W X → Env → Prop}
    (hopen : ∀ k s m E, A k s m E → m.opened.isSome = true) {k : Coins Bk} {m : Mid W X} {E : Env}
    (hin : InsideOf φ Bk chain hs b A (firstLen J.p.nums.stages) k m E)
    (hA : ∀ st m₀ E₀ (c : RowCoins [(firstPart J : Part V W X), restPart J]), A k st m₀ E₀ →
      lendRow Bk (Bk.rowsOf chain) (k.look chain) b.place
        [(firstPart J : Part V W X), restPart J] 0 = .ok c →
      AsksInFront J K n m₀.st.input (frontOf m₀) (restCoins J c.2.1))
    (ca : CsAll (restPart J : Part V W X).carries)
    (hca : carriedAt Bk k chain ⟨b.place, 1⟩ (restPart J : Part V W X).needsField = .ok ca) :
    AsksLeft J K n (stretches _ ca) m := by
  obtain ⟨st, m₀, E₀, c, h0, hc, hi, hfr, hfit⟩ :=
    behind_first_guarded J s next rest P hlaid hor hhalf hopen hin
  have hca' : carriedAt Bk k chain ⟨b.place, 1⟩ (restPart J : Part V W X) = .ok ca := by
    unfold carriedAt at hca ⊢
    rw [lendPart_behind] at hca
    exact hca
  obtain rfl : c.2.1.2.2 = ca :=
    Except.ok.inj ((carried_of_lent k chain b.place _ _ c hc).symm.trans hca')
  have h := asks_carried (V := V) J K n _ _ c.2.1 (hA st m₀ E₀ c h0 hc)
  rw [← hi, ← hfr] at h
  exact left_of_front J K n _ m s next rest P.stages hF hfit h

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.behind_first_guarded
#print axioms ProofFile.Honest.K12.left_of_inside_guarded
