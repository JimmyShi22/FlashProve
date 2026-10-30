-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/RunMid.lean: before a part that was called, the walk's rounds are
those of `play`, at a chain whose steps are blind. Suppose that a run of `runC` (Honest/Walk.lean)
has produced a real round, one that a prover's side made. Then the prover's run was still going on
before that round, and before every earlier round too; and, if no earlier step's message depends on
the opened columns that it is handed (`Step.Blind`, Honest/Blind.lean), these rounds, as produced,
are what `play` (Honest/Frame.lean) returns from the chain's start (`front_played`). So `midIn`
returns there, and what it has seen is what the start had seen and the rounds produced before
(`midIn_of`).

  1  `steps_part0`   a round without a move is under the part 0
  2  `walk_laid'`, `settle_mid`, `heard_mid`, `hearAtO_some`, `lays_field`, `live_back`,
     `told_live`   one walk
  3  `front_played`, `whole_played`   one chain, from its start
  4  `midIn_of`   `midIn` at an address before which the rounds are those of `play`

Limits.
  * The walk lengthens the state's field `opened` after each sub-protocol; `play` and `lays` carry
    it on as it is. So the walk's state and theirs agree but for that field (`settle_mid`,
    `heard_mid`, `live_back`, `whole_played`), and the rounds agree only under `hb` (`live_back`,
    `front_played`, `whole_played`).
  * `hb` (every step of a list is blind: `Step.Blind`, Honest/Blind.lean) is false at a list with
    one step that depends on the columns handed to it, and a lemma says nothing where its `hb` is
    false. `live_back`, `whole_played` and `lays_field` ask it of the whole list; `front_played`
    asks it of the first `n` steps alone, so it speaks of every round before the first step that
    depends on the columns, and not of that step's round or any behind it. Once the parts of the
    kind K10 that read the columns are laid, such a step stands in the first chain. Behind it the
    lemmas of Honest/Law/WalkMid.lean speak: they are stated of the walk's own state, with no
    hypothesis on the steps.
  * `hb` is shown at no chain here: `Part.steps_blind` (Honest/Blind.lean) reaches one part's steps
    alone.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Thread
import Johnson.Desc.ProofFile.Honest.Law.RunAtFile
import Johnson.Desc.ProofFile.Honest.GapAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl V W Y : Type}

/-! ## 1 A round without a move -/

theorem steps_part0 {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {hs : List (Placed V W Y)} : ∀ (bs : List (Block S Cl)) (ss : List (Step W Y)),
    chainSteps B rows look v bs hs = .ok ss →
    ∀ s ∈ ss, s.move.isSome = false → s.addr.part = 0
  | [], ss, h, s, hs', _ => by
    simp only [chainSteps] at h
    cases h
    cases hs'
  | b :: t, ss, h, s, hs', hm => by
    have h' : chainSteps B rows look v ([b] ++ t) hs = .ok ss := h
    rw [chainSteps_append] at h'
    obtain ⟨l₁, hl₁, h'⟩ := exBind_ok h'
    obtain ⟨l₂, hl₂, rfl⟩ := exMap_ok h'
    rcases List.mem_append.1 hs' with h1 | h2
    · cases hf : hs.find? fun g => g.place == b.place with
      | none =>
        rw [steps_one_none hf hl₁] at h1
        obtain ⟨r, -, rfl⟩ := List.mem_map.1 h1
        rfl
      | some g =>
        obtain ⟨-, e⟩ := chainSteps_rows [b] hs l₁ hl₁
        have e1 : (s.decl, s.oracles, s.addr.place, s.move.isSome) ∈
            l₁.map (fun s => (s.decl, s.oracles, s.addr.place, s.move.isSome)) :=
          List.mem_map.2 ⟨s, h1, rfl⟩
        rw [e] at e1
        obtain ⟨b', hb', hz⟩ := List.mem_flatMap.1 e1
        obtain ⟨z, -, e2⟩ := List.mem_map.1 hz
        have hb'' : b' = b := by simpa using hb'
        subst hb''
        have e3 : (hs.any fun h => h.place == b'.place) = s.move.isSome := congrArg (·.2.2.2) e2
        have e4 : (hs.any fun h => h.place == b'.place) = true :=
          List.any_eq_true.2 ⟨g, List.mem_of_find?_eq_some hf,
            List.find?_some (p := fun g : Placed V W Y => g.place == b'.place) hf⟩
        rw [e4, hm] at e3
        cases e3
    · exact steps_part0 t l₂ hl₂ s h2 hm

/-! ## 2 One walk -/

/-- A walk produces one round for each `Step`. -/
theorem walk_laid' (L : Lay) : ∀ (l : List (Step W Y)) (d : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y), walk L l d z = .ok z' →
    ∃ ps, z'.laid = z.laid ++ ps ∧ ps.length = l.length
  | [], [], z, z', h => by
    rw [walk_nil_ok h]
    exact ⟨[], (List.append_nil _).symm, rfl⟩
  | [], _ :: _, _, _, h => by simp [walk] at h
  | _ :: _, [], _, _, h => by simp [walk] at h
  | s :: l, d₀ :: d, z, z', h => by
    obtain ⟨x, z₁, -, hz, hw⟩ := walk_cons_ok h
    obtain ⟨ps, e1, e2⟩ := walk_laid' L l d z₁ z' hw
    refine ⟨⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d₀⟩ :: ps, ?_,
      congrArg (· + 1) e2⟩
    rw [e1, heard_laid hz, List.append_assoc]
    rfl

/-- `ChainProgress.settle` leaves the prover's run as it is but for the field `opened`, or takes it away. It
is `settle_same` (Honest/GapSame.lean) with `isSome` in the place of the state's name. -/
theorem settle_mid (L : Lay) (todo : List (Block S Cl)) (z z' : ChainProgress S Cl W Y)
    (hs : ChainProgress.settle L todo z = .ok z') (hm : z'.mid.isSome = true) :
    ∃ m o, z.mid = some m ∧ z'.mid = some { m with opened := o } := by
  obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.1 hm
  obtain ⟨m, o, h1, h2⟩ := settle_same L todo z z' m' hs hm'
  exact ⟨m, o, h1, by rw [hm', h2]⟩

/-- If the prover's run still goes on after a round, its state there is, but for the field
`opened`, `hearAtO` of the state before it, at whatever message x the round was given. -/
theorem heard_mid {L : Lay} {z z' : ChainProgress S Cl W Y} {s : Step W Y} {x : Told} {d : Fmt.Drawn}
    (hz : z.heard L s x d = .ok z') (hm : z'.mid.isSome = true) :
    ∃ m o, hearAtO z.mid s x d = .ok (some m) ∧ z'.mid = some { m with opened := o } := by
  obtain ⟨m', h1, hs⟩ := heard_ok hz
  obtain ⟨m, o, e1, e2⟩ := settle_mid L z.todo _ z' hs hm
  have e1' : m' = some m := e1
  subst e1'
  exact ⟨m, o, h1, e2⟩

theorem hearAtO_some {mo : Option (Mid W Y)} {s : Step W Y} {x : Told} {d : Fmt.Drawn}
    {m' : Option (Mid W Y)} (h : hearAtO mo s x d = .ok m') (hm : m'.isSome = true) :
    mo.isSome = true := by
  cases mo with
  | some _ => rfl
  | none =>
    cases h
    cases hm

/-- `lays` over blind steps (`Step.Blind`, Honest/Blind.lean) from a state with another field
`opened`: the same rounds, and the same state but for the field. -/
theorem lays_field : ∀ (l : List (Step W Y)) (d : List Fmt.Drawn) (m : Mid W Y)
    (o : Option (List OpenedColumn)), (∀ s ∈ l, s.Blind) →
    lays l d (some { m with opened := o }) =
      (lays l d (some m)).map fun y => (y.1, y.2.map ({ · with opened := o }))
  | [], [], m, o, _ => by
    rw [lays, lays]
    rfl
  | s :: l, d₀ :: d, m, o, hb => by
    rw [lays, lays]
    show (s.tell none { m with opened := o }).bind _ = Except.map _ ((s.tell none m).bind _)
    rw [tell_field (hb s List.mem_cons_self)]
    cases s.tell none m with
    | error e => rfl
    | ok x =>
      show ((s.hear x d₀ { m with opened := o }).map some).bind _ =
        Except.map _ (((s.hear x d₀ m).map some).bind _)
      rw [hear_field]
      cases s.hear x d₀ m with
      | error e => rfl
      | ok m' =>
        show (lays l d (some { m' with opened := o })).map _ =
          Except.map _ ((lays l d (some m')).map _)
        rw [lays_field l d m' o fun t ht => hb t (List.mem_cons_of_mem _ ht)]
        cases lays l d (some m') <;> rfl
  | [], _ :: _, _, _, _ => by simp [lays, Except.map]
  | _ :: _, [], _, _, _ => by simp [lays, Except.map]

/-- **If a walk over blind steps ends with the prover's run still going on, its rounds are those of
`lays` from its start**, and the two last states agree but for the field `opened`. Hypothesis `hb`:
no step's message depends on the opened columns that it is handed. At a list with a step that does
depend on them the lemma says nothing: the walk lengthens the field after each sub-protocol, `lays`
does not. -/
theorem live_back (L : Lay) : ∀ (l : List (Step W Y)) (d : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y), (∀ s ∈ l, s.Blind) → walk L l d z = .ok z' → z'.mid.isSome = true →
    ∃ ps m o, z'.laid = z.laid ++ ps ∧ lays l d z.mid = .ok (ps, some m) ∧
      z'.mid = some { m with opened := o }
  | [], [], z, z', _, h, hm => by
    rw [walk_nil_ok h] at hm ⊢
    cases hzm : z.mid with
    | none =>
      rw [hzm] at hm
      cases hm
    | some m => exact ⟨[], m, m.opened, (List.append_nil _).symm, rfl, rfl⟩
  | [], _ :: _, _, _, _, h, _ => by simp [walk] at h
  | _ :: _, [], _, _, _, h, _ => by simp [walk] at h
  | s :: l, d₀ :: d, z, z', hb, h, hm => by
    obtain ⟨x, z₁, hx, hz, hw⟩ := walk_cons_ok h
    obtain ⟨ps, m, o, e1, e2, e3⟩ :=
      live_back L l d z₁ z' (fun t ht => hb t (List.mem_cons_of_mem _ ht)) hw hm
    have hm₁ : z₁.mid.isSome = true := by
      cases hz₁ : z₁.mid with
      | some _ => rfl
      | none =>
        rw [hz₁] at e2
        have e4 : some m = none := congrArg (·.2) (lays_sub l d _ e2)
        cases e4
    obtain ⟨m₁, o₁, hh, e5⟩ := heard_mid hz hm₁
    rw [e5, lays_field l d m₁ o₁ fun t ht => hb t (List.mem_cons_of_mem _ ht)] at e2
    obtain ⟨⟨y1, y2⟩, hy, ey⟩ := map_ok e2
    have ey1 : y1 = ps := congrArg (·.1) ey
    have ey2 : y2.map ({ · with opened := o₁ }) = some m := congrArg (·.2) ey
    rw [← ey1] at e1
    cases y2 with
    | none => simp at ey2
    | some m₂ =>
      have hm2 : ({ m₂ with opened := o₁ } : Mid W Y) = m := Option.some.inj ey2
      subst hm2
      refine ⟨⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d₀⟩ :: y1, m₂, o,
        ?_, ?_, e3⟩
      · rw [e1, heard_laid hz, List.append_assoc]
        rfl
      · rw [say_eq] at hx
        simp only [lays]
        rw [hx]
        show ((hearAtO z.mid s x d₀).bind fun m' => (lays l d m').map _) = _
        rw [hh]
        show (lays l d (some m₁)).map _ = _
        rw [hy]
        rfl

/-- **If a walk produces a real round, the prover's run was going on at the walk's start.** -/
theorem told_live (L : Lay) : ∀ (l : List (Step W Y)) (d : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y) (ps : List Played), walk L l d z = .ok z' → z'.laid = z.laid ++ ps →
    (∃ p ∈ ps, p.told = true) → z.mid.isSome = true
  | [], [], z, z', ps, h, e, ⟨p, hp, _⟩ => by
    rw [walk_nil_ok h] at e
    have e' : ps = [] := List.self_eq_append_right.1 e
    rw [e'] at hp
    cases hp
  | [], _ :: _, _, _, _, h, _, _ => by simp [walk] at h
  | _ :: _, [], _, _, _, h, _, _ => by simp [walk] at h
  | s :: l, d₀ :: d, z, z', ps, h, e, ⟨p, hp, ht⟩ => by
    obtain ⟨x, z₁, hx, hz, hw⟩ := walk_cons_ok h
    obtain ⟨qs, e1, -⟩ := walk_laid' L l d z₁ z' hw
    have e2 : ps = ⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d₀⟩ :: qs := by
      rw [e1, heard_laid hz, List.append_assoc] at e
      exact (List.append_cancel_left e).symm
    rw [e2] at hp
    rcases List.mem_cons.1 hp with rfl | hp'
    · have ht' : x.told = true := ht
      cases hm : z.mid with
      | some _ => rfl
      | none =>
        rw [say_eq, hm] at hx
        have hx' : (Except.ok (subTold s.decl s.oracles) : Except Refusal Told) = .ok x := hx
        cases hx'
        cases ht'
    · have g := told_live L l d z₁ z' qs hw e1 ⟨p, hp', ht⟩
      obtain ⟨_, _, hh, -⟩ := heard_mid hz g
      exact hearAtO_some hh rfl

/-! ## 3 One chain, from its start -/

/-- **Before a real round, the rounds that a chain of blind steps has produced are those of
`play`.** `n`: how many rounds come before it. Hypothesis `hb`: the message of none of the first `n`
steps depends on the opened columns that it is handed (`Step.Blind`, Honest/Blind.lean); where one
of these does the lemma says nothing. Hypothesis `hp0`: every `Step` without a move is under the
part 0 (see `steps_part0`). `play` is taken with no stored run to fall back on, from the start as
the caller gives it: the field `opened` of `m₀` is not the walk's. -/
theorem front_played (L : Lay) (bs : List (Block S Cl)) (mo : Option (Mid W Y)) (v : Option S)
    {a z : ChainProgress S Cl W Y} {ss : List (Step W Y)} {ds : List Fmt.Drawn} {front : List OpenedColumn} (n : Nat)
    (ha : ChainProgress.start L bs mo v front = .ok a) (hz : walk L ss ds a = .ok z)
    (hb : ∀ s ∈ ss.take n, s.Blind)
    (hp0 : ∀ s ∈ ss, s.move.isSome = false → s.addr.part = 0)
    (ht : ∃ p ∈ z.laid.drop n, p.told = true) :
    ∃ m₀ m, mo = some m₀ ∧ play (ss.take n) (ds.take n) [] m₀ = .ok (z.laid.take n, m) := by
  have hlen := walk_len L ss ds a z hz
  have hal : a.laid = [] := by
    unfold ChainProgress.start at ha
    have g := settle_laid L bs _ a ha
    exact g
  have hz' : walk L (ss.take n ++ ss.drop n) (ds.take n ++ ds.drop n) a = .ok z := by
    rw [List.take_append_drop, List.take_append_drop]
    exact hz
  obtain ⟨z₁, h1, h2⟩ := walk_append_ok (ss.drop n) (ds.drop n) (ss.take n) (ds.take n) a z
    (by rw [List.length_take, List.length_take, hlen]) hz'
  obtain ⟨ps₁, f1, f1'⟩ := walk_laid' L _ _ a z₁ h1
  obtain ⟨ps₂, f2, -⟩ := walk_laid' L _ _ z₁ z h2
  rw [hal, List.nil_append] at f1
  have hn : ps₁.length = (ss.take n).length := f1'
  have hle : ps₁.length ≤ n := by
    rw [hn, List.length_take]
    exact Nat.min_le_left _ _
  have htake : z.laid.take n = ps₁ ∧ z.laid.drop n = ps₂ := by
    rw [f2, f1]
    by_cases hc : n ≤ ss.length
    · have e : ps₁.length = n := by rw [hn, List.length_take, Nat.min_eq_left hc]
      exact ⟨List.take_left' e, List.drop_left' e⟩
    · have hc' : ss.length ≤ n := Nat.le_of_lt (Nat.lt_of_not_le hc)
      have e0 : ss.drop n = [] := List.drop_eq_nil_of_le hc'
      have e1 : ds.drop n = [] := List.drop_eq_nil_of_le (by rw [hlen]; exact hc')
      rw [e0, e1] at h2
      have e2 := walk_nil_ok h2
      rw [e2] at f2
      have e3 : ps₂ = [] := List.self_eq_append_right.1 f2
      rw [e3, List.append_nil]
      exact ⟨List.take_of_length_le hle, List.drop_eq_nil_of_le hle⟩
  rw [htake.2] at ht
  have live₁ := told_live L _ _ z₁ z ps₂ h2 f2 ht
  obtain ⟨ps, m₁, o₁, g1, g2, -⟩ :=
    live_back L _ _ a z₁ hb h1 live₁
  rw [hal, List.nil_append] at g1
  have hps : ps = ps₁ := by rw [← g1, f1]
  have livea : a.mid.isSome = true := by
    cases hm : a.mid with
    | some _ => rfl
    | none =>
      rw [hm] at g2
      have e4 : some m₁ = none := congrArg (·.2) (lays_sub _ _ _ g2)
      cases e4
  obtain ⟨ma, hma⟩ := Option.isSome_iff_exists.1 livea
  obtain ⟨m₀, o, hmo, rfl⟩ := start_same ha hma
  rw [hma, lays_field _ _ m₀ o hb] at g2
  obtain ⟨⟨y1, y2⟩, hy, ey⟩ := map_ok g2
  have ey1 : y1 = ps := congrArg (·.1) ey
  obtain ⟨m, -, k2⟩ := lays_live _ _ m₀ _
    (fun s hs => hp0 s (List.mem_of_mem_take hs)) hy
  refine ⟨m₀, m, hmo, ?_⟩
  rw [htake.1, ← hps, ← ey1]
  exact k2

/-- **A chain of blind steps that ends with the prover's run still going on is that of `play`, as a
whole**, and the two last states agree but for the field `opened`. Hypothesis `hb`: as in
`live_back`. Hypothesis `hp0`: every `Step` without a move is under the part 0 (see
`steps_part0`). `play` is taken with no stored run to fall back on. -/
theorem whole_played (L : Lay) (bs : List (Block S Cl)) (mo : Option (Mid W Y)) (v : Option S)
    {a z : ChainProgress S Cl W Y} {ss : List (Step W Y)} {ds : List Fmt.Drawn} {front : List OpenedColumn}
    {m : Mid W Y}
    (ha : ChainProgress.start L bs mo v front = .ok a) (hz : walk L ss ds a = .ok z)
    (hb : ∀ s ∈ ss, s.Blind)
    (hp0 : ∀ s ∈ ss, s.move.isSome = false → s.addr.part = 0) (hm : z.mid = some m) :
    ∃ m₀ m', mo = some m₀ ∧ play ss ds [] m₀ = .ok (z.laid, m') ∧
      m = { m' with opened := m.opened } := by
  have hal : a.laid = [] := by
    unfold ChainProgress.start at ha
    have g := settle_laid L bs _ a ha
    exact g
  have live : z.mid.isSome = true := by rw [hm]; rfl
  obtain ⟨ps, m₁, o₁, g1, g2, g3⟩ := live_back L _ _ a z hb hz live
  rw [hal, List.nil_append] at g1
  have livea : a.mid.isSome = true := by
    cases hma : a.mid with
    | some _ => rfl
    | none =>
      rw [hma] at g2
      have e4 : some m₁ = none := congrArg (·.2) (lays_sub _ _ _ g2)
      cases e4
  obtain ⟨ma, hma⟩ := Option.isSome_iff_exists.1 livea
  obtain ⟨m₀, o, hmo, rfl⟩ := start_same ha hma
  rw [hma, lays_field _ _ m₀ o hb] at g2
  obtain ⟨⟨y1, y2⟩, hy, ey⟩ := map_ok g2
  have ey1 : y1 = ps := congrArg (·.1) ey
  have ey2 : y2.map ({ · with opened := o }) = some m₁ := congrArg (·.2) ey
  obtain ⟨m', k1, k2⟩ := lays_live _ _ m₀ _ hp0 hy
  have k1' : y2 = some m' := k1
  subst k1'
  have e5 : ({ m' with opened := o } : Mid W Y) = m₁ := Option.some.inj ey2
  subst e5
  rw [hm] at g3
  have e6 : m = { m' with opened := o₁ } := Option.some.inj g3
  refine ⟨m₀, m', hmo, ?_, ?_⟩
  · rw [g1, ← ey1]
    exact k2
  · subst e6
    rfl

/-! ## 4 `midIn` -/

theorem midIn_of {ss : List (Step W Y)} {ds : List Fmt.Drawn} {m₀ m : Mid W Y} {a : Addr}
    {ps : List Played} (ha : ss.any (·.addr == a) = true)
    (hp : play (ss.take (ss.takeWhile fun s => s.addr != a).length)
      (ds.take (ss.takeWhile fun s => s.addr != a).length) [] m₀ = .ok (ps, m)) :
    midIn ss ds [] m₀ a = .ok m ∧ m.seen = m₀.seen ++ roundsOf ps := by
  refine ⟨?_, (play_mid _ _ _ _ _ hp).2.2⟩
  unfold midIn
  simp only [ha, Bool.not_true, Bool.false_eq_true, if_false, hp]
  rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.steps_part0
#print axioms ProofFile.Honest.walk_laid'
#print axioms ProofFile.Honest.settle_mid
#print axioms ProofFile.Honest.heard_mid
#print axioms ProofFile.Honest.hearAtO_some
#print axioms ProofFile.Honest.lays_field
#print axioms ProofFile.Honest.live_back
#print axioms ProofFile.Honest.told_live
#print axioms ProofFile.Honest.front_played
#print axioms ProofFile.Honest.whole_played
#print axioms ProofFile.Honest.midIn_of
