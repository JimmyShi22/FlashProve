-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/WalkMid.lean: the state of the prover's run that a walk
(Honest/Walk.lean) holds, said of the walk itself. `ChainProgress.settle` lays the columns that a
sub-protocol has read into the state's field `opened`; `play` and `lays` carry that field on as it
is. The lemmas of Honest/Law/RunMid.lean, which go from the walk to `play` over several
sub-protocols, take a hypothesis on the steps (`Step.Blind`, Honest/Blind.lean). The lemmas of
this file have no such hypothesis: they speak of the walk's own state, and go to `lays` inside one
sub-protocol alone, where nothing is asked and the field stands still.

  1  `ChainProgress.From`, `settle_from`, `start_from`, `heard_from`, `walk_from`, `walk_mid`   along a walk:
     the input, the challenges that the stops may read, and the rounds shown. `ChainProgress.From m₀` holds
     of what `ChainProgress.start` returns from `m₀` (`start_from`); `ChainProgress.settle`, `ChainProgress.heard` and `walk`
     keep it wherever they return (`settle_from`, `heard_from`, `walk_from`)
  2  `walk_cut`   a walk, cut after its first n rounds
  3  `walk_in`   inside one sub-protocol, before its last round: the walk is `lays`
  4  `midInW_of`, `orRefused_some`   `midInW` (Honest/MidW.lean) where the walk over the rounds
     before the address returns. `orRefused_some`: `orRefused` (Honest/Owed.lean) of a state that
     was returned is that state
  5  `say_lt`, `okRound_lt`, `drawFit_elems`, `drawsFit_elems`, `walk_said`   the words of the
     rounds that a walk has collected. They stand here, and not in Honest/Law/CoverBelow.lean, which
     uses them, because Honest/Law/AcceptC.lean, which that file imports, calls two of them

Limits.
  * Beyond one sub-protocol nothing is said on the field `opened` (Honest/WalkOpened.lean has
    `ChainProgress.Inv`), on `st.heard` (Honest/WalkHeard.lean has `ChainProgress.Hears`) or on `st.own`.
  * `walk_in` stops before the sub-protocol's last round: after it the sub-protocol is asked.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.RunMid
import Johnson.Desc.ProofFile.Honest.Law.WalkFold
import Johnson.Desc.ProofFile.Honest.Law.StratCanonC
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk
import Johnson.Desc.ProofFile.Honest.WalkHeard
import Johnson.Desc.ProofFile.Honest.MidW
import Johnson.Desc.ProofFile.Honest.WalkLive
import Johnson.Desc.ProofFile.Honest.Owed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl W Y : Type}

/-! ## 1 Along a walk -/

/-- Where the run is still played: its input is that of `m₀`; the challenges that its stops may read
are those of `m₀` and then those of the rounds produced so far; and it has been shown what `m₀` had
been shown and then the rounds produced so far. -/
def ChainProgress.From (m₀ : Mid W Y) (z : ChainProgress S Cl W Y) : Prop :=
  ∀ m, z.mid = some m → m.st.input = m₀.st.input ∧ m.loc = m₀.loc ++ z.laid.map (·.drawn) ∧
    m.seen = m₀.seen ++ roundsOf z.laid

theorem settle_from (L : Lay) (m₀ : Mid W Y) : ∀ (bs : List (Block S Cl))
    (z z' : ChainProgress S Cl W Y), z.From m₀ → ChainProgress.settle L bs z = .ok z' → z'.From m₀
  | [], z, z', hz, h => by
    rw [ChainProgress.settle] at h
    obtain rfl := Except.ok.inj h
    exact hz
  | b :: bs, z, z', hz, h => by
    rw [ChainProgress.settle] at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact hz
    · obtain ⟨cols, -, h⟩ := of_bind_ok h
      refine settle_from L m₀ bs _ z' ?_ h
      intro m hm
      cases hzm : z.mid with
      | none =>
        simp [hzm] at hm
      | some m₁ =>
        have h0 := hz m₁ hzm
        split at hm
        · rw [hzm] at hm
          obtain rfl : m₁.took cols = m := Option.some.inj hm
          exact h0
        · cases hm

theorem start_from {L : Lay} {bs : List (Block S Cl)} {m₀ : Mid W Y} {v : Option S}
    {front : List OpenedColumn} {z : ChainProgress S Cl W Y} (h : ChainProgress.start L bs (some m₀) v front = .ok z) :
    z.From m₀ := by
  refine settle_from L _ bs _ z ?_ h
  intro m' hm
  split at hm
  · obtain rfl := Option.some.inj hm
    exact ⟨rfl, (List.append_nil _).symm, (List.append_nil _).symm⟩
  · cases hm

theorem heard_from {L : Lay} {m₀ : Mid W Y} {z z' : ChainProgress S Cl W Y} {s : Step W Y} {x : Told}
    {d : Fmt.Drawn} (hz : z.From m₀) (h : z.heard L s x d = .ok z') : z'.From m₀ := by
  unfold ChainProgress.heard at h
  obtain ⟨m', hm', h⟩ := of_bind_ok h
  refine settle_from L m₀ _ _ z' ?_ h
  intro m hm
  have hm2 : m' = some m := hm
  subst hm2
  cases hzm : z.mid with
  | none =>
    rw [hzm] at hm'
    cases hm'
  | some m₁ =>
    rw [hzm] at hm'
    obtain ⟨m₂, h1, e⟩ := map_ok hm'
    obtain rfl := Option.some.inj e
    obtain ⟨a1, a2, a3⟩ := hz m₁ hzm
    obtain ⟨b1, b2, b3⟩ := hear_mid h1
    refine ⟨b1.trans a1, ?_, ?_⟩
    · show m₂.loc = m₀.loc ++ List.map Played.drawn (z.laid ++ [_])
      rw [b2, a2, List.map_append, List.append_assoc]
      rfl
    · show m₂.seen = m₀.seen ++ roundsOf (z.laid ++ [_])
      rw [b3, a3, roundsOf, roundsOf, List.map_append, List.append_assoc]
      rfl

theorem walk_from (L : Lay) (m₀ : Mid W Y) : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y), z.From m₀ → walk L ss ds z = .ok z' → z'.From m₀
  | [], [], z, z', hz, h => by
    rw [walk] at h
    obtain rfl := Except.ok.inj h
    exact hz
  | s :: ss, d :: ds, z, z', hz, h => by
    rw [walk] at h
    obtain ⟨x, -, h⟩ := of_bind_ok h
    obtain ⟨z₁, h1, h⟩ := of_bind_ok h
    exact walk_from L m₀ ss ds z₁ z' (heard_from hz h1) h
  | [], _ :: _, _, _, _, h => by simp [walk] at h
  | _ :: _, [], _, _, _, h => by simp [walk] at h

/-- **The state that a chain's walk holds, from the chain's start**: the start's input; the start's
challenges for the stops, then the walk's; what the start had been shown, then the rounds produced.
`ha`, `hz`: the start and the walk return. `hm`: the run is still played. No hypothesis on the
steps. -/
theorem walk_mid {L : Lay} {bs : List (Block S Cl)} {m₀ m : Mid W Y} {v : Option S}
    {front : List OpenedColumn} {a z : ChainProgress S Cl W Y} {ss : List (Step W Y)} {ds : List Fmt.Drawn}
    (ha : ChainProgress.start L bs (some m₀) v front = .ok a) (hz : walk L ss ds a = .ok z)
    (hm : z.mid = some m) :
    m.st.input = m₀.st.input ∧ m.loc = m₀.loc ++ ds ∧ m.seen = m₀.seen ++ roundsOf z.laid := by
  obtain ⟨h1, h2, h3⟩ := walk_from L m₀ ss ds a z (start_from ha) hz m hm
  have e := walk_laid_drawn L ss ds a z hz
  rw [start_laid ha, List.map_nil, List.nil_append] at e
  rw [e] at h2
  exact ⟨h1, h2, h3⟩

/-! ## 2 A walk, cut -/

/-- **A walk that began with no round produced, cut after its first n rounds.** `hn`: it has n steps
or more. The walk over the first n steps returns and has produced the whole walk's first n rounds;
the walk over the other steps leads from it to the same end. -/
theorem walk_cut {L : Lay} {ss : List (Step W Y)} {ds : List Fmt.Drawn} {a z : ChainProgress S Cl W Y}
    (hal : a.laid = []) (hz : walk L ss ds a = .ok z) (n : Nat) (hn : n ≤ ss.length) :
    ∃ y, walk L (ss.take n) (ds.take n) a = .ok y ∧ walk L (ss.drop n) (ds.drop n) y = .ok z ∧
      y.laid = z.laid.take n ∧ z.laid = y.laid ++ z.laid.drop n := by
  have hl := walk_len L ss ds a z hz
  have hz' : walk L (ss.take n ++ ss.drop n) (ds.take n ++ ds.drop n) a = .ok z := by
    rw [List.take_append_drop, List.take_append_drop]
    exact hz
  obtain ⟨y, h1, h2⟩ := walk_append_ok (ss.drop n) (ds.drop n) (ss.take n) (ds.take n) a z
    (by rw [List.length_take, List.length_take, hl]) hz'
  obtain ⟨ps₁, f1, f1'⟩ := walk_laid' L _ _ a y h1
  obtain ⟨ps₂, f2, -⟩ := walk_laid' L _ _ y z h2
  rw [hal, List.nil_append] at f1
  have e1 : y.laid.length = n := by rw [f1, f1', List.length_take, Nat.min_eq_left hn]
  have e2 : y.laid = z.laid.take n := by
    rw [f2]
    exact (List.take_left' e1).symm
  refine ⟨y, h1, h2, e2, ?_⟩
  rw [e2, List.take_append_drop]

/-! ## 3 Inside one sub-protocol -/

/-- **Inside one sub-protocol, before its last round, a walk is the rounds' messages and updates**:
nothing is asked, and the walk's other fields stand still. `b`: the next sub-protocol to be asked.
Its rounds produced before (`z.own`) and the steps walked are together fewer than `b` has rounds. -/
theorem walk_in {L : Lay} {b : Block S Cl} {bs : List (Block S Cl)} :
    ∀ (l : List (Step W Y)) (ds : List Fmt.Drawn) (z z' : ChainProgress S Cl W Y), z.todo = b :: bs →
    z.own.length + l.length < b.rounds.length → walk L l ds z = .ok z' →
    ∃ y, lays l ds z.mid = .ok y ∧ z' = z.grown y
  | [], [], z, z', _, _, h => by
    rw [walk_nil_ok h]
    exact ⟨([], z.mid), by rw [lays], by cases z; simp [ChainProgress.grown]⟩
  | [], _ :: _, _, _, _, _, h => by simp [walk] at h
  | _ :: _, [], _, _, _, _, h => by simp [walk] at h
  | s :: l, d :: ds, z, z', ht, hlen, h => by
    obtain ⟨x, z₁, hx, hz, h⟩ := walk_cons_ok h
    obtain ⟨m', hm, hs⟩ := heard_ok hz
    have hx' : sayAt z.mid s = .ok x := (say_eq z s).symm.trans hx
    rw [ht] at hs
    have hw : (z.own ++ [(⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩ :
        Played)]).length < b.rounds.length := by
      rw [List.length_append, List.length_singleton]
      simp only [List.length_cons] at hlen
      omega
    rw [settle_wait L b bs _ hw] at hs
    have e := Except.ok.inj hs
    subst e
    obtain ⟨y, hy, hs'⟩ := walk_in l ds _ z' rfl (by
      show (z.own ++ [_]).length + l.length < b.rounds.length
      rw [List.length_append, List.length_singleton]
      simp only [List.length_cons] at hlen
      omega) h
    refine ⟨(⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩ :: y.1, y.2),
      ?_, ?_⟩
    · have hy' : lays l ds m' = .ok y := hy
      rw [lays]
      simp only [hx', hm, hy', Except.bind, Except.map]
    · rw [hs']
      unfold ChainProgress.grown
      simp only [List.append_assoc, List.singleton_append, ht]

/-! ## 4 `midInW` -/

/-- `midInW` at an address before which the walk returns: that walk's own state. `ha`: a step stands
at the address. -/
theorem midInW_of {L : Lay} {ss : List (Step W Y)} {ds : List Fmt.Drawn} {z y : ChainProgress S Cl W Y}
    {a : Addr} (ha : ss.any (·.addr == a) = true)
    (hw : walk L (ss.take (ss.takeWhile fun s => s.addr != a).length)
      (ds.take (ss.takeWhile fun s => s.addr != a).length) z = .ok y) :
    midInW L ss ds z a = .ok y.mid := by
  unfold midInW
  simp only [ha, Bool.not_true, Bool.false_eq_true, if_false, hw, Except.map]

theorem orRefused_some {e : Except Refusal (Option (Mid W Y))} {m : Mid W Y}
    (h : e = .ok (some m)) : orRefused e = .ok m := by
  rw [h]
  rfl

/-! ## 5 The words of the rounds that a walk has collected -/

/-- The words of the items of a walk's message are below the prime. -/
theorem say_lt {z : ChainProgress S Cl W Y} {s : Step W Y} {x : Told} (h : z.say s = .ok x) :
    ∀ a ∈ x.vals, LtGot a := by
  cases hm : z.mid with
  | none =>
    have hs' : (Except.ok (subTold s.decl s.oracles) : Except Refusal Told) = .ok x := by
      rw [← h]
      unfold ChainProgress.say
      rw [hm]
    cases hs'
    exact sub_lt _ _
  | some m =>
    have hs' : s.tell none m = .ok x := by
      rw [← h]
      unfold ChainProgress.say
      rw [hm]
    exact told_lt hs'

/-- One round passes the library's test on words. `hv`: its items. `hd`: its drawn elements. -/
theorem okRound_lt {vals : List Fmt.ItemValue} {d : Fmt.Drawn} (hv : ∀ a ∈ vals, LtGot a)
    (hd : (d.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true) :
    viewWordsBelowPrime ⟨[⟨vals, d⟩], []⟩ = true := by
  simp only [viewWordsBelowPrime, List.all_nil, Bool.and_true]
  rw [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨hd, ?_⟩
  show (List.all vals _) = true
  rw [List.all_eq_true]
  intro g hg
  have h1 := hv g hg
  cases g with
  | f x => exact decide_eq_true h1
  | e x => simpa [LtGot, and_assoc] using h1
  | answer x => simpa [LtGot, and_assoc] using h1
  | word x => rfl
  | root x => rfl

/-- A challenge that a round can draw has drawn elements whose words are below the prime. -/
theorem drawFit_elems {d : Fmt.DeclaredRound} {R : Fmt.Drawn} (h : drawFit d R = true) :
    (R.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true := by
  simp only [drawFit, Bool.and_eq_true] at h
  exact h.1.2

/-- The same for a list of rounds. -/
theorem drawsFit_elems : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    drawsFit ds Rs = true → ∀ R ∈ Rs,
      (R.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true
  | [], [], _, _, hR => by cases hR
  | [], _ :: _, h, _, _ => by simp [drawsFit] at h
  | _ :: _, [], h, _, _ => by simp [drawsFit] at h
  | _ :: ds, _ :: Rs, h, R, hR => by
    simp only [drawsFit, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hR with e | hR'
    · rw [e]
      exact drawFit_elems h.1
    · exact drawsFit_elems ds Rs h.2 R hR'

/-- The rounds that a walk has collected pass the library's test on words, if the drawn elements of
the challenges do and the rounds that it had laid before do. -/
theorem walk_said (L : Lay) : ∀ (l : List (Step W Y)) (d : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y),
    (∀ R ∈ d, (R.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true) →
    viewWordsBelowPrime ⟨roundsOf z.laid, []⟩ = true → walk L l d z = .ok z' →
    viewWordsBelowPrime ⟨roundsOf z'.laid, []⟩ = true
  | [], [], z, z', _, h, hw => by
    rw [walk_nil_ok hw]
    exact h
  | [], _ :: _, _, _, _, _, hw => by simp [walk] at hw
  | _ :: _, [], _, _, _, _, hw => by simp [walk] at hw
  | s :: l, d₀ :: d, z, z', hd, h, hw => by
    obtain ⟨x, z₁, hx, hz, hw₁⟩ := walk_cons_ok hw
    refine walk_said L l d z₁ z' (fun R hR => hd R (List.mem_cons_of_mem _ hR)) ?_ hw₁
    rw [heard_laid hz, roundsOf_append]
    exact (okRounds_append _ _).2 ⟨h, okRound_lt (say_lt hx) (hd d₀ List.mem_cons_self)⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.settle_from
#print axioms ProofFile.Honest.start_from
#print axioms ProofFile.Honest.heard_from
#print axioms ProofFile.Honest.walk_from
#print axioms ProofFile.Honest.walk_mid
#print axioms ProofFile.Honest.walk_cut
#print axioms ProofFile.Honest.walk_in
#print axioms ProofFile.Honest.midInW_of
#print axioms ProofFile.Honest.orRefused_some
#print axioms ProofFile.Honest.say_lt
#print axioms ProofFile.Honest.okRound_lt
#print axioms ProofFile.Honest.drawFit_elems
#print axioms ProofFile.Honest.drawsFit_elems
#print axioms ProofFile.Honest.walk_said
#print axioms ProofFile.Honest.ChainProgress.From
