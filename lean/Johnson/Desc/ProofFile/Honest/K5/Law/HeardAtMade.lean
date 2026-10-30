-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/HeardAtMade.lean: conditional: what the verifier's state holds of an attention
segment's own rounds (kind K5), seen from a later border of a thread, as a function of what the prover's run has
heard. By the three steps of Johnson/Desc/ProofFile/Honest/Thread/MemberLaw.lean: an earlier sub-protocol's own step
("made_member"); "my decision sets this field to that function of its own rounds' challenges" (here); "no later
sub-protocol changes that field" ("fold_keeps"). General in the thread's parameters: no head, no size.

  k5_step_is         every yes of the member's step: an attention segment stands open, the kind's hearing has
                     returned from its ledger at the step's rounds, and the state behind is "behind"
  k5_step_keeps_g    the member's step leaves what the lookup on the calls returned: in the form that "fold_keeps"
                     takes
  k5_step_lays       behind the member's step the field heard5 holds the hearing's return
  reads_of_slice     on lists: challenges that hold a stretch of what was heard hold what rounds drew whose
                     challenges are that stretch
  heard5_at_made     at a border b behind the member j: the field heard5 holds the return of the kind's hearing at
                     rounds whose challenges are the member's own slice of what was heard. Conditional: that the
                     sub-protocols between keep the field (hk)
  points_at_made     so the prover's named points and weights, made of what was heard, are the verifier's, made of
                     that field: field by field, in front of every part
  pointsSame_at_made the same at the verifier's own road from the field to the points ("ptsFrom"), and in the form
                     "PointsSame": the two lists of points lay one list of tables
  heard5_next, points_next, pointsSame_next   at the border next behind the member: nothing stands between, and
                     the premise hk falls
  att_of_heard5      where the field holds something an attention segment stands open
  heard5_sent        a sending's own yes leaves the field, where it holds something
  g_sent             and it leaves what the lookup on the calls returned: in the letters of k5_step_keeps_g
  pointsSame_sent    "pointsSame_next" at the state behind the yes of the sending that follows the member: the state
                     in front of the quiet step that makes the tables

The premise hk is meant for borders inside the segment: the field holds nothing wherever no attention segment stands
open (att_of_heard5, read the other way).
The key points zk and the lookup's share lk of what the tables read are one letter each on both sides: that what the
state holds of the lookup on the calls is what the prover's reader makes of what was heard, in the key points and in
what the tables read, is another sentence, on the lookup's rounds, and is not said here.

Limits. "DecidesAs p blk" (Member.lean) and the thread's clause "Made" are premises: nothing here shows that a
thread's border is ever reached. Both calls of the function for the points are premises where they stand. The
equations are word for word. Nothing is said of a value that is sent. No property of the protocol is claimed:
nothing on soundness, completeness or what anything reveals.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Member
import Johnson.Desc.ProofFile.Honest.Thread.MemberLaw
import Johnson.Desc.K5.Honest.Law.Returns
import Johnson.Desc.K5.Honest.Law.PointsIs
import Johnson.Desc.K5.Honest.Law.PointsTable
import Johnson.Desc.K5.Honest.Law.ReadsAfter
import Johnson.Desc.Sound.RunIsDecide
import Johnson.Desc.First.Att.RunsK

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Claim OpenedColumn First.S First.AttOwn noDigest foldBlocks foldBlocks_nil)
open VerifiableInference.Desc.First.Att.P (Par Heard Left Pts LookIn hear pointsOf ptsFrom behind)
open H2K5.Honest (Pub5 Chal Reads PtsTo PointsSame ptsOf heard_is_ours points_same points_laid k5_yes_is)

/-! ## 1 The member's own step -/

section
variable {p : Par} {blk : Block First.S Claim}

/-- **Every yes of the member's step.** Conditional: the member decides as the kind does. -/
theorem k5_step_is (Dc : DecidesAs p blk) {ft : Nat} {s s' : First.S} {rs : List Fmt.RoundView}
    {c : List OpenedColumn} {n : Nat} (h : blk.step ft s rs c = .ok (s', n)) :
    ∃ a hd G, s.here = .att a ∧ hear p.own (a.F, rs.map noDigest, 0) = some (hd, G, [], 0) ∧
      s' = behind s a hd G :=
  k5_yes_is p ((Dc.decides _ _ _ _).1
    ((VerifiableInference.Desc.Sound.step_ok_iff ft blk s s' rs c n).1 h).2.2.2).1

/-- **The member's step leaves what the lookup on the calls returned.** -/
theorem k5_step_keeps_g (Dc : DecidesAs p blk) (ft : Nat) (g : OnBytes.Model.Forest.Heard)
    (s : First.S) (rs : List Fmt.RoundView) (c : List OpenedColumn) (s' : First.S) (n : Nat)
    (h : blk.step ft s rs c = .ok (s', n)) (hq : ∃ a, s.here = .att a ∧ a.g = some g) :
    ∃ a, s'.here = .att a ∧ a.g = some g := by
  obtain ⟨a, hd, G, e, -, rfl⟩ := k5_step_is Dc h
  obtain ⟨a', e', hg⟩ := hq
  rw [e] at e'
  cases e'
  exact ⟨_, rfl, hg⟩

/-- **Behind the member's step the field holds the hearing's return.** -/
theorem k5_step_lays (Dc : DecidesAs p blk) {ft : Nat} {s s' : First.S} {rs : List Fmt.RoundView}
    {c : List OpenedColumn} {n : Nat} (h : blk.step ft s rs c = .ok (s', n)) :
    ∃ (F G : Fork) (hd : Heard), hear p.own (F, rs.map noDigest, 0) = some (hd, G, [], 0) ∧
      s'.heard5? = some hd := by
  obtain ⟨a, hd, G, -, hh, rfl⟩ := k5_step_is Dc h
  exact ⟨a.F, G, hd, hh, rfl⟩

end

/-! ## 2 On lists -/

/-- **Challenges that hold a stretch of what was heard hold what rounds drew whose challenges are that stretch.**
heard: all that was heard; i, n: the stretch's first number and length; H: how much of what was heard is kept, at
least to the stretch's end. -/
theorem reads_of_slice {heard : List Fmt.Drawn} {rs : List Fmt.RoundView} {i n H : Nat}
    (hr : rs.map (·.drawn) = (heard.drop i).take n) (hH : i + n ≤ H) (zk : Array (Array OnBytes.E)) :
    Reads ⟨zk, (heard.take H).drop i⟩ (rs.map noDigest) := by
  intro t r ht
  rw [List.getElem?_map] at ht
  obtain ⟨r0, h0, rfl⟩ := Option.map_eq_some_iff.1 ht
  have h1 : ((heard.drop i).take n)[t]? = some r0.drawn := by
    rw [← hr, List.getElem?_map, h0]
    rfl
  have ht' : t < n := by
    have h2 := (List.getElem?_eq_some_iff.1 h1).1
    rw [List.length_take] at h2
    omega
  rw [List.getElem?_take_of_lt ht', List.getElem?_drop] at h1
  have hlt : i + t < H := by omega
  show (((heard.take H).drop i)[t]?).map (·.elems) = some r0.drawn.elems
  rw [List.getElem?_drop, List.getElem?_take_of_lt hlt, h1]
  rfl

/-! ## 3 At the thread -/

variable {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk First.S Claim V W X Pb) {p : Par}
  {blk : Block First.S Claim}

/-- **From a later border: the field heard5 holds the return of the kind's hearing at rounds whose challenges are
the member's own slice of what was heard.** Conditional: the member decides as the kind does; the thread's clause
"Made" at the border; hk: each sub-protocol between the member and the border keeps the field. -/
theorem heard5_at_made (Dc : DecidesAs p blk) {b j : Nat} (hj : j < b)
    (hblk : T.bs[j]? = some blk) {k : Coins Bk} {s : First.S} {m : Mid W X} {E : Env}
    (hM : T.Made b k s m E)
    (hk : ∀ hd : Heard, ∀ x ∈ (T.bs.take b).drop (j + 1), ∀ t rs c t' n,
      x.step T.ft t rs c = .ok (t', n) → t.heard5? = some hd → t'.heard5? = some hd) :
    ∃ (F G : Fork) (hd : Heard) (rs : List Fmt.RoundView),
      hear p.own (F, rs.map noDigest, 0) = some (hd, G, [], 0) ∧
      rs.map (·.drawn) = heardFrom m.st (T.front + roundsTo T.bs j) blk.rounds.length ∧
      s.heard5? = some hd := by
  obtain ⟨sj, sj', rs, c, n, rs', c', hs, hr, hf⟩ := made_member T hj hblk hM
  obtain ⟨F, G, hd, hh, h5⟩ := k5_step_lays Dc hs
  exact ⟨F, G, hd, rs, hh, hr,
    fold_keeps T.ft (fun t => t.heard5? = some hd) _ (hk hd) sj' rs' c' _ hf h5⟩

/-- **The prover's named points and weights, made of what was heard, are the verifier's, made of the state's
field**, field by field, in front of every part. P: the place's public numbers on the prover's side; zk: the key
points, one letter on both sides; H: how much of what was heard the prover's reader is handed, at least to the end
of the member's rounds; L: the rows that the verifier lays. Conditional: as "heard5_at_made"; and the return of
both calls of the function for the points. -/
theorem points_at_made (Dc : DecidesAs p blk) {b j : Nat} (hj : j < b)
    (hblk : T.bs[j]? = some blk) {k : Coins Bk} {s : First.S} {m : Mid W X} {E : Env}
    (hM : T.Made b k s m E)
    (hk : ∀ hd : Heard, ∀ x ∈ (T.bs.take b).drop (j + 1), ∀ t rs c t' n,
      x.step T.ft t rs c = .ok (t', n) → t.heard5? = some hd → t'.heard5? = some hd) :
    ∃ hd : Heard, s.heard5? = some hd ∧
      ∀ P : Pub5, P.x = p.own → ∀ (zk : Array (Array OnBytes.E)) (H : Nat),
        T.front + roundsTo T.bs j + blk.rounds.length ≤ H → ∀ (L : Left) (p₀ pv : Pts),
        ptsOf P ⟨zk, (m.st.heard.take H).drop (T.front + roundsTo T.bs j)⟩ = some p₀ →
        pointsOf P.g zk hd L = some pv → ∀ q, PtsTo P.x q p₀ pv := by
  obtain ⟨F, G, hd, rs, hh, hr, h5⟩ := heard5_at_made T Dc hj hblk hM hk
  refine ⟨hd, h5, fun P hx zk H hH L p₀ pv hp₀ hp q => ?_⟩
  rw [← hx] at hh
  exact points_same P (heard_is_ours P _ hh (reads_of_slice hr hH zk) q) hp₀ hp

/-- **The same at the verifier's own road from the field to the points, and as one list of tables.** F: the ledger
that the verifier's road reads. Conditional: as "points_at_made". -/
theorem pointsSame_at_made (Dc : DecidesAs p blk) {b j : Nat} (hj : j < b)
    (hblk : T.bs[j]? = some blk) {k : Coins Bk} {s : First.S} {m : Mid W X} {E : Env}
    (hM : T.Made b k s m E)
    (hk : ∀ hd : Heard, ∀ x ∈ (T.bs.take b).drop (j + 1), ∀ t rs c t' n,
      x.step T.ft t rs c = .ok (t', n) → t.heard5? = some hd → t'.heard5? = some hd) :
    ∃ hd : Heard, s.heard5? = some hd ∧
      ∀ P : Pub5, P.x = p.own → ∀ (zk : Array (Array OnBytes.E)) (H : Nat),
        T.front + roundsTo T.bs j + blk.rounds.length ≤ H → ∀ (F : Fork) (p₀ pv : Pts),
        ptsOf P ⟨zk, (m.st.heard.take H).drop (T.front + roundsTo T.bs j)⟩ = some p₀ →
        ptsFrom P.g zk hd F = some pv → ∀ lk : LookIn, PointsSame P.g lk p₀ pv := by
  obtain ⟨hd, h5, K⟩ := points_at_made T Dc hj hblk hM hk
  refine ⟨hd, h5, fun P hx zk H hH F p₀ pv hp₀ hp lk => ?_⟩
  unfold ptsFrom at hp
  obtain ⟨L, -, hp'⟩ := Option.bind_eq_some_iff.1 hp
  exact points_laid (K P hx zk H hH L p₀ pv hp₀ hp') P.g lk

/-! ## 4 At the border next behind the member -/

/-- Nothing stands between a member and the border next behind it. -/
theorem none_between {α : Type} (l : List α) (j : Nat) : (l.take (j + 1)).drop (j + 1) = [] :=
  List.drop_eq_nil_of_le (by rw [List.length_take]; exact Nat.min_le_left _ _)

/-- "heard5_at_made" at the border next behind the member: the premise on the sub-protocols between falls. -/
theorem heard5_next (Dc : DecidesAs p blk) {j : Nat} (hblk : T.bs[j]? = some blk) {k : Coins Bk}
    {s : First.S} {m : Mid W X} {E : Env} (hM : T.Made (j + 1) k s m E) :
    ∃ (F G : Fork) (hd : Heard) (rs : List Fmt.RoundView),
      hear p.own (F, rs.map noDigest, 0) = some (hd, G, [], 0) ∧
      rs.map (·.drawn) = heardFrom m.st (T.front + roundsTo T.bs j) blk.rounds.length ∧
      s.heard5? = some hd :=
  heard5_at_made T Dc (Nat.lt_succ_self j) hblk hM fun _ x hx => by
    rw [none_between] at hx
    cases hx

/-- "points_at_made" at the border next behind the member. -/
theorem points_next (Dc : DecidesAs p blk) {j : Nat} (hblk : T.bs[j]? = some blk) {k : Coins Bk}
    {s : First.S} {m : Mid W X} {E : Env} (hM : T.Made (j + 1) k s m E) :
    ∃ hd : Heard, s.heard5? = some hd ∧
      ∀ P : Pub5, P.x = p.own → ∀ (zk : Array (Array OnBytes.E)) (H : Nat),
        T.front + roundsTo T.bs j + blk.rounds.length ≤ H → ∀ (L : Left) (p₀ pv : Pts),
        ptsOf P ⟨zk, (m.st.heard.take H).drop (T.front + roundsTo T.bs j)⟩ = some p₀ →
        pointsOf P.g zk hd L = some pv → ∀ q, PtsTo P.x q p₀ pv :=
  points_at_made T Dc (Nat.lt_succ_self j) hblk hM fun _ x hx => by
    rw [none_between] at hx
    cases hx

/-- "pointsSame_at_made" at the border next behind the member. -/
theorem pointsSame_next (Dc : DecidesAs p blk) {j : Nat} (hblk : T.bs[j]? = some blk)
    {k : Coins Bk} {s : First.S} {m : Mid W X} {E : Env} (hM : T.Made (j + 1) k s m E) :
    ∃ hd : Heard, s.heard5? = some hd ∧
      ∀ P : Pub5, P.x = p.own → ∀ (zk : Array (Array OnBytes.E)) (H : Nat),
        T.front + roundsTo T.bs j + blk.rounds.length ≤ H → ∀ (F : Fork) (p₀ pv : Pts),
        ptsOf P ⟨zk, (m.st.heard.take H).drop (T.front + roundsTo T.bs j)⟩ = some p₀ →
        ptsFrom P.g zk hd F = some pv → ∀ lk : LookIn, PointsSame P.g lk p₀ pv :=
  pointsSame_at_made T Dc (Nat.lt_succ_self j) hblk hM fun _ x hx => by
    rw [none_between] at hx
    cases hx

/-! ## 5 Behind the sending that follows the member -/

/-- Where the field holds something an attention segment stands open. -/
theorem att_of_heard5 {s : First.S} {hd : Heard} (h : s.heard5? = some hd) :
    ∃ a, s.here = .att a ∧ a.heard5 = some hd := by
  unfold VerifiableInference.Desc.First.S.heard5? at h
  split at h
  next a ha => exact ⟨a, ha, h⟩
  next => cases h

/-- **A sending's own yes leaves the field**, where it holds something. -/
theorem heard5_sent {Cl' : Type} {q : OnBytes.Params.First} {gp : _root_.Desc.Plain.GPar}
    {link piece moment : Nat} {arrays : Option (List Nat)} {s s₁ : First.S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h1 : (VerifiableInference.Desc.K1.laterAt (Cl := Cl') q gp link piece moment arrays).decide
      s rs gs = .ok s₁) {hd : Heard} (h5 : s.heard5? = some hd) : s₁.heard5? = some hd := by
  obtain ⟨a, ha, e5⟩ := att_of_heard5 h5
  obtain ⟨L', F', hm, -⟩ := H2K5.Honest.k1_leaves h1 ha
  unfold VerifiableInference.Desc.First.S.heard5?
  rw [hm]
  exact e5

/-- **A sending's own yes leaves what the lookup on the calls returned.** -/
theorem g_sent {Cl' : Type} {q : OnBytes.Params.First} {gp : _root_.Desc.Plain.GPar}
    {link piece moment : Nat} {arrays : Option (List Nat)} {s s₁ : First.S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h1 : (VerifiableInference.Desc.K1.laterAt (Cl := Cl') q gp link piece moment arrays).decide
      s rs gs = .ok s₁) {g : OnBytes.Model.Forest.Heard}
    (hq : ∃ a, s.here = .att a ∧ a.g = some g) : ∃ a, s₁.here = .att a ∧ a.g = some g := by
  obtain ⟨a, ha, hg⟩ := hq
  obtain ⟨L', F', hm, -⟩ := H2K5.Honest.k1_leaves h1 ha
  exact ⟨_, hm, hg⟩

/-- **"pointsSame_next" at the state behind the yes of the sending that follows the member.** Conditional: as
"pointsSame_next"; h1: the sending's own yes from the thread's state. -/
theorem pointsSame_sent (Dc : DecidesAs p blk) {j : Nat} (hblk : T.bs[j]? = some blk)
    {k : Coins Bk} {s : First.S} {m : Mid W X} {E : Env} (hM : T.Made (j + 1) k s m E)
    {Cl' : Type} {q : OnBytes.Params.First} {gp : _root_.Desc.Plain.GPar}
    {link piece moment : Nat} {arrays : Option (List Nat)} {s₁ : First.S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h1 : (VerifiableInference.Desc.K1.laterAt (Cl := Cl') q gp link piece moment arrays).decide
      s rs gs = .ok s₁) :
    ∃ hd : Heard, s₁.heard5? = some hd ∧
      ∀ P : Pub5, P.x = p.own → ∀ (zk : Array (Array OnBytes.E)) (H : Nat),
        T.front + roundsTo T.bs j + blk.rounds.length ≤ H → ∀ (F : Fork) (p₀ pv : Pts),
        ptsOf P ⟨zk, (m.st.heard.take H).drop (T.front + roundsTo T.bs j)⟩ = some p₀ →
        ptsFrom P.g zk hd F = some pv → ∀ lk : LookIn, PointsSame P.g lk p₀ pv := by
  obtain ⟨hd, h5, K⟩ := pointsSame_next T Dc hblk hM
  exact ⟨hd, heard5_sent h1 h5, K⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_step_is
#print axioms ProofFile.Honest.K5.k5_step_keeps_g
#print axioms ProofFile.Honest.K5.k5_step_lays
#print axioms ProofFile.Honest.K5.reads_of_slice
#print axioms ProofFile.Honest.K5.heard5_at_made
#print axioms ProofFile.Honest.K5.points_at_made
#print axioms ProofFile.Honest.K5.pointsSame_at_made
#print axioms ProofFile.Honest.K5.none_between
#print axioms ProofFile.Honest.K5.heard5_next
#print axioms ProofFile.Honest.K5.points_next
#print axioms ProofFile.Honest.K5.pointsSame_next
#print axioms ProofFile.Honest.K5.att_of_heard5
#print axioms ProofFile.Honest.K5.heard5_sent
#print axioms ProofFile.Honest.K5.g_sent
#print axioms ProofFile.Honest.K5.pointsSame_sent
