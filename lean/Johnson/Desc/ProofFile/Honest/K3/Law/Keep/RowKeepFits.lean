-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Keep/RowKeepFits.lean: the frame's own player goes through on a
lookup's row that passes its tables on (`lookRowKeep`, Honest/K3/RowKeep.lean), and yields the
rounds that the row's parts show when each is played alone. Conditional on `Keeps.Shaped`: each
stage's job has the shape of the stage's call. Stated at the row's letters (`Keeps`): no job and no
store is named. Definitions that the statements need, and theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: a row played alone is `aloneRow`, the state behind it
`endRow`; `NoStops` and `RowFits` are the two hypotheses of `play_row` (all in
Honest/K3/Law/PlayPart.lean); a move sends n scalars (`Sends`, Honest/K3/Law/SumFits.lean) if at all
coins, at all that was shown (every list of rounds, every value of the columns opened) and at every
state it answers with n scalars and no table.

What is defined.
  `RowSends`: every move of every part of a row sends the stated number of scalars.
  `Keeps.Shaped`: the hypothesis on the letters: a job just where the stage has a call, and its
    earlier job has that call as its shape.
  `bareKeeps`: letters whose jobs have the stages' calls as shapes and return empty lists: an
    instance of `Keeps.Shaped`, for that purpose alone.
  `rowKeepOf`: the kept row over a list of stages, each with its number.

What is shown. General in the row:
  `fits_of_sendsAt`: `fits_of_sends` (Honest/K3/Law/RowPlays.lean) at any type of what is passed on.
  `rowFits_of_sends`, `aloneRow_of_sends`: a row with `RowSends` meets `RowFits` at entries that
    state these numbers of scalars; and played alone it answers, at as many challenges as it has
    moves.
  `sends_withPass`, `sends_lastHand`, `keepPart_sends`: replacing what moves pass on keeps what they
    send; so `keepPart` sends what `scalarsOf` states at the earlier job's shape, where no variable
    of that shape has just one coefficient.
Of the kept row:
  `noStops_keep`: **no part of the row ever stops**: without a hypothesis.
  `partKeep_sends`, `rowKeep_sends`: each part sends what its stage's call states.
  `rowFits_keep`: **every message of the row has the shape of the planner's entry.**
  `aloneRow_keep_some`: played alone, the row answers.
  `play_rowKeep`: **the frame's player goes through on the row's steps and yields the rounds of the
    row played alone**; with the state, the challenges and the rounds that it leaves, and what each
    played round bears: the lookup's place, that a half made it, no table.
  `bare_shaped`, `Keeps.Lawful.shaped`: `Keeps.Shaped` has an instance; `Keeps.Lawful`
    (Honest/K3/Law/Keep/RowKeepLaw.lean) gives it.

Hypotheses that remain, by name.
  `hK : Kp.Shaped a.face`: for whoever fills the letters to show.
  `hv`: (in `keepPart_sends`) no variable of the earlier job's shape has just one coefficient. `hL`:
    (in `Keeps.Lawful.shaped`) `Keeps.Lawful`.
  `hok : a.face.ok = true`, `hes : entriesFit a.face es = true`: the tests on the lookup's numbers,
    and that the entries are the verifier's but for the work: what `RowPlaysFull`
    (Honest/K3/Law/RowPlays.lean) asks for the earlier row.
  `hd : ds.length = es.length`: as many challenges as entries.

Imported: Honest/SumKeep.lean and Honest/SumLaw/.

Users. Honest/K3/Law/Keep/SeatKeepFits.lean and Honest/K3/Law/Keep/SeatPlays.lean
[not in this library] import this file; Honest/K3/Law/Keep/SameRounds.lean points here in its
limits.

Limits. It says that rounds come and whose they are; nothing on what they are worth, and nothing
here ties them to the earlier row's (that is Honest/K3/Law/Keep/RowKeepLaw.lean's). The row is the
one typed at its own state (`lookRowKeep`): the row seated by `Part.lift` (`proverSideOfLookupInChainKeepingTablesAtOneOwner`) is not
spoken of. Nothing on how long a move takes.
The state in front of a play is laid of the letter seen (its rounds and its columns opened); behind
the play the columns opened stand as they stood in front.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.RowKeepLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3

/-- **Each stage's job has the shape of the stage's call**, and there is a job just where there is a
call. A definition, meant as a hypothesis. -/
def Keeps.Shaped (Kp : Keeps) (f : LFace) : Prop :=
  ∀ s, (Kp.job s).map (·.base.shape) = s.call f

/-- Letters whose jobs have the stages' calls as shapes and return empty lists. -/
def bareKeeps (f : LFace) : Keeps :=
  { job := fun s => (s.call f).map fun k =>
      { base :=
          { shape := k, points := fun _ _ => [], lead := fun _ _ => [], round := fun _ _ _ => []
            inY := fun _ _ _ _ => [], ends := fun _ _ _ => [] }
        start := fun _ _ _ => ⟨[], [], 0, #[], []⟩
        bind := fun K _ => K, round := fun _ => [], inY := fun _ _ => [], ends := fun _ => [] }
    store := fun _ _ => ⟨#[], #[], #[], #[]⟩ }

/-- `Keeps.Shaped` has an instance. -/
theorem bare_shaped (f : LFace) : (bareKeeps f).Shaped f := fun s => by
  show ((s.call f).map _).map _ = s.call f
  cases s.call f <;> rfl

/-- `Keeps.Lawful` gives `Keeps.Shaped`. -/
theorem Keeps.Lawful.shaped {Kp : Keeps} {R : Reads} {J : LookJobs Ask} {a : At}
    (hL : Kp.Lawful R J a) : Kp.Shaped a.face := fun s => by
  cases hk : s.call a.face with
  | none => rw [hL.job_none s hk]; rfl
  | some k =>
    obtain ⟨Jk, h1, h2⟩ := hL.job_some s k hk
    rw [h1]
    show some Jk.base.shape = some k
    rw [h2]
    rfl

end ProofFile.Honest.K3

namespace ProofFile.Honest.K3.Law
open OnBytes (E)
open VerifiableInference.Desc (Oracle)
open VerifiableInference.Desc.K3 (entriesV entriesFit)
open ProofFile.Honest.SumLaw (alone aloneFrom)

variable {V W X K C : Type}

/-! ## 1 General in the row -/

/-- Every move of every part of the row sends the stated number of scalars. -/
def RowSends (nss : List (List Nat)) (ps : List (Part V W X)) : Prop :=
  AllTwo (fun (ns : List Nat) (p : Part V W X) => AllTwo Sends ns p.moves) nss ps

/-- `fits_of_sends` at any type of what is passed on. -/
theorem fits_of_sendsAt : ∀ (ns : List Nat) (ms : List (Move C W X)) (es : List Fmt.Entry),
    AllTwo Sends ns ms → es.map cutOf = ns.map (fun n => (24 * n, 0, 0)) →
    AllTwo (fun (r : Fmt.DeclaredRound × List Oracle) (mv : Move C W X) =>
      ∀ (c : C) (sn : Seen) (u : State W X) (y : Sending), mv.say c sn u = .ok y →
        y.fits r.1 r.2 = true) (es.map fun e => (declOf e, ([] : List Oracle))) ms
  | [], [], [], _, _ => trivial
  | [], [], _ :: _, _, h => by simp at h
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim
  | _ :: _, _ :: _, [], _, h => by simp at h
  | n :: ns, mv :: ms, e :: es, h, he => by
    simp only [List.map_cons, List.cons.injEq, cutOf, Prod.mk.injEq] at he
    refine ⟨fun c sn u y hy => ?_, fits_of_sendsAt ns ms es h.2 he.2⟩
    obtain ⟨l, hl, hn⟩ := h.1 c sn u
    rw [hl] at hy
    obtain rfl := Except.ok.inj hy
    exact fits_sayE l e (by rw [hn]; exact he.1.1) he.1.2.1 he.1.2.2

/-- A row whose moves send the stated numbers of scalars meets `RowFits` at entries that state these
numbers. -/
theorem rowFits_of_sends : ∀ (ps : List (Part V W X)) (nss : List (List Nat))
    (es : List Fmt.Entry) (c : RowCoins ps), RowSends nss ps →
    es.map cutOf = nss.flatten.map (fun n => (24 * n, 0, 0)) →
    RowFits ps (es.map fun e => (declOf e, ([] : List Oracle))) c
  | [], [], es, _, _, h => by
    have : es = [] := by simpa using h
    subst this
    rfl
  | [], _ :: _, _, _, hs, _ => hs.elim
  | _ :: _, [], _, _, hs, _ => hs.elim
  | p :: ps, ns :: nss, es, c, hs, h => by
    have hm : ns.length = p.moves.length := allTwo_length hs.1
    rw [List.flatten_cons, List.map_append] at h
    have hn : (ns.map fun n => (24 * n, 0, 0)).length = p.moves.length := by
      rw [List.length_map, hm]
    have h1 : (es.take p.moves.length).map cutOf = ns.map fun n => (24 * n, 0, 0) := by
      rw [List.map_take, h]
      exact List.take_left' hn
    have h2 : (es.drop p.moves.length).map cutOf = nss.flatten.map fun n => (24 * n, 0, 0) := by
      rw [List.map_drop, h]
      exact List.drop_left' hn
    have hlen : p.moves.length ≤ es.length := by
      have := congrArg List.length h
      simp only [List.length_map, List.length_append] at this
      omega
    refine ⟨?_, fun r hr sn u y hy => ?_, ?_⟩
    · rw [List.length_map]
      exact hlen
    · rw [← List.map_take] at hr
      exact allTwo_zip (fits_of_sendsAt _ _ _ hs.1 h1) r hr c.1 sn u y hy
    · rw [← List.map_drop]
      exact rowFits_of_sends ps nss _ c.2 hs.2 h2

/-- Such a row, played alone, answers, at as many challenges as it has moves. -/
theorem aloneRow_of_sends : ∀ (ps : List (Part V W X)) (nss : List (List Nat)) (c : RowCoins ps)
    (t : State W X) (seen : Seen) (ds : List Fmt.Drawn), RowSends nss ps →
    ds.length = nss.flatten.length → ∃ y, aloneRow ps c t seen ds = some y
  | [], [], _, _, _, [], _, _ => ⟨[], rfl⟩
  | [], [], _, _, _, _ :: _, _, h => by simp at h
  | [], _ :: _, _, _, _, _, hs, _ => hs.elim
  | _ :: _, [], _, _, _, _, hs, _ => hs.elim
  | p :: ps, ns :: nss, c, t, seen, ds, hs, h => by
    have hm : ns.length = p.moves.length := allTwo_length hs.1
    rw [List.flatten_cons, List.length_append] at h
    obtain ⟨y₁, hy₁⟩ := aloneFrom_some c.1 p.moves t seen (ds.take p.moves.length)
      (fun mv hmv sn u => by
        obtain ⟨l', hl', _⟩ := allTwo_right (Q := fun mv => ∀ c sn u, ∃ l' : List E,
          mv.say c sn u = .ok (sayE l') ∧ True) (fun n b hb c sn u => by
            obtain ⟨l', h1, _⟩ := hb c sn u
            exact ⟨l', h1, trivial⟩) hs.1 mv hmv c.1 sn u
        exact ⟨_, hl'⟩)
      (by rw [List.length_take]; omega)
    obtain ⟨y₂, hy₂⟩ := aloneRow_of_sends ps nss c.2
      (endFrom p.moves t (ds.take p.moves.length)) (seen.plus y₁) (ds.drop p.moves.length) hs.2
      (by rw [List.length_drop]; omega)
    refine ⟨y₁ ++ y₂, ?_⟩
    have hy₁' : alone p c.1 t seen (ds.take p.moves.length) = some y₁ := hy₁
    show (alone p c.1 t seen (ds.take p.moves.length)).bind (fun x =>
      (aloneRow ps c.2 (endFrom p.moves t (ds.take p.moves.length)) (seen.plus x)
        (ds.drop p.moves.length)).map (x ++ ·)) = _
    rw [hy₁']
    show (aloneRow ps c.2 _ (seen.plus y₁) _).map (y₁ ++ ·) = _
    rw [hy₂]
    rfl

/-- Moves with what they pass on replaced send what they sent. -/
theorem sends_withPass (pass : Nat → State W X → X) :
    ∀ (ns : List Nat) (ms : List (Move C W X)) (n : Nat),
      AllTwo Sends ns ms → AllTwo Sends ns (withPass pass n ms)
  | [], [], _, _ => trivial
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | _ :: ns, _ :: ms, n, h => ⟨h.1, sends_withPass pass ns ms (n + 1) h.2⟩

/-- The same where the last move alone is turned. -/
theorem sends_lastHand (g : State W X → X) : ∀ (ms : List (Move C W X)) (ns : List Nat),
    AllTwo Sends ns ms → AllTwo Sends ns (lastHandMoves g ms)
  | [], _, h => h
  | [_], [], h => h.elim
  | [_], _ :: _, h => ⟨h.1, h.2⟩
  | _ :: _ :: _, [], h => h.elim
  | _ :: mv' :: l, _ :: ns, h => ⟨h.1, sends_lastHand g (mv' :: l) ns h.2⟩

/-- **`keepPart` sends, round by round, as many scalars as `scalarsOf` states** at the earlier job's
shape, whatever the job's functions return, where no variable of that shape has just one
coefficient. -/
theorem keepPart_sends (name endName : String) (J : KeepJob W X K)
    (hv : ∀ v ∈ J.base.shape.vs, v.d ≠ 1) :
    AllTwo Sends (scalarsOf J.base.shape) (keepPart (V := V) name endName J).moves :=
  sends_withPass J.pass _ _ 0 (sumPart_sends name endName J.job hv)

/-! ## 2 The kept row -/

/-- The kept row over a list of stages, each with its number. -/
abbrev rowKeepOf (Kp : Keeps) (a : At) (V : Type) (l : List (Stage × Nat)) :
    List (Part V Ask RowOwn) :=
  l.map fun x => partKeep Kp a x.1 x.2

theorem partKeep_noStops (Kp : Keeps) (a : At) (s : Stage) (i : Nat) :
    (∀ f o, (partKeep (V := V) Kp a s i).bad f o = none) ∧
      ∀ v f o, (partKeep (V := V) Kp a s i).hid v f o = none := by
  cases hj : Kp.job s with
  | none =>
    by_cases hs : s = .alpha
    · subst hs
      rw [partKeep_alpha Kp a i hj]
      exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
    · rw [partKeep_none Kp a s i hj hs]
      exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  | some Jk =>
    by_cases hs : s = .bits
    · subst hs
      rw [partKeep_bits Kp a i Jk hj]
      exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
    · rw [partKeep_some Kp a s i Jk hj hs]
      exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- **No part of the kept row ever stops.** -/
theorem noStops_keep (Kp : Keeps) (a : At) : NoStops (lookRowKeep (V := V) Kp a) := by
  intro p hp
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 hp
  exact partKeep_noStops Kp a x.1 x.2

/-- Each part of the kept row sends what its stage's call states. Conditional on `Keeps.Shaped`. -/
theorem partKeep_sends (Kp : Keeps) (a : At) (hK : Kp.Shaped a.face) (s : Stage) (i : Nat) :
    AllTwo Sends (stageCounts a.face s) (partKeep (V := V) Kp a s i).moves := by
  have hs' := hK s
  cases hj : Kp.job s with
  | none =>
    rw [hj] at hs'
    have hc : s.call a.face = none := hs'.symm
    have e : stageCounts a.face s = [0] := by simp only [stageCounts, hc]
    rw [e]
    by_cases hs : s = .alpha
    · subst hs
      rw [partKeep_alpha Kp a i hj]
      exact ⟨fun _ _ _ => ⟨[], rfl, rfl⟩, trivial⟩
    · rw [partKeep_none Kp a s i hj hs]
      exact ⟨fun _ _ _ => ⟨[], rfl, rfl⟩, trivial⟩
  | some Jk =>
    rw [hj] at hs'
    have hc : s.call a.face = some Jk.base.shape := hs'.symm
    have e : stageCounts a.face s = scalarsOf Jk.base.shape := by simp only [stageCounts, hc]
    have h0 := keepPart_sends (V := V) (sumName a.place i) (endName a.place i) Jk
      (stage_vars a.face s _ hc)
    rw [e]
    by_cases hs : s = .bits
    · subst hs
      rw [partKeep_bits Kp a i Jk hj]
      exact sends_lastHand _ _ _ h0
    · rw [partKeep_some Kp a s i Jk hj hs]
      exact h0

theorem rowKeep_sends (Kp : Keeps) (a : At) (hK : Kp.Shaped a.face) :
    ∀ l : List (Stage × Nat),
      RowSends (l.map fun x => stageCounts a.face x.1) (rowKeepOf Kp a V l)
  | [] => trivial
  | x :: l => ⟨partKeep_sends Kp a hK x.1 x.2, rowKeep_sends Kp a hK l⟩

/-- What the stages' entries state, stage by stage. -/
theorem cut_flat (f : LFace) : ∀ l : List (Stage × Nat),
    (l.flatMap fun x => Stage.entries f x.1).map cutOf =
      (l.map fun x => stageCounts f x.1).flatten.map fun n => (24 * n, 0, 0)
  | [] => rfl
  | x :: l => by
    rw [List.flatMap_cons, List.map_append, List.map_cons, List.flatten_cons, List.map_append,
      entries_cut, cut_flat f l]

/-- Entries that are the verifier's but for the work state what the stages' calls state. -/
theorem keep_cut (f : LFace) (hok : f.ok = true) (es : List Fmt.Entry)
    (hes : entriesFit f es = true) :
    es.map cutOf =
      ((stages f).zipIdx.map fun x => stageCounts f x.1).flatten.map fun n => (24 * n, 0, 0) := by
  have h2 := two_le_planes_of_ok _ hok
  rw [← cut_flat, flatMap_zipIdx_fst (Stage.entries f), entries_stages _ h2]
  have e : (es.map fun e => { e with work := 0 }) = entriesV f := eq_of_beq hes
  rw [← e, List.map_map]
  rfl

/-- **Every message of the kept row has the shape of the planner's entry.** Conditional on
`Keeps.Shaped`, on the tests on the lookup's numbers (hok), and on entries that are the verifier's
but for the work (hes). -/
theorem rowFits_keep (Kp : Keeps) (a : At) (hK : Kp.Shaped a.face) (hok : a.face.ok = true)
    (es : List Fmt.Entry) (hes : entriesFit a.face es = true)
    (c : RowCoins (lookRowKeep (V := V) Kp a)) :
    RowFits (lookRowKeep Kp a) (es.map fun e => (declOf e, ([] : List Oracle))) c :=
  rowFits_of_sends (rowKeepOf Kp a V (stages a.face).zipIdx) _ es c (rowKeep_sends Kp a hK _)
    (keep_cut a.face hok es hes)

/-- Played alone, the kept row answers. Conditional on `Keeps.Shaped`, on hok and hes as in
`rowFits_keep`, and on as many challenges as entries (hd). -/
theorem aloneRow_keep_some (Kp : Keeps) (a : At) (hK : Kp.Shaped a.face) (hok : a.face.ok = true)
    (es : List Fmt.Entry) (hes : entriesFit a.face es = true)
    (c : RowCoins (lookRowKeep (V := V) Kp a)) (t : State Ask RowOwn) (seen : Seen)
    (ds : List Fmt.Drawn) (hd : ds.length = es.length) :
    ∃ x, aloneRow (lookRowKeep Kp a) c t seen ds = some x :=
  aloneRow_of_sends (rowKeepOf Kp a V (stages a.face).zipIdx) _ c t seen ds
    (rowKeep_sends Kp a hK _) (by
      have := congrArg List.length (keep_cut a.face hok es hes)
      simp only [List.length_map] at this
      rw [hd, this])

/-- **The frame's player goes through on the kept row's steps and yields the rounds of the row
played alone.** Conditional on `Keeps.Shaped`, on hok and hes as in `rowFits_keep`, and on as many
challenges as entries (hd). -/
theorem play_rowKeep (Kp : Keeps) (a : At) (hK : Kp.Shaped a.face) (hok : a.face.ok = true)
    (es : List Fmt.Entry) (hes : entriesFit a.face es = true) (name : String) (v : Option V)
    (c : RowCoins (lookRowKeep (V := V) Kp a)) (ds : List Fmt.Drawn) (hd : ds.length = es.length)
    (back : List Fmt.RoundView) (t : State Ask RowOwn) (loc : List Fmt.Drawn) (seen : Seen) :
    ∃ y x, aloneRow (lookRowKeep Kp a) c t seen ds = some x ∧
      play (rowSteps name a.place v (lookRowKeep Kp a) 0
        (es.map fun e => (declOf e, ([] : List Oracle))) c) ds back
        ⟨t, loc, seen.rounds, seen.opened⟩ = .ok y ∧
      roundsOf y.1 = x ∧
      y.2 = ⟨endRow (lookRowKeep (V := V) Kp a) t ds, loc ++ ds, seen.rounds ++ x, seen.opened⟩ ∧
      ∀ q ∈ y.1, q.place = a.place ∧ q.told = true ∧ q.tables = [] := by
  obtain ⟨x, hx⟩ := aloneRow_keep_some Kp a hK hok es hes c t seen ds hd
  obtain ⟨y, hy, hy1, hy2⟩ := play_row name a.place v _ 0 _ c ds back t loc seen x
    (noStops_keep Kp a) (rowFits_keep Kp a hK hok es hes c) hx
  exact ⟨y, x, hx, hy, hy1, hy2, played_row name a.place v _ 0 _ c ds back _ y hy
    (fun r hr => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.1 hr
      rfl)⟩

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.bare_shaped
#print axioms ProofFile.Honest.K3.Keeps.Lawful.shaped
#print axioms ProofFile.Honest.K3.Law.fits_of_sendsAt
#print axioms ProofFile.Honest.K3.Law.rowFits_of_sends
#print axioms ProofFile.Honest.K3.Law.aloneRow_of_sends
#print axioms ProofFile.Honest.K3.Law.sends_withPass
#print axioms ProofFile.Honest.K3.Law.sends_lastHand
#print axioms ProofFile.Honest.K3.Law.keepPart_sends
#print axioms ProofFile.Honest.K3.Law.partKeep_noStops
#print axioms ProofFile.Honest.K3.Law.noStops_keep
#print axioms ProofFile.Honest.K3.Law.partKeep_sends
#print axioms ProofFile.Honest.K3.Law.rowKeep_sends
#print axioms ProofFile.Honest.K3.Law.cut_flat
#print axioms ProofFile.Honest.K3.Law.keep_cut
#print axioms ProofFile.Honest.K3.Law.rowFits_keep
#print axioms ProofFile.Honest.K3.Law.aloneRow_keep_some
#print axioms ProofFile.Honest.K3.Law.play_rowKeep
