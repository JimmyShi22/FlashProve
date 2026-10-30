-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Keep/SeatKeepFits.lean: the frame's own player on a lookup's
row that passes its tables on, seated in a chain's letters (`proverSideOfLookupInChainKeepingTablesAtOneOwner`, Honest/K3/RowKeep.lean):
it goes through; and at the filling `fastKeeps` it yields the rounds, and leaves the state, that it
yields and leaves on the seated earlier row (`proverSideOfLookupInChainAtOneOwner`, Honest/K3/Row.lean). The first is
conditional on `Keeps.Shaped`; the second on the hypotheses of `sameSeat_real` and
`sameSeatEnd_real` (Honest/K3/Law/Keep/SameRounds.lean); both on the tests on the lookup's numbers
and entries. Theorems alone.

Terms. Honest/K3/GLOSSARY.md. In this file: `RowSends`, `Keeps.Shaped`:
Honest/K3/Law/Keep/RowKeepFits.lean; get reads the row's own state in what the chain's parts pass
on, set lays it there.

What is shown. General in the row:
  `rowSends_sum`: a row with `RowSends` has as many moves as numbers are stated.
  `sends_lift`, `rowSends_lift`: a row seated by `Part.lift` sends what the row sends: at any get
    and set; no law of theirs is needed.
  `play_of_sends`: **a row that never stops and has `RowSends`**, at entries that state these
    numbers and at as many challenges: played alone it answers, and the frame's player goes through
    on its steps and yields the same rounds; with all that the player leaves, and what each played
    round bears.
Of the two rows:
  `partOf_sends`, `rowOld_sends`, `noStops_old`: the earlier row sends what its stages' calls state
    and never stops: at any reader of the points (Honest/K3/Law/RowPlays.lean has it at one).
  `play_seatKeep`: **the player goes through on the seated kept row**, at the row's letters.
  `play_seatOld`: the same of the seated earlier row.
  `fastKeeps_shaped`: `Keeps.Shaped` holds at the filling.
  `playSeat_same`: **at the filling and at the reader that a lot seats, the player goes through on
    both seated rows, yields the same rounds and leaves the same state**: the chain's state as it
    was, with the row's challenges heard.

Hypotheses that remain, by name.
  `hK : Kp.Shaped a.face` (`play_seatKeep` alone): for whoever fills the letters to show; at
    `fastKeeps` it is shown.
  `hok : a.face.ok = true`, `hes : entriesFit a.face es = true`, `hd : ds.length = es.length`: as in
    Honest/K3/Law/Keep/RowKeepFits.lean.
  In `playSeat_same`, as in `sameSeat_real` and `sameSeatEnd_real`: `hgs`, `hss`, `hsg`: the three
    laws of get and set; `h0`: in front of the row get reads `rowOwn₀`; `hw`: the input is settled
    at a.base; `hb`: a.base challenges at least are heard in front of the row; `hc`: the two rows'
    coins are read alike (`sameSeatCoins`: for all coins of the kept row there are such coins of the
    earlier).
  In `play_of_sends`: `hN`, `hS`, `hcut`: `NoStops`; `RowSends`; the entries state these numbers of
    scalars.

Imported: Honest/SumKeepLaw.lean, Honest/SumKeep.lean and Honest/SumLaw/.

Users. Honest/K3/Law/Keep/LentAlike.lean [not in this library] and
Honest/K3/Law/Keep/LotsPlayed.lean [not in this library] import this file.

Beside it. Honest/K3/Law/Keep/SeatPlays.lean [not in this library] (not imported) holds the seated
kept row, played, against the seated earlier row played alone, at the row's letters too
(`playSeat_keep`, `playSeat_real`). This file holds played against played; that the player goes
through under `Keeps.Shaped` alone; and the lemma that is general in the row.

Limits. One row at its place: nothing on a chain of several places, on a lot, or on the book's
tests. Of what was played, the rounds are compared (`roundsOf`), not what else a played round bears.
It says that rounds come and that they are the same; nothing on what they are worth. Nothing on how
long a move takes.
The state in front of a play is laid of the letter seen (its rounds and its columns opened); behind
the play the columns opened stand as they stood in front.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.RowKeepFits
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.SameRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E)
open VerifiableInference.Desc (Oracle Place)
open VerifiableInference.Desc.K3 (entriesFit)
open ProofFile.Honest.SumLaw (alone aloneFrom)

variable {V V' W W' X Y C V₁ W₁ X₁ : Type}

/-! ## 1 General in the row -/

/-- A row with `RowSends` has as many moves as numbers are stated. -/
theorem rowSends_sum : ∀ (nss : List (List Nat)) (ps : List (Part V W X)), RowSends nss ps →
    (ps.map (·.moves.length)).sum = nss.flatten.length
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | ns :: nss, p :: ps, h => by
    rw [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append,
      rowSends_sum nss ps h.2, allTwo_length h.1]

/-- Seated moves send what the moves send. -/
theorem sends_lift (wit : W → W') (get : X → Y) (set : X → Y → X) :
    ∀ (ns : List Nat) (ms : List (Move C W' Y)),
      AllTwo Sends ns ms → AllTwo Sends ns (ms.map (Move.lift wit get set))
  | [], [], _ => trivial
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: ns, _ :: ms, h =>
    ⟨fun c sn u => h.1 c sn (u.narrow wit get), sends_lift wit get set ns ms h.2⟩

/-- A seated row sends what the row sends. -/
theorem rowSends_lift (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X) :
    ∀ (nss : List (List Nat)) (ps : List (Part V' W' Y)),
      RowSends nss ps → RowSends nss (ps.map (Part.lift see wit get set))
  | [], [], _ => trivial
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: nss, p :: ps, h =>
    ⟨sends_lift wit get set _ p.moves h.1, rowSends_lift see wit get set nss ps h.2⟩

/-- **A row that never stops and whose moves send the stated numbers of scalars**, at entries that
state these numbers (hcut) and at as many challenges as entries (hd): played alone it answers, and
the frame's player goes through on its steps and yields the same rounds. -/
theorem play_of_sends (ps : List (Part V W X)) (nss : List (List Nat)) (hN : NoStops ps)
    (hS : RowSends nss ps) (es : List Fmt.Entry)
    (hcut : es.map cutOf = nss.flatten.map (fun n => (24 * n, 0, 0))) (name : String) (pl : Place)
    (v : Option V) (c : RowCoins ps) (ds : List Fmt.Drawn) (hd : ds.length = es.length)
    (back : List Fmt.RoundView) (t : State W X) (loc : List Fmt.Drawn) (seen : Seen) :
    ∃ y x, aloneRow ps c t seen ds = some x ∧
      play (rowSteps name pl v ps 0 (es.map fun e => (declOf e, ([] : List Oracle))) c) ds back
        ⟨t, loc, seen.rounds, seen.opened⟩ = .ok y ∧
      roundsOf y.1 = x ∧ y.2 = ⟨endRow ps t ds, loc ++ ds, seen.rounds ++ x, seen.opened⟩ ∧
      ∀ q ∈ y.1, q.place = pl ∧ q.told = true ∧ q.tables = [] := by
  have hl : ds.length = nss.flatten.length := by
    have := congrArg List.length hcut
    simp only [List.length_map] at this
    rw [hd, this]
  obtain ⟨x, hx⟩ := aloneRow_of_sends ps nss c t seen ds hS hl
  obtain ⟨y, hy, hy1, hy2⟩ := play_row name pl v ps 0 _ c ds back t loc seen x hN
    (rowFits_of_sends ps nss es c hS hcut) hx
  exact ⟨y, x, hx, hy, hy1, hy2, played_row name pl v ps 0 _ c ds back _ y hy
    (fun r hr => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.1 hr
      rfl)⟩

/-! ## 2 The earlier row, at any reader of the points -/

theorem partOf_sends (R : Reads) (J : LookJobs W) (a : At) (s : Stage) (i : Nat) :
    AllTwo Sends (stageCounts a.face s) (partOf (V := V) R J a s i).moves := by
  cases hk : s.call a.face with
  | none =>
    have e : stageCounts a.face s = [0] := by simp only [stageCounts, hk]
    rw [partOf_quiet R J a s i hk, e]
    exact ⟨fun _ _ _ => ⟨[], rfl, rfl⟩, trivial⟩
  | some k =>
    have e : stageCounts a.face s = scalarsOf k := by simp only [stageCounts, hk]
    rw [partOf_call R J a s i k hk, e]
    exact sumPart_sends _ _ (jobOf R J a s k) (stage_vars a.face s k hk)

theorem rowOld_sends (R : Reads) (J : LookJobs W) (a : At) : ∀ l : List (Stage × Nat),
    RowSends (l.map fun x => stageCounts a.face x.1)
      (l.map fun x => partOf (V := V) R J a x.1 x.2)
  | [] => trivial
  | x :: l => ⟨partOf_sends R J a x.1 x.2, rowOld_sends R J a l⟩

/-- No part of the earlier row ever stops. -/
theorem noStops_old (R : Reads) (J : LookJobs W) (a : At) : NoStops (lookRow (V := V) R J a) := by
  intro p hp
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 hp
  cases hk : x.1.call a.face with
  | none =>
    rw [partOf_quiet R J a x.1 x.2 hk]
    exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  | some k =>
    rw [partOf_call R J a x.1 x.2 k hk]
    exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-! ## 3 The two seated rows -/

/-- **The frame's player goes through on the seated kept row**, and yields the rounds of that row
played alone. Conditional on `Keeps.Shaped`, on the tests on the lookup's numbers (hok), on entries
that are the verifier's but for the work (hes), and on as many challenges as entries (hd). No law of
get and set is asked. -/
theorem play_seatKeep (Kp : Keeps) (a : At) (wit : W₁ → Ask) (get : X₁ → RowOwn)
    (set : X₁ → RowOwn → X₁) (hK : Kp.Shaped a.face) (hok : a.face.ok = true)
    (es : List Fmt.Entry) (hes : entriesFit a.face es = true) (name : String) (v : Option V₁)
    (c : RowCoins (proverSideOfLookupInChainKeepingTablesAtOneOwner (V₁ := V₁) Kp wit get set a).parts) (ds : List Fmt.Drawn)
    (hd : ds.length = es.length) (back : List Fmt.RoundView) (t : State W₁ X₁) (loc : List Fmt.Drawn)
    (seen : Seen) :
    ∃ y x, aloneRow (proverSideOfLookupInChainKeepingTablesAtOneOwner Kp wit get set a).parts c t seen ds = some x ∧
      play (rowSteps name a.place v (proverSideOfLookupInChainKeepingTablesAtOneOwner Kp wit get set a).parts 0
        (es.map fun e => (declOf e, ([] : List Oracle))) c) ds back
        ⟨t, loc, seen.rounds, seen.opened⟩ = .ok y ∧
      roundsOf y.1 = x ∧
      y.2 = ⟨endRow (proverSideOfLookupInChainKeepingTablesAtOneOwner (V₁ := V₁) Kp wit get set a).parts t ds, loc ++ ds,
        seen.rounds ++ x, seen.opened⟩ ∧
      ∀ q ∈ y.1, q.place = a.place ∧ q.told = true ∧ q.tables = [] :=
  play_of_sends (proverSideOfLookupInChainKeepingTablesAtOneOwner (V₁ := V₁) Kp wit get set a).parts _
    (noStops_liftG (fun _ => ()) wit get set _ (noStops_keep Kp a))
    (rowSends_lift (fun _ => ()) wit get set _ _ (rowKeep_sends Kp a hK (stages a.face).zipIdx))
    es (keep_cut a.face hok es hes) name a.place v c ds hd back t loc seen

/-- The same of the seated earlier row. Conditional on hok, hes and hd. -/
theorem play_seatOld (R : Reads) (J : LookJobs W) (a : At) (wit : W₁ → W)
    (hok : a.face.ok = true) (es : List Fmt.Entry) (hes : entriesFit a.face es = true)
    (name : String) (v : Option V₁)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) R J wit a).parts) (ds : List Fmt.Drawn)
    (hd : ds.length = es.length) (back : List Fmt.RoundView) (t : State W₁ X₁) (loc : List Fmt.Drawn)
    (seen : Seen) :
    ∃ y x, aloneRow (proverSideOfLookupInChainAtOneOwner R J wit a).parts c t seen ds = some x ∧
      play (rowSteps name a.place v (proverSideOfLookupInChainAtOneOwner R J wit a).parts 0
        (es.map fun e => (declOf e, ([] : List Oracle))) c) ds back
        ⟨t, loc, seen.rounds, seen.opened⟩ = .ok y ∧
      roundsOf y.1 = x ∧
      y.2 = ⟨endRow (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) R J wit a).parts t ds, loc ++ ds,
        seen.rounds ++ x, seen.opened⟩ ∧
      ∀ q ∈ y.1, q.place = a.place ∧ q.told = true ∧ q.tables = [] :=
  play_of_sends (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) R J wit a).parts _
    (noStops_liftG (fun _ => ()) wit (fun _ => ()) (fun x _ => x) _ (noStops_old R J a))
    (rowSends_lift (fun _ => ()) wit (fun _ => ()) (fun x _ => x) _ _
      (rowOld_sends R J a (stages a.face).zipIdx))
    es (keep_cut a.face hok es hes) name a.place v c ds hd back t loc seen

/-- `Keeps.Shaped` holds at the filling. -/
theorem fastKeeps_shaped (R : Reads) (row : E → Nat → E) (a : At) :
    (fastKeeps R row a).Shaped a.face :=
  (fastKeeps_lawful R row a).shaped

/-- **At the filling and at the reader that a lot seats: the frame's player goes through on the
seated kept row and on the seated earlier row, yields the same rounds, and leaves the same state**:
the chain's state as it was, with the row's challenges heard. Conditional on hok, hes, hd; on hgs,
hss, hsg (the laws of get and set); on h0 (in front of the row get reads `rowOwn₀`); on hw (the
input is settled at a.base); on hb (a.base challenges at least are heard in front of the row); and
on hc (the two rows' coins are read alike). -/
theorem playSeat_same (row : E → Nat → E) (a : At) (wit : W₁ → Ask) (get : X₁ → RowOwn)
    (set : X₁ → RowOwn → X₁) (hgs : ∀ x y, get (set x y) = y)
    (hss : ∀ x y y', set (set x y) y' = set x y') (hsg : ∀ x, set x (get x) = x)
    (t₁ : State W₁ X₁) (h0 : get t₁.own = rowOwn₀) (hw : Ask.Settled a.base (wit t₁.input))
    (hb : a.base ≤ t₁.heard.length) (hok : a.face.ok = true) (es : List Fmt.Entry)
    (hes : entriesFit a.face es = true) (name : String) (v : Option V₁)
    (c : RowCoins (proverSideOfLookupInChainKeepingTablesAtOneOwner (V₁ := V₁) (fastKeeps theReads row a) wit get set a).parts)
    (c' : RowCoins
      (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) theReads (fastJobs a.face row).asked wit a).parts)
    (hc : RowRel SpentSame _ _
      (unliftG (fun _ => ()) wit get set (lookRowKeep (fastKeeps theReads row a) a) c)
      (unlift (fun _ => ()) wit (lookRow theReads (fastJobs a.face row).asked a) c'))
    (ds : List Fmt.Drawn) (hd : ds.length = es.length) (back : List Fmt.RoundView)
    (loc : List Fmt.Drawn) (seen : Seen) :
    ∃ y y',
      play (rowSteps name a.place v
        (proverSideOfLookupInChainKeepingTablesAtOneOwner (fastKeeps theReads row a) wit get set a).parts 0
        (es.map fun e => (declOf e, ([] : List Oracle))) c) ds back
        ⟨t₁, loc, seen.rounds, seen.opened⟩ = .ok y ∧
      play (rowSteps name a.place v
        (proverSideOfLookupInChainAtOneOwner theReads (fastJobs a.face row).asked wit a).parts 0
        (es.map fun e => (declOf e, ([] : List Oracle))) c') ds back
        ⟨t₁, loc, seen.rounds, seen.opened⟩ = .ok y' ∧
      roundsOf y.1 = roundsOf y'.1 ∧ y.2 = y'.2 ∧
      y.2 = ⟨⟨t₁.input, t₁.heard ++ ds, t₁.own⟩, loc ++ ds,
        seen.rounds ++ roundsOf y.1, seen.opened⟩ := by
  obtain ⟨y, x, hx, hy, hy1, hy2, _⟩ := play_seatKeep (fastKeeps theReads row a) a wit get set
    (fastKeeps_shaped theReads row a) hok es hes name v c ds hd back t₁ loc seen
  obtain ⟨y', x', hx', hy', hy1', hy2', _⟩ := play_seatOld (X₁ := X₁) theReads
    (fastJobs a.face row).asked a wit hok es hes name v c' ds hd back t₁ loc seen
  have hxx : x = x' := by
    have e := sameSeat_real row a wit get set hgs t₁ h0 hw hb c c' hc seen ds
    rw [hx, hx'] at e
    exact Option.some.inj e
  have hcut := congrArg List.length (keep_cut a.face hok es hes)
  simp only [List.length_map] at hcut
  have hlK : ds.length =
      ((lookRowKeep (V := Unit) (fastKeeps theReads row a) a).map (·.moves.length)).sum := by
    rw [hd, hcut]
    exact (rowSends_sum _ _ (rowKeep_sends (fastKeeps theReads row a) a
      (fastKeeps_shaped theReads row a) (stages a.face).zipIdx)).symm
  have hlO : ds.length =
      ((lookRow (V := Unit) theReads (fastJobs a.face row).asked a).map (·.moves.length)).sum := by
    rw [hd, hcut]
    exact (rowSends_sum _ _ (rowOld_sends theReads (fastJobs a.face row).asked a
      (stages a.face).zipIdx)).symm
  have eK := sameSeatEnd_real (V₁ := V₁) row a wit get set hgs hss hsg t₁ h0 hw hb ds hlK
  have eO : endRow (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) theReads (fastJobs a.face row).asked wit
      a).parts t₁ ds = ⟨t₁.input, t₁.heard ++ ds, t₁.own⟩ :=
    endRow_lift_keep (fun _ => ()) wit _ t₁ ds hlO
  rw [eK] at hy2
  rw [eO] at hy2'
  refine ⟨y, y', hy, hy', ?_, ?_, ?_⟩
  · rw [hy1, hy1', hxx]
  · rw [hy2, hy2', hxx]
  · rw [hy2, hy1]

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.rowSends_sum
#print axioms ProofFile.Honest.K3.Law.sends_lift
#print axioms ProofFile.Honest.K3.Law.rowSends_lift
#print axioms ProofFile.Honest.K3.Law.play_of_sends
#print axioms ProofFile.Honest.K3.Law.partOf_sends
#print axioms ProofFile.Honest.K3.Law.rowOld_sends
#print axioms ProofFile.Honest.K3.Law.noStops_old
#print axioms ProofFile.Honest.K3.Law.play_seatKeep
#print axioms ProofFile.Honest.K3.Law.play_seatOld
#print axioms ProofFile.Honest.K3.Law.fastKeeps_shaped
#print axioms ProofFile.Honest.K3.Law.playSeat_same
