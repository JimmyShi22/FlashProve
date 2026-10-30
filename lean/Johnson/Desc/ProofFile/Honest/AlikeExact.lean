-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AlikeExact.lean: `ExactMember` (Honest/Small/Field.lean: the field
`exact` of `Good`, Honest/Side.lean, at one member, without its hypothesis on the opened columns; it
gives that field at every `pre`) IS CARRIED FROM A PART TO THE SAME PART WITH OTHER MOVES
(`Part.reMove`, Honest/AlikeParts.lean), WHERE THE TWO LISTS OF MOVES SAY THE SAME (`MovesTo`: at
every value of the opened columns); and from a row to the row with other moves (`reRow`, `RowTo`,
Honest/AlikeRow.lean). Written by the authors of the honest side of the output head's own rounds
(K6), in the frame's folder, by its authors' leave; general in the kind. No definition; eight
theorems with their proofs.

What it is not.
  * IT SHOWS `ExactMember` OF NO PART: one sentence is carried from a part of which it is had.
  * THE SIMULATOR IS THE EARLIER MEMBER'S OWN, UNTURNED. Coins are bound under "for all" and never
    taken apart. The measures on both sides are the earlier member's: the function under the left
    one is replaced by an equal function (`shows_re`).
  * Of `Good`'s fields `fits`, `plays`, `acc` and `fresh` nothing is carried here. Both parts are
    parts of honest provers; of a simulator nothing is said but that it is unturned.
  * A RELATION T THAT NO TWO STATES MEET MAKES THE PREMISES ON THE MOVES TRUE FOR NOTHING: whoever
    calls `shows_re` or `exactMember_re` says at which states T is met. `exact_reRow` asks it: every
    state of the second sort has a related one of the first (back, hk).
  * OF T IT IS ASKED THAT IT KEEPS THE INPUT (hT). THAT IT KEEPS THE LIST OF CHALLENGES HEARD IS NOT
    ASKED: no proof here spends it: that the moves say the same from two related states is the
    premise's own to give (q, hM, `RowTo`). A caller's T will as a rule keep both (`StateBy`).
  * That a prover's side HAS a row with other moves, and that the moves say the same, are premises.
  * Nothing on what is passed on: `Side.shows` drops the state behind a part.
  * One side: nothing on a chain, a run or a prover as a whole. Nothing on cost.
  * Nothing on any property of the protocol.

  `shown_alike`        two answers that are alike show the same
  `stopAt_re`          the part with other moves stops where the part stops, if it has as many
  `shows_re`           (A) WHAT THE PART SHOWS, PLAYED ALONE, THE PART WITH OTHER MOVES SHOWS: at
                       the same coins, challenges and positions, from two related stands of a run
                       (the same opened columns among what relates them)
  `exactMember_re`     (B) THE SENTENCE AT ONE MEMBER. hOn: wherever the second entry sentence
                       holds, a related stand of the first run, with the same opened columns, has
                       the first
  `members_re`         the members of a row with other moves are the row's members with other moves
  `membersOf_rounds`, `members_rounds`   a member has as many rounds as its part has moves, where
                       the rounds suffice; so at a side that passes `Side.fits`
  `exact_reRow`        (C) THE SENTENCE AT ALL MEMBERS OF THE ROW. The earlier row's is asked at the
                       entry sentence that always holds: its strongest form: at every value of the
                       opened columns, whatever front holds. Whoever has it under another entry
                       sentence, as one that ties the columns to front, calls `exactMember_re`

By. `steps_alike`, `steps_faced` (Honest/AlikeParts.lean), `play_alike` (Honest/Alike.lean),
`Placed.rounds_eq_sum` (Honest/AlikeRow.lean).
-/
import Johnson.Desc.ProofFile.Honest.AlikeRow
import Johnson.Desc.ProofFile.Honest.Small.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Oracle)
open ProofFile.Honest.Small (ExactMember)

variable {S Cl V W X X' Pb : Type}

/-! ## 1 One part -/

/-- Two answers that are alike, read by two readers that agree on alike values: one value, or none
at both. -/
theorem shown_alike {α β γ : Type} {P : α → β → Prop} {f : α → γ} {g : β → γ}
    (h : ∀ a b, P a b → f a = g b) :
    ∀ {x : Except Refusal α} {y : Except Refusal β}, AnsAlike P x y →
      x.toOption.map f = y.toOption.map g
  | .ok a, .ok b, q => congrArg some (h a b q)
  | .error _, .error _, _ => rfl
  | .ok _, .error _, q => False.elim q
  | .error _, .ok _, q => False.elim q

/-- CONDITIONAL: hn: as many moves. The part with other moves stops where the part stops, and by the
same stop. -/
theorem stopAt_re (p : Part V W X) (mvs : List (Move p.Coins W X'))
    (hn : mvs.length = p.moves.length) (v : Option V) (loc ds : List Fmt.Drawn) :
    (p.reMove mvs).stopAt v loc ds = p.stopAt v loc ds := by
  have e : (p.reMove mvs).moves.length = p.moves.length := hn
  unfold Part.stopAt
  rw [e]
  rfl

/-- CONDITIONAL: hb: the two sides have one sub-protocol; hT: T KEEPS THE INPUT; hn, hr: as many
moves as the part has, and as many rounds; hm: the two stands of a run are related: the same
challenges for the stops, the same rounds shown and the same opened columns, the states in T; q:
from them the two lists of moves say the same, at every value of the opened columns, not at the
stands' own alone: more than the end reads. **(A) WHAT THE PART SHOWS IS WHAT THE PART WITH OTHER
MOVES SHOWS.** -/
theorem shows_re (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (σ' : Side S Cl V W X' Pb)
    (hb : σ'.block = σ.block) (u : Member V W X Pb) (mvs : List (Move u.part.Coins W X'))
    (T : State W X → State W X' → Prop) (hT : ∀ t t', T t t' → t.input = t'.input)
    (hn : mvs.length = u.part.moves.length) (hr : u.rounds.length = u.part.moves.length)
    (c : u.part.Coins) (m : Mid W X) (m' : Mid W X') (hm : MidBy T m m')
    (q : MovesTo c T u.part.moves mvs m.st m'.st m.seen) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) :
    σ.shows φ u c m ds asks =
      σ'.shows φ ⟨u.number, u.rounds, u.part.reMove mvs, u.sim⟩ c m' ds asks := by
  have hi : m'.st.input = m.st.input := (hT _ _ hm.2.2).symm
  have a := steps_alike u.part mvs σ.block.name ⟨σ.block.place, u.number⟩ u.rounds
    (φ.sees m.st.input) c T m m' hn hr hm.1 hm.2.1 q
  have f := steps_faced u.part mvs σ.block.name ⟨σ.block.place, u.number⟩ u.rounds
    (φ.sees m.st.input) c hn
  have e := shown_alike (f := fun y => shownOf y.1 asks) (g := fun y => shownOf y.1 asks)
    (fun _ _ r => congrArg (fun l => shownOf l asks) r.1)
    (play_alike (MidBy T) _ _ ds [] m m' f a)
  unfold Side.shows
  rw [hb, hi]
  exact e

/-- CONDITIONAL: hb, hT (T KEEPS THE INPUT), hn, hr as at `shows_re`; hM: from every two related
states, at all coins, whatever rounds were shown and whatever the opened columns, the two lists of
moves say the same; hOn (the related stand holds the second stand's own opened columns: `MidBy`);
he: the sentence at the member u. **(B) THE SENTENCE AT THE MEMBER WITH OTHER MOVES.** Its simulator
is u's. -/
theorem exactMember_re (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (σ' : Side S Cl V W X' Pb)
    (hb : σ'.block = σ.block) (u : Member V W X Pb) (mvs : List (Move u.part.Coins W X'))
    (T : State W X → State W X' → Prop) (hT : ∀ t t', T t t' → t.input = t'.input)
    (hn : mvs.length = u.part.moves.length) (hr : u.rounds.length = u.part.moves.length)
    (hM : ∀ c t t' seen, T t t' → MovesTo c T u.part.moves mvs t t' seen) (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (On' : (u : Member V W X' Pb) → CsAll u.part.carries → Mid W X' → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (hOn : ∀ ca m' front, On' ⟨u.number, u.rounds, u.part.reMove mvs, u.sim⟩ ca m' front →
      ∃ m, MidBy T m m' ∧ On u ca m front)
    (he : ExactMember φ σ chain firstTree On bud u) :
    ExactMember φ σ' chain firstTree On' bud ⟨u.number, u.rounds, u.part.reMove mvs, u.sim⟩ := by
  intro ca m' front ds asks hO hs hd hbd hh hst
  obtain ⟨m, hm, hOm⟩ := hOn ca m' front hO
  have hi : m.st.input = m'.st.input := hT _ _ hm.2.2
  have hst' : u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid := by
    rw [hi, hm.1, ← stopAt_re u.part mvs hn]
    exact hst
  have k := he ca m front ds asks hOm ((congrArg Seen.rounds hm.2.1).trans hs) hd hbd hh hst'
  have fe : (fun c : Cs u.part.takes × CsAll u.part.spends =>
        σ.shows φ u (c.1, c.2, ca) m ds asks) =
      fun c => σ'.shows φ ⟨u.number, u.rounds, u.part.reMove mvs, u.sim⟩ (c.1, c.2, ca) m' ds
        asks :=
    funext fun c => shows_re φ σ σ' hb u mvs T hT hn hr (c.1, c.2, ca) m m' hm
      (hM _ _ _ _ hm.2.2) ds asks
  rw [fe, hi] at k
  exact k

/-! ## 2 A row -/

/-- CONDITIONAL: `RowTo`. **The members of the row with other moves are the row's members with other
moves**: the same numbers, rounds and simulators. ss: the simulators. -/
theorem members_re (T : State W X → State W X' → Prop) :
    ∀ (ps : List (Part V W X)) (R : ReRow X' ps) (ss : List (Sim Pb)) (j : Nat)
      (rs : List (Fmt.DeclaredRound × List Oracle)), RowTo T ps R →
      ∀ u' ∈ membersOf ((reRow ps R).zip ss) j rs, ∃ u ∈ membersOf (ps.zip ss) j rs,
        ∃ mvs : List (Move u.part.Coins W X'), mvs.length = u.part.moves.length ∧
          (∀ c t t' seen, T t t' → MovesTo c T u.part.moves mvs t t' seen) ∧
          u' = ⟨u.number, u.rounds, u.part.reMove mvs, u.sim⟩
  | [], _, _, _, _, _, u', h => by
    cases (show u' ∈ ([] : List (Member V W X' Pb)) from h)
  | _ :: _, _, [], _, _, _, u', h => by
    cases (show u' ∈ ([] : List (Member V W X' Pb)) from h)
  | p :: ps, R, s :: ss, j, rs, hR, u', h => by
    have hlen : R.1.length = p.moves.length := hR.1.1
    have h' : u' ∈ (⟨j, rs.take R.1.length, p.reMove R.1, s⟩ : Member V W X' Pb) ::
        membersOf ((reRow ps R.2).zip ss) (j + 1) (rs.drop R.1.length) := h
    rw [hlen] at h'
    have h0 : membersOf ((p :: ps).zip (s :: ss)) j rs =
        (⟨j, rs.take p.moves.length, p, s⟩ : Member V W X Pb) ::
          membersOf (ps.zip ss) (j + 1) (rs.drop p.moves.length) := rfl
    rw [h0]
    rcases List.mem_cons.1 h' with rfl | h2
    · exact ⟨⟨j, rs.take p.moves.length, p, s⟩, List.mem_cons_self .., R.1, hlen, hR.1.2, rfl⟩
    · obtain ⟨u, hu, mvs, a, b, c⟩ :=
        members_re T ps R.2 ss (j + 1) (rs.drop p.moves.length) hR.2 u' h2
      exact ⟨u, List.mem_cons_of_mem _ hu, mvs, a, b, c⟩

/-- CONDITIONAL: the rounds suffice for the row's moves. A member has as many rounds as its part has
moves. -/
theorem membersOf_rounds : ∀ (row : List (Part V W X × Sim Pb)) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)), (row.map (·.1.moves.length)).sum ≤ rs.length →
    ∀ u ∈ membersOf row j rs, u.rounds.length = u.part.moves.length
  | [], _, _, _, u, h => by
    cases (show u ∈ ([] : List (Member V W X Pb)) from h)
  | x :: l, j, rs, hs, u, h => by
    rw [List.map_cons, List.sum_cons] at hs
    have h' : u ∈ (⟨j, rs.take x.1.moves.length, x.1, x.2⟩ : Member V W X Pb) ::
        membersOf l (j + 1) (rs.drop x.1.moves.length) := h
    rcases List.mem_cons.1 h' with rfl | h2
    · show (rs.take x.1.moves.length).length = x.1.moves.length
      rw [List.length_take]
      omega
    · exact membersOf_rounds l (j + 1) (rs.drop x.1.moves.length)
        (by rw [List.length_drop]; omega) u h2

/-- CONDITIONAL: the side passes `Side.fits`. The same at a side's members. -/
theorem members_rounds {σ : Side S Cl V W X Pb} (hf : σ.fits = true) :
    ∀ u ∈ σ.members, u.rounds.length = u.part.moves.length := by
  unfold Side.fits at hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨_, h1⟩, h2⟩ := hf
  unfold Side.members
  refine membersOf_rounds σ.row 0 _ ?_
  rw [List.length_zip, h2, Nat.min_self, ← h1, Placed.rounds_eq_sum]
  show _ ≤ ((σ.row.map (·.1)).map (·.moves.length)).sum
  rw [List.map_map]
  exact Nat.le_refl _

/-- CONDITIONAL: hb: one sub-protocol; hp, hp': the first side's row is the parts ps with the
simulators ss, the second's the parts with other moves with the same simulators; hT: T KEEPS THE
INPUT; hR: `RowTo`; hf: the first side passes `Side.fits`; back, hk: every state of the second sort
has a related one of the first; he: the sentence at every member of the first side, at the entry
sentence that always holds: there `ExactMember` is asked at every value of the opened columns,
whatever front holds: so where its five other hypotheses hold at two states that differ in the
opened columns alone, with one front, it asks that what the part shows has one law at both
(Honest/Small/Field.lean, Limits).
**(C) THE SENTENCE AT EVERY MEMBER OF THE SECOND SIDE, AT EVERY ENTRY SENTENCE.** -/
theorem exact_reRow (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (σ' : Side S Cl V W X' Pb)
    (hb : σ'.block = σ.block) (ps : List (Part V W X)) (R : ReRow X' ps) (ss : List (Sim Pb))
    (hp : σ.row = ps.zip ss) (hp' : σ'.row = (reRow ps R).zip ss)
    (T : State W X → State W X' → Prop) (hT : ∀ t t', T t t' → t.input = t'.input)
    (hR : RowTo T ps R) (hf : σ.fits = true) (back : State W X' → State W X)
    (hk : ∀ t', T (back t') t') (chain firstTree : Nat)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (he : ∀ u ∈ σ.members, ExactMember φ σ chain firstTree (fun _ _ _ _ => True) bud u)
    (On' : (u : Member V W X' Pb) → CsAll u.part.carries → Mid W X' → Before → Prop) :
    ∀ u' ∈ σ'.members, ExactMember φ σ' chain firstTree On' bud u' := by
  intro u' hu'
  have h1 : u' ∈ membersOf ((reRow ps R).zip ss) 0 (σ.block.rounds.zip σ.block.oracles) := by
    unfold Side.members at hu'
    rw [hp', hb] at hu'
    exact hu'
  obtain ⟨u, hu, mvs, hn, hM, rfl⟩ := members_re T ps R ss 0 _ hR u' h1
  have hu2 : u ∈ σ.members := by
    unfold Side.members
    rw [hp]
    exact hu
  exact exactMember_re φ σ σ' hb u mvs T hT hn (members_rounds hf u hu2) hM chain firstTree
    (fun _ _ _ _ => True) On' bud
    (fun _ m' _ _ => ⟨⟨back m'.st, m'.loc, m'.seen, m'.opened⟩, ⟨rfl, rfl, hk m'.st⟩, True.intro⟩)
    (he u hu2)

end ProofFile.Honest

#print axioms ProofFile.Honest.shown_alike
#print axioms ProofFile.Honest.stopAt_re
#print axioms ProofFile.Honest.shows_re
#print axioms ProofFile.Honest.exactMember_re
#print axioms ProofFile.Honest.members_re
#print axioms ProofFile.Honest.membersOf_rounds
#print axioms ProofFile.Honest.members_rounds
#print axioms ProofFile.Honest.exact_reRow
