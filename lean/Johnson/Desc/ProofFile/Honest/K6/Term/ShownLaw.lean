--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/ShownLaw.lean: general in the kind. A part of a prover's side
whose simulator reads its own coins alone, whose rounds read no table, which never stops, and which
meets `ExactMember` (Honest/Small/Field.lean) with nothing asked of the state before it: WHAT SUCH A
PART SHOWS, PLAYED ALONE, HAS ONE LAW AT ALL STATES. THIS IS THE ONE-TIME PAD's FACT: it is true of any
masked part, WHATEVER IT MASKS, right or wrong; it is the part's MARGINAL law, over spent runs TAKEN as
fresh; it is NOT the law of a run's view, in which other parts show more of the same coins.
`ExactMember` is the text of the field `exact` of `Good` without its premise on the opened columns: it
is asked at more states, so it says MORE than the field, and it is no field of `Good`. From the field
alone the first lemma does not follow by this proof. A file apart, with few imports, because among
many imports Lean's search for "the type of a part's coins has a member" runs out of its budget.

WHAT IT IS NOT. One conditional lemma on the frame's own definitions. No kind is named; nothing is said
of a protocol or a prover. ONE PART AT A TIME, PLAYED ALONE, its spent runs TAKEN as uniform and
independent of the state. Nothing on soundness, completeness or hiding.

  `shownLaw`             the law of what a part shows, played alone: the left side of `exact`
  `pair_of_membersOf`    a member's part and simulator are a pair of the row
  `frontOfSeen`, `frontOfSeen_seen`   a front that holds given earlier rounds and no column
  `readsOf_of_no_read`, `holds_of_no_read`   rounds that read no table ask no column of a front
  `shownLaw_same`        the lemma
  `shownLaw_same_at`     the same from the field's own text, at states whose opened columns fit it
  `shows_isSome_of_exact`   such a part shows something at every coin
-/
import Johnson.Desc.ProofFile.Honest.Small.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Place Oracle)
open ProofFile.Honest.Small

variable {S Cl V W Y Pb : Type}

/-- **The law of what a part shows, played alone**: over its own coins and the runs that it spends,
all uniform; at fixed carried runs, state before the part, challenges and positions. It is the left
side of the field `exact` of `Good` (Honest/Side.lean). -/
noncomputable def shownLaw (φ : Face V W Pb) (σ : Side S Cl V W Y Pb) (u : Member V W Y Pb)
    (ca : CsAll u.part.carries) (m : Mid W Y) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) :=
  (Prob.unif (Cs u.part.takes × CsAll u.part.spends)).map
    fun c => σ.shows φ u (c.1, c.2, ca) m ds asks

/-- A member's part and simulator are a pair of the row. -/
theorem pair_of_membersOf : ∀ (row : List (Part V W Y × Sim Pb)) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (u : Member V W Y Pb), u ∈ membersOf row j rs →
    (u.part, u.sim) ∈ row
  | [], _, _, _, h => absurd h List.not_mem_nil
  | x :: l, j, rs, u, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (pair_of_membersOf l (j + 1) _ u h')

/-- **A front that holds given earlier rounds and no column.** The chain's number that it writes
beside each round is 0; no statement here reads it. -/
def frontOfSeen (seen : List Fmt.RoundView) : Before :=
  ⟨seen.map fun r => (0, ⟨r.vals, []⟩, r.drawn), []⟩

theorem frontOfSeen_seen (seen : List Fmt.RoundView) : (frontOfSeen seen).seen = seen := by
  unfold frontOfSeen Before.seen
  rw [List.map_map]
  exact (List.map_congr_left fun _ _ => rfl).trans (List.map_id seen)

/-- Rounds that read no stored table and open no tree make no read. -/
theorem readsOf_of_no_read (chain firstTree : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) :
    ∀ (decls : List Fmt.DeclaredRound) (ds : List Fmt.Drawn),
      (∀ d ∈ decls, d.stored = [] ∧ d.opens = []) → readsOf chain firstTree stored tree decls ds = []
  | [], _, _ => by unfold readsOf; rfl
  | _ :: _, [], _ => by unfold readsOf; rfl
  | d :: decls, R :: Rs, h => by
    unfold readsOf
    rw [(h d (List.mem_cons_self ..)).1, (h d (List.mem_cons_self ..)).2,
      readsOf_of_no_read chain firstTree stored tree decls Rs
        fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

/-- So every front has all the columns that they ask. -/
theorem holds_of_no_read (f : Before) (chain firstTree : Nat) (decls : List Fmt.DeclaredRound)
    (ds : List Fmt.Drawn) (h : ∀ d ∈ decls, d.stored = [] ∧ d.opens = []) :
    f.holds chain firstTree decls ds = true := by
  unfold Before.holds
  rw [readsOf_of_no_read chain firstTree _ _ decls ds h]
  rfl

/-- CONDITIONAL on its four premises. **What such a part shows, played alone, has one law at all
states.** exact: `ExactMember`, which says more than the field `exact` of `Good`, with nothing asked
of the state. tell: the simulator's output is a function of its own coins alone. reads: the part's
rounds read no table. stops: the part never stops. m, m': any two states of the prover's run before
the part, each with its own input (true of any masked part, whatever it masks). -/
theorem shownLaw_same {φ : Face V W Pb} {σ : Side S Cl V W Y Pb} {chain firstTree : Nat}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop} {u : Member V W Y Pb}
    (exact : ExactMember φ σ chain firstTree (fun _ _ _ _ => True) bud u)
    (tell : ∀ pub pub' front front' ds ds' asks asks' c,
      u.sim.tell pub front ds asks c = u.sim.tell pub' front' ds' asks' c)
    (reads : ∀ d ∈ u.rounds.map (·.1), d.stored = [] ∧ d.opens = [])
    (stops : ∀ v loc ds, u.part.stopAt v loc ds = none)
    (ca ca' : CsAll u.part.carries) (m m' : Mid W Y) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) (hd : drawsFit (u.rounds.map (·.1)) ds = true)
    (hb : bud u.number ds asks) :
    shownLaw φ σ u ca m ds asks = shownLaw φ σ u ca' m' ds asks := by
  have hno : ∀ n : Mid W Y, u.part.stopAt (φ.sees n.st.input) n.loc ds ≠ some .hid := by
    intro n
    rw [stops]
    exact fun e => nomatch e
  unfold shownLaw
  rw [exact ca m (frontOfSeen m.seen) ds asks trivial (frontOfSeen_seen _).symm hd hb
      (holds_of_no_read _ chain firstTree _ ds reads) (hno m),
    exact ca' m' (frontOfSeen m'.seen) ds asks trivial (frontOfSeen_seen _).symm hd hb
      (holds_of_no_read _ chain firstTree _ ds reads) (hno m')]
  congr 1
  funext c
  exact tell _ _ _ _ _ _ _ _ c

/-- CONDITIONAL. **The same from the field's own text** (`ExactMemberAt pre`: the field `exact` of `Good`
at one member), at two states whose opened columns are what the field asks beside the front that
holds their earlier rounds and no column. -/
theorem shownLaw_same_at {pre : List (Nat × Nat × List Fmt.DeclaredRound)} {φ : Face V W Pb}
    {σ : Side S Cl V W Y Pb} {chain firstTree : Nat}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop} {u : Member V W Y Pb}
    (exact : ExactMemberAt pre φ σ chain firstTree (fun _ _ _ _ => True) bud u)
    (tell : ∀ pub pub' front front' ds ds' asks asks' c,
      u.sim.tell pub front ds asks c = u.sim.tell pub' front' ds' asks' c)
    (reads : ∀ d ∈ u.rounds.map (·.1), d.stored = [] ∧ d.opens = [])
    (stops : ∀ v loc ds, u.part.stopAt v loc ds = none)
    (ca ca' : CsAll u.part.carries) (m m' : Mid W Y)
    (hm : m.opened = (frontOfSeen m.seen).opened (readsBefore pre (frontOfSeen m.seen)))
    (hm' : m'.opened = (frontOfSeen m'.seen).opened (readsBefore pre (frontOfSeen m'.seen)))
    (ds : List Fmt.Drawn) (asks : List (List (List Nat)))
    (hd : drawsFit (u.rounds.map (·.1)) ds = true) (hb : bud u.number ds asks) :
    shownLaw φ σ u ca m ds asks = shownLaw φ σ u ca' m' ds asks := by
  have hno : ∀ n : Mid W Y, u.part.stopAt (φ.sees n.st.input) n.loc ds ≠ some .hid := by
    intro n
    rw [stops]
    exact fun e => nomatch e
  unfold shownLaw
  rw [exact ca m (frontOfSeen m.seen) ds asks trivial (frontOfSeen_seen _).symm hm hd hb
      (holds_of_no_read _ chain firstTree _ ds reads) (hno m),
    exact ca' m' (frontOfSeen m'.seen) ds asks trivial (frontOfSeen_seen _).symm hm' hd hb
      (holds_of_no_read _ chain firstTree _ ds reads) (hno m')]
  congr 1
  funext c
  exact tell _ _ _ _ _ _ _ _ c

/-- CONDITIONAL. **Such a part shows something at every coin**, where its simulator always says
something: so the two sides of `ExactMember` are not "nothing" on both sides. -/
theorem shows_isSome_of_exact {φ : Face V W Pb} {σ : Side S Cl V W Y Pb} {chain firstTree : Nat}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop} {u : Member V W Y Pb}
    (exact : ExactMember φ σ chain firstTree (fun _ _ _ _ => True) bud u)
    (tellSome : ∀ pub front ds asks c, (u.sim.tell pub front ds asks c).isSome = true)
    (reads : ∀ d ∈ u.rounds.map (·.1), d.stored = [] ∧ d.opens = [])
    (stops : ∀ v loc ds, u.part.stopAt v loc ds = none)
    (ca : CsAll u.part.carries) (m : Mid W Y) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) (hd : drawsFit (u.rounds.map (·.1)) ds = true)
    (hb : bud u.number ds asks) (c : Cs u.part.takes × CsAll u.part.spends) :
    (σ.shows φ u (c.1, c.2, ca) m ds asks).isSome = true := by
  have hno : u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid := by
    rw [stops]
    exact fun e => nomatch e
  have e := exact ca m (frontOfSeen m.seen) ds asks trivial (frontOfSeen_seen _).symm hd hb
    (holds_of_no_read _ chain firstTree _ ds reads) hno
  have h1 : σ.shows φ u (c.1, c.2, ca) m ds asks ∈
      ((Prob.unif (Cs u.part.takes × CsAll u.part.spends)).map
        fun c => σ.shows φ u (c.1, c.2, ca) m ds asks).support :=
    (PMF.mem_support_map_iff _ _ _).2 ⟨c, by simp, rfl⟩
  rw [e] at h1
  obtain ⟨b, -, hb'⟩ := (PMF.mem_support_map_iff _ _ _).1 h1
  rw [← hb']
  exact tellSome _ _ _ _ b

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.shownLaw
#print axioms ProofFile.Honest.K6.pair_of_membersOf
#print axioms ProofFile.Honest.K6.frontOfSeen
#print axioms ProofFile.Honest.K6.frontOfSeen_seen
#print axioms ProofFile.Honest.K6.readsOf_of_no_read
#print axioms ProofFile.Honest.K6.holds_of_no_read
#print axioms ProofFile.Honest.K6.shownLaw_same
#print axioms ProofFile.Honest.K6.shownLaw_same_at
#print axioms ProofFile.Honest.K6.shows_isSome_of_exact
