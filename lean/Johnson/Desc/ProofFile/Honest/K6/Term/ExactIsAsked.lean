--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/ExactIsAsked.lean: AGAINST EMPTINESS. The conditions `exact` and
`fresh` of `Good`, and the statement on each part's marginal law (Honest/K6/Term/MarginalLaw.lean), are
asked only at challenges that the part's rounds can draw and at positions within bud; `exact` also at a
front that fits the state. Here: at each of the eight members of the sub-protocol "the output head's
own rounds" (kind K6) such challenges, positions, state and front EXIST, all premises of the field
`exact` together, at every `pre` and every input; and there each part shows something at every coin.

WHAT IT IS NOT. The challenges are made up (every drawn element is (1, 0, 0): `fitOne`,
Honest/K6/Law/DrawsThatFit.lean); the state is written by hand: nothing heard, nothing seen. Nobody
is said to draw these challenges and no run is said to reach that state. That some public files are
in scope and pass the library's test is not shown here (it is `files_pass`,
AtFullSide/K1/SimAtTerm.lean). Nothing on soundness, completeness or hiding.

  `head_member_draws_fit`   at every member some challenges fit
  `startState`              a state written by hand, at a given input, with the opened columns that the
                            field asks beside the front that holds nothing
  `head_exact_is_asked`     all premises of the field `exact` together, at every member, `pre`, input
  `head_shows_something`    where `exact` is asked, each part shows something at every coin
  `head_showsSome`          the same in the kind-free form `ShowsSome` (Honest/KindSheet.lean)
  `head_exact_is_asked_at_maker`, `head_showsSome_at_maker`   at what the honest prover's maker returns: the
                            premises of `exact` can be met at each of eight members; the parts show something
-/
import Johnson.Desc.ProofFile.Honest.KindSheet
import Johnson.Desc.ProofFile.Honest.K6.Law.DrawsThatFit
import Johnson.Desc.ProofFile.Honest.K6.Term.MarginalLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Place Chain Oracle)
open VerifiableInference.Desc.Kinds
open ProofFile.Honest.Small

variable {S Cl X W₀ Rc Tr X₀ : Type}

section
variable {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
  {wit : Local W₀ Rc Inst Tr → HeadAsk} {p : Head.Par} {at_ : Place}

/-- CONDITIONAL: the structure `HeadSeated`. **At every member some challenges fit.** -/
theorem head_member_draws_fit (h : HeadSeated σ wit p at_) :
    ∀ u ∈ σ.members,
      drawsFit (u.rounds.map (·.1)) ((u.rounds.map (·.1)).map fitOne) = true := by
  intro u hu
  refine drawsFit_fitOne _ fun z hz => ?_
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hz
  have hm := (List.of_mem_zip (mem_rounds_of_member hu hr)).1
  rw [h.rounds] at hm
  exact head_known p _ hm

/-- A member's rounds read no table. -/
theorem head_member_reads_nothing (h : HeadSeated σ wit p at_) :
    ∀ u ∈ σ.members, ∀ d ∈ u.rounds.map (·.1), d.stored = [] ∧ d.opens = [] := by
  intro u hu d hd
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hd
  have hz := (List.of_mem_zip (mem_rounds_of_member hu hr)).1
  rw [h.rounds] at hz
  exact head_reads_nothing p _ hz

/-- A member's part never stops. -/
theorem head_member_never_stops (h : HeadSeated σ wit p at_) :
    ∀ u ∈ σ.members, ∀ v loc ds, u.part.stopAt v loc ds = none := by
  intro u hu
  have hq : (u.part, u.sim) ∈ headSided (X := X) wit p at_ := by
    rw [← h.row]
    exact pair_of_membersOf σ.row 0 _ u hu
  have hstop := headSided_cases wit p at_
    (Q := fun q => (∀ loc ds, q.1.bad loc ds = none) ∧ ∀ v loc ds, q.1.hid v loc ds = none)
    (fun _ => ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩)
    (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩)
    (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩) _ hq
  exact K5.stopAt_none u.part hstop.1 hstop.2

end

/-- **A state written by hand**: the given input and own state; nothing heard, nothing seen; the
opened columns that the field `exact` asks at `pre` beside the front that holds nothing. -/
def startState {W Y : Type} (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (input : W) (own : Y) :
    Mid W Y :=
  ⟨⟨input, [], own⟩, [], [], (frontOfSeen []).opened (readsBefore pre (frontOfSeen []))⟩

section
variable {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
  {wit : Local W₀ Rc Inst Tr → HeadAsk} {p : Head.Par} {at_ : Place}

/-- CONDITIONAL: the structure `HeadSeated`. **ALL PREMISES OF THE FIELD `exact` CAN BE MET TOGETHER**, at
every member, every `pre`, every face, every input and own state: On asks nothing; the other six are
listed. So the field is asked somewhere at each of the eight. -/
theorem head_exact_is_asked (h : HeadSeated σ wit p at_)
    (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (input : Local W₀ Rc Inst Tr) (own : X) :
    ∀ u ∈ σ.members, ∃ (m : Mid (Local W₀ Rc Inst Tr) X) (front : Before) (ds : List Fmt.Drawn)
      (asks : List (List (List Nat))),
      m.st.input = input ∧ m.seen = front.seen ∧
      m.opened = front.opened (readsBefore pre front) ∧
      drawsFit (u.rounds.map (·.1)) ds = true ∧ headBud u.number ds asks ∧
      front.holds 0 0 (u.rounds.map (·.1)) ds = true ∧
      u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid := by
  intro u hu
  refine ⟨startState pre input own, frontOfSeen [], (u.rounds.map (·.1)).map fitOne, [], rfl,
    (frontOfSeen_seen []).symm, rfl, head_member_draws_fit h u hu, rfl,
    holds_of_no_read _ 0 0 _ _ (head_member_reads_nothing h u hu), ?_⟩
  rw [head_member_never_stops h u hu]
  exact fun e => nomatch e

/-- CONDITIONAL: the structure `HeadSeated`. **Where `exact` is asked, each part shows something at
every coin**: the two sides of `exact` are not "nothing" on both sides. -/
theorem head_shows_something (h : HeadSeated σ wit p at_)
    (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst)
    (u : Member (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst) (hu : u ∈ σ.members)
    (ca : CsAll u.part.carries) (m : Mid (Local W₀ Rc Inst Tr) X) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) (hd : drawsFit (u.rounds.map (·.1)) ds = true)
    (hb : headBud u.number ds asks) (c : Cs u.part.takes × CsAll u.part.spends) :
    (σ.shows φ u (c.1, c.2, ca) m ds asks).isSome = true := by
  have hq : (u.part, u.sim) ∈ headSided (X := X) wit p at_ := by
    rw [← h.row]
    exact pair_of_membersOf σ.row 0 _ u hu
  have hsome := headSided_cases wit p at_
    (Q := fun q => ∀ pub front ds asks c, (q.2.tell pub front ds asks c).isSome = true)
    (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ _ => rfl) _ hq
  exact shows_isSome_of_exact (head_exact_all φ h 0 0 (fun _ _ _ _ => True) headBud u hu) hsome
    (head_member_reads_nothing h u hu) (head_member_never_stops h u hu) ca m ds asks hd hb c

/-- The same in the kind-free form `ShowsSome` (Honest/KindSheet.lean), at every `pre`. -/
theorem head_showsSome (h : HeadSeated σ wit p at_)
    (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) :
    ShowsSome pre φ σ 0 0 (fun _ _ _ _ => True) headBud := by
  intro u hu ca m front ds asks _ _ _ hd hb _ _ c e
  have hs := head_shows_something h φ u hu ca m ds asks hd hb c
  rw [e] at hs
  cases hs

end

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: the hypothesis h; the maker returns. **At what the honest prover's maker returns**: the
lot lays a row; it has a side over the returned description's first chain; that side has eight
members; and at each of them all premises of the field `exact` can be met together, at every `pre`,
input and own state. General in the filling. -/
theorem head_exact_is_asked_at_maker (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (weights : Pub → W₀ → Weights)
    (falls : List (Fall A.F.S₁)) (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (input : Local W₀ Rc Inst Cells) (own : X) :
    ∃ r ∈ (headSimulatorLot (Rc := Rc) (X := X) weights).rows A.Z A.G,
    ∃ σ, Side.seated A.F.first.blocksInOrder r.place r.row falls = some σ ∧ σ.members.length = 8 ∧
    ∀ u ∈ σ.members, ∃ (m : Mid (Local W₀ Rc Inst Cells) X) (front : Before)
      (ds : List Fmt.Drawn) (asks : List (List (List Nat))),
      m.st.input = input ∧ m.seen = front.seen ∧
      m.opened = front.opened (readsBefore pre front) ∧
      drawsFit (u.rounds.map (·.1)) ds = true ∧ r.bud u.number ds asks ∧
      front.holds 0 0 (u.rounds.map (·.1)) ds = true ∧
      u.part.stopAt (Face.own.sees m.st.input) m.loc ds ≠ some .hid := by
  have hG₀ := (atPure_ok hA).2.1
  obtain ⟨G, B, H, rd, rw', rfl⟩ := atPure_is h.laid hA
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G := hG₀
  have hrow := headSimulatorLot_one_row (Rc := Rc) (X := X) h hG weights
  refine ⟨_, by rw [hrow]; exact List.mem_cons_self .., ?_⟩
  obtain ⟨σ₀, hσ₀, hS⟩ := head_lot_seated (Rc := Rc) (X := X) (head_lotSeatB_under_head h hG) id
    (weights Zp) falls _ (by
      show _ ∈ (headSimulatorLot (Rc := Rc) (X := X) weights).rows Zp G
      rw [hrow]
      exact List.mem_cons_self ..)
  refine ⟨σ₀, hσ₀, ?_, head_exact_is_asked hS .own pre input own⟩
  exact (congrArg List.length (head_members hS)).trans
    (by simp [headSided, headRow, headParts, headSims])

/-- CONDITIONAL: the hypothesis h; the maker returns. **At what the honest prover's maker returns, each
part of each row of the lot shows something at every coin**, wherever the field `exact` speaks: in the
form `ShowsSome`, at the row's own On and bud, at every `pre` and list of falls. General in the filling. -/
theorem head_showsSome_at_maker (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (weights : Pub → W₀ → Weights) :
    ∀ r ∈ (headSimulatorLot (Rc := Rc) (X := X) weights).rows A.Z A.G,
    ∀ (falls : List (Fall A.F.S₁)) σ, Side.seated A.F.first.blocksInOrder r.place r.row falls = some σ →
    ∀ pre, ShowsSome pre .own σ 0 0 r.On r.bud := by
  have hG₀ := (atPure_ok hA).2.1
  obtain ⟨G, B, H, rd, rw', rfl⟩ := atPure_is h.laid hA
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G := hG₀
  intro r hr falls σ hσ pre
  obtain ⟨σ₀, hσ₀, hS⟩ := head_lot_seated (Rc := Rc) (X := X) (head_lotSeatB_under_head h hG) id
    (weights Zp) falls r hr
  obtain rfl : σ₀ = σ := Option.some.inj (hσ₀.symm.trans hσ)
  obtain ⟨a, rfl⟩ := headSimulatorLot_rows hr
  exact head_showsSome hS .own pre

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.head_member_draws_fit
#print axioms ProofFile.Honest.K6.head_member_reads_nothing
#print axioms ProofFile.Honest.K6.head_member_never_stops
#print axioms ProofFile.Honest.K6.startState
#print axioms ProofFile.Honest.K6.head_exact_is_asked
#print axioms ProofFile.Honest.K6.head_shows_something
#print axioms ProofFile.Honest.K6.head_showsSome
#print axioms ProofFile.Honest.K6.head_exact_is_asked_at_maker
#print axioms ProofFile.Honest.K6.head_showsSome_at_maker
