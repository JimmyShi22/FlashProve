-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/StandAtMember.lean: the kind "lookup" (K3): the premises
inside `ExactMember` (Honest/Small/Field.lean) meet at a stand that is named, at every member of
every side seated over the row that passes its tables on; and what the sentence gives there. So the
sentence of `k3_exact_kept_head` (Honest/K3/Law/Thread/ExactKeptHead.lean) is not empty at any
member. Theorems; no definition; two local instances of a proposition's class: as instances no other
file sees them; their two names stand in this file's namespace.

Never to be retold as "the row that passes its tables on is simulated".

The stand, by name. No value of it is bound by "there is". The front is empty: `⟨[], []⟩`. The run
between two rounds is `⟨st, [], [], o⟩`: st, the state, is a letter (its types are letters); so is
o, the columns opened so far, bound by "for all". No positions are asked: `[]`. The challenges are,
round by round, `MarkToy.shown z.entry 0`
(Honest/K3/Good/MarkToy.lean): every drawn element is 1, every position and every matrix entry 0, no
digest. The carried coins stand under "for all". On' and bud are "true".

What is shown.
  `draws_shown`: of whatever kind: where the format knows every round's name, these challenges pass
    `drawsFit`. By `MarkToy.drawFit_toy`.
  `holds_bare`: of whatever kind: at rounds declared bare, every front passes `Before.holds`:
    nothing is read. By `reads_none` (Honest/K3/Law/LotMember.lean).
  `stopAt_none`: of whatever kind: a part whose two stops never speak stops nowhere.
  `rounds_keep_head`: conditional on the head, the site, the side and the member: the member's
    rounds are a stretch of the plan's entries at the site, declared bare, and the format knows each
    name.
  `no_stop_keep`: conditional on the side and the member: the member's part stops nowhere.
  `six_at_member`: **conditional on the head, the site, the side and the member: the four premises
    of `ExactMember` that are not "true" at On' and bud := "true" hold at the stand.** At every
    member, with a call or without; at every filling's letters: no hK, no lens.
  `at_stand_member`: **so, conditional besides on the lens and hK: the end of `ExactMember` at the
    stand: the two laws are one there.** It is `ExactMember`'s own end at the named values: no new
    sentence on a law. In front of it stand two local instances, `Nonempty (Cs d)` and
    `Nonempty (CsAll ds)`, by `default`: under this file's imports Lean's search for them ran out of
    its allowance on the statement; no allowance is raised.
  `opened_at_stand`: the premise of `Good`'s field `exact` on the columns opened, which
    `ExactMember` does not have, holds at the stand where o is what the front holds for the reads of
    `pre`; at every `pre`; by unfolding.

Hypotheses that remain. h: `P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x`. Conditional on the head
`P5J.AtMgA`. That it holds at the goals' two named sets of public files is a sealed theorem
(`headMember_named`, AtFullSide/Top/HeadMemberAtGap.lean), with that file's own limits; this file
does not call it: AtFullSide/Honest/K3/StandAtNamed.lean [not in this library] does. In
`at_stand_member`: the lens and hK.

Imported: ExactKeptHead.lean and this house's files beneath it;
Honest/K3/Good/MarkToy.lean; Honest/K3/Good/H3/Entries.lean (`entriesV_tame`, `fit_mem`).

Limits. A stand shows that the sentence speaks of something at the member: not that a run reaches
it. The front, the challenges and the state are the writer's choice, not a run's: the challenge is 1
at every round, the shift, alpha and the sumchecks' own among them: a point at which much collapses.
At On' and bud := "true" alone. It adds nothing to what `ExactMember` says. One reading by a
stand-in one floor down: the site's public list of entries, `s.p.entries.getD []`. Of `Good`'s other
fields nothing. Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExactKeptHead
import Johnson.Desc.ProofFile.Honest.K3.Good.MarkToy
import Johnson.Desc.ProofFile.Honest.K3.Good.H3.Entries
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.LiftLens

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Chain Oracle)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest.Small (ExactMember)
open ProofFile.Honest.K3.Good (MarkToy.shown MarkToy.drawFit_toy entriesV_tame fit_mem)

variable {V W X Pb : Type}

/-- Where the format knows every round's name, the named challenges pass `drawsFit`. -/
theorem draws_shown : ∀ zs : List Fmt.DeclaredRound,
    (∀ z ∈ zs, (Fmt.kindOf z.entry.name).isSome = true) →
    drawsFit zs (zs.map fun z => MarkToy.shown z.entry 0) = true
  | [], _ => rfl
  | z :: zs, h => by
    show (drawFit z (MarkToy.shown z.entry 0) &&
      drawsFit zs (zs.map fun z => MarkToy.shown z.entry 0)) = true
    rw [MarkToy.drawFit_toy z (h z List.mem_cons_self) 0 (by decide),
      draws_shown zs fun z' hz' => h z' (List.mem_cons_of_mem _ hz')]
    rfl

/-- At rounds declared bare every front passes `Before.holds`. -/
theorem holds_bare (front : Before) (chain firstTree : Nat) (es : List Fmt.Entry)
    (ds : List Fmt.Drawn) : front.holds chain firstTree (es.map declOf) ds = true := by
  unfold Before.holds
  rw [show readsOf chain firstTree (fun _ _ => none) (fun _ => none) (es.map declOf) ds = [] from
    reads_none chain firstTree _ _ es ds]
  rfl

/-- A part whose two stops never speak stops nowhere. -/
theorem stopAt_none (p : Part V W X) (h1 : ∀ f o, p.bad f o = none)
    (h2 : ∀ v f o, p.hid v f o = none) (v : Option V) (loc ds : List Fmt.Drawn) :
    p.stopAt v loc ds = none := by
  unfold Part.stopAt
  refine List.findSome?_eq_none_iff.2 fun j _ => ?_
  have e : (v.bind fun u => p.hid u loc (ds.take j)) = none := by
    cases v with
    | none => rfl
    | some u => exact h2 u loc (ds.take j)
  rw [h1, e]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Conditional on `P5J.AtMgA`, the site, the side and the member: the member's rounds are a stretch
of the plan's entries, declared bare, and the format knows each name. -/
theorem rounds_keep_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (A : FillKeep W)
    (get : X → RowOwn) (set : X → RowOwn → X) (fs : List (Fall TS)) (s : Site)
    (hs : s ∈ lookSites Zp) (σ' : Side TS ProofFile.Cl V W X Pb)
    (hσ : Side.seated cF.blocksInOrder s.at_.place (rowPairsKeep A get set s) fs = some σ')
    (u' : Member V W X Pb) (hu : u' ∈ σ'.members) :
    ∃ es' : List Fmt.Entry, u'.rounds.map (·.1) = es'.map declOf ∧
      ∀ e ∈ es', (Fmt.kindOf e.name).isSome = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b, hb, hbs⟩ := lot_of_site _ _ _ _ _ Zp Bs base cF _ _ O s hs
  obtain ⟨hf, _, _⟩ := block_of_seated _ cF.blocksInOrder s.at_.place fs σ' hσ
  have hm : σ'.block ∈ cF.blocksInOrder := List.mem_of_find?_eq_some hf
  have hp : σ'.block.place = s.at_.place := by simpa using List.find?_some hf
  have hmp : σ'.block.place = b.place := hp.trans hbs.symm
  have hk : σ'.block.planOk = true := IM.plan_flat O h.laid.planOk _ hm
  obtain ⟨_, e1, _, e3, e4⟩ :=
    site_block _ _ _ _ _ Zp Bs base cF _ _ O s hs b σ'.block hb hbs hm hmp hk
  obtain ⟨_, g1, g2, _⟩ := memberAtSite _ _ _ _ _ Zp Bs base cF _ _ O b hb σ'.block hm hmp
  have hu' : u' ∈ membersOf σ'.row 0 (σ'.block.rounds.zip σ'.block.oracles) := hu
  rw [g1.trans e3, g2.trans e4, zip_bare] at hu'
  obtain ⟨i, y, _, rfl⟩ := membersOf_spec _ 0 _ u' hu'
  refine ⟨(((s.p.entries.getD []).drop
    ((σ'.row.take i).map fun y => y.1.moves.length).sum).take y.1.moves.length), ?_, fun e he => ?_⟩
  · show ((((s.p.entries.getD []).map fun e => (declOf e, ([] : List Oracle))).drop _).take _).map
      (·.1) = _
    simp only [List.map_take, List.map_drop, List.map_map]
    rfl
  · have he' : e ∈ s.p.entries.getD [] := List.mem_of_mem_drop (List.mem_of_mem_take he)
    obtain ⟨_, _, k, hk', _⟩ := entriesV_tame _ _ (fit_mem _ _ e1 e he')
    exact Option.isSome_iff_exists.2 ⟨k, hk'⟩

/-- Conditional on the side and the member: the member's part stops nowhere. -/
theorem no_stop_keep {S Cl : Type} (A : FillKeep W) (get : X → RowOwn) (set : X → RowOwn → X)
    (s : Site) (bs : List (VerifiableInference.Desc.Block S Cl)) (fs : List (Fall S))
    (σ' : Side S Cl V W X Pb)
    (hσ : Side.seated bs s.at_.place (rowPairsKeep A get set s) fs = some σ')
    (u' : Member V W X Pb) (hu : u' ∈ σ'.members) (v : Option V) (loc ds : List Fmt.Drawn) :
    u'.part.stopAt v loc ds = none := by
  obtain ⟨_, hr, _⟩ := block_of_seated _ bs s.at_.place fs σ' hσ
  obtain ⟨i, y, hy, rfl⟩ := membersOf_spec σ'.row 0 _ u' hu
  have hm : y.1 ∈ (proverSideOfLookupInChainKeepingTablesAtOneOwner (V₁ := V) (A.keeps s) (A.wit s) get set s.at_).parts := by
    rw [← rowPairsKeep_parts (Pb := Pb), ← hr]
    exact List.mem_map.2 ⟨y, List.mem_of_getElem? hy, rfl⟩
  have hn := noStops_liftG (fun _ : V => ()) (A.wit s) get set _ (noStops_keep (A.keeps s) s.at_)
    y.1 hm
  exact stopAt_none y.1 hn.1 hn.2 v loc ds

/-- **The four premises of `ExactMember` that are not "true" at On' and bud := "true" hold at the
named stand.** Conditional on `P5J.AtMgA`, the site, the side and the member. -/
theorem six_at_member (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (A : FillKeep W)
    (get : X → RowOwn) (set : X → RowOwn → X) (fs : List (Fall TS)) (s : Site)
    (hs : s ∈ lookSites Zp) (σ' : Side TS ProofFile.Cl V W X Pb)
    (hσ : Side.seated cF.blocksInOrder s.at_.place (rowPairsKeep A get set s) fs = some σ')
    (u' : Member V W X Pb) (hu : u' ∈ σ'.members) (φ : Face V W Pb)
    (chain firstTree : Nat) (st : State W X) (o : Option (List VerifiableInference.Desc.OpenedColumn)) :
    (⟨st, [], [], o⟩ : Mid W X).seen = (⟨[], []⟩ : Before).seen ∧
      drawsFit (u'.rounds.map (·.1)) ((u'.rounds.map (·.1)).map fun z => MarkToy.shown z.entry 0) =
        true ∧
      (⟨[], []⟩ : Before).holds chain firstTree (u'.rounds.map (·.1))
        ((u'.rounds.map (·.1)).map fun z => MarkToy.shown z.entry 0) = true ∧
      u'.part.stopAt (φ.sees st.input) []
        ((u'.rounds.map (·.1)).map fun z => MarkToy.shown z.entry 0) ≠ some .hid := by
  obtain ⟨es', e1, e2⟩ := rounds_keep_head h A get set fs s hs σ' hσ u' hu
  refine ⟨rfl, draws_shown _ fun z hz => ?_, ?_, ?_⟩
  · rw [e1] at hz
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hz
    exact e2 e he
  · rw [e1]
    exact holds_bare _ chain firstTree es' _
  · rw [no_stop_keep A get set s cF.blocksInOrder fs σ' hσ u' hu]
    exact fun k => nomatch k

/-- Found at once. Under this file's imports Lean's search for this instance runs out of its
allowance before it reaches `Inhabited (Cs d)` (Honest/Frame.lean). A proposition: whichever proof
is found, the terms in which it stands are the same. -/
local instance (priority := high) csNonempty (d : Due) : Nonempty (Cs d) := ⟨default⟩

/-- The like for `CsAll`. -/
local instance (priority := high) csAllNonempty (ds : List (String × Due)) : Nonempty (CsAll ds) :=
  ⟨default⟩

/-- Never to be retold as "the row that passes its tables on is simulated". **What the sentence
gives at the named stand.** Conditional on `P5J.AtMgA`, the site, the side, the member, the lens and
hK. -/
theorem at_stand_member (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (A : FillKeep W)
    (get : X → RowOwn) (set : X → RowOwn → X) (fs : List (Fall TS)) (s : Site)
    (hs : s ∈ lookSites Zp) (σ' : Side TS ProofFile.Cl V W X Pb)
    (hσ : Side.seated cF.blocksInOrder s.at_.place (rowPairsKeep A get set s) fs = some σ')
    (u' : Member V W X Pb) (hu : u' ∈ σ'.members) (φ : Face V W Pb)
    (chain firstTree : Nat) (st : State W X) (o : Option (List VerifiableInference.Desc.OpenedColumn))
    (hgs : ∀ x y, get (set x y) = y)
    (hsg : ∀ x, set x (get x) = x) (hK : ∀ s ∈ lookSites Zp, (A.keeps s).Shaped s.at_.face)
    (ca : CsAll u'.part.carries) :
    (Prob.unif (Cs u'.part.takes × CsAll u'.part.spends)).map
        (fun c => σ'.shows φ u' (c.1, c.2, ca) (⟨st, [], [], o⟩ : Mid W X)
          ((u'.rounds.map (·.1)).map fun z => MarkToy.shown z.entry 0) []) =
      (Prob.unif (Cs u'.sim.takes)).map fun c =>
        u'.tells φ c st.input (⟨[], []⟩ : Before)
          ((u'.rounds.map (·.1)).map fun z => MarkToy.shown z.entry 0) [] := by
  obtain ⟨_, hall⟩ := k3_exact_kept_head h φ A get set hgs hsg hK fs chain firstTree
    (fun _ _ _ _ => True) (fun _ _ _ => True)
  obtain ⟨σ'', hσ'', hex⟩ := hall s hs
  obtain rfl : σ'' = σ' := Option.some.inj (hσ''.symm.trans hσ)
  obtain ⟨a, b, c, d⟩ := six_at_member h A get set fs s hs σ'' hσ u' hu φ chain firstTree st o
  exact hex u' hu ca ⟨st, [], [], o⟩ ⟨[], []⟩ _ [] trivial a b trivial c d

/-- **The premise of the field `exact` of `Good` on the columns opened (the one that
`ExactMemberAt`, Honest/Small/Field.lean, has beyond the six of `ExactMember`) holds at the stand,
where o is what the front holds for the reads of `pre`**: at every `pre`. By unfolding: o is chosen
so. `six_at_member` and `at_stand_member` hold at every o, so at this one: there all seven premises
meet. -/
theorem opened_at_stand (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (st : State W X) :
    (⟨st, [], [], (⟨[], []⟩ : Before).opened (readsBefore pre ⟨[], []⟩)⟩ : Mid W X).opened =
      (⟨[], []⟩ : Before).opened (readsBefore pre ⟨[], []⟩) := rfl

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.draws_shown
#print axioms ProofFile.Honest.K3.Law.AtThr.holds_bare
#print axioms ProofFile.Honest.K3.Law.AtThr.stopAt_none
#print axioms ProofFile.Honest.K3.Law.AtThr.rounds_keep_head
#print axioms ProofFile.Honest.K3.Law.AtThr.no_stop_keep
#print axioms ProofFile.Honest.K3.Law.AtThr.six_at_member
#print axioms ProofFile.Honest.K3.Law.AtThr.at_stand_member
#print axioms ProofFile.Honest.K3.Law.AtThr.opened_at_stand
