-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/H2K5R/StatesRawAtOpen.lean: KIND K5: WHAT THE SEATED ATTENTION SEGMENT's HEARING SUB-PROTOCOL 2 STATES IS THE KIND's FOUR NAMED RUNS THEMSELVES, NO GUARD AROUND THEM; and the sentence on the run "join" that the lookup argument's files want, in those files' letters. A join of theorems that lie.

Why. The lookup argument's digits' sub-protocol must hand on every public test that stays open behind it; at an attention segment two of these stand for K5's runs. The lookup argument's files want one sentence (below: k05_join_raw) and the form runsN_keeps.

Main names:
  `runsN_cases`: a member of runsN A is one of the kind's three own runs, typed at Claim, or the run "join".
  `runsN_keeps`: "first", "keys" and "second" hand back the state that they were handed. NO NEW ARGUMENT: K5Law.runsK_step (Johnson/Desc/First/Att/Claims/RunsStep.lean), read through runN.
  `runsN_pass`: all four pass the seat's guard (VerifiableInference.OnPublicFiles.Pass, Johnson/Desc/First/Look/K03StatesRaw.lean): the three by runsN_keeps and sameOut_of_open; "join" as in K05_join_of_open.
  `K05_states_raw_of_open`: from an opening, at every o: statesOfLink Lk 2 = runsN a (K05_states_of_open with the guard struck by map_guard_eq, Johnson/Desc/First/Look/K03StatesRaw.lean).
  `att_odd`: an attention segment below 25 is 2 g + 1 with g < 12.
  `k05_join_raw`: **in the goals' scope, at every attention segment: one Lk and one a for five clauses.**
PREMISES: of the last: the scope (hS · hR), the opening O, l < 25, attention at l. IS IT EMPTY HERE? Under an opening in scope: NO OPENING IS SHOWN IN LEAN.
No soundness of the protocol is claimed. Nothing is claimed on completeness or hiding.

-/
import Johnson.H2K5R.JoinAtOpen
import Johnson.H2K5R.OwesAtOpen
import Johnson.H2K5R.LawAtEntry
import Johnson.IMR.Subs
import Johnson.Desc.First.Att.Claims.RunsStep
import Johnson.Desc.First.Att.Door.Law.K5RestOpen
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim Block Chain Link FileDescription)
open VerifiableInference.Desc.K9 (statesOfLink)
open VerifiableInference.OnPublicFiles (pass_of_puts join_puts k03_atS2_calls map_guard_eq)

/-- A member of the four is one of the kind's three own runs, typed at Claim, or "join". -/
theorem runsN_cases (A : Attention.Plan) : ∀ x ∈ runsN A,
    (∃ r ∈ runsK (seatCO (parCOf A)) (parCOf A), x = (r.1, runN r.2)) ∨
      x = ("join", runN (K3.joinRun (K3.seatCalls (Cl := Aff) id) (keysOfO A))) := by
  intro x hx
  have hx' : x ∈ (runsO A).map fun r => (r.1, runN r.2) := hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx'
  have hr' : r ∈ (runsK (seatCO (parCOf A)) (parCOf A)).flatMap fun r =>
      if r.1 == "keys" then [r, ("join", K3.joinRun (K3.seatCalls (Cl := Aff) id) (keysOfO A))]
      else [r] := hr
  obtain ⟨r0, hr0, hm⟩ := List.mem_flatMap.1 hr'
  have hm' : r ∈ (if r0.1 == "keys" then
      [r0, ("join", K3.joinRun (K3.seatCalls (Cl := Aff) id) (keysOfO A))] else [r0]) := hm
  split at hm'
  · rcases List.mem_cons.1 hm' with h1 | hm2
    · exact Or.inl ⟨r0, hr0, by rw [h1]⟩
    · have h2 := List.mem_singleton.1 hm2
      exact Or.inr (by rw [h2])
  · have h1 := List.mem_singleton.1 hm'
    exact Or.inl ⟨r0, hr0, by rw [h1]⟩

/-- **(b1) K5's three own runs leave the state**: whatever "first", "keys" or "second", typed at Claim, returns, its state is the state that it was handed. (The form that the lookup argument's files want.) -/
theorem runsN_keeps (A : Attention.Plan) :
    ∀ x ∈ runsN A, x.1 ≠ "join" → ∀ (n : ℕ) (t : First.S) (y : List Claim × First.S), x.2 n t = .ok y → y.2 = t := by
  intro x hx hne n t y h
  rcases runsN_cases A x hx with ⟨r, hr, rfl⟩ | rfl
  · obtain ⟨l, e, -⟩ := runN_ok h
    exact K5Law.runsK_step _ _ r hr n t l y.2 e
  · exact absurd rfl hne

/-- **(b2) All four runs pass the seat's guard.** -/
theorem runsN_pass (A : Attention.Plan) : ∀ x ∈ runsN A, VerifiableInference.OnPublicFiles.Pass x.2 := by
  intro x hx
  rcases runsN_cases A x hx with ⟨r, hr, rfl⟩ | rfl
  · intro n t y h
    obtain ⟨l, e, -⟩ := runN_ok h
    rw [K5Law.runsK_step _ _ r hr n t l y.2 e]
    exact sameOut_of_open t t rfl
  · show VerifiableInference.OnPublicFiles.Pass (runN (K3.joinRun (K3.seatCalls (Cl := Aff) id) (keysOfO A)))
    rw [join_runN_eq]
    exact pass_of_puts (join_puts _ k03_atS2_calls _)

/-- **(b3) What the seated attention segment's hearing sub-protocol 2 states IS K5's four runs: the guard struck. From an opening, at every o.** -/
theorem K05_states_raw_of_open {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block First.S Claim)}
    {c : Chain First.S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open o pol lay KL F Z Bs base c A B) (h4 : Bs.G₀.W.p4 = true) {g : ℕ}
    (hg : g < Bs.G₀.W.NGr) {a : Attention.Plan} (ha : Bs.G₀.W.A[g]? = some a) :
    ∃ Lk : Link First.S Claim, c.links[2 * g + 1]? = some Lk ∧ statesOfLink Lk 2 = runsN a := by
  obtain ⟨Lk, -, e1, -, hL⟩ := K05_states_of_open O h4 hg ha
  exact ⟨Lk, e1, hL.trans (map_guard_eq _ (runsN_pass a))⟩

/-- An attention segment below 25 is 2 g + 1 with g < 12. -/
theorem att_odd (l : ℕ) (hl : l < 25)
    (hsub : VerifiableInference.Desc.Sound.linksFull[l]? = some .attention) : ∃ g, g < 12 ∧ l = 2 * g + 1 := by
  have h : ((List.range 25).all fun l =>
      Decidable.decide (VerifiableInference.Desc.Sound.linksFull[l]? = some ModelPart.attention → l % 2 = 1 ∧ l < 24)) =
      true := by decide
  have h2 := of_decide_eq_true (List.all_eq_true.1 h l (List.mem_range.2 hl)) hsub
  exact ⟨l / 2, by omega, by omega⟩

/-- **(a) In the goals' scope, at the description as it is opened, at every attention segment: one Lk and one a serve all five clauses.** (The sentence that the lookup argument's files want, in their letters; "join" in both forms, made of forms and then typed | the lookup's own run at K3Lot.ofForm; its stronger form as the last clause.) -/
theorem k05_join_raw {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block First.S Claim)} {c : Chain First.S Claim}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (hsub : VerifiableInference.Desc.Sound.linksFull[l]? = some .attention) :
    ∃ (Lk : Link First.S Claim) (a : Attention.Plan), c.links[l]? = some Lk ∧
      K3Lot.readersAt Bs.G₀.W l = some (readersOfO a) ∧
      (statesOfLink Lk 2).find? (fun x => x.1 == "join") =
        some ("join", runN (K3.joinRun (K3.seatCalls (Cl := Aff) id) (keysOfO a))) ∧
      (statesOfLink Lk 2).find? (fun r => r.1 == "join") = some ("join", K3.joinRun (K3.seatCalls K3Lot.ofForm) (keysOfO a)) ∧
      statesOfLink Lk 2 = runsN a := by
  obtain ⟨g, hg, rfl⟩ := att_odd l hl hsub
  obtain ⟨h4, g', hg', e⟩ := att_only O.pub O.blank (IM.subs_att hS hR O.pub O.blank hg)
  obtain rfl : g' = g := by omega
  obtain ⟨-, -, b', -, -, hb', -⟩ := k5_alone O h4 hg'
  unfold k5AtN at hb'
  obtain ⟨a, ha, -⟩ := Option.map_eq_some_iff.1 hb'
  obtain ⟨Lk, e1, hs⟩ := K05_states_raw_of_open O h4 hg' ha
  refine ⟨Lk, a, e1, H2K5.Door.readersAt_att h4 ha, ?_, ?_, hs⟩
  · rw [hs]
    exact find_join a
  · rw [hs, find_join, join_runN_eq]

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.runsN_cases
#print axioms VerifiableInference.Desc.First.Att.P.runsN_keeps
#print axioms VerifiableInference.Desc.First.Att.P.runsN_pass
#print axioms VerifiableInference.Desc.First.Att.P.K05_states_raw_of_open
#print axioms VerifiableInference.Desc.First.Att.P.att_odd
#print axioms VerifiableInference.Desc.First.Att.P.k05_join_raw
#print axioms K5Law.runsK_step
#print axioms VerifiableInference.Desc.First.Att.P.find_join
