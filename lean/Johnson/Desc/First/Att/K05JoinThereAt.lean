-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05JoinThereAt.lean: kind K5: THE TABLE's PUBLIC TEST formsInT (
FormsIn.lean) AT ITS GENERIC READER (ReaderOf.lean), AT THE RUN "join" OF K5's BLOCK (runsN,
Att/SeatN.lean: the lookup's joinRun at K5's key forms), HOLDS AT THE RECORD BEHIND THE HEARING's LAY:
what the table's item formsInT m 2 "join" stands for (the driver's (2, "join")).

Main names:
  `readerOf_runN'`: the generic reader at a run of forms carried to claims that returns (l, s2) at s,
    where s2's ledger has no mark on a slot that s's lacks: it gives l and no late slot.
  `find_join`: the run in runsN A, by name.
  `joinRun_behind`: what the run returns at the record behind the lay.
  `keys_parts`: "keys"' return at the seat, taken apart.
  `formsInT_join_behind`: **formsInT (Readers.ofStates states) own 2 "join" (behind s a h G) = true.**
Premises: those of k5_join_there (Att/K05JoinThere.lean) at c := parCOf A and g := what the lookup on the
calls was heard to leave (a.lookHeard); the join is not yet made (unpaid); joinF returns.
Limits: as there. The key forms are made at a.g's points, the join at a.lookHeard: that the two are
one record is said by nothing here. Nothing on the lookup's run "planes".
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05JoinThere
import Johnson.Desc.First.Att.K05FormsMadeAt
import Johnson.Desc.First.Att.K5Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc (named need Claim)
open VerifiableInference.Desc.K9 (affInT Read Readers segAt? formsInT mergeOf lateOf ownRow readerOf
  RunOf)

/-- The generic reader at a run of forms that turns no mark on a slot. -/
theorem readerOf_runN' {states : ℕ → List (RunOf First.S)} {b : ℕ} {name nm : String}
    {r : ℕ → First.S → Except String (List Aff × First.S)} {s s2 : First.S} {l : List Aff}
    {G G2 : Fork} (hf : ((states b).find? fun x => x.1 == name) = some (nm, runN r))
    (hr : r 0 s = .ok (l, s2)) (hG : s.fork? = some G) (hG2 : s2.fork? = some G2)
    (hl : lateOf G G2 = []) (ho : ∀ f ∈ l, f.ents.all (ownRow G) = true) :
    readerOf states b name s = some { forms := l, late := [] } := by
  unfold readerOf
  rw [hf]
  have h1 : runN r 0 s = .ok (l.map claimOf, s2) := by
    unfold runN
    rw [hr]
    rfl
  simp only [Option.bind_some, h1, hG, hG2]
  have h2 : ((l.map claimOf).all fun c =>
      c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (ownRow G)) = true := by
    refine List.all_eq_true.2 fun c hc => ?_
    obtain ⟨f, hfl, rfl⟩ := List.mem_map.1 hc
    show (true && true && f.ents.all (ownRow G)) = true
    rw [ho f hfl]
    rfl
  rw [if_pos h2, hl, List.map_map]
  have h3 : ((fun c : Claim => c.form) ∘ claimOf) = id := rfl
  rw [h3, List.map_id]

theorem find_join (A : Attention.Plan) : ((runsN A).find? fun x => x.1 == "join") =
    some ("join", runN (K3.joinRun (K3.seatCalls (Cl := Aff) id) (keysOfO A))) := rfl

section
variable {s : First.S} {a : First.AttOwn} {x : Params.AttentionRounds} {rs : List Fmt.RoundView} {h : Heard}
  {G : Fork} {i : Runs.In} {K : ℕ}

/-- What the run "join" returns at the record behind the lay. -/
theorem joinRun_behind (A : Attention.Plan) {gL : Forest.Heard} (hg : a.lookHeard = some gL)
    (hun : K3.unpaid G gL.owedJoin = true) {kf : Array Aff}
    (hk : keysOfO A (behind s a h G) = some kf) {y : Aff × Fork × OnBytes.K.Kc.Tape}
    (hj : Look.joinF gL kf G [] = some y) :
    K3.joinRun (K3.seatCalls (Cl := Aff) id) (keysOfO A) 0 (behind s a h G) =
      .ok ([y.1], (behind s a h G).putFork y.2.1) := by
  unfold K3.joinRun
  have e1 : (K3.seatCalls (Cl := Aff) id).fork (behind s a h G) = some G := rfl
  have e2 : (K3.seatCalls (Cl := Aff) id).heard (behind s a h G) = some gL := hg
  rw [e1, e2, hk]
  simp only [named, need, hun, hj, if_true, bind, Except.bind, pure, Except.pure]
  rfl

/-- "keys"' return at the seat, taken apart. -/
theorem keys_parts {c : ParC} {t : First.S} {l₁ : List Aff} {j : Runs.JoinsP} {kf : Array Aff}
    (hin : inOf (seatCO c) c t = some (i, K)) (h1 : Runs.firstRun i K = some (l₁, j))
    (hk : keysOfK (seatCO c) c t = some kf) : ∃ k3, Runs.keysRun i k3 j = some kf := by
  unfold keysOfK at hk
  simp only [hin, h1, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff] at hk
  obtain ⟨k3, _, hk⟩ := hk
  exact ⟨k3, hk⟩

/-- **What the table's item formsInT m 2 "join" stands for holds behind the lay.** -/
theorem formsInT_join_behind (states : ℕ → List (RunOf First.S)) (A : Attention.Plan)
    (hst : states 2 = runsN A) (own : List (ℕ × ℕ))
    (hh : hear x (a.F, rs, 0) = some (h, G, [], 0)) (hz : Sized a.F)
    (hin : inOf (seatCO (parCOf A)) (parCOf A) (behind s a h G) = some (i, K)) {l₁ : List Aff}
    {j : Runs.JoinsP} (h1 : Runs.firstRun i K = some (l₁, j)) {kf : Array Aff}
    (hk : keysOfK (seatCO (parCOf A)) (parCOf A) (behind s a h G) = some kf)
    (gf : GeoFits (parCOf A).geo x) (U : U3There own s a (parCOf A)) {gL : Forest.Heard}
    (hg : a.lookHeard = some gL) (hcE : gL.cEnd.ents = #[]) (hcF : Fo.FilledA a.F gL.cEnd)
    (hun : K3.unpaid G gL.owedJoin = true) {y : Aff × Fork × OnBytes.K.Kc.Tape}
    (hj : Look.joinF gL kf G [] = some y) :
    formsInT (Readers.ofStates states) own 2 "join" (behind s a h G) = true := by
  obtain ⟨k3, hk3⟩ := keys_parts hin h1 hk
  have hT := k5_join_there own hh hz hin h1 hk3 gf U none hcE hcF hj
  have hG2 : ((behind s a h G).putFork y.2.1).fork? = some (G.paid gL.owedJoin) := by
    rw [joinF_ledger hj]
    rfl
  refine formsInT_of (l := [y.1]) own segAt_behind rfl (readerOf_runN' (by rw [hst]; exact find_join A)
    (joinRun_behind A hg hun hk hj) rfl hG2 (lateOf_paid G _) fun f hf => ?_) fun f hf => ?_
  · obtain rfl := List.mem_singleton.1 hf
    exact all_ownRow hT.2
  · obtain rfl := List.mem_singleton.1 hf
    exact hT.1

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.readerOf_runN'
#print axioms VerifiableInference.Desc.First.Att.P.joinRun_behind
#print axioms VerifiableInference.Desc.First.Att.P.formsInT_join_behind
