-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/RespectsK4Q.lean: MEMBERS OF Q.Respects (Johnson/Desc/K1/Law/RestQDef.lean: a
run of claims reads nothing of what a later commitment of kind K1 or the reads' quiet step writes):
THE TWO RUNS "front" AND "back" OF THE KIND K4, at the kind's own text
(Johnson/Desc/First/K4/Block.lean, AtS.lean, AtC.lean; OnBytes/Desc/First/K4/Plain.lean) and as K4's
lot lays them (ProofFile.k4Block, Johnson/Desc/ProofFile/Lot/K4.lean). TYPED FOR K4's
RUNS: as reported, K4's files hold no law of this form. K4's files have, in a file that is not
in this file's build (Johnson/Road/K4/K4ClaimsBlind.lean), what the two runs are (claims_eq, runOf_eq)
and that what a reader sees of a run's return hangs on "own" and the ledger alone (seen_runOf):
section 2 here says the like in its own forty lines and can give way to calls of these. Definitions,
and statements with their proofs.

How. Each run reads, of the state inside a segment of the sort "layers", what the kind's own rounds
heard (own) and the ledger, and lays the ledger back. Of the ledger its two programs read shown
values and lay hiding coefficients and marks "added": they read no mark "root"
(Johnson/Desc/K1/Law/RespectsAtt.lean's calculus Markless is called).
Main names:
  PastMarks f         at two ledgers that part in the marks "root" alone: where f answers at the one
                      it answers at the other, with the same forms and two such ledgers.
  pscRow_markless · ownClaim_past · shown_rest · formsBack_past · formsFrontWith_past
  k4RunS · k4RunS_lay the run at the chain's state, and what it is inside such a segment.
  respects_k4RunS     **a run of that form is a member.**
  k4Block_respects    **hK4 of hRd_seated (Johnson/Desc/K1/Law/ReadersSeated.lean)**, at every
                      place's parameters.
What is not claimed. That a run answers anywhere. Nothing on soundness, on an honest prover or on
hiding.

-/
import Johnson.Desc.K1.Law.RespectsAttQ
import Johnson.Desc.First.K4.AtC
import Johnson.Desc.ProofFile.Lot.K4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc (Block Claim named)
open VerifiableInference.Desc.First (S Here LayOwn)
open OnBytes.Desc.First.K4 (seatOwn part? setPart blockAtS blockAtC claimOf formsBack
  formsFrontWith formsFrontNoRows formsFront ownClaim rowsSummand planesParts front back)

/-! ## 1 The two programs on the ledger read no mark "root" -/

/-- Where f answers at a ledger it answers, with the same forms, at every ledger that parts from it
in the marks "root" alone; the ledgers behind part in these alone. -/
def PastMarks {α : Type} (f : Fork → Option (α × Fork)) : Prop :=
  ∀ F F', forkRest F = forkRest F' → ∀ x, f F = some x →
    ∃ G', f F' = some (x.1, G') ∧ forkRest x.2 = forkRest G'

theorem pscRow_markless (p : Psc) (S0 : E) (kept : Aff) : Markless (Fl.pscRow p S0 kept) :=
  Markless.ofBind _ _ (Markless.ofMust _) fun _ =>
    Markless.ofBind _ _ (hideRun_markless _ _ _) fun _ => Markless.ofPure _

theorem ownClaim_past (p : Psc) (S0 : E) (kept : Aff) : PastMarks (ownClaim p S0 kept) := by
  intro F F' h x hx
  unfold ownClaim at hx ⊢
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
  have k := pscRow_markless p S0 kept F F' [] h
  simp only [hy] at k
  obtain ⟨G', k1, k2⟩ := k
  exact ⟨G', by rw [k1]; rfl, k2⟩

theorem shown_rest {F F' : Fork} (h : forkRest F = forkRest F') (j : ℕ) :
    F'.shown j = F.shown j := by
  have a1 : F'.ns = F.ns := (congrArg Fork.ns h).symm
  have a2 : F'.gotF = F.gotF := (congrArg Fork.gotF h).symm
  have a3 : F'.vp = F.vp := (congrArg Fork.vp h).symm
  unfold Fork.shown
  rw [a1, a2, a3]

theorem formsBack_past (o : Layer.Own) : PastMarks (formsBack o) := by
  intro F F' h x hx
  have e : ∀ G : Fork, formsBack o G =
      (ownClaim o.wo.toWsMerged.p o.wo.toWsMerged.fvp {} G).bind fun y =>
        some ((back o y.1).toArray, y.2.paid o.H.fo.owedJoin) := fun _ => rfl
  rw [e] at hx ⊢
  obtain ⟨y, hy, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨G', k1, k2⟩ := ownClaim_past _ _ _ F F' h y hy
  obtain rfl := Option.some.inj hx
  exact ⟨G'.paid _, by rw [k1]; rfl, paid_rest k2 _⟩

theorem formsFrontWith_past (rows : Bool) (P : Layer.Pub) (g : ℕ) (o : Layer.Own) :
    PastMarks (formsFrontWith rows P g o) := by
  intro F F' h x hx
  have e : ∀ G : Fork, formsFrontWith rows P g o G =
      ((Array.range (4 * P.y.NI)).mapM fun i => G.shown (o.H.tV.sEnd + i)).bind fun sh =>
        (ownClaim o.H.tV.p (rowsSummand P.y o.H sh) {} G).bind fun y1 =>
          (planesParts o.v o.H.fo).bind fun pp =>
            (ownClaim o.H.fo.leaves oneE pp.1 y1.2).bind fun y2 =>
              (front rows P g o y1.1 y2.1).bind fun fs =>
                some (fs.toArray, ((if rows then y2.2.paid o.H.fo.owedObjects else y2.2).paid
                  o.H.fo.owedPlanes)) := fun _ => rfl
  have hsh : (fun i => F'.shown (o.H.tV.sEnd + i)) = fun i => F.shown (o.H.tV.sEnd + i) :=
    funext fun i => shown_rest h _
  rw [e] at hx ⊢
  rw [hsh]
  obtain ⟨sh, h0, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨y1, h1, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨pp, h2, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨y2, h3, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨fs, h4, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain rfl := Option.some.inj hx
  obtain ⟨G1, k1, r1⟩ := ownClaim_past _ _ _ F F' h y1 h1
  obtain ⟨G2, k2, r2⟩ := ownClaim_past _ _ _ y1.2 G1 r1 y2 h3
  refine ⟨(if rows then G2.paid o.H.fo.owedObjects else G2).paid o.H.fo.owedPlanes, ?_, ?_⟩
  · rw [h0, Option.bind_some, k1, Option.bind_some, h2, Option.bind_some]
    show (ownClaim o.H.fo.leaves oneE pp.1 G1).bind _ = _
    rw [k2, Option.bind_some]
    show (front rows P g o y1.1 y2.1).bind _ = _
    rw [h4, Option.bind_some]
  · cases rows
    · exact paid_rest r2 _
    · exact paid_rest (paid_rest r2 _) _

/-! ## 2 The run at the chain's state -/

/-- K4's run of the name nm and the program f, as the kind's sub-protocol at the chain's state and at
the one type of a claim states it. -/
def k4RunS (nm : String) (f : Layer.Own → Fork → Option (Array Aff × Fork)) (t : S) :
    Except String (List Claim × S) :=
  ((named "the part is not there" (part? t)).bind fun p =>
    (OnBytes.Desc.First.K4.runOf seatOwn nm f p).map fun y => (y.1, setPart t y.2)).map fun y =>
      (y.1.map claimOf, y.2)

/-- Inside a segment of the sort "layers". -/
theorem k4RunS_lay (nm : String) (f : Layer.Own → Fork → Option (Array Aff × Fork)) (s : S)
    (a : LayOwn) (ha : s.here = .lay a) (o : Layer.Own) (ho : a.own = some o)
    (x : Array Aff × Fork) (hx : f o a.F = some x) :
    k4RunS nm f s = .ok (x.1.toList.map claimOf,
      { s with here := .lay { a with F := x.2 }
               rowsOwed := if s.noneWaits then none else s.rowsOwed }) := by
  unfold k4RunS part? OnBytes.Desc.First.K4.runOf
  rw [ha]
  simp [named, seatOwn, ho, hx, setPart, bind, Except.bind, Except.map, pure, Except.pure]

/-- What an accept says. -/
theorem k4RunS_ok (nm : String) (f : Layer.Own → Fork → Option (Array Aff × Fork)) (s : S)
    (y : List Claim × S) (h : k4RunS nm f s = .ok y) :
    ∃ a o x, s.here = .lay a ∧ a.own = some o ∧ f o a.F = some x := by
  cases ha : s.here with
  | lay a =>
    cases ho : a.own with
    | none =>
      unfold k4RunS part? OnBytes.Desc.First.K4.runOf at h
      rw [ha] at h
      simp [named, seatOwn, ho, bind, Except.bind, Except.map] at h
    | some o =>
      cases hx : f o a.F with
      | none =>
        unfold k4RunS part? OnBytes.Desc.First.K4.runOf at h
        rw [ha] at h
        simp [named, seatOwn, ho, hx, bind, Except.bind, Except.map] at h
      | some x => exact ⟨a, o, x, rfl, ho, hx⟩
  | _ =>
    unfold k4RunS part? at h
    rw [ha] at h
    simp [named, Except.bind, Except.map] at h

theorem restOf_lay (s : S) (a : LayOwn) (ha : s.here = .lay a) (G : Fork) (r : Option ℕ) :
    Q.restOf { s with here := .lay { a with F := G }, rowsOwed := r } = Q.restOf (s.putFork G) := by
  simp [Q.restOf, Q.blank, Q.blankHere, restOf, hereRest, S.putFork, ha]

/-- **A run of that form is a member.** -/
theorem respects_k4RunS (nm : String) (f : Layer.Own → Fork → Option (Array Aff × Fork))
    (hf : ∀ o, PastMarks (f o)) : Q.Respects fun _ s => k4RunS nm f s := by
  intro s s' hA cl t e
  have e' : k4RunS nm f s = .ok (cl, t) := e
  obtain ⟨a, o, x, ha, ho, hx⟩ := k4RunS_ok nm f s _ e'
  rw [k4RunS_lay nm f s a ha o ho x hx] at e'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj e')
  have hh : (Q.restOf s).here = (Q.restOf s').here := congrArg S.here hA
  cases ha' : s'.here with
  | lay a' =>
    have e1 : Q.blankHere (hereRest (.lay a)) = Q.blankHere (hereRest (.lay a')) := by
      rw [← ha, ← ha']
      exact hh
    have e2 := Here.lay.inj e1
    have o1 : a'.own = a.own := (congrArg LayOwn.own e2).symm
    have o2 : forkRest a.F = forkRest a'.F := congrArg LayOwn.F e2
    obtain ⟨G', k1, k2⟩ := hf o a.F a'.F o2 x hx
    refine ⟨_, k4RunS_lay nm f s' a' ha' o (o1.trans ho) (x.1, G') k1, ?_⟩
    show Q.restOf _ = Q.restOf _
    rw [restOf_lay s a ha, restOf_lay s' a' ha']
    exact hA.putFork k2
  | _ =>
    exfalso
    have e1 : Q.blankHere (hereRest s.here) = Q.blankHere (hereRest s'.here) := hh
    rw [ha, ha'] at e1
    cases e1

/-! ## 3 K4's lot's sub-protocols -/

/-- **Each run of K4's lot's sub-protocol at a place is a member.** -/
theorem k4Block_respects (x : Bool × OnBytes.Desc.First.K4.Par) :
    ∀ r ∈ (ProofFile.k4Block x).claims, Q.Respects r.2 := by
  intro r hr
  have hr' : r ∈ [("front", fun (_ : ℕ) s => k4RunS "K4.claims-front"
        (formsFrontNoRows x.2.P x.2.g) s),
      ("back", fun (_ : ℕ) s => k4RunS "K4.claims-back" formsBack s)] := hr
  have : r = ("front", fun (_ : ℕ) s => k4RunS "K4.claims-front"
        (formsFrontNoRows x.2.P x.2.g) s) ∨
      r = ("back", fun (_ : ℕ) s => k4RunS "K4.claims-back" formsBack s) := by
    simpa using hr'
  rcases this with h | h
  · rw [h]
    exact respects_k4RunS _ _ fun o => formsFrontWith_past false x.2.P x.2.g o
  · rw [h]
    exact respects_k4RunS _ _ formsBack_past

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.pscRow_markless
#print axioms VerifiableInference.Desc.K1.ownClaim_past
#print axioms VerifiableInference.Desc.K1.shown_rest
#print axioms VerifiableInference.Desc.K1.formsBack_past
#print axioms VerifiableInference.Desc.K1.formsFrontWith_past
#print axioms VerifiableInference.Desc.K1.k4RunS_lay
#print axioms VerifiableInference.Desc.K1.k4RunS_ok
#print axioms VerifiableInference.Desc.K1.restOf_lay
#print axioms VerifiableInference.Desc.K1.respects_k4RunS
#print axioms VerifiableInference.Desc.K1.k4Block_respects
