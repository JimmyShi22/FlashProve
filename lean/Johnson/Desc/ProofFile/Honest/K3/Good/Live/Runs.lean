-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/Live/Runs.lean: the kind "lookup" (K3): at every return of one
of the lookup's three seated runs of claims, at a state that meets the condition of
Honest/K3/Good/Live/Clause.lean: every slot in that run's window is live in the run's claims: some
claim that takes its own number names it with a coefficient that is not 0. At "join" and "planes"
conditional on one hypothesis on the calling kind's forms. Definitions and theorems.

Terms. Honest/K3/GLOSSARY.md ("window", "run (of claims): objects, guests, planes, join", "seat",
"caller"). In this file: "live" is `liveAt` (Johnson/Desc/K9/Honest/SlotsLive.lean). The seated runs
are `objectsRun` (Johnson/Top/H/K3RunsLaw.lean), `joinRun` and `planesRun`
(Johnson/Desc/First/Look/K3Runs.lean). p holds the place's public parameters, h is its shape; a
window (`windowOf`, Honest/K3/GoodDraws.lean) counts from the place's first slot, p.first.

What is defined and shown.
  `KeysClear keys t j`: the hypothesis on the caller at "join": none of the key forms that the
    caller hands in at the state t names slot j.
  `BitsClear readers t j`: the hypothesis on the caller at "planes": none of the forms by which the
    caller reads the planes' matrix at the two points, at the state t, names slot j.
  `clause_open`: the condition, opened at the place's shape.
  `sc_getD`, `sc_joinForm`, `sc_atForm`: the coefficient of the form of "join" on a slot that no key
    form names is minus that of the key side's last form; the planes' value as a form has the
    coefficient 0 on a slot that no reader's form names.
  `objects_live`, `join_live`, `planes_live`: the title's sentence, run by run.

Hypotheses that remain.
  `hf`, `hc`: the seat's claim of a form has that form and takes its own number. At the two seats of
    the first chain with the claim `fun a => { form := a }` both hold by `rfl`.
  `hp`: the place's parameters make the shape h.
  `hz`: the run returns. `J`: what the seat reads as heard at the state meets the condition.
  `hj`: j is in the run's window.
  `hK`: (in the helpers `sc_getD`, `sc_joinForm`) no key form of the array names slot j.
  `hk` ("join"), `hb` ("planes"): the hypothesis on the caller, at the slot p.first + j. They are
    facts on the calling kind's text. Shown in part: Honest/K3/Good/Live/Bridges.lean
    (`bitsClear_att`): `BitsClear` at the readers of an attention link, at every plan, state and
    slot; nothing there on key forms (by its head that link's key forms do name slots), on the
    head's link or on a layers' link. They speak of the one slot j and of slots alone: nothing is
    asked on the entries that a form names.

How the proof goes. The library says what each run's list of claims is: `objects_cut`,
`objects_answer` (Johnson/Top/H/Keep/K3Inv.lean, K3Late.lean), `joinRun_cut` (K3RunsLaw.lean),
`planesRun_claims` (Johnson/Desc/Kinds/Law/RowPlanes.lean). The forms are functions of what was
heard and of the caller's forms; the ledger enters no coefficient. `gives_pure`
(Honest/K3/Good/Live/Pure.lean) gives a form of what was heard with a coefficient that is not 0; the
seated form has the same coefficient, up to the sign at "join", because the caller's part has the
coefficient 0.

Users. Honest/K3/Good/Live/Unnamed.lean imports this file.

Limits. That no other run names a slot of a run's window is not said. At the lookup on the digits of
a smallness test the library seats "objects" alone; the slots of the two other windows are named
there by claims of the smallness test's own run, of which nothing is said here. No instance of the
hypotheses together is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.Clause
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.Pure
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeRows
import Johnson.Top.H.Keep.K3Late
import Johnson.Desc.Kinds.Law.RowPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good.Live
open OnBytes (E zeroE oneE subE mulE scaleE)
open OnBytes.Model (Fork Aff Reading)
open OnBytes.Model.Forest (Shape Heard)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.Part.MaskedSum (rowAff)
open VerifiableInference.Desc.First.Look (P)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf toHeard toHeardG Seat Readers joinRun
  planesRun)
open VerifiableInference.Desc.K9H (liveAt)
open VerifiableInference.OnPublicFiles (objectsRun objects_cut objects_answer join_heard joinRun_cut)
open VerifiableInference.Desc.Kinds.Head.Law (planesRun_claims)
open VerifiableInference.Desc.Kinds.Head.Law.Planes (planeForms atForm countForm colWeight nCols)
open ProofFile.Honest.K3.Law (toHeard_fields)
open ProofFile.Honest.K3.Law.Exchange (toHeard_parts)

/-! ## The hypotheses on the caller -/

/-- **At "join"**: none of the key forms that the caller hands in at t names slot j. -/
def KeysClear {S : Type} (keys : S → Option (Array Aff)) (t : S) (j : Nat) : Prop :=
  ∀ KF, keys t = some KF → ∀ a ∈ KF, Clear a j

/-- **At "planes"**: none of the forms by which the caller reads the planes' matrix at the two
points, at t, names slot j. -/
def BitsClear {S : Type} (readers : Readers S) (t : S) (j : Nat) : Prop :=
  ∀ r, readers t = some r → ∀ e col a, r.1 e col = some a → Clear a j

/-! ## The condition, opened -/

/-- The condition `ClauseBy` at a place with a shape, opened into its clauses. F and rs are bound by
"∃" and held by what functions return at them alone: some values: not said to be the step's own. -/
theorem clause_open {T : LFace → List Fmt.Drawn → Bool} {p : P} {h : Shape}
    (hp : p.shape = some h) {o : Option Heard} (J : ClauseBy T p o) :
    ∃ (H : Heard) (F G : Fork) (rs : List Fmt.RoundView) (g : HeardV), o = some H ∧ 1 ≤ h.d ∧
      F.next = p.first ∧ hearV (faceOf h) F rs = some (g, G) ∧
      toHeard h (toHeardG g) = some H ∧ canDraw (faceOf h) (rs.map (·.drawn)) = true ∧
      T (faceOf h) (rs.map (·.drawn)) = true := by
  obtain ⟨H, eH, JH⟩ := J
  obtain ⟨h', F, G, rs, g, hp', a1, a2, a3, a4, a5, a6⟩ := JH.parts
  obtain rfl : h' = h := Option.some.inj (hp'.symm.trans hp)
  exact ⟨H, F, G, rs, g, eH, a1, a2, a3, a4, a5, a6⟩

/-! ## Coefficients of the seated forms -/

theorem sc_getD {KF : Array Aff} {j : Nat} (hK : ∀ a ∈ KF, Clear a j) (c : Nat) :
    sc (KF.getD c (Aff.ofConst zeroE)) j = 0 := by
  rw [Array.getD_eq_getD_getElem?]
  by_cases hc : c < KF.size
  · rw [Array.getElem?_eq_getElem hc]
    exact sc_clear (hK _ (Array.getElem_mem hc))
  · rw [Array.getElem?_eq_none (by omega)]
    exact sc_ofConst _ _

/-- On a slot that no key form names, the form of "join" has minus the coefficient of the key side's
last form. -/
theorem sc_joinForm (H : Heard) {KF : Array Aff} {j : Nat} (hK : ∀ a ∈ KF, Clear a j) :
    sc (_root_.Fo.joinForm H KF) j = - sc H.cEnd j := by
  have hb : ∀ c : Nat, sc (Aff.ofConst (subE H.alpha (scaleE c.toUInt64 H.theta)) -
      KF.getD c (Aff.ofConst zeroE)) j = 0 := by
    intro c
    rw [sc_sub, sc_ofConst, sc_getD hK]
    ring
  have hfold : sc ((List.range KF.size).foldl
      (fun (f : Aff) c =>
        Aff.addMul f
          (Aff.ofConst (subE H.alpha (scaleE c.toUInt64 H.theta)) -
            KF.getD c (Aff.ofConst zeroE))
          (H.e.getD c zeroE))
      (Aff.ofConst zeroE)) j = sc (Aff.ofConst zeroE) j :=
    sc_fold _ _ j hb _ _
  unfold _root_.Fo.joinForm
  rw [sc_sub, sc_add, hfold, sc_ofConst, sc_ofConst]
  ring

/-- On a slot that no reader's form names, the planes' value as a form has the coefficient 0. -/
theorem sc_atForm (H : Heard) (lm e : Nat) (bit : Nat → Nat → Aff) {j : Nat}
    (hb : ∀ col, sc (bit e col) j = 0) : sc (atForm H lm e bit) j = 0 := by
  unfold atForm
  rw [sc_fold (fun col => bit e col) (fun col => colWeight H lm e col) j hb, sc_ofConst]

/-! ## The three runs -/

variable {S : Type}

/-- **"objects".** -/
theorem objects_live (seat : Seat S Claim) (hf : ∀ a, (seat.claim a).form = a)
    (hc : ∀ a, (seat.claim a).eqFirst = none) {p : P} {h : Shape} (hp : p.shape = some h)
    {i : ℕ} {t : S} {z : List Claim × S} (hz : objectsRun seat i t = .ok z)
    (J : Clause p (seat.heard t)) {j : ℕ} (hj : j ∈ windowOf (faceOf h) .objects) :
    liveAt z.1 (p.first + j) = true := by
  obtain ⟨H, F, G, rs, g, eH, hd, hn, hh, hto, hcd, hgd⟩ := clause_open hp J
  obtain ⟨F1, H1, e1, e2, _⟩ := objects_cut seat (l := z.1) (s' := z.2) hz
  obtain rfl : H1 = H := Option.some.inj (e2.symm.trans eH)
  rw [objects_answer seat i e1 e2] at hz
  rw [← congrArg Prod.fst (Except.ok.inj hz)]
  show liveAt (H1.rows.toList.map seat.claim) _ = true
  obtain ⟨_, _, _, _, hrows, _⟩ := toHeard_parts hto
  rw [hrows, ← hn]
  exact live_of_sc seat hf hc (gives_pure hd hcd hh .objects (goodRun_of _ _ hgd .objects) hj)

/-- **"join".** Conditional on the hypothesis on the caller's key forms. -/
theorem join_live (seat : Seat S Claim) (hf : ∀ a, (seat.claim a).form = a)
    (hc : ∀ a, (seat.claim a).eqFirst = none) (keys : S → Option (Array Aff)) {p : P} {h : Shape}
    (hp : p.shape = some h) {i : ℕ} {t : S} {z : List Claim × S}
    (hz : joinRun seat keys i t = .ok z) (J : Clause p (seat.heard t)) {j : ℕ}
    (hj : j ∈ windowOf (faceOf h) .join) (hk : KeysClear keys t (p.first + j)) :
    liveAt z.1 (p.first + j) = true := by
  obtain ⟨H, F, G, rs, g, eH, hd, hn, hh, hto, hcd, hgd⟩ := clause_open hp J
  obtain ⟨F1, H1, e1, e2⟩ := join_heard seat keys (l := z.1) (s' := z.2) hz
  obtain rfl : H1 = H := Option.some.inj (e2.symm.trans eH)
  obtain ⟨KF, hK, _, hcl, _⟩ := joinRun_cut seat keys (cl := z.1) (s' := z.2) e1 e2 hz
  rw [hcl]
  show liveAt ([_root_.Fo.joinForm H1 KF].map seat.claim) _ = true
  refine live_of_sc seat hf hc ⟨_, List.mem_singleton.2 rfl, ?_⟩
  rw [sc_joinForm H1 (hk KF hK)]
  obtain ⟨point, form, hkeys, _, _, _, _, hce, _⟩ := toHeard_parts hto
  obtain ⟨a, ha, hne⟩ := gives_pure hd hcd hh .join (goodRun_of _ _ hgd .join) hj
  have ha' : a ∈ g.keys.map (·.2) := ha
  rw [hkeys] at ha'
  obtain rfl : a = form := List.mem_singleton.1 ha'
  rw [hce, ← hn]
  exact neg_ne_zero.2 hne

/-- **"planes".** Conditional on the hypothesis on the caller's readers. -/
theorem planes_live (seat : Seat S Claim) (hf : ∀ a, (seat.claim a).form = a)
    (hc : ∀ a, (seat.claim a).eqFirst = none) (lm : ℕ) (readers : Readers S) {p : P} {h : Shape}
    (hp : p.shape = some h) {i : ℕ} {t : S} {z : List Claim × S}
    (hz : planesRun seat lm readers i t = .ok z) (J : Clause p (seat.heard t)) {j : ℕ}
    (hj : j ∈ windowOf (faceOf h) .planes) (hb : BitsClear readers t (p.first + j)) :
    liveAt z.1 (p.first + j) = true := by
  obtain ⟨H, F, G, rs, g, eH, hd, hn, hh, hto, hcd, hgd⟩ := clause_open hp J
  obtain ⟨H1, r, e2, hr, hy⟩ := planesRun_claims seat lm readers i t z hz
  obtain rfl : H1 = H := Option.some.inj (e2.symm.trans eH)
  obtain ⟨_, eL, eB, _⟩ := toHeard_fields hto
  have hbit : ∀ e col, sc ((r.1 e col).getD {}) (p.first + j) = 0 := by
    intro e col
    cases hx : r.1 e col with
    | none => exact sc_empty _
    | some a => exact sc_clear (hb r hr e col a hx)
  have hat : ∀ e, sc (atForm H1 lm e fun e col => (r.1 e col).getD {}) (p.first + j) = 0 :=
    fun e => sc_atForm H1 lm e _ (hbit e)
  have hl : (planeForms H1 lm (fun e col => (r.1 e col).getD {})
      fun col => (r.2 col).getD {}).toList =
      [H1.leaves.rowForm oneE (Aff.scale (atForm H1 lm 0 fun e col => (r.1 e col).getD {})
          H1.leavesA),
        Aff.slot H1.sBit - atForm H1 lm 1 (fun e col => (r.1 e col).getD {}),
        countForm H1 lm fun col => (r.2 col).getD {}] := rfl
  rw [hy, hl]
  obtain ⟨a, ha, hne⟩ := gives_pure hd hcd hh .planes (goodRun_of _ _ hgd .planes) hj
  rw [hn] at hne
  have ha' : a ∈ [rowAff g.leaves oneE {}, Aff.slot g.sBit] := ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
  rcases ha' with rfl | rfl
  · refine live_of_sc seat hf hc ⟨_, List.mem_cons_self .., ?_⟩
    rw [eL, sc_leaves, hat 0, mul_zero, add_zero]
    exact hne
  · refine live_of_sc seat hf hc ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
    rw [sc_sub, hat 1, sub_zero, eB]
    exact hne

end ProofFile.Honest.K3.Good.Live

#print axioms ProofFile.Honest.K3.Good.Live.clause_open
#print axioms ProofFile.Honest.K3.Good.Live.sc_getD
#print axioms ProofFile.Honest.K3.Good.Live.sc_joinForm
#print axioms ProofFile.Honest.K3.Good.Live.sc_atForm
#print axioms ProofFile.Honest.K3.Good.Live.objects_live
#print axioms ProofFile.Honest.K3.Good.Live.join_live
#print axioms ProofFile.Honest.K3.Good.Live.planes_live
