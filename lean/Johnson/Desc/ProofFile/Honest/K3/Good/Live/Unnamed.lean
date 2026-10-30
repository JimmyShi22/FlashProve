-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/Live/Unnamed.lean: the kind "lookup" (K3): at every return of
the lookup's seated runs "objects" and "planes", at a state that holds what the lookup's hearing
left: no claim of the run names a slot outside the lookup's own stretch of slots. At "planes"
conditional on the calling kind's forms not naming that slot. Definitions and theorems.

Terms. Honest/K3/GLOSSARY.md ("slot", "run (of claims): objects, guests, planes, join", "seat",
"caller"). In this file: "no claim names slot j" is `unnamedAt`
(Johnson/Desc/K9/Honest/SlotsLive.lean). p holds the place's public parameters, h is its shape. The
lookup's own stretch is from p.first on, `Forest.elems h` slots.

What is defined and shown.
  `Outside p h j`: slot j is not in the lookup's own stretch.
  `PinsClear readers t j`: a hypothesis on the caller at "planes": none of the forms by which the
    caller reads the planes' matrix for the counts, at the state t, names slot j. (The other,
    `BitsClear`, is in Honest/K3/Good/Live/Runs.lean.)
  `clear_addSlot_fold`, `clear_addSlots`, `clear_rowForm`: the verifier program's row form of a
    sumcheck (`Psc.rowForm`, OnBytes/Model/Psc.lean) names a slot only if the start form or the kept
    form names it, or it is one of the sumcheck's own.
  `clear_atForm`, `clear_countForm`: the planes' value and the counts' sum as forms name a slot only
    if a form of the caller's names it.
  `objects_unnamed`, `planes_unnamed`: the title's sentence.

Hypotheses that remain.
  `hf`: the seat's claim of a form has that form.
  `hp`: the place's parameters make the shape h. `hz`: the run returns.
  `J`: what the seat reads as heard at the state meets the condition of
    Honest/K3/Good/Live/Clause.lean, at any test T: the samples' values are not used.
  `hj`: `Outside p h j`. That a given slot of another kind (at the head's link: the slot of the
    merge) is outside the stretches of the link's two lookups is a fact on the link's plan: it is
    shown nowhere in this folder.
  `hb`, `hq` ("planes"): the two hypotheses on the caller, at slot j: facts on the calling kind's
    text. Shown in part: Honest/K3/Good/Live/Bridges.lean (`bitsClear_att`, `pinsClear_att`): both
    at the readers of an attention link, at every plan, state and slot; nothing there on the head's
    link or on a layers' link.
  `ha`, `hs`, `hk`: (in the helpers `clear_addSlots`, `clear_rowForm`) the form in front, the start
    form and the kept form do not name slot j. In the same two helpers `hj` is another sentence: j
    lies in front of or behind the stretch. `hb`: (in `clear_atForm`) no column's form names slot j;
    `hq`: (in `clear_countForm`) no column's pin form does.

How the proof goes. `heard_names` (Honest/K3/Parts/NamesOwn.lean) says which slots the heard rows,
the start form of the leaves' sumcheck, its own slots and the bits' end slot are, from the hearing's
return alone. `walk_length` (Honest/K3/Law/Seated.lean) counts the own slots in the program's
structure.

Users. Honest/K3/Good/Live/Bridges.lean and Honest/K3/Good/Live/LiveGuards.lean
[not in this library] import this file.

Limits. Nothing on "join". No instance of the hypotheses together is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.Runs
import Johnson.Desc.ProofFile.Honest.K3.Law.SlotsElems

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good.Live
open OnBytes (E zeroE oneE subE mulE)
open OnBytes.Model (Fork Aff Psc addSlot addSlots)
open OnBytes.Model.Forest (Shape Heard)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First.Look (P)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf toHeard toHeardG toPsc Seat Readers planesRun)
open VerifiableInference.Desc.K9H (unnamedAt)
open VerifiableInference.OnPublicFiles (objectsRun objects_cut objects_answer)
open VerifiableInference.Desc.Kinds.Head.Law (planesRun_claims)
open VerifiableInference.Desc.Kinds.Head.Law.Planes (planeForms atForm countForm colWeight nCols)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.Exchange (toHeard_parts)
open ProofFile.Honest.K3.Parts (heard_names)

/-- Slot j is not in the lookup's own stretch of slots. -/
def Outside (p : P) (h : Shape) (j : Nat) : Prop :=
  j < p.first ∨ p.first + OnBytes.Model.Forest.elems h ≤ j

/-- **At "planes"**: none of the forms by which the caller reads the planes' matrix for the counts,
at t, names slot j. -/
def PinsClear {S : Type} (readers : Readers S) (t : S) (j : Nat) : Prop :=
  ∀ r, readers t = some r → ∀ col a, r.2 col = some a → Clear a j

/-! ## The seated forms -/

theorem clear_addSlot_fold {j : Nat} : ∀ (u : List E) (first : Nat) (f : Aff), Clear f j →
    (j < first ∨ first + u.length ≤ j) → Clear (u.foldl addSlot (first, f)).2 j
  | [], _, _, hf, _ => hf
  | x :: u, first, f, hf, h => by
    rw [List.foldl_cons]
    show Clear (u.foldl addSlot (first + 1, Aff.addMul f (Aff.slot first) x)).2 j
    rw [List.length_cons] at h
    exact clear_addSlot_fold u (first + 1) _ (clear_addMul hf (clear_slot (by omega)) x) (by omega)

theorem clear_addSlots {a : Aff} {first j : Nat} (form : Array E) (ha : Clear a j)
    (hj : j < first ∨ first + form.size ≤ j) : Clear (addSlots a first form) j := by
  unfold addSlots
  rw [← Array.foldl_toList]
  exact clear_addSlot_fold form.toList first a ha (by rwa [Array.length_toList])

/-- The program's row form names a slot only if the start form or the kept form names it, or it is
one of the sumcheck's own. -/
theorem clear_rowForm (q : Psc) (S0 : E) {kept : Aff} {j : Nat} (hs : Clear q.start j)
    (hk : Clear kept j) (hj : j < q.first ∨ q.first + q.walk.1.length ≤ j) :
    Clear (q.rowForm S0 kept) j := by
  unfold Psc.rowForm
  exact clear_addMul (clear_addMul (clear_addSlots _ (clear_ofConst _ _) (by simpa using hj))
    (clear_sub (clear_ofConst _ _) hs) _) hk _

theorem clear_atForm (H : Heard) (lm e : Nat) (bit : Nat → Nat → Aff) {j : Nat}
    (hb : ∀ col, Clear (bit e col) j) : Clear (atForm H lm e bit) j := by
  unfold atForm
  exact clear_fold _ (fun f col hf => clear_addMul hf (hb col) _) _ _ (clear_ofConst _ _)

theorem clear_countForm (H : Heard) (lm : Nat) (pin : Nat → Aff) {j : Nat}
    (hq : ∀ col, Clear (pin col) j) : Clear (countForm H lm pin) j := by
  unfold countForm
  exact clear_fold _ (fun f col hf => clear_add hf (hq col)) _ _ (clear_ofConst _ _)

/-! ## The two runs -/

variable {S : Type}

/-- **"objects" names no slot outside the lookup's own stretch.** -/
theorem objects_unnamed {T : LFace → List Fmt.Drawn → Bool} (seat : Seat S Claim)
    (hf : ∀ a, (seat.claim a).form = a) {p : P} {h : Shape} (hp : p.shape = some h) {i : ℕ}
    {t : S} {z : List Claim × S} (hz : objectsRun seat i t = .ok z)
    (J : ClauseBy T p (seat.heard t)) {j : ℕ} (hj : Outside p h j) : unnamedAt z.1 j = true := by
  obtain ⟨H, F, G, rs, g, eH, _, hn, hh, hto, _, _⟩ := clause_open hp J
  obtain ⟨F1, H1, e1, e2, _⟩ := objects_cut seat (l := z.1) (s' := z.2) hz
  obtain rfl : H1 = H := Option.some.inj (e2.symm.trans eH)
  rw [objects_answer seat i e1 e2] at hz
  rw [← congrArg Prod.fst (Except.ok.inj hz)]
  show unnamedAt (H1.rows.toList.map seat.claim) _ = true
  obtain ⟨_, _, _, _, hrows, _⟩ := toHeard_parts hto
  obtain ⟨hokf, hm⟩ := hearV_messages hh
  obtain ⟨n1, _⟩ := heard_names (two_le_planes_of_ok _ hokf) hm
  rw [hrows]
  unfold Outside at hj
  rw [← ProofFile.Honest.K3.Law.Spec.slots_elems, ← hn] at hj
  exact unnamed_of_clear seat hf fun a ha => clear_of_in (n1 a ha) hj

/-- **"planes" names no slot outside the lookup's own stretch that the caller's forms do not name.**
Conditional on the two hypotheses on the caller's readers. -/
theorem planes_unnamed {T : LFace → List Fmt.Drawn → Bool} (seat : Seat S Claim)
    (hf : ∀ a, (seat.claim a).form = a) (lm : ℕ) (readers : Readers S) {p : P} {h : Shape}
    (hp : p.shape = some h) {i : ℕ} {t : S} {z : List Claim × S}
    (hz : planesRun seat lm readers i t = .ok z) (J : ClauseBy T p (seat.heard t)) {j : ℕ}
    (hj : Outside p h j) (hb : BitsClear readers t j) (hq : PinsClear readers t j) :
    unnamedAt z.1 j = true := by
  obtain ⟨H, F, G, rs, g, eH, _, hn, hh, hto, _, _⟩ := clause_open hp J
  obtain ⟨H1, r, e2, hr, hy⟩ := planesRun_claims seat lm readers i t z hz
  obtain rfl : H1 = H := Option.some.inj (e2.symm.trans eH)
  obtain ⟨_, eL, eB, _⟩ := toHeard_fields hto
  obtain ⟨hokf, hm⟩ := hearV_messages hh
  obtain ⟨_, _, n3, n4, n5, n6, n7⟩ := heard_names (two_le_planes_of_ok _ hokf) hm
  unfold Outside at hj
  rw [← ProofFile.Honest.K3.Law.Spec.slots_elems, ← hn] at hj
  have hbit : ∀ e col, Clear ((r.1 e col).getD {}) j := by
    intro e col
    cases hx : r.1 e col with
    | none => exact clear_empty _
    | some a => exact hb r hr e col a hx
  have hpin : ∀ col, Clear ((r.2 col).getD {}) j := by
    intro col
    cases hx : r.2 col with
    | none => exact clear_empty _
    | some a => exact hq r hr col a hx
  have hl : (planeForms H1 lm (fun e col => (r.1 e col).getD {})
      fun col => (r.2 col).getD {}).toList =
      [H1.leaves.rowForm oneE (Aff.scale (atForm H1 lm 0 fun e col => (r.1 e col).getD {})
          H1.leavesA),
        Aff.slot H1.sBit - atForm H1 lm 1 (fun e col => (r.1 e col).getD {}),
        countForm H1 lm fun col => (r.2 col).getD {}] := rfl
  rw [hy, hl]
  refine unnamed_of_clear seat hf fun a ha => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · rw [eL]
    refine clear_rowForm _ _ (clear_of_in n3 hj) (clear_scale (clear_atForm H1 lm 0 _ (hbit 0)) _) ?_
    rw [walk_length]
    show j < g.leaves.first ∨ g.leaves.first + _ ≤ j
    omega
  · rw [eB]
    exact clear_sub (clear_slot (by omega)) (clear_atForm H1 lm 1 _ (hbit 1))
  · exact clear_countForm H1 lm _ hpin

end ProofFile.Honest.K3.Good.Live

#print axioms ProofFile.Honest.K3.Good.Live.clear_addSlot_fold
#print axioms ProofFile.Honest.K3.Good.Live.clear_addSlots
#print axioms ProofFile.Honest.K3.Good.Live.clear_rowForm
#print axioms ProofFile.Honest.K3.Good.Live.clear_atForm
#print axioms ProofFile.Honest.K3.Good.Live.clear_countForm
#print axioms ProofFile.Honest.K3.Good.Live.objects_unnamed
#print axioms ProofFile.Honest.K3.Good.Live.planes_unnamed
