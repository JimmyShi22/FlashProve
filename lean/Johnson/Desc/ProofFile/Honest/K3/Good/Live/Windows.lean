-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/Live/Windows.lean: the kind "lookup" (K3): which slots the
windows of a lookup's three runs of claims are, as numbers: at any shape, and at the two lookups of
an attention link, in the numbers of the link's plan. Theorems.

Terms. Honest/K3/GLOSSARY.md ("window", "run (of claims): objects, guests, planes, join", "slot",
"face"). In this file: W is the verifier's public structure (`Verify.Public`), a the plan of the
attention link 2 g + 1 (`Attention.Plan`), p the public parameters of a lookup's place (`placeAt`,
Johnson/Desc/First/Look/LookKind.lean). A run's window (`windowOf`, Honest/K3/GoodDraws.lean) counts
from the lookup's first slot, p.first.

What is shown.
  `sum_split`, `window_cover`, `window_lt`, `window_iff`: the three windows together are just the
    numbers below `Forest.elems h`.
  `via_next`: the seated hearing moves the ledger's next slot by `Forest.elems h`.
  `next_behind`: so behind an accepting step of a sub-protocol of the lookups' form (`FormAt`,
    Honest/K3/Law/MemberOne.lean) the ledger that the seat reads has the next slot p.first +
    `Forest.elems h`.
  `plan_msgs`, `ns_msgs`: the plan's number of slots is its number of scalars sent (a.ns = a.nMsg).
  `calls_att`: at the lookup on the calls: the shape is a.fs and the first slot is 0. So its windows
    are the slots below `Forest.elems a.fs`.
  `digits_att`: at the lookup on the digits: the shape is a.seam.tl.f9; the first slot is
    `Forest.elems a.fs + slotsOf (script a.own)`; the first slot and `Forest.elems a.seam.tl.f9` add
    up to a.nMsg. So its windows are the last `Forest.elems a.seam.tl.f9` slots below a.nMsg.

Hypotheses that remain. In `next_behind`: the form (`Fm`), the place's shape (`hp`) and the step's
acceptance (`hst`). In `via_next`: `hp`, and `hv`: the seated hearing returns. In `window_cover`,
`window_lt`: `h2`: the face has two planes at least; `hj`: j is below the face's slots, or in a
window. In `plan_msgs`: `e`: the planner returns the plan. In `calls_att`, `digits_att`: `hX`: W is
what `Verify.publicOf` returns; in `ns_msgs`: `hP`: the library's `PlanIs W`
(Johnson/Desc/First/Att/GuardPublic.lean), which holds at every such return (`planIs_public`,
there); `ha`: a is the plan number g; in `calls_att` and `digits_att` also: W.p4 holds (`h4`: a
group has two links), and the place's parameters are there (`e`). `sum_split` has a hypothesis
without a name (j < l.sum).

How the proof goes. By the library's `place_att` (Johnson/Desc/First/Look/K3PlaceLetters.lean),
`place_digits`, `planIs_tiles` (Johnson/Desc/First/Att/K05PlanOfPublic.lean) and `digits_shape`
(Johnson/Desc/First/Att/GuardPlanDigits.lean). `plan_msgs` takes the planner's text apart, in the
way of the library's `planA_rows0` (OnBytes/Tie/Pv/Lookup/Ends/BatRows.lean), and with that file's
own device: a local tactic macro, "dead", under `set_option hygiene false`, which closes the branch
of a test in which the planner throws.


Limits. Numbers alone: that a run's claims name these slots, and with which coefficients, is for the
files on the runs in this folder. The plan's numbers are given at an attention link alone: nothing
is said on the head's link or on a layers' link (the library's `place_head` and `place_lay` are in
the same file as `place_att`). `next_atSite` (Honest/K3/Law/Thread/NextBehind.lean) has the sentence
of `next_behind` at the description's own member, under two more hypotheses (a public test on the
slots in use, and the lookup's condition on the state in front). `sum_split` and `window_cover` are
also in Honest/K3/Good/AtBatch.lean [not in this library], in another namespace; that file is not
imported.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.Clause
import Johnson.Desc.ProofFile.Honest.K3.Good.Gives
import Johnson.Desc.ProofFile.Honest.K3.Law.SlotsElems
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CEndBelow
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.StateBehind
import Johnson.Desc.First.Look.K3PlaceLetters
import Johnson.Desc.First.Att.K05PlanOfPublic
import Johnson.Desc.First.Att.GuardPlanDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good.Live
open OnBytes OnBytes.Model
open OnBytes.Model.Forest (Shape Heard)
open VerifiableInference.Desc.First.Look (P placeAt placeAt_iff place_att)
open VerifiableInference.Desc.First.Att.P (PlanIs planIs_public planIs_tiles odd_facts slotsOf script)
open VerifiableInference.Desc.K3 (faceOf)
open VerifiableInference.Desc.K3.Law (hearVia)
open ProofFile.Honest.K3.Law
open Fo.BatRows (bindE_ok)

/-! ## At any shape -/

/-- A number below a list's sum lies in the stretch of one member. -/
theorem sum_split : ∀ (l : List Nat) (j : Nat), j < l.sum →
    ∃ n, n < l.length ∧ (l.take n).sum ≤ j ∧ j < (l.take (n + 1)).sum
  | [], j, h => by simp at h
  | a :: l, j, h => by
    by_cases ha : j < a
    · exact ⟨0, by simp, by simp, by simpa using ha⟩
    · rw [List.sum_cons] at h
      obtain ⟨n, h1, h2, h3⟩ := sum_split l (j - a) (by omega)
      refine ⟨n + 1, by simpa using h1, ?_, ?_⟩
      · rw [List.take_succ_cons, List.sum_cons]
        omega
      · rw [List.take_succ_cons, List.sum_cons]
        omega

/-- Each of the lookup's slots is in the window of some run. -/
theorem window_cover {f : LFace} (h2 : 2 ≤ f.planes) {j : Nat} (hj : j < f.slots) :
    ∃ r, j ∈ windowOf f r := by
  rw [← slots_stages f h2] at hj
  obtain ⟨n, h1, h3, h4⟩ := sum_split _ j hj
  rw [List.length_map] at h1
  have hs : (stages f)[n]? = some (stages f)[n] := List.getElem?_eq_getElem h1
  obtain ⟨a1, a2⟩ := slotsIn_at hs
  have e1 : (((stages f).map (Stage.slots f)).take n).sum = slotsIn f n := by
    unfold slotsIn
    rw [List.map_take]
  have e2 : (((stages f).map (Stage.slots f)).take (n + 1)).sum = slotsIn f (n + 1) := by
    unfold slotsIn
    rw [List.map_take]
  rw [e1] at h3
  rw [e2, a2] at h4
  unfold Stage.slots at h4
  have hm : (stages f)[n] ∈ stages f := List.getElem_mem h1
  by_cases ho : j - slotsIn f n < (stages f)[n].own f
  · refine ⟨runOf f (stages f)[n] false, List.mem_flatMap.2 ⟨_, hm, List.mem_append_left _ ?_⟩⟩
    rw [if_pos (by simp)]
    exact List.mem_map.2 ⟨j - slotsIn f n, List.mem_range.2 ho, by rw [a1]; omega⟩
  · refine ⟨runOf f (stages f)[n] true, List.mem_flatMap.2 ⟨_, hm, List.mem_append_right _ ?_⟩⟩
    rw [if_pos (by simp)]
    exact List.mem_map.2 ⟨j - slotsIn f n - (stages f)[n].own f, List.mem_range.2 (by omega),
      by rw [a1]; omega⟩

/-- A window holds slots of the lookup alone. -/
theorem window_lt {f : LFace} (h2 : 2 ≤ f.planes) {r : Run} {j : Nat} (hj : j ∈ windowOf f r) :
    j < f.slots := by
  unfold windowOf at hj
  obtain ⟨s, hs, hj⟩ := List.mem_flatMap.1 hj
  obtain ⟨n, hn⟩ := List.getElem?_of_mem hs
  obtain ⟨a1, a2⟩ := slotsIn_at hn
  have hle : slotsIn f (n + 1) ≤ f.slots := by
    have h := slotsIn_mono f (Nat.le_max_left (n + 1) (stages f).length)
    have e : slotsIn f (max (n + 1) (stages f).length) = f.slots := by
      unfold slotsIn
      rw [List.take_of_length_le (Nat.le_max_right _ _), slots_stages f h2]
    rwa [e] at h
  unfold Stage.slots at a2
  rcases List.mem_append.1 hj with h1 | h1
  · split at h1
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h1
      have := List.mem_range.1 hi
      omega
    · simp at h1
  · split at h1
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h1
      have := List.mem_range.1 hi
      omega
    · simp at h1

/-- **The three windows together are just the numbers below `Forest.elems h`.** -/
theorem window_iff (h : Shape) (j : Nat) :
    j < Forest.elems h ↔ ∃ r, j ∈ windowOf (faceOf h) r := by
  have h2 : 2 ≤ (faceOf h).planes := by
    show 2 ≤ 32
    omega
  rw [← Spec.slots_elems]
  exact ⟨window_cover h2, fun ⟨_, hr⟩ => window_lt h2 hr⟩

/-- The seated hearing moves the ledger's next slot by `Forest.elems h`. -/
theorem via_next {p : P} {h : Shape} {F G : Fork} {rs : List Fmt.RoundView} {H : Heard}
    (hp : p.shape = some h) (hv : hearVia p F rs = some (H, G)) :
    G.next = F.next + Forest.elems h := by
  obtain ⟨_, g, h1, _⟩ := via_parts hp hv
  rw [← Spec.slots_elems]
  exact AtThr.messagesV_next (hearV_messages h1).2

/-- **Behind an accepting step of a sub-protocol of the lookups' form the ledger's next slot is the
place's first slot plus `Forest.elems h`.** Conditional on the form and on the acceptance. -/
theorem next_behind {Cl : Type} {claim : Aff → Cl} {X : Verify.Public} {i : Nat} {d : Bool}
    {p : P} {b : VerifiableInference.Desc.Block VerifiableInference.Desc.First.S Cl}
    (Fm : FormAt claim X i d p b) {h : Shape} (hp : p.shape = some h) (ft : Nat)
    (s t : VerifiableInference.Desc.First.S) (n : Nat) (rs : List Fmt.RoundView)
    (c : List VerifiableInference.Desc.OpenedColumn) (hst : b.step ft s rs c = .ok (t, n)) :
    ∃ G, (seatOf claim d).fork t = some G ∧ G.next = p.first + Forest.elems h := by
  obtain ⟨F, H, G, a1, a2, _, a4, a5, hQ⟩ := AtThr.form_state Fm ft s t n rs c hst
  have hG : (seatOf claim d).fork ((seatOf claim d).put s H G) = some G := by
    cases d with
    | false => exact (ProofFile.Honest.K3.Law.calls_put claim s H G a1 a2).2.1
    | true => exact (ProofFile.Honest.K3.Law.digits_put claim s H G a1).2.1
  obtain ⟨_, c', hc'⟩ := behind_hands claim hQ hG
  refine ⟨_, hc', ?_⟩
  show G.next = _
  rw [via_next hp a5, beq_iff_eq.1 a4]

/-! ## The plan's two counts -/

set_option hygiene false in
/-- Closes the branch of a test in which something is thrown. -/
local macro "dead" : tactic => `(tactic| first
  | (obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done)
  | (obtain ⟨_, _, e⟩ := bindE_ok e; obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done))

/-- What the planner returns has as many slots as scalars sent. -/
theorem plan_msgs (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (A : Attention.Plan) (e : Attention.plan settings i cf = .ok A) : A.ns = A.nMsg := by
  unfold Attention.plan at e
  dsimp only at e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨⟨S, fs⟩, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨seam0, _, e⟩ := bindE_ok e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨seam, _, e⟩ := bindE_ok e
  cases e
  rfl

variable {W : Verify.Public} {g : ℕ} {a : Attention.Plan}

/-- So has each attention plan of the public structure. -/
theorem ns_msgs (hP : PlanIs W) (ha : W.A[g]? = some a) : a.ns = a.nMsg := by
  obtain ⟨A0, pf, h0, e⟩ := hP g a ha
  subst e
  exact plan_msgs _ _ _ A0 h0

/-! ## At an attention link -/

variable {pol KL : ByteArray} {layout : Option ByteArray}

/-- **The lookup on the calls of an attention link**: its shape and its first slot. -/
theorem calls_att (hX : Verify.publicOf pol KL layout = .ok W) (h4 : W.p4 = true)
    (ha : W.A[g]? = some a) {p : P} (e : placeAt W (2 * g + 1) false = some p) :
    p.shape = some a.fs ∧ p.first = 0 := by
  obtain ⟨hn, h0, eg⟩ := odd_facts (W := W) (g := g) h4
  obtain ⟨a', ha', e1, _, e2, _⟩ := place_att hX e hn h0
  rw [eg] at ha'
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  exact ⟨e1, e2⟩

/-- **The lookup on the digits of an attention link**: its shape and its first slot, in the plan's
numbers. -/
theorem digits_att (hX : Verify.publicOf pol KL layout = .ok W) (h4 : W.p4 = true)
    (ha : W.A[g]? = some a) {p : P} (e : placeAt W (2 * g + 1) true = some p) :
    p.shape = some a.seam.tl.f9 ∧ p.first = Forest.elems a.fs + slotsOf (script a.own) ∧
      p.first + Forest.elems a.seam.tl.f9 = a.nMsg := by
  have hP := planIs_public hX
  have ht := planIs_tiles hP ha
  obtain ⟨x, hx, rfl⟩ := placeAt_iff.1 e
  obtain ⟨xd, hxd, e1, _⟩ :=
    VerifiableInference.Desc.First.Att.P.place_digits h4 ha (by omega)
  obtain rfl : xd = x := Option.some.inj (hxd.symm.trans hx)
  have hf : (P.ofPlace (Params.settingOf W.P.frame) true xd).first = xd.F.next := rfl
  refine ⟨VerifiableInference.Desc.First.Att.P.digits_shape hP h4 ha hx _, ?_, ?_⟩
  · rw [hf, e1]
    omega
  · rw [hf, e1, ← ns_msgs hP ha]
    omega

end ProofFile.Honest.K3.Good.Live

#print axioms ProofFile.Honest.K3.Good.Live.sum_split
#print axioms ProofFile.Honest.K3.Good.Live.window_cover
#print axioms ProofFile.Honest.K3.Good.Live.window_lt
#print axioms ProofFile.Honest.K3.Good.Live.window_iff
#print axioms ProofFile.Honest.K3.Good.Live.via_next
#print axioms ProofFile.Honest.K3.Good.Live.next_behind
#print axioms ProofFile.Honest.K3.Good.Live.plan_msgs
#print axioms ProofFile.Honest.K3.Good.Live.ns_msgs
#print axioms ProofFile.Honest.K3.Good.Live.calls_att
#print axioms ProofFile.Honest.K3.Good.Live.digits_att
