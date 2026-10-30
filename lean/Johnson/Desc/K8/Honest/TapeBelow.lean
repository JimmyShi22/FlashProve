-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/TapeBelow.lean: THE PLAIN FUNCTIONS ON A LEDGER AND A TAPE (`Fl`,
OnBytes/K/Kc/Flat.lean): MORE LAWS FOR THE LIBRARY's RULE `Meaning.HKT.Walk D x Q`
(Johnson/Meaning/HKTDrawn.lean: from a tape all of whose drawn elements have the property D the
routine x leaves such a tape, and its value has Q): EVERY CHALLENGE THAT A MASKED SUMCHECK GATHERS
HAS D; AND, WHERE 0 HAS D AND EVERY COORDINATE OF THE POINT FROM WHICH IT STARTS HAS D, SO HAS EVERY
COORDINATE OF THE POINT THAT A RUN OF LEVELS OF A PRODUCT TREE LEAVES (`Prod.run`,
Johnson/Desc/First/Prod/Level.lean). General in D, as that file is; it is called at D := «the words
lie below the prime». Lemmas on the verifier's own text; none of the library's goals.

  `walk_foldlM`, `walk_mapM` two rules more: a fold of steps; a list of steps
  `walk_pointAll` a drawn point: each of its coordinates has D (the library's `walk_point` says
                   True)
  `PscAll D p`, `walk_pscBeginR`, `walk_pscRoundR`, `walk_roundInR`, `walk_pscEndsR` the masked
                   sumcheck, with a postcondition on the challenges r
  **`walk_whole`** the stand-in for a whole masked sumcheck: its challenges
  `layBack_all` challenges laid back into a point of zeros
  `walk_level`, `PointAll D s`, `walk_turn`, **`walk_run`** a level; a turn (whatever point it
                   starts from); a run of levels, from a point that is PointAll
By: the library's `Good`, `Walk`, its rules `walk_pure`, `walk_bind`, `walk_mono`, its steps
`walk_ask`, `walk_take`, `walk_change`, `walk_must`, `walk_need`, `walk_onTape`, `walk_read`,
`walk_readSum`, `walk_answer`, `walk_empty`, `walk_pscRow`, `good_closeN`, `good_closeOne` (all
Johnson/Meaning/HKTDrawn.lean) · its instance LawfulMonad Fl (OnBytes/Desc/First/FlGrows.lean), for
List.mapM_cons.
WRITTEN A FURTHER TIME, WITH ANOTHER POSTCONDITION: the four walks through the masked sumcheck are,
bind by bind, the library's `walk_pscBegin`, `walk_pscRound`, `walk_roundIn`, `walk_pscEnds`
(HKTDrawn.lean), which follow the field eps; these follow the field r.
KIN IN THE LIBRARY: `walk_foldlM` is in the manner of `grows_foldlM`
(OnBytes/Desc/First/FlGrows.lean), the like rule for the class `Grows`. HKTDrawn.lean's
`walk_levelRounds`, `walk_levelIn` walk `Fl.levelIn` (OnBytes/K/Kc/Flat.lean), with the
postcondition True; `Prod.level` is another text (Prod/Level.lean's head says how it differs).
Johnson/Top/H/Keep/CEndTurns.lean carries «the words lie below the prime» through the lookup on a
road of its own (`AllOk`, `at_ok`, `evs_ok`, `level_end2`, `lkPad_end2`), to another end: the factor
beta is not 0. None hands the point that a run of levels leaves.
KIN, AND FIRST: that the words of every coordinate of zy lie below the prime where the rounds'
sampled words do is shown, on another road (the structure that the challenges alone make), behind an
accepting step of the member at the lookup on the digits, at all 25 segments, under the library's
`P5J.AtMgA` and one premise more, in Johnson/Desc/ProofFile/Honest/K3/Law/Thread/DigitsPointsAt.lean
(`digits_points_link`, `ok_zy_at`, `ok_layBack`).
Limits. From a return alone: nothing says that a function returns. ON WHAT IS DRAWN ALONE: nothing
on the elements that are sent. Nothing on the ledger.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Meaning.HKTDrawn
import Johnson.Desc.First.Prod.Level
import OnBytes.Desc.First.FlGrows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.K.Kc
open _root_.Meaning.HKT (Good Walk walk_pure walk_bind walk_mono walk_ask walk_take walk_change
  walk_must walk_need walk_onTape walk_read walk_readSum walk_answer walk_empty walk_pscRow
  good_closeN good_closeOne)

variable {D : E → Prop}

/-- A fold of steps. -/
theorem walk_foldlM {α σ : Type} {f : σ → α → Fl σ} {Q : σ → Prop}
    (hf : ∀ s a, Q s → Walk D (f s a) Q) : ∀ (l : List α) (s : σ), Q s → Walk D (l.foldlM f s) Q
  | [], s, hs => by
    rw [List.foldlM_nil]
    exact walk_pure s hs
  | a :: l, s, hs => by
    rw [List.foldlM_cons]
    exact walk_bind (hf s a hs) fun s' hs' => walk_foldlM hf l s' hs'

/-- A list of steps whose values are not looked at. -/
theorem walk_mapM {α β : Type} {f : α → Fl β} (hf : ∀ a, Walk D (f a) fun _ => True) :
    ∀ l : List α, Walk D (l.mapM f) fun _ => True
  | [] => by
    rw [List.mapM_nil]
    exact walk_pure _ trivial
  | a :: l => by
    rw [List.mapM_cons]
    exact walk_bind (hf a) fun _ _ => walk_bind (walk_mapM hf l) fun _ _ => walk_pure _ trivial

/-- The drawn point: each of its coordinates. -/
theorem walk_pointAll (r : RoundName) (n : Nat) :
    Walk D (Fl.point r n) fun v => ∀ x ∈ v.toList, D x :=
  walk_onTape fun t a u g e => by
    unfold Fl.pointOn at e
    obtain ⟨⟨d, u'⟩, e1, e⟩ := Option.map_eq_some_iff.mp e
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact good_closeN g e1

variable (D) in
/-- Every challenge that a masked sumcheck has gathered has the property. -/
def PscAll (p : Psc) : Prop := ∀ x ∈ p.r.toList, D x

theorem walk_pscBeginR (C : Aff) : Walk D (Fl.pscBegin C) (PscAll D) := by
  unfold Fl.pscBegin Fl.pscBeginAt Fl.publicPart
  refine walk_bind (walk_ask _) fun _ _ => ?_
  refine walk_bind (Q1 := PscAll D) ?_ fun p hp => walk_pure _ hp
  refine walk_bind (walk_take _) fun _ _ => walk_bind walk_readSum fun _ _ =>
    walk_bind (walk_answer _) fun _ _ => walk_pure _ ?_
  intro x hx
  simp at hx

theorem walk_pscRoundR (p : Psc) (w : OnBytes.Psc.Weight) (name : String) (nz : Nat)
    (hp : PscAll D p) :
    Walk D (Fl.pscRound p w (closeOne name nz)) fun y => D y.1 ∧ PscAll D y.2 := by
  unfold Fl.pscRound
  refine walk_bind (walk_must _) fun _ _ => walk_bind (walk_read _) fun _ _ =>
    walk_bind (walk_must _) fun _ _ =>
    walk_bind (walk_onTape (Q := D) fun _ _ _ g e => good_closeOne g e) fun r hr =>
    walk_bind (walk_take _) fun _ _ => walk_pure _ ⟨hr, ?_⟩
  intro x hx
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact hp x hx
  · exact hr

theorem walk_roundInR (form : RoundForm) (p : Psc) (z : E) (degree : Nat) (hp : PscAll D p) :
    Walk D (Fl.roundIn form p z degree) fun y => D y.1 ∧ PscAll D y.2 := by
  unfold Fl.roundIn
  exact walk_bind (walk_must _) fun _ _ => walk_bind (walk_need _) fun w _ =>
    walk_pscRoundR p w _ _ hp

theorem walk_pscEndsR (p : Psc) (dY n : Nat) (hp : PscAll D p) :
    Walk D (Fl.pscEnds p dY n) fun y => PscAll D y.2 := by
  unfold Fl.pscEnds
  refine walk_bind (walk_must _) fun _ _ => walk_bind (walk_pscRoundR p _ _ _ hp) fun y hy => ?_
  obtain ⟨beta, q⟩ := y
  exact walk_bind (walk_read _) fun _ _ => walk_bind (walk_must _) fun _ _ =>
    walk_bind (walk_empty _) fun _ _ => walk_bind (walk_take _) fun _ _ =>
      walk_bind (walk_change _) fun _ _ => walk_pure _ hy.2

/-- **The masked sumcheck's challenges.** -/
theorem walk_whole (C : Aff) (zs : List E) (dY n : Nat) (endTerm : List E → E) :
    Walk D (Prod.wholeStandIn C zs dY n endTerm) fun w => ∀ x ∈ w.challenges, D x := by
  unfold Prod.wholeStandIn
  refine walk_bind (walk_pscBeginR C) fun p hp => ?_
  refine walk_bind (walk_foldlM (Q := PscAll D) (fun q z hq =>
    walk_bind (walk_roundInR _ q z _ hq) fun x hx => walk_pure _ hx.2) zs p hp) fun q hq => ?_
  refine walk_bind (walk_pscEndsR q dY n hq) fun y hy => ?_
  obtain ⟨sEnd, q'⟩ := y
  exact walk_bind (walk_mapM (fun i => walk_ask _) _) fun _ _ =>
    walk_bind (walk_mono (walk_pscRow _ _ _) fun _ _ => trivial) fun _ _ => walk_pure _ hy

/-- Laying challenges back into a point of zeros. -/
theorem layBack_all (h0 : D zeroE) (m : Nat) (order : List Nat) (cs : List E)
    (h : ∀ x ∈ cs, D x) : ∀ x ∈ (Prod.layBack m order cs).toList, D x := by
  unfold Prod.layBack
  have key : ∀ (l : List (Nat × E)) (r : Array E), (∀ y ∈ l, D y.2) → (∀ x ∈ r.toList, D x) →
      ∀ x ∈ (l.foldl (fun (r : Array E) y => r.set! (m - 1 - y.1) y.2) r).toList, D x := by
    intro l
    induction l with
    | nil => exact fun r _ hr => hr
    | cons y l ih =>
      intro r hl hr
      rw [List.foldl_cons]
      refine ih _ (fun z hz => hl z (List.mem_cons_of_mem _ hz)) fun x hx => ?_
      rw [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds] at hx
      rcases List.mem_or_eq_of_mem_set hx with hx | rfl
      · exact hr x hx
      · exact hl y List.mem_cons_self
  refine key _ _ (fun y hy => h y.2 (List.of_mem_zip hy).2) fun x hx => ?_
  rw [Array.toList_replicate] at hx
  rw [List.eq_of_mem_replicate hx]
  exact h0

/-- **One level.** -/
theorem walk_level (h0 : D zeroE) (m : Nat) (z : Array E) (order : List Nat) (C : Aff) :
    Walk D (Prod.level m z order C) fun o => D o.xi ∧ ∀ x ∈ o.r.toList, D x := by
  unfold Prod.level
  exact walk_bind (walk_whole _ _ _ _ _) fun w hw => walk_bind (walk_answer _) fun xi hxi =>
    walk_pure _ ⟨hxi, layBack_all h0 m order _ fun x hx => hw x (List.mem_of_mem_take hx)⟩

variable (D) in
/-- Every coordinate of the point that a run of levels carries has the property. -/
def PointAll (s : Prod.Carried) : Prop := ∀ x ∈ s.point.toList, D x

theorem walk_turn (h0 : D zeroE) (order : List Nat) (s : Prod.Carried) (m : Nat) :
    Walk D (Prod.turn order s m) (PointAll D) := by
  unfold Prod.turn
  refine walk_bind (walk_level h0 _ _ _ _) fun o ho => walk_pure _ ?_
  intro x hx
  have hx' : x ∈ (#[o.xi] ++ o.r).toList := hx
  simp only [Array.toList_append, List.mem_append, List.mem_singleton] at hx'
  rcases hx' with hx' | hx'
  · have e : x = o.xi := by simpa using hx'
    rw [e]
    exact ho.1
  · exact ho.2 x hx'

/-- **A RUN OF LEVELS: every coordinate of the point that it leaves has the property.** -/
theorem walk_run (h0 : D zeroE) (m0 n : Nat) (orders : Nat → List Nat) (s : Prod.Carried)
    (hs : PointAll D s) : Walk D (Prod.run m0 n orders s) (PointAll D) := by
  unfold Prod.run
  exact walk_foldlM (fun s' i _ => walk_turn h0 _ s' _) _ s hs

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.walk_foldlM
#print axioms VerifiableInference.Desc.First.K8.Honest.walk_mapM
#print axioms VerifiableInference.Desc.First.K8.Honest.walk_pointAll
#print axioms VerifiableInference.Desc.First.K8.Honest.walk_pscBeginR
#print axioms VerifiableInference.Desc.First.K8.Honest.walk_pscRoundR
#print axioms VerifiableInference.Desc.First.K8.Honest.walk_roundInR
#print axioms VerifiableInference.Desc.First.K8.Honest.walk_pscEndsR
#print axioms VerifiableInference.Desc.First.K8.Honest.walk_whole
#print axioms VerifiableInference.Desc.First.K8.Honest.layBack_all
#print axioms VerifiableInference.Desc.First.K8.Honest.walk_level
#print axioms VerifiableInference.Desc.First.K8.Honest.walk_turn
#print axioms VerifiableInference.Desc.First.K8.Honest.walk_run
