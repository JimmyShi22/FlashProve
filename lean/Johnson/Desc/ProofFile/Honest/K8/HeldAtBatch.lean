-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/HeldAtBatch.lean: THE SMALLNESS TEST: THE FIRST CLAUSE OF THE PREMISE OF
ITS RUN "K8.equations" (eqPreB, Johnson/Desc/K8/Honest/EqAllBools.lean) AT A STATE REACHED IN FRONT OF A
SEGMENT's BATCHING: THE LIST OF TABLES IS HELD. It asks nothing of what the state holds but that it is
reached. Statements and proofs. None of the library's goals.

Why it holds. The step behind the sending of the reads closes the list, and the list that it closes is the
one that the state's reading S.funs? gives. The members between that step and the batching leave the
reading wide, which holds the mark "closed" and the record's own list, and they leave S.funs?.

  wideFuns_stretch   those members keep wide and the list
  joined_closed      behind the closing step, joined behind any sub-protocol: the list is closed and is
                     what S.funs? gives
  closed_at_reads    the same at a state reached behind a member that stands under that block
  held_of_wide       what wide and the list carry to a later state
  closed_below, closed_at_head  at a state reached at 14 l + 9 (l < 24), at 347: the record is there, S.funs?
                     gives its list, and that list is held
  **held_at_batching**, **held_at_batching_head**  so at whatever record and list the state shows
  **funsHeld_below**, **funsHeld_at_head**  **the clause, at the part**: at every part of such a state
  **funsHeld_at_batch**  the two at once: l < 25, at the segment's number

Limits. Under an opening of the description, in the goals' scope, at every first state. "Reached" is a
premise: nothing here shows it of a thread. Where the state has no part the clause says nothing. Of the
list nothing is said but that it is held: not what it holds. Nothing is claimed on completeness,
soundness or hiding.
-/
import Johnson.Desc.First.Link.Law.FunsAtBatch
import Johnson.Desc.K8.ReadsQuietClosed
import Johnson.Desc.First.K8.LawWideK3
import Johnson.Desc.First.K8.LawCondK1
import Johnson.Desc.First.K8.LawReadyAtt
import Johnson.Desc.First.TailClaims.K8SitsBetween
import Johnson.Desc.K1.Law.TlAtRecord
import Johnson.Top.H0.MergeLaw.LeavesTl
import Johnson.P1K8R.FrontAtSeat
import OnBytes.Flat.LinksFreeHeadC

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc
open VerifiableInference.Desc.First (S kindsBeforeBatching)
open VerifiableInference.Desc.First.TailClaims.Law (partOf partOf_some)
open VerifiableInference.Desc.LinkJoin (StretchKeeps stretch_back stretch_back_head sameFuns_stretch)
open VerifiableInference.Desc.First.K8 (wide wideOf wide_congr)
open Johnson.Desc.First.Walk.Tied (Reach stepYes_decide)

/-- The members between the reads' sending and the batching leave the reading wide and the list. -/
theorem wideFuns_stretch : StretchKeeps fun s s' => wide s' = wide s ∧ s'.funs? = s.funs? where
  trans := fun _ _ _ h k => ⟨k.1.trans h.1, k.2.trans h.2⟩
  k8 := fun p s rs gs s' h =>
    ⟨VerifiableInference.Desc.First.K8.hear_leaves_wide (Cl := Claim) p.toPar s rs gs s' h,
      sameFuns_stretch.k8 p s rs gs s' h⟩
  k1 := fun q gp link piece moment arrays s rs gs s' h =>
    ⟨congrArg (Option.map wideOf)
      (VerifiableInference.Desc.K1.laterAt_tl q gp link piece moment arrays s s' rs gs h).1,
      sameFuns_stretch.k1 q gp link piece moment arrays s rs gs s' h⟩
  k3 := fun claim readers X codes shape a _ hb s rs gs s' h =>
    ⟨VerifiableInference.Desc.First.K8.theStated_leaves_wide hb s rs gs s' h,
      sameFuns_stretch.k3 claim readers X codes shape a hb s rs gs s' h⟩
  k11 := fun Pm s rs gs s' h =>
    ⟨congrArg (Option.map wideOf)
      (VerifiableInference.Desc.First.MergeLaw.decide_leaves_tl Pm h),
      sameFuns_stretch.k11 Pm s rs gs s' h⟩

/-- Behind the step that closes the list, joined behind any sub-protocol. -/
theorem joined_closed (k : Block S Unit) (nm : String) (G : ProofFile.Ground) (l : Nat) (X : Stages.LinkH)
    (piece : Nat) (n : String) (a : Place) (w : String) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (Block.andThen nm k (ProofFile.orLoud n a w (ProofFile.readsQuietAt G l X piece))).decide s rs gs =
      .ok s') :
    ∃ tl, s'.tl? = some tl ∧ tl.funClosed = true ∧ s'.funs? = some tl.funs := by
  obtain ⟨_, _, H⟩ := VerifiableInference.Desc.bindOk
    (x := k.decide s (rs.take k.rounds.length) (gs.take k.openings)) h
  rcases First.K8.Ready.quiet_arms G l X piece n a w H with
    ⟨_, A, _, hd⟩ | ⟨_, _, _, ⟨_, _, _, hd⟩ | ⟨_, hd⟩⟩
  · obtain ⟨_, _, _, _, _, c, _, _, _, _, _, hc, rfl⟩ := K5Law.reads_next_o A _ s' hd
    have e := First.K8.Ready.closeStep_tl hc
    exact ⟨c.tl, rfl, congrArg HTailF2.funClosed e,
      (congrArg (fun y : HTailF2 => some y.funs) e).symm⟩
  · obtain ⟨tl, funs, e1, e2, e3, e4⟩ := VerifiableInference.Desc.K8.ReadsQuiet.layers_closed hd
    exact ⟨tl, e1, e2, by rw [e3]; exact e4⟩
  · obtain ⟨tl, funs, e1, e2, e3, e4⟩ := VerifiableInference.Desc.K8.ReadsQuiet.head_closed hd
    exact ⟨tl, e1, e2, by rw [e3]; exact e4⟩

/-- What wide and the list carry to a later state. -/
theorem held_of_wide {s₀ s : S} {tl : HTailF2} (e1 : s₀.tl? = some tl) (e2 : tl.funClosed = true)
    (e3 : s₀.funs? = some tl.funs) (qw : wide s = wide s₀) (qf : s.funs? = s₀.funs?) :
    ∃ tl', s.tl? = some tl' ∧ s.funs? = some tl'.funs ∧ tl'.funsHeld tl'.funs = true := by
  have ew : wide s = some (wideOf tl) := by
    rw [qw]
    show s₀.tl?.map wideOf = some (wideOf tl)
    rw [e1]
    rfl
  obtain ⟨tl', etl', ee⟩ := Option.map_eq_some_iff.1 ew
  obtain ⟨_, _, _, c1, c2, _, _⟩ := wide_congr ee
  refine ⟨tl', etl', ?_, ?_⟩
  · rw [qf, e3, c2]
  · rw [OnBytes.Flat.funsHeld_self, c1]
    exact e2

/-- Where the state shows the record and its list and that list is held, so it is at its part. -/
theorem part_held {s : S} {tl : HTailF2} (ht : s.tl? = some tl) (hf : s.funs? = some tl.funs)
    (held : tl.funsHeld tl.funs = true) :
    ∀ q, partOf s = some q → q.tl.funsHeld q.funs = true := fun q hq => by
  obtain ⟨a1, -, a3⟩ := partOf_some.1 hq
  have e1 : q.tl = tl := Option.some.inj (a1.symm.trans ht)
  have e2 : q.funs = tl.funs := Option.some.inj (a3.symm.trans hf)
  rw [e1, e2]
  exact held

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- Behind the member that sends the reads the list is closed and is the record's own. -/
theorem closed_at_reads {G : ProofFile.Ground} {b : Block S ProofFile.Cl} {k l pr : Nat} {Xl : Stages.LinkH}
    {reads : Option (List Nat)} (hf : c.blocksInOrder[k]? = some b)
    (hu : b.Under (IM.k1Reads Z G l Xl pr reads)) {z : Q} {s : S}
    (h : Reach 0 c.blocksInOrder start (k + 1) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ tl.funClosed = true ∧ s.funs? = some tl.funs := by
  obtain ⟨z', s₀, s', b₀, e, -, hb, hy⟩ := OnBytes.Road.K4.reach_pred h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  obtain rfl : b = b₀ := Option.some.inj (hf.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  exact joined_closed _ _ G l Xl _ _ _ _ (hu _ _ _ _ hd)

/-- In front of a batching below the head's the list is closed and is the record's own. -/
theorem closed_below (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24) {z : Q}
    {s : S} (h : Reach 0 c.blocksInOrder start (14 * l + 9) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ s.funs? = some tl.funs ∧ tl.funsHeld tl.funs = true := by
  obtain ⟨s₀, r0, qw, qf⟩ := stretch_back wideFuns_stretch hS hR O hl h
  by_cases he : l % 2 = 0
  · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
    obtain ⟨_, _, _, _, hf, _, hu⟩ := P1K8S.reads_under hS hR O (l := 2 * g) (by omega) .layers
      (IM.subs_at hS hR O.pub O.blank (g := g) (by omega)) 3 (by unfold kindsBeforeBatching; rfl)
      (Or.inl rfl)
    obtain ⟨tl, e1, e2, e3⟩ := closed_at_reads (k := 14 * (2 * g) + 5) hf hu r0
    exact held_of_wide e1 e2 e3 qw qf
  · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
    obtain ⟨_, _, _, _, hf, _, hu⟩ := P1K8S.reads_under hS hR O (l := 2 * g + 1) (by omega)
      .attention (IM.subs_att hS hR O.pub O.blank (g := g) (by omega)) 3
      (by unfold kindsBeforeBatching; cases (2 * g + 1 == 0) <;> rfl) (Or.inl rfl)
    obtain ⟨tl, e1, e2, e3⟩ := closed_at_reads (k := 14 * (2 * g + 1) + 5) hf hu r0
    exact held_of_wide e1 e2 e3 qw qf

/-- The like in front of the head's batching. -/
theorem closed_at_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {z : Q} {s : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, s)) :
    ∃ tl, s.tl? = some tl ∧ s.funs? = some tl.funs ∧ tl.funsHeld tl.funs = true := by
  obtain ⟨s₀, r0, qw, qf⟩ := stretch_back_head wideFuns_stretch hS hR O h
  obtain ⟨_, _, _, _, hf, _, hu⟩ := P1K8S.reads_under hS hR O (l := 24) (by omega) .head
    (IM.subs_head hS hR O.pub O.blank) 4 (by unfold kindsBeforeBatching; rfl) (Or.inr rfl)
  obtain ⟨tl, e1, e2, e3⟩ := closed_at_reads (k := 342) hf hu r0
  exact held_of_wide e1 e2 e3 qw qf

/-- **At a state reached in front of a batching below the head's, whatever record and list the state
shows: the list is held.** -/
theorem held_at_batching (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24) {z : Q}
    {s : S} (h : Reach 0 c.blocksInOrder start (14 * l + 8 + 1) (z, s)) :
    ∀ tl funs, s.tl? = some tl → s.funs? = some funs → tl.funsHeld funs = true := by
  obtain ⟨tl', e1, e2, e3⟩ := closed_below hS hR O hl h
  intro tl funs ht hf
  have a1 : tl' = tl := Option.some.inj (e1.symm.trans ht)
  have a2 : tl'.funs = funs := Option.some.inj (e2.symm.trans hf)
  rw [← a2, ← a1]
  exact e3

/-- **The like in front of the head's batching.** -/
theorem held_at_batching_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {z : Q} {s : S}
    (h : Reach 0 c.blocksInOrder start (337 + 10) (z, s)) :
    ∀ tl funs, s.tl? = some tl → s.funs? = some funs → tl.funsHeld funs = true := by
  obtain ⟨tl', e1, e2, e3⟩ := closed_at_head hS hR O h
  intro tl funs ht hf
  have a1 : tl' = tl := Option.some.inj (e1.symm.trans ht)
  have a2 : tl'.funs = funs := Option.some.inj (e2.symm.trans hf)
  rw [← a2, ← a1]
  exact e3

/-- **At every part of a state reached in front of a batching below the head's the list is held.** -/
theorem funsHeld_below (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24) {z : Q}
    {s : S} (h : Reach 0 c.blocksInOrder start (14 * l + 9) (z, s)) :
    ∀ q, partOf s = some q → q.tl.funsHeld q.funs = true := by
  obtain ⟨tl, e1, e2, e3⟩ := closed_below hS hR O hl h
  exact part_held e1 e2 e3

/-- **The like in front of the head's batching.** -/
theorem funsHeld_at_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {z : Q} {s : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, s)) :
    ∀ q, partOf s = some q → q.tl.funsHeld q.funs = true := by
  obtain ⟨tl, e1, e2, e3⟩ := closed_at_head hS hR O h
  exact part_held e1 e2 e3

/-- **The two at once, at the segment's number.** -/
theorem funsHeld_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25) {z : Q}
    {s : S} (h : Reach 0 c.blocksInOrder start (if l = 24 then 347 else 14 * l + 9) (z, s)) :
    ∀ q, partOf s = some q → q.tl.funsHeld q.funs = true := by
  by_cases h24 : l = 24
  · rw [if_pos h24] at h
    exact funsHeld_at_head hS hR O h
  · rw [if_neg h24] at h
    exact funsHeld_below hS hR O (by omega) h

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.wideFuns_stretch
#print axioms ProofFile.Honest.K8.joined_closed
#print axioms ProofFile.Honest.K8.held_of_wide
#print axioms ProofFile.Honest.K8.part_held
#print axioms ProofFile.Honest.K8.closed_at_reads
#print axioms ProofFile.Honest.K8.closed_below
#print axioms ProofFile.Honest.K8.closed_at_head
#print axioms ProofFile.Honest.K8.held_at_batching
#print axioms ProofFile.Honest.K8.held_at_batching_head
#print axioms ProofFile.Honest.K8.funsHeld_below
#print axioms ProofFile.Honest.K8.funsHeld_at_head
#print axioms ProofFile.Honest.K8.funsHeld_at_batch
