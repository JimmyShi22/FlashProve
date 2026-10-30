-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
MOVED, TO THE LETTER, INTO Law/K6Claims.lean (which imports nothing of the batching kind's law):
join_spec, wide_bare, keyVectorsAt, join_hands. What this head says of them holds there.
Johnson/Desc/Kinds/Law/JoinRunAtS.lean: THE BATCHING KIND's PREMISE ON A RUN OF CLAIMS (RunOk) AT
THE OUTPUT HEAD's FOURTH RUN "join" (the lookup's run K3.joinRun, fed with the head's six key
vectors), AT THE CARRIED RECORD, under named premises on the letters that all kinds share. With a
tool for every run in the head's link that does no more to the record than mark an owed claim as
added. Statements and proofs.

  MarksRun φ Ok run fs   the run's shape: hands: a yes hands back the record with ONE OWED CLAIM OF
                 THE HEAD's LEDGER MARKED AS ADDED (Fork.paid), nothing else turned; forms: as the
                 tool for runs that leave the record as it is asks
                 (Johnson/Desc/First/Link/Law/StillRun.lean: Still.forms).
  marks_plainOk, marks_runOk   PlainOk and RunOk of such a run, under that tool's hOk and hFu, and
                 hkeep: a writing of the head's ledger leaves the shared reader as it is.
  join_spec      where "join" returns: its one claim is the plain claim of the form of "join" at
                 what the lookup has heard and the caller's keys; the record behind is the record
                 with the owed claim "join" marked.
  keyVectorsAt, fsJoin the key vectors at given letters; the run's one form, read off what is fixed.
  JoinPromise    THE SECOND NAMED PREMISE ON Ok: the lookup's last claim's slots are filled in the
                 snapshot.
  join_hands, join_door   the record behind "join"; the door's duty (the link's law asks it of
                 every run beside RunOk): under no premise.
  join_marks, join_hOk, join_runOk   MAIN: RunOk of "join".

WHAT IT IS NOT. AN IMPLICATION. OWED: K6Promise (Law/RunsStillAtS.lean; one half:
Law/K6PromiseBorder.lean) · JoinPromise (K6On's sixth clause in front of the head's block; carried
by "later") · hFu (the entries) · hkeep (paid for the closed reader by PhiAll.phi_k11_keep). The
marks on owed claims are guarded by nothing in RunOk. No member. Nothing on soundness.
LETTERS. No letter stands under "there is" in the tops. MarksRun.hands: a, i: pinned by the two
equations.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RunsStillAtS
import Johnson.Desc.Kinds.Law.K6Claims
import Johnson.Desc.First.Link.Law.K11Run

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff Reading)
open OnBytes.PscRun (Later paid_later)
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.K4Values (refWorld values_ref)

section Tool

variable {α K : Type}

/-- The shape of a run in the head's link that marks an owed claim as added and turns nothing else.
-/
structure MarksRun (φ : S → α) (Ok : α × Option Pub9 → Prop)
    (run : Nat → S → Except String (List Claim × S))
    (fs : α × Option Pub9 → Option (List Aff)) : Prop where
  hands : ∀ n e c e₁, run n e = .ok (c, e₁) → ∃ (a : HeadOwn) (i : Nat), e.here = .head a ∧
    e₁ = { e with here := .head { a with F := a.F.paid i } }
  forms : ∀ q n e c e₁, Fx9 φ Ok q e → run n e = .ok (c, e₁) →
    ∃ l, fs q = some l ∧ c = l.map fun f => ({ form := f } : Claim)

variable [Field K] (ρ : Reading K)

/-- **PlainOk OF A RUN THAT MARKS AN OWED CLAIM.** -/
theorem marks_plainOk (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)
    (run : Nat → S → Except String (List Claim × S)) (fs : α × Option Pub9 → Option (List Aff))
    (hrun : MarksRun φ Ok run fs)
    (hkeep : ∀ (s : S) (a : HeadOwn) (G : Fork), s.here = .head a →
      φ { s with here := .head { a with F := G } } = φ s)
    (hOk : ∀ q l u, Ok q → fs q = some l → q.2 = some u →
      ∀ f ∈ l, ∀ x ∈ f.slots.toList, OnBytes.PscRun.Filled u.F x.1)
    (ent : α × Option Pub9 → Bound K → Nat → Nat → Nat → K)
    (hFu : ∀ q l t b y, Fx9 φ Ok q t → Fu t → atS.get? t = some b → fs q = some l →
      ∀ f ∈ l, ∀ x ∈ f.ents.toList,
        (worldAt ρ b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx) :
    PlainOk ρ atS (O9 φ Ok Fu) (Fx9 φ Ok) run (valsStill ρ fs ent) (lenStill fs) := by
  intro q front e a9 c e₁ hf hg ha hs hr
  obtain ⟨a, i, h1, rfl⟩ := hrun.hands front e c e₁ hr
  obtain ⟨l, hq, rfl⟩ := hrun.forms q front e c _ hf hr
  obtain ⟨a₁, ha₁, f1, f2, f3, f4⟩ := K11Run.get_head e a9 ha a h1 (a.F.paid i)
  have hf0 := hf
  obtain ⟨hok, _, u, b0, hu, hb0, gu⟩ := hf
  obtain rfl : a9 = b0 := Option.some.inj (ha.symm.trans hb0)
  have hUF : Later u.F a.F := by rw [← f4]; exact gu.1
  have hl : Later a.F (a.F.paid i) := paid_later _ _
  have hgo : GoesOn (pubOf a9) a₁ :=
    ⟨by rw [f1]; show Later a9.F _; rw [f4]; exact hl,
      by rw [f1]; show a.F.planClaimsF = a9.F.planClaimsF; rw [f4],
      by rw [f1]; show a.F.trees.map LinkJoin.look = a9.F.trees.map LinkJoin.look; rw [f4],
      by rw [f2]; rfl, by rw [f2]; rfl, f3⟩
  have hmore : more9 φ e { e with here := .head { a with F := a.F.paid i } } :=
    ⟨hkeep e a _ h1, fun a' ha' => by
      have ea : a' = a9 := Option.some.inj (ha'.symm.trans ha)
      rw [ea]
      exact ⟨a₁, ha₁, hgo⟩⟩
  obtain ⟨a0, ha0, g1, _⟩ := hg
  obtain rfl : a9 = a0 := Option.some.inj (ha.symm.trans ha0)
  have hfx1 := fx_of_more φ Ok q e _ hf0 hmore
  refine ⟨a₁, ha₁, by rw [f1, f4]; rfl, by rw [f1, f4]; rfl,
    ⟨a₁, ha₁, by rw [f2]; exact g1, by
      rw [f1]
      show a.F.LS.size = a.F.ns
      rw [← f4]
      exact hs⟩, hmore, hfx1, by simp [lenStill, hq], fun cl hcl => ?_,
    fun t b y ht hfull hb => ?_⟩
  · obtain ⟨f, _, rfl⟩ := List.mem_map.1 hcl
    rfl
  · obtain ⟨b', hb', gb⟩ := ht.2.1.2 a₁ ha₁
    obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
    have hGB : Later (a.F.paid i) b.F := by
      have := gb.1
      rwa [show (pubOf a₁).F = a.F.paid i from f1] at this
    have hfx : Fx9 φ Ok q t := fx_of_more φ Ok q _ t hfx1 ht.2.1
    simp only [valsStill, hu, hq, Option.getD_some]
    exact values_ref ρ l b.L u.F b.F [] (ent q y) y (hUF.trans (hl.trans hGB))
      (fun _ h => absurd h List.not_mem_nil)
      (fun f hf' x hx => Or.inr (hOk q l u hok hq hu f hf' x hx))
      (fun f hf' x hx => hFu q l t b y hfx hfull hb hq f hf' x hx)

/-- **RunOk OF SUCH A RUN.** -/
theorem marks_runOk (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)
    (run : Nat → S → Except String (List Claim × S)) (fs : α × Option Pub9 → Option (List Aff))
    (hrun : MarksRun φ Ok run fs)
    (hkeep : ∀ (s : S) (a : HeadOwn) (G : Fork), s.here = .head a →
      φ { s with here := .head { a with F := G } } = φ s)
    (hOk : ∀ q l u, Ok q → fs q = some l → q.2 = some u →
      ∀ f ∈ l, ∀ x ∈ f.slots.toList, OnBytes.PscRun.Filled u.F x.1)
    (ent : α × Option Pub9 → Bound K → Nat → Nat → Nat → K)
    (hFu : ∀ q l t b y, Fx9 φ Ok q t → Fu t → atS.get? t = some b → fs q = some l →
      ∀ f ∈ l, ∀ x ∈ f.ents.toList,
        (worldAt ρ b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx) :
    RunOk ρ atS (O9 φ Ok Fu) (Fx9 φ Ok) run (plainTm (valsStill ρ fs ent)) (lenStill fs) :=
  runOk_of_plain ρ atS (O9 φ Ok Fu) (Fx9 φ Ok) run _ _ (part_of_more φ)
    (marks_plainOk ρ φ Ok Fu run fs hrun hkeep hOk ent hFu)

end Tool

section At

variable {α : Type} (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Par)

/-- The one form of "join", read off what is fixed in front. -/
noncomputable def fsJoin (kap : α → Option Seen) (q : α × Option Pub9) : Option (List Aff) :=
  match kap q.1, q.2 with
  | some z, some u => (lettersOf h iU3 p z u.F).bind fun v =>
      (if z.opened then z.lookHeard else none).map fun g => [Came.joinForm g (keyVectorsAt v)]
  | _, _ => none

/-- **THE SECOND NAMED PREMISE ON THE SHARED PROMISE.** -/
def JoinPromise (kap : α → Option Seen) (Ok : α × Option Pub9 → Prop) : Prop :=
  ∀ q z u g, Ok q → kap q.1 = some z → q.2 = some u → z.lookHeard = some g → CEndFilled g u.F

/-- **The door's duty of "join"**: all that the door reads beside the ledger stays. -/
theorem join_door (n : Nat) (e : S) (c : List Claim) (e₁ : S)
    (hr : K3.joinRun (K3.seatCalls asClaim) (callerKeys p (seatAt h iU3)) n e = .ok (c, e₁)) :
    KeepsDoor atS e e₁ := by
  obtain ⟨a, i, h1, rfl⟩ := join_hands h iU3 p n e c e₁ hr
  intro a9 ha
  obtain ⟨a₁, ha₁, _, f2, f3, _⟩ := K11Run.get_head e a9 ha a h1 (a.F.paid i)
  exact ⟨a₁, ha₁, by rw [f2], f3⟩

variable (φ : S → α) (Ok : α × Option Pub9 → Prop) (kap : α → Option Seen)
  (hkap : ∀ e, kap (φ e) = seenOf e) (hP : K6Promise h iU3 p kap Ok)
  (hJ : JoinPromise kap Ok)

include hkap hP in
/-- **"join" MARKS ONE OWED CLAIM, AND ITS FORM IS READ OFF WHAT IS FIXED.** -/
theorem join_marks :
    MarksRun φ Ok (K3.joinRun (K3.seatCalls asClaim) (callerKeys p (seatAt h iU3)))
      (fsJoin h iU3 p kap) where
  hands := fun n e c e₁ hr => join_hands h iU3 p n e c e₁ hr
  forms := fun q n e c e₁ hf hr => by
    obtain ⟨hok, hq, u, b, hu, hb, hL, _, hK, _⟩ := hf
    obtain ⟨F, g, KF, hF, hg, hKF, rfl, _⟩ := join_spec _ n e c e₁ hr
    unfold callerKeys at hKF
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hKF
    have hl : lettersAt p (seatAt h iU3) e = .ok v := by
      cases hl : lettersAt p (seatAt h iU3) e with
      | error m => rw [hl] at hv; cases hv
      | ok w =>
        rw [hl] at hv
        exact congrArg Except.ok (Option.some.inj hv)
    -- the record stands in the head's link
    have hz : ∃ z, seenOf e = some z := by
      unfold seenOf
      cases hh : e.here with
      | head o => exact ⟨_, rfl⟩
      | _ =>
        exfalso
        unfold lettersAt at hl
        have hH : (seatAt h iU3).heard e = none := by
          show (match e.here with
            | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
              allOf o.F x (some (keptOf q x.wpl.sL))
            | _ => none) = none
          rw [hh]
        cases hg' : given p (seatAt h iU3) e with
        | error m => rw [hg'] at hl; cases hl
        | ok g' => rw [hg', hH] at hl; cases hl
    obtain ⟨z, hz⟩ := hz
    have hk : kap q.1 = some z := by rw [← hq, hkap, hz]
    have hFb : e.fork? = some b.F := by
      have := K11Run.get_head
      obtain ⟨o, ho, hoF, hzz⟩ := sees_of_seen hz hF
      obtain ⟨_, _, _, _, _, f4⟩ := K11Run.get_head e b hb o ho o.F
      rw [hF, f4, hoF]
    have hw := letters_back h iU3 p (hP q z u hok hk hu) (sees_of_seen hz hFb) hL
      (LinkJoin.widths_of_looks _ _ hK) hl
    -- what the lookup has heard is what z shows
    have hzg : (if z.opened then z.lookHeard else none) = some g := by
      obtain ⟨o, ho, _, rfl⟩ := sees_of_seen hz hF
      unfold S.lookHeard? at hg
      rw [ho] at hg
      exact hg
    refine ⟨[Came.joinForm g (keyVectorsAt v)], ?_, rfl⟩
    unfold fsJoin
    rw [hk, hu]
    simp only [hw, Option.bind_some, hzg, Option.map_some]

include hP hJ in
/-- **The tool's premise on slots.** -/
theorem join_hOk : ∀ q l u, Ok q → fsJoin h iU3 p kap q = some l → q.2 = some u →
    ∀ f ∈ l, ∀ x ∈ f.slots.toList, OnBytes.PscRun.Filled u.F x.1 := by
  intro q l u hok hl hu f hf x hx
  unfold fsJoin at hl
  rw [hu] at hl
  cases hk : kap q.1 with
  | none => rw [hk] at hl; cases hl
  | some z =>
    rw [hk] at hl
    obtain ⟨v, hv, hl⟩ := Option.bind_eq_some_iff.mp hl
    obtain ⟨F0, G, rs, hW, hh, hL⟩ := ready_at_letters h iU3 p (hP q z u hok hk hu) hv
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hl
    obtain rfl := List.mem_singleton.mp hf
    have hzg : z.lookHeard = some g := by
      by_cases ho : z.opened = true
      · simpa [ho] using hg
      · simp [ho] at hg
    have hc := hJ q z u g hok hk hu hzg
    -- the reads' entries name no slot
    obtain ⟨s0, _, e0⟩ := lettersOf_some h iU3 p hv
    have hb : (∀ r i, (v.2.2.final.entry r i).slots = #[]) ∧
        (∀ r i, (v.2.2.head.entry r i).slots = #[]) ∧ ∀ i, (v.2.2.final.wide i).slots = #[] := by
      unfold lettersAt at e0
      cases hg' : given p (seatAt h iU3) s0 with
      | error m => rw [hg'] at e0; cases e0
      | ok g' =>
        rw [hg'] at e0
        cases hH : (seatAt h iU3).heard s0 with
        | none => rw [hH] at e0; cases e0
        | some H =>
          rw [hH] at e0
          cases hx' : (seatAt h iU3).reads s0 with
          | none => rw [hx'] at e0; cases e0
          | some y =>
            rw [hx'] at e0
            have e1 := Except.ok.inj e0
            subst e1
            exact ⟨(reads_bare h iU3 hx').1, (reads_bare h iU3 hx').2, wide_bare h iU3 hx'⟩
    letI := v.1
    letI := v.2.1
    letI := v.2.2
    -- P: every slot that the form names is filled in the snapshot
    have TT := hear_takes (⟨hW.2.1, hW.2.2, hW.1⟩ : OnBytes.PscRun.Sized F0) hh
    have fill : ∀ j, F0.next ≤ j → j < G.next → OnBytes.PscRun.Filled u.F j := fun j h1 h2 =>
      (hL.keep j (TT.full j h1 (by rw [← TT.next]; exact h2))).1
    have C : Kept fun f : Form => ∀ x ∈ f.slots.toList, OnBytes.PscRun.Filled u.F x.1 :=
      { addMul := fun {a b} k ha hb' x hx => by
          rw [addMul_slots] at hx
          rcases List.mem_append.mp hx with h' | h'
          · exact ha x h'
          · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h'
            exact hb' y hy
        bare := fun f _ hs x hx => by
          rw [hs] at hx
          simp at hx }
    refine joinForm_has C g (keyVectorsAt v) (fun c hc' => ?_) hc x hx
    have hks := keys_slotsIn hW hh hb.1 hb.2.1 hb.2.2
    unfold keyVectorsAt
    intro y hy
    have hlen : c < v.1.calls.length := by
      simpa [keyVectorsAt] using hc'
    rw [Came.getD_map_toArray v.1.calls (fun c => keyVector key c.1 c.2) c hlen (Aff.ofConst zeroE)
      (0, [])] at hy
    have := hks _ _ y hy
    exact fill _ this.1 this.2

variable {K : Type} [Field K] (ρ : Reading K)

include hkap hP hJ in
/-- **RunOk OF "join".** -/
theorem join_runOk (Fu : S → Prop)
    (hkeep : ∀ (s : S) (a : HeadOwn) (G : Fork), s.here = .head a →
      φ { s with here := .head { a with F := G } } = φ s)
    (ent : α × Option Pub9 → Bound K → Nat → Nat → Nat → K)
    (hFu : ∀ q l t b y, Fx9 φ Ok q t → Fu t → atS.get? t = some b →
      fsJoin h iU3 p kap q = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList,
        (worldAt ρ b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx) :
    RunOk ρ atS (O9 φ Ok Fu) (Fx9 φ Ok)
      (K3.joinRun (K3.seatCalls asClaim) (callerKeys p (seatAt h iU3)))
      (plainTm (valsStill ρ (fsJoin h iU3 p kap) ent)) (lenStill (fsJoin h iU3 p kap)) :=
  marks_runOk ρ φ Ok Fu _ _ (join_marks h iU3 p φ Ok kap hkap hP) hkeep
    (join_hOk h iU3 p Ok kap hP hJ) ent hFu

end At

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.marks_runOk
#print axioms VerifiableInference.Desc.Kinds.Head.Law.join_door
#print axioms VerifiableInference.Desc.Kinds.Head.Law.join_marks
#print axioms VerifiableInference.Desc.Kinds.Head.Law.join_hOk
#print axioms VerifiableInference.Desc.Kinds.Head.Law.join_runOk
