-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/RunRel.lean: EVERY RUN OF A LINK's TWO ORDERS STANDS IN A RELATION
BETWEEN THE RECORD IN FRONT AND THE RECORD BEHIND, THE RELATION ASKED A KIND's RUN AT A TIME.
RelRuns.lean asks it of six WRITINGS; a sentence that reads the ledger (its sizes) is not kept by
«some ledger is laid»: it wants the run's own yes. Here the nine premises are on the runs.

What is said.
  `RunRests B`: B holds of a record and itself, and of a yes of: the layers' own kind's «front»,
    «back», «free-slot»; the merge's run; the output head's «join»; the smallness test's three runs.
    `runRests_of_rel`: the six writings give the nine. `run_layers`, `run_attention`, `run_head`:
    **B e e₁ at every yes of every run of both orders**, from `RunRests B`, the sort's Take and, as
    it stands, the same of the lookup's runs.

Limits. IMPLICATIONS, as the three structures are. The lookup's runs' share stays a premise. Nothing
on soundness.

-/
import Johnson.Desc.First.Link.Law.RelRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Wrote frontAtC backAtC blockAtC)
open VerifiableInference.Desc.First.MergeLaw (claim_inv)
open Johnson.Desc.First.ForkMerge (headMergeClaim)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K4Run
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open K5Law

variable {β : Type}

/-- **The relation holds of a yes of each known run.** -/
structure RunRests (B : S → S → Prop) : Prop where
  refl : ∀ s, B s s
  front : ∀ (p : OnBytes.Desc.First.K4.Par) r, (blockAtC p).claims.lookup "front" = some r →
    ∀ n e c e₁, r n e = .ok (c, e₁) → B e e₁
  back : ∀ (p : OnBytes.Desc.First.K4.Par) r, (blockAtC p).claims.lookup "back" = some r →
    ∀ n e c e₁, r n e = .ok (c, e₁) → B e e₁
  free : ∀ (p : OnBytes.Desc.First.K4.Par) r, (blockAtC p).after.lookup "free-slot" = some r →
    ∀ e e₁, r e = .ok e₁ → B e e₁
  merge : ∀ n e c e₁, headMergeClaim n e = .ok (c, e₁) → B e e₁
  join : ∀ (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Par) n e c e₁,
    K3.joinRun (K3.seatCalls asClaim) (callerKeys p (seatAt h iU3)) n e = .ok (c, e₁) → B e e₁
  eq : ∀ n e c e₁, k8Run.2 n e = .ok (c, e₁) → B e e₁
  ls : ∀ e e₁, k8LsTail e = .ok e₁ → B e e₁
  tests : ∀ nU e e₁, k8Tests nU e = .ok e₁ → B e e₁

variable {B : S → S → Prop}

/-- The six writings give the nine. -/
theorem runRests_of_rel (R : RelRests B) : RunRests B where
  refl := R.refl
  front p r h0 n e c e₁ hr := by
    obtain ⟨a, _, _, G, _, _, _, hw⟩ := frontAtC h0 hr
    exact R.wrote _ _ _ _ hw
  back p r h0 n e c e₁ hr := by
    obtain ⟨a, _, _, G, _, _, _, hw⟩ := backAtC h0 hr
    exact R.wrote _ _ _ _ hw
  free p r h0 e e₁ hr := by
    obtain ⟨a, hw⟩ := k4_freeSlot_wrote h0 hr
    exact R.wrote _ _ _ _ hw
  merge := merge_rel R
  join := join_rel R
  eq := R.eq
  ls := R.ls
  tests := R.tests

theorem hands_run (R : RunRests B) {run : ℕ → S → Except String (List Claim × S)}
    (hh : ∀ n e c e₁, run n e = .ok (c, e₁) → e₁ = e) (n : ℕ) (e : S) (c : List Claim) (e₁ : S)
    (hr : run n e = .ok (c, e₁)) : B e e₁ := by
  rw [hh n e c e₁ hr]
  exact R.refl e

theorem idle_run (R : RunRests B) {run : ℕ → S → Except String (List Claim × S)} (h : Idle run)
    (n : ℕ) (e : S) (c : List Claim) (e₁ : S) (hr : run n e = .ok (c, e₁)) : B e e₁ := by
  obtain rfl : e = e₁ := congrArg Prod.snd (Except.ok.inj ((h n e).symm.trans hr))
  exact R.refl e

/-- **THE RUNS OF BOTH ORDERS OF A LAYERS' LINK STAND IN THE RELATION.** -/
theorem run_layers (R : RunRests B) {l : ℕ} {L : Link S Claim}
    (hL : SegAt l .layers L) {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {p : OnBytes.Desc.First.K4.Par} {nU : Array ℕ}
    {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : LayersTake L u ψ Ok Fu p nU ent tm4 t3 l3)
    (k3f : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → B e e₁)
    :
    (∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) → B e e₁) ∧
      ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → B e e₁ := by
  obtain ⟨eo, ea⟩ := order_at hL
  refine ⟨?_, ?_⟩
  · rw [eo, order_layers]
    refine ⟨k3f _ (by simp),
      fun run h => rel_under (A.ties.tGuests 1 (by simp) run h) (idle_run R fun _ _ => rfl),
      fun run h n e c e₁ hr => ?_, k3f _ (by simp),
      fun run h => rel_under (A.ties.tGuests 6 (by simp) run h) (idle_run R fun _ _ => rfl),
      fun run h => ?_, fun run h n e c e₁ hr => ?_⟩
    · obtain ⟨r, h0, hu⟩ := A.ties.tFront run h
      exact R.front p r h0 n e c e₁ (hu n e c e₁ hr)
    · exact rel_under (A.ties.tEq run h) fun n e c e₁ hr => R.eq n e c e₁ hr
    · obtain ⟨r, h0, hu⟩ := A.ties.tBack run h
      exact R.back p r h0 n e c e₁ (hu n e c e₁ hr)
  · rw [ea, after_layers]
    refine ⟨fun run h => ?_, fun run h e e₁ hr => ?_, fun run h => ?_⟩
    · exact relAfter_under (A.ties.tLs run h) R.ls
    · obtain ⟨r, h0, hu⟩ := A.ties.tFree run h
      exact R.free p r h0 e e₁ (hu e e₁ hr)
    · exact relAfter_under (A.ties.tTests run h) (R.tests nU)

/-- **THE RUNS OF BOTH ORDERS OF AN ATTENTION LINK STAND IN THE RELATION.** -/
theorem run_attention (R : RunRests B) {l : ℕ} {L : Link S Claim}
    (hL : SegAt l .attention L) {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)}
    {c : First.Att.P.ParC} {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : AttTake L u ψ Ok Fu rd c nU ent tm4 t3 l3)
    (k3f : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run,
      At L o run → ∀ n e c' e₁, run n e = .ok (c', e₁) → B e e₁)
    :
    (∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) → B e e₁) ∧
      ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → B e e₁ := by
  obtain ⟨eo, ea⟩ := order_at hL
  refine ⟨?_, ?_⟩
  · rw [eo, order_attention]
    refine ⟨k3f _ (by simp),
      fun run h => rel_under (A.ties.tGuests 1 (by simp) run h) (idle_run R fun _ _ => rfl),
      fun run h => ?_, fun run h => ?_, k3f _ (by simp), fun run h => ?_, k3f _ (by simp),
      k3f _ (by simp),
      fun run h => rel_under (A.ties.tGuests 6 (by simp) run h) (idle_run R fun _ _ => rfl),
      fun run h => ?_⟩
    · exact rel_under (A.ties.tFirst run h)
        (hands_run R (still_first (phiAll u ψ) Ok rd c A.hrd A.okK5).hands)
    · exact rel_under (A.ties.tKeys run h) (hands_run R (still_keys (phiAll u ψ) Ok c).hands)
    · exact rel_under (A.ties.tSecond run h)
        (hands_run R (still_second (phiAll u ψ) Ok rd c A.hrd A.okK5).hands)
    · exact rel_under (A.ties.tEq run h) fun n e c' e₁ hr => R.eq n e c' e₁ hr
  · rw [ea, after_attention]
    refine ⟨fun run h => ?_, fun run h => ?_⟩
    · exact relAfter_under (A.ties.tLs run h) R.ls
    · exact relAfter_under (A.ties.tTests run h) (R.tests nU)

/-- **THE RUNS OF BOTH ORDERS OF THE HEAD's LINK STAND IN THE RELATION.** -/
theorem run_head (R : RunRests B) {l : ℕ} {L : Link S Claim}
    (hL : SegAt l .head L) {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {h : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ} {p : Par}
    {kap : Phi β → Option Seen} {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : HeadTake L u ψ Ok Fu h iU3 l' piece p kap nU ent tm4 t3 l3)
    (k3f : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → B e e₁)
    :
    (∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) → B e e₁) ∧
      ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → B e e₁ := by
  obtain ⟨eo, ea⟩ := order_at hL
  have k6 : ∀ name ∈ ["norm", "policy", "logits"], ∀ run, At L (3, name) run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → B e e₁ := fun name hn run hr => by
    obtain ⟨r, h0, hu⟩ := A.ties.tK6 name hn run hr
    exact rel_under hu (hands_run R
      (k6_still h iU3 p (phiAll u ψ) Ok kap A.hkap A.okK6 l' piece name r h0).hands)
  refine ⟨?_, ?_⟩
  · rw [eo, order_head]
    refine ⟨k3f _ (by simp),
      fun run hr => rel_under (A.ties.tGuests 2 (by simp) run hr) (idle_run R fun _ _ => rfl),
      k6 "norm" (by simp), fun run hr => ?_, k6 "policy" (by simp), k3f _ (by simp),
      k3f _ (by simp),
      fun run hr => rel_under (A.ties.tGuests 7 (by simp) run hr) (idle_run R fun _ _ => rfl),
      fun run hr => ?_, k6 "logits" (by simp), fun run hr => ?_⟩
    · exact rel_under (A.ties.tJoin run hr) (R.join h iU3 p)
    · exact rel_under (A.ties.tEq run hr) fun n e c e₁ hr => R.eq n e c e₁ hr
    · exact rel_under (A.ties.tMerge run hr) R.merge
  · rw [ea, after_head]
    refine ⟨fun run hr => ?_, fun run hr => ?_⟩
    · exact relAfter_under (A.ties.tLs run hr) R.ls
    · exact relAfter_under (A.ties.tTests run hr) (R.tests nU)


end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.runRests_of_rel
#print axioms VerifiableInference.Desc.LinkJoin.run_layers
#print axioms VerifiableInference.Desc.LinkJoin.run_attention
#print axioms VerifiableInference.Desc.LinkJoin.run_head
