-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/KeepsRuns.lean: THE MARK OF FAILURE IS KEPT BY THE TWO MOVES OF A LINK,
AT EACH OF THE THREE SORTS: `MoveKeeps (·.failed)` (Johnson/Desc/First/Batch/Law/KeepsField.lean) at
`moves₁ L rl ++ moves₂ L`, from the ties of the assembly (PayLayers.lean, PayAttention.lean,
PayHead.lean). So the batching kind's «a mark stays» (`join_marks`) has its premise at a segment
that the driver makes.

What is said.
  `wrote_failed`, `merge_failed`, `join_failed`, `hands_failed`, `idle_failed`: what a run of the
    layers' own kind writes, the merge's run, the output head's «join», a run that hands the record
    back and an idle run keep the mark. `failed_layers`, `failed_attention`, `failed_head`: **the
    duty of both moves at each sort**, from `LayersTake`, `AttTake`, `HeadTake` and, as it stands,
    the same duty of the lookup's runs that these leave as premises.

Limits. IMPLICATIONS, as the three structures are. The duty is an EQUATION (the field is as it was):
more than «a mark stays» asks. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.JoinKeeps
import Johnson.Desc.First.Link.Law.PayAttention
import Johnson.Desc.First.Link.Law.PayHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Wrote frontAtC backAtC)
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

theorem wrote_failed {e e₁ : S} {a : First.LayOwn} {G : Fork} (hw : Wrote e a G e₁) :
    e₁.failed = e.failed := by
  obtain ⟨_, rfl⟩ := hw
  rfl

theorem merge_failed (n : ℕ) (e : S) (c : List Claim) (e₁ : S)
    (hr : headMergeClaim n e = .ok (c, e₁)) : e₁.failed = e.failed := by
  obtain ⟨a, wo, G, h1, hwo, rfl, rfl, hrunG⟩ := claim_inv hr
  rfl

theorem join_failed (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Par) (n : ℕ) (e : S)
    (c : List Claim) (e₁ : S)
    (hr : K3.joinRun (K3.seatCalls asClaim) (callerKeys p (seatAt h iU3)) n e = .ok (c, e₁)) :
    e₁.failed = e.failed := by
  obtain ⟨a, i, _, rfl⟩ := join_hands h iU3 p n e c e₁ hr
  rfl

/-- A run that hands the record back keeps every field. -/
theorem hands_failed {run : ℕ → S → Except String (List Claim × S)}
    (hh : ∀ n e c e₁, run n e = .ok (c, e₁) → e₁ = e) (n : ℕ) (e : S) (c : List Claim) (e₁ : S)
    (hr : run n e = .ok (c, e₁)) : e₁.failed = e.failed := by
  rw [hh n e c e₁ hr]

theorem idle_failed {run : ℕ → S → Except String (List Claim × S)} (h : Idle run) (n : ℕ) (e : S)
    (c : List Claim) (e₁ : S) (hr : run n e = .ok (c, e₁)) : e₁.failed = e.failed := by
  obtain rfl : e = e₁ := congrArg Prod.snd (Except.ok.inj ((h n e).symm.trans hr))
  rfl

/-- **BOTH MOVES OF A LAYERS' LINK KEEP THE MARK.** -/
theorem failed_layers {l : ℕ} {L : Link S Claim}
    (hL : SegAt l .layers L) {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {p : OnBytes.Desc.First.K4.Par} {nU : Array ℕ}
    {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : LayersTake L u ψ Ok Fu p nU ent tm4 t3 l3)
    (k3f : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → e₁.failed = e.failed)
    (rl : List (TermedRun S (Q β) Cb.Gl.E)) :
    ∀ m ∈ moves₁ L rl ++ moves₂ (α := Phi β) L, MoveKeeps (·.failed) m.move := by
  obtain ⟨eo, ea⟩ := order_at hL
  refine moves_keepL (·.failed) L rl ?_ ?_
  · rw [eo, order_layers]
    refine ⟨k3f _ (by simp),
      fun run h => keep_under _ (A.ties.tGuests 1 (by simp) run h) (idle_failed fun _ _ => rfl),
      fun run h n e c e₁ hr => ?_, k3f _ (by simp),
      fun run h => keep_under _ (A.ties.tGuests 6 (by simp) run h) (idle_failed fun _ _ => rfl),
      fun run h => ?_, fun run h n e c e₁ hr => ?_⟩
    · obtain ⟨r, h0, hu⟩ := A.ties.tFront run h
      obtain ⟨a, _, _, G, _, _, _, hw⟩ := frontAtC h0 (hu n e c e₁ hr)
      exact wrote_failed hw
    · exact keep_under _ (A.ties.tEq run h) fun n e c e₁ hr => k8Run_failed n e e₁ c hr
    · obtain ⟨r, h0, hu⟩ := A.ties.tBack run h
      obtain ⟨a, _, _, G, _, _, _, hw⟩ := backAtC h0 (hu n e c e₁ hr)
      exact wrote_failed hw
  · rw [ea, after_layers]
    refine ⟨fun run h => ?_, fun run h e e₁ hr => ?_, fun run h => ?_⟩
    · exact keepAfter_under _ (A.ties.tLs run h) k8LsTail_failed
    · obtain ⟨r, h0, hu⟩ := A.ties.tFree run h
      obtain ⟨a, hw⟩ := k4_freeSlot_wrote h0 (hu e e₁ hr)
      exact wrote_failed hw
    · exact keepAfter_under _ (A.ties.tTests run h) (k8Tests_failed nU)

/-- **BOTH MOVES OF AN ATTENTION LINK KEEP THE MARK.** -/
theorem failed_attention {l : ℕ} {L : Link S Claim}
    (hL : SegAt l .attention L) {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)}
    {c : First.Att.P.ParC} {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : AttTake L u ψ Ok Fu rd c nU ent tm4 t3 l3)
    (k3f : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run,
      At L o run → ∀ n e c' e₁, run n e = .ok (c', e₁) → e₁.failed = e.failed)
    (rl : List (TermedRun S (Q β) Cb.Gl.E)) :
    ∀ m ∈ moves₁ L rl ++ moves₂ (α := Phi β) L, MoveKeeps (·.failed) m.move := by
  obtain ⟨eo, ea⟩ := order_at hL
  refine moves_keepL (·.failed) L rl ?_ ?_
  · rw [eo, order_attention]
    refine ⟨k3f _ (by simp),
      fun run h => keep_under _ (A.ties.tGuests 1 (by simp) run h) (idle_failed fun _ _ => rfl),
      fun run h => ?_, fun run h => ?_, k3f _ (by simp), fun run h => ?_, k3f _ (by simp),
      k3f _ (by simp),
      fun run h => keep_under _ (A.ties.tGuests 6 (by simp) run h) (idle_failed fun _ _ => rfl),
      fun run h => ?_⟩
    · exact keep_under _ (A.ties.tFirst run h)
        (hands_failed (still_first (phiAll u ψ) Ok rd c A.hrd A.okK5).hands)
    · exact keep_under _ (A.ties.tKeys run h) (hands_failed (still_keys (phiAll u ψ) Ok c).hands)
    · exact keep_under _ (A.ties.tSecond run h)
        (hands_failed (still_second (phiAll u ψ) Ok rd c A.hrd A.okK5).hands)
    · exact keep_under _ (A.ties.tEq run h) fun n e c' e₁ hr => k8Run_failed n e e₁ c' hr
  · rw [ea, after_attention]
    refine ⟨fun run h => ?_, fun run h => ?_⟩
    · exact keepAfter_under _ (A.ties.tLs run h) k8LsTail_failed
    · exact keepAfter_under _ (A.ties.tTests run h) (k8Tests_failed nU)

/-- **BOTH MOVES OF THE HEAD's LINK KEEP THE MARK.** -/
theorem failed_head {l : ℕ} {L : Link S Claim}
    (hL : SegAt l .head L) {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {h : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ} {p : Par}
    {kap : Phi β → Option Seen} {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : HeadTake L u ψ Ok Fu h iU3 l' piece p kap nU ent tm4 t3 l3)
    (k3f : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → e₁.failed = e.failed)
    (rl : List (TermedRun S (Q β) Cb.Gl.E)) :
    ∀ m ∈ moves₁ L rl ++ moves₂ (α := Phi β) L, MoveKeeps (·.failed) m.move := by
  obtain ⟨eo, ea⟩ := order_at hL
  have k6 : ∀ name ∈ ["norm", "policy", "logits"], ∀ run, At L (3, name) run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → e₁.failed = e.failed := fun name hn run hr => by
    obtain ⟨r, h0, hu⟩ := A.ties.tK6 name hn run hr
    exact keep_under _ hu (hands_failed
      (k6_still h iU3 p (phiAll u ψ) Ok kap A.hkap A.okK6 l' piece name r h0).hands)
  refine moves_keepL (·.failed) L rl ?_ ?_
  · rw [eo, order_head]
    refine ⟨k3f _ (by simp),
      fun run hr => keep_under _ (A.ties.tGuests 2 (by simp) run hr) (idle_failed fun _ _ => rfl),
      k6 "norm" (by simp), fun run hr => ?_, k6 "policy" (by simp), k3f _ (by simp),
      k3f _ (by simp),
      fun run hr => keep_under _ (A.ties.tGuests 7 (by simp) run hr) (idle_failed fun _ _ => rfl),
      fun run hr => ?_, k6 "logits" (by simp), fun run hr => ?_⟩
    · exact keep_under _ (A.ties.tJoin run hr) (join_failed h iU3 p)
    · exact keep_under _ (A.ties.tEq run hr) fun n e c e₁ hr => k8Run_failed n e e₁ c hr
    · exact keep_under _ (A.ties.tMerge run hr) merge_failed
  · rw [ea, after_head]
    refine ⟨fun run hr => ?_, fun run hr => ?_⟩
    · exact keepAfter_under _ (A.ties.tLs run hr) k8LsTail_failed
    · exact keepAfter_under _ (A.ties.tTests run hr) (k8Tests_failed nU)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.failed_layers
#print axioms VerifiableInference.Desc.LinkJoin.failed_attention
#print axioms VerifiableInference.Desc.LinkJoin.failed_head
