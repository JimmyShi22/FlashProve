-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/ThetaRunAt.lean: THE SMALLNESS TEST: "A LEDGER IS OPEN AND ITS BATCHING
ELEMENT IS θ" IS HANDED ON BY EACH RUN THAT A LINK's TWO ORDERS NAME (the order that the batching
gathers, and the order behind it), AT A LINK OF EACH OF THE THREE SORTS: from the library's
gathering of that sort's ties (`LayersTake`, `AttTake`, `HeadTake`) and the like sentence at the
lookups' runs alone. Each is one call of the library's law on the runs of a link's two orders
(`run_layers`, `run_attention`, `run_head`, Johnson/Desc/First/Link/Law/RunRel.lean) at
`rests_theta` (Johnson/Desc/K8/Honest/ThetaRests.lean). None of the library's goals.

  `ThetaAt Lk os`   a named premise: the sentence is handed on at the entries of the list os
  `ThetaRun Lk`   it is handed on at every entry of the link's order, and at every entry of the
                   order behind
  **`thetaRun_layers`**, **`thetaRun_attention`**, **`thetaRun_head`**   SegAt l ‹the sort› L → ‹the
                   sort's ties› → ThetaAt L ‹the lookups' entries of that sort› → ThetaRun L
Limits. THE SORT's TIES AND `ThetaAt` AT THE LOOKUPS' ENTRIES ARE PREMISES: two entries at a
feed-forward link, four at an attention link, three at the head's: that a lookup's run leaves the
ledger's batching element is not shown here. NOTHING ON THE ADDING OF THE CLAIMS, which stands
between the two orders; nothing on the draw. That no run between writes the data's vectors of powers
is not said here.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.ThetaRests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.K9L (Bound GE8)
open VerifiableInference.Desc.PhiAll (Phi)
open VerifiableInference.Desc.LinkJoin (Q HasFork SegAt LayersTake AttTake HeadTake run_layers
  run_attention run_head)

/-- The sentence is handed on at the entries of a list. -/
def ThetaAt (Lk : Link S Claim) (os : List (ℕ × String)) : Prop :=
  ∀ θ : E, ∀ o ∈ os, ∀ run, LinkJoin.At Lk o run → ∀ n e c e₁, run n e = .ok (c, e₁) →
    HasFork (fun G => G.theta = θ) e → HasFork (fun G => G.theta = θ) e₁

/-- The sentence is handed on at every entry of the link's two orders. -/
def ThetaRun (Lk : Link S Claim) : Prop :=
  ThetaAt Lk Lk.order ∧
    ∀ θ : E, ∀ o ∈ Lk.orderAfter, ∀ run, LinkJoin.AtAfter Lk o run → ∀ e e₁, run e = .ok e₁ →
      HasFork (fun G => G.theta = θ) e → HasFork (fun G => G.theta = θ) e₁

variable {β : Type} {l : ℕ} {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
  {Fu : S → Prop} {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
  {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
  {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}

/-- **At a feed-forward link.** -/
theorem thetaRun_layers (hL : SegAt l .layers L) {p : OnBytes.Desc.First.K4.Par}
    (A : LayersTake L u ψ Ok Fu p nU ent tm4 t3 l3)
    (k3 : ThetaAt L [(1, "objects"), (6, "objects")]) : ThetaRun L :=
  ⟨fun θ => (run_layers (rests_theta θ) hL A (k3 θ)).1,
    fun θ => (run_layers (rests_theta θ) hL A (k3 θ)).2⟩

/-- **At an attention link.** -/
theorem thetaRun_attention (hL : SegAt l .attention L)
    {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : First.Att.P.ParC}
    (A : AttTake L u ψ Ok Fu rd c nU ent tm4 t3 l3)
    (k3 : ThetaAt L [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")]) : ThetaRun L :=
  ⟨fun θ => (run_attention (rests_theta θ) hL A (k3 θ)).1,
    fun θ => (run_attention (rests_theta θ) hL A (k3 θ)).2⟩

/-- **At the head's link.** -/
theorem thetaRun_head (hL : SegAt l .head L) {h : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ}
    {p : Kinds.Head.Par} {kap : Phi β → Option Kinds.Head.Law.Seen}
    (A : HeadTake L u ψ Ok Fu h iU3 l' piece p kap nU ent tm4 t3 l3)
    (k3 : ThetaAt L [(2, "objects"), (2, "planes"), (7, "objects")]) : ThetaRun L :=
  ⟨fun θ => (run_head (rests_theta θ) hL A (k3 θ)).1,
    fun θ => (run_head (rests_theta θ) hL A (k3 θ)).2⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.thetaRun_layers
#print axioms VerifiableInference.Desc.First.K8.Honest.thetaRun_attention
#print axioms VerifiableInference.Desc.First.K8.Honest.thetaRun_head
