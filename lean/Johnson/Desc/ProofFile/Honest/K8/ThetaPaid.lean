-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/ThetaPaid.lean: THE SMALLNESS TEST: THE ONE SENTENCE THAT
Johnson/Desc/K8/Honest/ThetaRunAt.lean LEFT OPEN ON THE LOOKUPS' RUNS (`ThetaAt` at the lookups'
entries of a link's order: an accepting call of each of these runs hands on "a ledger is open and
its batching element is θ") IS PAID, UNDER THE LIBRARY's HEAD, AT EACH OF THE 25 LINKS OF THE FIRST
CHAIN: by the three lemmas of Johnson/Desc/ProofFile/Honest/K3/Law/ThetaKept.lean, whose ends are
`ThetaAt` unfolded once: Lean takes each for the other. So every run that a link's two orders name
hands the sentence on, from the sort's ties alone. None of the library's goals.

  **`thetaAt_layers`**, **`thetaAt_attention`**, **`thetaAt_head`**   the head · g < 12 · L is the
                   chain's link number 2 g | 2 g + 1 | 24 ⊢ ThetaAt L ‹the lookups' entries: two |
                   four | three›
  **`thetaRun_layers_paid`**, **`thetaRun_attention_paid`**, **`thetaRun_head_paid`**   these ·
                   SegAt · the sort's ties ⊢ ThetaRun L
Limits. THE LIBRARY's HEAD IS A PREMISE HERE: no member of it is joined here; THE FULL SIZE ALONE.
`SegAt` and the sort's ties stay premises. THE THREE LEMMAS THAT PAY LIE IN ANOTHER FILE: this file
stands over it, adds no proof of its own to it, and is no better than it. The link is named as a
member of the chain's list of links.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.ThetaRunAt
import Johnson.Desc.ProofFile.Honest.K3.Law.ThetaKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.K9L (Bound GE8)
open VerifiableInference.Desc.PhiAll (Phi)
open VerifiableInference.Desc.LinkJoin (Q SegAt LayersTake AttTake HeadTake)
open VerifiableInference.Desc.First.K8.Honest (ThetaAt ThetaRun thetaRun_layers thetaRun_attention
  thetaRun_head)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **At a feed-forward link.** -/
theorem thetaAt_layers (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {L : Link S Claim} (hL : cF.links[2 * g]? = some L) :
    ThetaAt L [(1, "objects"), (6, "objects")] :=
  K3.Law.theta_at_layers h g hg hL

/-- **At an attention link.** -/
theorem thetaAt_attention (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {L : Link S Claim} (hL : cF.links[2 * g + 1]? = some L) :
    ThetaAt L [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")] :=
  K3.Law.theta_at_attention h g hg hL

/-- **At the head's link.** -/
theorem thetaAt_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {L : Link S Claim}
    (hL : cF.links[24]? = some L) :
    ThetaAt L [(2, "objects"), (2, "planes"), (7, "objects")] :=
  K3.Law.theta_at_head h hL

variable {β : Type} {l : ℕ} {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
  {Fu : S → Prop} {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
  {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
  {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}

/-- So at a feed-forward link every run of the two orders hands the sentence on. -/
theorem thetaRun_layers_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    (hL : cF.links[2 * g]? = some L) (hS : SegAt l .layers L)
    {p : OnBytes.Desc.First.K4.Par} (A : LayersTake L u ψ Ok Fu p nU ent tm4 t3 l3) :
    ThetaRun L :=
  thetaRun_layers hS A (thetaAt_layers h hg hL)

/-- At an attention link. -/
theorem thetaRun_attention_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ}
    (hg : g < 12) (hL : cF.links[2 * g + 1]? = some L) (hS : SegAt l .attention L)
    {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : First.Att.P.ParC}
    (A : AttTake L u ψ Ok Fu rd c nU ent tm4 t3 l3) : ThetaRun L :=
  thetaRun_attention hS A (thetaAt_attention h hg hL)

/-- At the head's link. -/
theorem thetaRun_head_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hL : cF.links[24]? = some L) (hS : SegAt l .head L) {hs : OnBytes.Model.Head.Shape}
    {iU3 l' piece : ℕ} {p : Kinds.Head.Par} {kap : Phi β → Option Kinds.Head.Law.Seen}
    (A : HeadTake L u ψ Ok Fu hs iU3 l' piece p kap nU ent tm4 t3 l3) : ThetaRun L :=
  thetaRun_head hS A (thetaAt_head h hL)

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.thetaAt_layers
#print axioms ProofFile.Honest.K8.thetaAt_attention
#print axioms ProofFile.Honest.K8.thetaAt_head
#print axioms ProofFile.Honest.K8.thetaRun_layers_paid
#print axioms ProofFile.Honest.K8.thetaRun_attention_paid
#print axioms ProofFile.Honest.K8.thetaRun_head_paid
