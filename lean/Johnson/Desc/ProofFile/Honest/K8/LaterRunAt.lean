-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/LaterRunAt.lean: THE SMALLNESS TEST: THE NAMED PREMISE `LaterRun`
OF `termsBack_four` (Johnson/Desc/ProofFile/Honest/K8/TermsBackFour.lean: each run that a link's
order names hands on "a ledger is open and is later than U") AT A LINK OF EACH OF THE THREE SORTS:
from the library's gathering of that sort's ties (`LayersTake`, `AttTake`, `HeadTake`) and the like
sentence at the lookups' runs alone. Each is one call of the library's law on the runs of a link's
two orders (`run_layers`, `run_attention`, `run_head`, Johnson/Desc/First/Link/Law/RunRel.lean) at
`rests_later` (Johnson/Desc/K8/Honest/LaterRests.lean). None of the library's goals.

  `LaterAt Lk os`   a named premise: `LaterRun`'s sentence at the entries of the list os alone
  **`laterRun_layers`**, **`laterRun_attention`**, **`laterRun_head`**   SegAt l ‹the sort› L → ‹the
                   sort's ties› → LaterAt L ‹the lookups' entries of that sort› → LaterRun L
Limits. THE SORT's TIES AND `LaterAt` AT THE LOOKUPS' ENTRIES ARE PREMISES: two entries at a
feed-forward link, four at an attention link, three at the head's: that a lookup's run yields a
later ledger is not shown here. Nothing on the draw.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.TermsBackFour
import Johnson.Desc.K8.Honest.LaterRests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest (rests_later)
open VerifiableInference.Desc.K9L (Bound GE8)
open VerifiableInference.Desc.PhiAll (Phi)
open VerifiableInference.Desc.LinkJoin (Q HasFork SegAt LayersTake AttTake HeadTake run_layers
  run_attention run_head)

/-- `LaterRun`'s sentence at the entries of a list alone. -/
def LaterAt (Lk : Link S Claim) (os : List (ℕ × String)) : Prop :=
  ∀ U : Fork, OnBytes.PscRun.Sized U → ∀ o ∈ os, ∀ run, LinkJoin.At Lk o run →
    ∀ n e c e₁, run n e = .ok (c, e₁) →
      HasFork (fun G => OnBytes.PscRun.Later U G) e → HasFork (fun G => OnBytes.PscRun.Later U G) e₁

variable {β : Type} {l : ℕ} {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
  {Fu : S → Prop} {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
  {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
  {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}

/-- **At a feed-forward link.** -/
theorem laterRun_layers (hL : SegAt l .layers L) {p : OnBytes.Desc.First.K4.Par}
    (A : LayersTake L u ψ Ok Fu p nU ent tm4 t3 l3)
    (k3 : LaterAt L [(1, "objects"), (6, "objects")]) : LaterRun L :=
  fun U hU => (run_layers (rests_later hU) hL A (k3 U hU)).1

/-- **At an attention link.** -/
theorem laterRun_attention (hL : SegAt l .attention L)
    {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : First.Att.P.ParC}
    (A : AttTake L u ψ Ok Fu rd c nU ent tm4 t3 l3)
    (k3 : LaterAt L [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")]) : LaterRun L :=
  fun U hU => (run_attention (rests_later hU) hL A (k3 U hU)).1

/-- **At the head's link.** -/
theorem laterRun_head (hL : SegAt l .head L) {h : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ}
    {p : Kinds.Head.Par} {kap : Phi β → Option Kinds.Head.Law.Seen}
    (A : HeadTake L u ψ Ok Fu h iU3 l' piece p kap nU ent tm4 t3 l3)
    (k3 : LaterAt L [(2, "objects"), (2, "planes"), (7, "objects")]) : LaterRun L :=
  fun U hU => (run_head (rests_later hU) hL A (k3 U hU)).1

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.laterRun_layers
#print axioms ProofFile.Honest.K8.laterRun_attention
#print axioms ProofFile.Honest.K8.laterRun_head
