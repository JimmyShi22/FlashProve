-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/FullAtSort.lean: `OwesFull` (LinkOwes.lean: the debt on the state behind
the last move) PAID AT EACH OF THE THREE SORTS OF LINK, at `Fu := FullAt nU` (GoodFull.lean), from
the sort's Take and the lookup's runs' share of «good stays». Three theorems: calls of `hend_of`,
`run_layers`, `run_attention`, `run_head` at `rests_good`.

Limits. IMPLICATIONS, as the three Takes are: and these now stand AT `Fu := FullAt nU`: their ten
fields on Fu are sentences on the ledger that the run of self tests leaves: not paid here. Nothing
on soundness.

-/
import Johnson.Desc.First.Link.Law.GoodFull
import Johnson.Desc.First.Link.Law.LinkOwes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.PhiAll

variable {β : Type}

/-- **OwesFull AT A LAYERS' LINK.** -/
theorem full_layers {l : ℕ} {L : Link S Claim} (hL : SegAt l .layers L) {u : HTailF2}
    {ψ : S → β} {Ok : Q β → Prop} {p : OnBytes.Desc.First.K4.Par} {nU : Array ℕ}
    {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : LayersTake L u ψ Ok (FullAt nU) p nU ent tm4 t3 l3)
    (k3g : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → good9 e → good9 e₁) :
    OwesFull L (FullAt nU) (tmL p ent tm4 t3) (lenL p l3) :=
  ⟨hend_of L nU _ (run_layers rests_good hL A k3g).1 (run_layers rests_good hL A k3g).2
    [(4, "K8.lsTail"), (2, "free-slot")] (4, "K8.tests") (by rw [(order_at hL).2]; rfl)
    A.ties.tTests⟩

/-- **OwesFull AT AN ATTENTION LINK.** -/
theorem full_attention {l : ℕ} {L : Link S Claim} (hL : SegAt l .attention L) {u : HTailF2}
    {ψ : S → β} {Ok : Q β → Prop} {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)}
    {c : First.Att.P.ParC} {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : AttTake L u ψ Ok (FullAt nU) rd c nU ent tm4 t3 l3)
    (k3g : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run,
      At L o run → ∀ n e c' e₁, run n e = .ok (c', e₁) → good9 e → good9 e₁) :
    OwesFull L (FullAt nU) (tmA rd c ent tm4 t3) (lenA rd c l3) :=
  ⟨hend_of L nU _ (run_attention rests_good hL A k3g).1 (run_attention rests_good hL A k3g).2
    [(4, "K8.lsTail")] (4, "K8.tests") (by rw [(order_at hL).2]; rfl) A.ties.tTests⟩

/-- **OwesFull AT THE HEAD's LINK.** -/
theorem full_head {l : ℕ} {L : Link S Claim} (hL : SegAt l .head L) {u : HTailF2} {ψ : S → β}
    {Ok : Q β → Prop} {h : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ} {p : Kinds.Head.Par}
    {kap : Phi β → Option Kinds.Head.Law.Seen} {nU : Array ℕ}
    {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : HeadTake L u ψ Ok (FullAt nU) h iU3 l' piece p kap nU ent tm4 t3 l3)
    (k3g : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → good9 e → good9 e₁) :
    OwesFull L (FullAt nU) (tmH h iU3 p kap ent tm4 t3) (lenH h iU3 p kap l3) :=
  ⟨hend_of L nU _ (run_head rests_good hL A k3g).1 (run_head rests_good hL A k3g).2
    [(5, "K8.lsTail")] (5, "K8.tests") (by rw [(order_at hL).2]; rfl) A.ties.tTests⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.full_layers
#print axioms VerifiableInference.Desc.LinkJoin.full_attention
#print axioms VerifiableInference.Desc.LinkJoin.full_head
