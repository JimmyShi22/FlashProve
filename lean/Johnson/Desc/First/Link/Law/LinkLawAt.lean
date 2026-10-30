-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LinkLawAt.lean: TWO OF `LinkOwes`' EIGHT LISTS OF DEBTS (LinkOwes.lean),
PAID AT EACH OF THE THREE SORTS OF LINK: `OwesRuns` by the assembly of the kinds' laws
(PayLayers.lean, PayAttention.lean, PayHead.lean); `OwesNumbers` by the test on the exponents
(ExpsAt.lean). Eight theorems.

What is said. `names_once`: a guard for the tables of terms. `entries_within`: every entry of the
orders names a hearing block of a number from 1 to 8. `runs_layers`, `runs_attention`, `runs_head`:
**`OwesRuns` at each sort**, at the closed φ and the sort's table of terms, from what the kinds'
laws take there (`LayersTake`, `AttTake`, `HeadTake`). `numbers_layers`, `numbers_attention`,
`numbers_head`: **`OwesNumbers` at each sort**, from d ≤ 2 ^ 60 and, at every state that is ready,
`EqTake` and `PlainE` of the lookup's entries.

Limits. IMPLICATIONS: shown of no record of the protocol. The other six lists (`OwesBlocks`,
`OwesPieces`, `OwesCaller`, `OwesFull`, `OwesConds`, `OwesLetters`) are not touched here. Nothing on
soundness.

-/
import Johnson.Desc.First.Link.Law.ExpsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.PhiAll

variable {β : Type}

/-- A GUARD for the tables of terms, which are keyed by an entry's name: in each of the three orders
every name but "objects" and "guests" stands once. A tripwire for the build: no law takes it. The
tables give "guests" one term at both its blocks: right because both runs are idle. -/
theorem names_once (sub : First.ModelPart) :
    (((First.orderOf sub).map (·.2)).filter fun n => n != "objects" && n != "guests").Nodup := by
  cases sub <;> decide

/-- Every entry of the three orders, in front of the batching and behind it, names a hearing block
of a number from 1 to 8. A tripwire for the build, as names_once is. -/
theorem entries_within (sub : First.ModelPart) :
    (∀ o ∈ First.orderOf sub, 1 ≤ o.1 ∧ o.1 ≤ 8) ∧
      ∀ o ∈ First.orderAfterOf sub, 1 ≤ o.1 ∧ o.1 ≤ 8 := by
  cases sub <;> decide

/-! ## The debts on the runs -/

/-- **OwesRuns AT A LAYERS' LINK.** -/
theorem runs_layers {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop} {Fu : S → Prop}
    {p4 : OnBytes.Desc.First.K4.Par} {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : LayersTake L u ψ Ok Fu p4 nU ent tm4 t3 l3) :
    OwesRuns .layers L (phiAll u ψ) Ok Fu (tmL p4 ent tm4 t3) (lenL p4 l3) :=
  ⟨phi_layers A, pay_layers A, payd_layers A, quiet_layers A, quietd_layers A⟩

/-- **OwesRuns AT AN ATTENTION LINK.** -/
theorem runs_attention {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)}
    {c : First.Att.P.ParC} {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : AttTake L u ψ Ok Fu rd c nU ent tm4 t3 l3) :
    OwesRuns .attention L (phiAll u ψ) Ok Fu (tmA rd c ent tm4 t3) (lenA rd c l3) :=
  ⟨phi_att A, pay_att A, payd_att A, quiet_att A, quietd_att A⟩

/-- **OwesRuns AT THE HEAD's LINK.** -/
theorem runs_head {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop} {Fu : S → Prop}
    {h : OnBytes.Model.Head.Shape} {iU3 l piece : ℕ} {p6 : Kinds.Head.Par}
    {kap : Phi β → Option Kinds.Head.Law.Seen} {nU : Array ℕ}
    {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : HeadTake L u ψ Ok Fu h iU3 l piece p6 kap nU ent tm4 t3 l3) :
    OwesRuns .head L (phiAll u ψ) Ok Fu (tmH h iU3 p6 kap ent tm4 t3) (lenH h iU3 p6 kap l3) :=
  ⟨phi_head A, pay_head A, payd_head A, quiet_head A, quietd_head A⟩

/-! ## The debts on the numbers -/

/-- **OwesNumbers AT A LAYERS' LINK.** -/
theorem numbers_layers {l : ℕ} {L : Link S Claim} (hL : SegAt l .layers L) (u : HTailF2)
    (ψ : S → β) (Ok : Q β → Prop) (p : OnBytes.Desc.First.K4.Par)
    (ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8) (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ) (d : ℕ)
    (hd : d ≤ 2 ^ 60)
    (E : ∀ s, k9OnA s = true ∧ Ok (fixed9 (phiAll u ψ) s) → ∃ tlb funs v, ∀ y,
      EqTake tm4 (fixed9 (phiAll u ψ) s) y
        (lenRuns (fixed9 (phiAll u ψ) s) (rlOf L (tmL p ent tm4 t3) (lenL p l3))) d tlb funs v ∧
      ∀ o ∈ [(1, "objects"), (6, "objects")],
        PlainE (tmL p ent tm4 t3) (lenL p l3) (fixed9 (phiAll u ψ) s) y o) :
    OwesNumbers L (phiAll u ψ) Ok (tmL p ent tm4 t3) (lenL p l3) d :=
  ⟨hd, hokF_layers hL u ψ Ok p ent tm4 t3 l3 d E⟩

/-- **OwesNumbers AT AN ATTENTION LINK.** -/
theorem numbers_attention {l : ℕ} {L : Link S Claim} (hL : SegAt l .attention L) (u : HTailF2)
    (ψ : S → β) (Ok : Q β → Prop) (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard))
    (c : First.Att.P.ParC) (ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ) (d : ℕ)
    (hd : d ≤ 2 ^ 60)
    (E : ∀ s, k9OnA s = true ∧ Ok (fixed9 (phiAll u ψ) s) → ∃ tlb funs v, ∀ y,
      EqTake tm4 (fixed9 (phiAll u ψ) s) y
        (lenRuns (fixed9 (phiAll u ψ) s) (rlOf L (tmA rd c ent tm4 t3) (lenA rd c l3))) d tlb funs
        v ∧
      ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")],
        PlainE (tmA rd c ent tm4 t3) (lenA rd c l3) (fixed9 (phiAll u ψ) s) y o) :
    OwesNumbers L (phiAll u ψ) Ok (tmA rd c ent tm4 t3) (lenA rd c l3) d :=
  ⟨hd, hokF_attention hL u ψ Ok rd c ent tm4 t3 l3 d E⟩

/-- **OwesNumbers AT THE HEAD's LINK.** -/
theorem numbers_head {l : ℕ} {L : Link S Claim} (hL : SegAt l .head L) (u : HTailF2) (ψ : S → β)
    (Ok : Q β → Prop) (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Kinds.Head.Par)
    (kap : Phi β → Option Kinds.Head.Law.Seen) (ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ) (d : ℕ)
    (hd : d ≤ 2 ^ 60)
    (E : ∀ s, k9OnA s = true ∧ Ok (fixed9 (phiAll u ψ) s) → ∃ tlb funs v, ∀ y,
      EqTake tm4 (fixed9 (phiAll u ψ) s) y
        (lenRuns (fixed9 (phiAll u ψ) s)
          (rlOf L (tmH h iU3 p kap ent tm4 t3) (lenH h iU3 p kap l3))) d tlb funs v ∧
      ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")],
        PlainE (tmH h iU3 p kap ent tm4 t3) (lenH h iU3 p kap l3) (fixed9 (phiAll u ψ) s) y o) :
    OwesNumbers L (phiAll u ψ) Ok (tmH h iU3 p kap ent tm4 t3) (lenH h iU3 p kap l3) d :=
  ⟨hd, hokF_head hL u ψ Ok h iU3 p kap ent tm4 t3 l3 d E⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.names_once
#print axioms VerifiableInference.Desc.LinkJoin.entries_within
#print axioms VerifiableInference.Desc.LinkJoin.runs_layers
#print axioms VerifiableInference.Desc.LinkJoin.runs_attention
#print axioms VerifiableInference.Desc.LinkJoin.runs_head
#print axioms VerifiableInference.Desc.LinkJoin.numbers_layers
#print axioms VerifiableInference.Desc.LinkJoin.numbers_attention
#print axioms VerifiableInference.Desc.LinkJoin.numbers_head
