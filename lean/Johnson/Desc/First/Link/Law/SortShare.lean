-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortShare.lean: THE RUNS' SHARE OF A LINK (`LinkShare`, RidesAtMg.lean)
FROM A SORT's Take, AS A LEMMA OF ITS OWN, AND THE FIELD hbook₂ OF WHAT IS LEFT OF A LINK's LAW
(`CoreRest2`, LinkRestAtSort2.lean; `CoreLeft`) FROM THE SHARE. Theorems: calls.

Why. In LinkRestAtSort2 | 3 the share is built inside the three theorems' proofs: nobody else could
call it. hbook₂ ("the frame's move behind the batching leaves the book") stayed a field although it
follows from the share.

What is said.
  `linkShare_layers`, `linkShare_att`, `linkShare_head`: LinkShare L p from the segment's sort, the
    sort's Take (at any letters), three facts on the lookup argument's runs (k3p: a yes puts a
    ledger; k3s, k3sL: a sized ledger stays open), the batching's draw and p.rows ≠ 0. The terms
    are those of LinkRestAtSort2.
  `hbook2_of_share`: **hbook₂, in its own text, from LinkShare**: the share's field "stand" at the
    relation "the book is the same" (rests_book, KeepsAny.lean), then hbook2_at
    (LettersAt.lean).

Limits. BOOK-KEEPING. The Take and the three facts on the lookup's runs are premises. Nothing on
soundness.

-/
import Johnson.Desc.First.Link.Law.RidesAtMg
import Johnson.Desc.First.Link.Law.LettersAt
import Johnson.Desc.First.Link.Law.NumRuns
import Johnson.Desc.First.Link.Law.LinkAtSort
import Johnson.Desc.First.Link.Law.KeepsAny

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.PhiAll

variable {β : Type}

/-- **THE RUNS' SHARE OF A LAYERS' LINK, FROM THE SORT's Take.** -/
theorem linkShare_layers {l : ℕ} {L : Link S Claim} (hL : SegAt l .layers L) {u : HTailF2}
    {ψ : S → β} {Ok : Q β → Prop} {Fu : S → Prop}
    {p4 : OnBytes.Desc.First.K4.Par}
    {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : LayersTake L u ψ Ok Fu p4 nU ent tm4 t3 l3)
    (k3p : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c,
      e₁) → ∃ G, e₁ = e.putFork G)
    (k3s : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c,
      e₁) → HasFork Sized e → HasFork Sized e₁)
    (k3sL : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run → ∀ n e c e₁, run n e = .ok
      (c, e₁) → HasFork (fun F => Sized F ∧ F.LS.size = F.ns) e → HasFork (fun F => Sized F ∧
      F.LS.size = F.ns) e₁)
    (p : Where) (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (rows : p.rows ≠ 0) : LinkShare L p :=
  ⟨drawB, rows,
    fun _ Rr hf => rel_layers Rr hL A fun o ho run hr n e c e₁ hy => by
      obtain ⟨G, rfl⟩ := k3p o ho run hr n e c e₁ hy
      exact hf e G,
    ⟨(4, "K8.equations"), by rw [(order_at hL).1]; decide, A.ties.tEq⟩,
    (run_layers (rests_fork sizedLS_rests) hL A k3sL).1,
    (run_layers (rests_fork sized_rests) hL A k3s).2⟩

/-- **THE RUNS' SHARE OF AN ATTENTION LINK, FROM THE SORT's Take.** -/
theorem linkShare_att {l : ℕ} {L : Link S Claim} (hL : SegAt l .attention L) {u : HTailF2}
    {ψ : S → β} {Ok : Q β → Prop} {Fu : S → Prop}
    {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)}
    {c : First.Att.P.ParC}
    {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : AttTake L u ψ Ok Fu rd c nU ent tm4 t3 l3)
    (k3p : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run → ∀
      n e c e₁, run n e = .ok (c, e₁) → ∃ G, e₁ = e.putFork G)
    (k3s : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run → ∀
      n e c e₁, run n e = .ok (c, e₁) → HasFork Sized e → HasFork Sized e₁)
    (k3sL : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → HasFork (fun F => Sized F ∧ F.LS.size = F.ns) e → HasFork
      (fun F => Sized F ∧ F.LS.size = F.ns) e₁)
    (p : Where) (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (rows : p.rows ≠ 0) : LinkShare L p :=
  ⟨drawB, rows,
    fun _ Rr hf => rel_attention Rr hL A fun o ho run hr n e c e₁ hy => by
      obtain ⟨G, rfl⟩ := k3p o ho run hr n e c e₁ hy
      exact hf e G,
    ⟨(4, "K8.equations"), by rw [(order_at hL).1]; decide, A.ties.tEq⟩,
    (run_attention (rests_fork sizedLS_rests) hL A k3sL).1,
    (run_attention (rests_fork sized_rests) hL A k3s).2⟩

/-- **THE RUNS' SHARE OF THE HEAD's LINK, FROM THE SORT's Take.** -/
theorem linkShare_head {l : ℕ} {L : Link S Claim} (hL : SegAt l .head L) {u : HTailF2}
    {ψ : S → β} {Ok : Q β → Prop} {Fu : S → Prop}
    {hS : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ} {p6 : Kinds.Head.Par}
    {kap : Phi β → Option Kinds.Head.Law.Seen}
    {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : HeadTake L u ψ Ok Fu hS iU3 l' piece p6 kap nU ent tm4 t3 l3)
    (k3p : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run → ∀ n e c e₁,
      run n e = .ok (c, e₁) → ∃ G, e₁ = e.putFork G)
    (k3s : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run → ∀ n e c e₁,
      run n e = .ok (c, e₁) → HasFork Sized e → HasFork Sized e₁)
    (k3sL : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run → ∀ n e c e₁,
      run n e = .ok (c, e₁) → HasFork (fun F => Sized F ∧ F.LS.size = F.ns) e → HasFork (fun F =>
      Sized F ∧ F.LS.size = F.ns) e₁)
    (p : Where) (drawB : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (rows : p.rows ≠ 0) : LinkShare L p :=
  ⟨drawB, rows,
    fun _ Rr hf => rel_head Rr hL A fun o ho run hr n e c e₁ hy => by
      obtain ⟨G, rfl⟩ := k3p o ho run hr n e c e₁ hy
      exact hf e G,
    ⟨(5, "K8.equations"), by rw [(order_at hL).1]; decide, A.ties.tEq⟩,
    (run_head (rests_fork sizedLS_rests) hL A k3sL).1,
    (run_head (rests_fork sized_rests) hL A k3s).2⟩

/-- **hbook₂ FROM THE SHARE.** -/
theorem hbook2_of_share {α : Type} {L : Link S Claim} {p : Where} (h : LinkShare L p) :
    ∀ m ∈ (moves₂ (α := α) L).map (·.move), MoveBook m :=
  hbook2_at L (h.stand (fun e e₁ => e₁.book = e.book) (relRests_of_field rests_book)
    fun s G => rests_book.fork s G).2

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.linkShare_layers
#print axioms VerifiableInference.Desc.LinkJoin.linkShare_att
#print axioms VerifiableInference.Desc.LinkJoin.linkShare_head
#print axioms VerifiableInference.Desc.LinkJoin.hbook2_of_share
