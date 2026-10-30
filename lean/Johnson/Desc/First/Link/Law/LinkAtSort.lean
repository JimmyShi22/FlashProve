-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LinkAtSort.lean: WHAT A YES OF THE BATCHING's BLOCK AND OF THE FRAME's
BLOCK BEHIND IT DOES TO THE RECORD, AT EACH OF THE THREE SORTS OF LINK, WITH THE RUNS' SHARE PAID:
from the sort's Take and ONE sentence on the lookup's runs («a yes turns the record by a writing of
the ledger alone»). Theorems: a gathering of BkLink.lean, LaidAt.lean, OwedRides.lean, RelRuns.lean,
KeepsAny.lean.

What is said.
  `fold_runs`: a yes of the link's gatherer finds a run at every entry of the order.
    `relRests_of_field`: a field that rests under the four writings gives a relation that holds of
    the six. `RunsStand L B`: every yes of every run of both orders stands in B. `TwoBlocks L pp`:
    **a yes of the batching's block stands in `Rb` and makes the two public facts; a yes of the
    frame's block behind it stands in `Rb` and keeps them.** `two_blocks`: that, from `RunsStand` at
    whatever relation holds of the six writings and of a writing of the ledger, and the tie of the
    entry «K8.equations». `blocks_layers`, `blocks_attention`, `blocks_head`: **`TwoBlocks` at each
    sort.**

Limits. IMPLICATIONS, as the three Takes are; of these only the ties to the kinds' runs and four
facts on the letters are spent. The lookup's sentence is a premise at its nine entries (K3's files
hold it of K3's runs; the ties of the entries to these runs are owed). That the batching's block
is a draw with the gatherer behind it (hb₁) and that its round counts a row are premises. Nothing on
soundness.

-/
import Johnson.Desc.First.Link.Law.BkLink
import Johnson.Desc.First.Link.Law.KeepsAny

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS Where owedOf)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.JoinAtBlocks

/-- A yes of the link's gatherer finds a run at every entry of the order. -/
theorem fold_runs (each : ℕ × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) : ∀ (order : List (ℕ × String)) (x z : List Claim × S),
      order.foldl (fun (acc : Except String (List Claim × S)) o =>
        acc.bind fun x => claimsInStep each bs x o) (.ok x) = .ok z →
      ∀ o ∈ order, ∃ run, ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = some run
  | [], _, _, _, _, ho => nomatch ho
  | o :: l, x, z, h, o', ho' => by
    have h' : l.foldl (fun (acc : Except String (List Claim × S)) o =>
        acc.bind fun x => claimsInStep each bs x o) (claimsInStep each bs x o) = .ok z := h
    cases hs : claimsInStep each bs x o with
    | error e =>
      rw [hs, claimsInFold_error] at h'
      exact nomatch h'
    | ok x' =>
      rw [hs] at h'
      rcases List.mem_cons.1 ho' with rfl | ho'
      · obtain ⟨run, hl, _⟩ := step_gstep each bs x x' o' hs
        exact ⟨run, hl⟩
      · exact fold_runs each bs l x' z h' o' ho'

/-- A field that rests under the four writings gives a relation that holds of the six. -/
theorem relRests_of_field {γ : Type} {f : S → γ} (R : FieldRests f) :
    RelRests fun e e₁ => f e₁ = f e where
  refl _ := rfl
  wrote := R.wrote
  head := R.head
  eq n e c e₁ h := k8Run_keeps R n e e₁ c h
  ls := k8LsTail_keeps R
  tests := k8Tests_keeps R

/-- Every yes of every run of both orders stands in B. -/
def RunsStand (L : Link S Claim) (B : S → S → Prop) : Prop :=
  (∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) → B e e₁) ∧
    ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → B e e₁

/-- **What the two blocks' yeses do to the record.** -/
def TwoBlocks (L : Link S Claim) (pp : Where) : Prop :=
  (∀ ft s rs cols s' k, L.batchB.step ft s rs cols = .ok (s', k) → Rb s s' ∧ TwoFacts pp s') ∧
    ∀ ft s rs cols s' k, L.behindB.step ft s rs cols = .ok (s', k) →
      Rb s s' ∧ (TwoFacts pp s → TwoFacts pp s')

/-- **The two blocks, from the runs' share.** -/
theorem two_blocks (L : Link S Claim) (pp : Where) (hp0 : pp.rows ≠ 0)
    (hb₁ : DrawMoves atS pp [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (H : ∀ B : S → S → Prop, RelRests B → (∀ s G, B s (s.putFork G)) → RunsStand L B)
    (oE : ℕ × String) (hoE : oE ∈ L.order) (hE : ∀ run, At L oE run → Under run k8Run.2) :
    TwoBlocks L pp := by
  have hRb := H Rb rests_rb rb_putFork
  have hLa := H _ rests_laid fun s G => laidOk_congr (pair_putFork s G)
  have hOw := H _ (relRests_of_field rests_owed) rests_owed.fork
  refine ⟨fun ft s rs cols s' k h => ⟨rb_batch L pp hb₁ hRb.1 ft s rs cols s' k h, ?_⟩,
    fun ft s rs cols s' k h => ⟨rb_behind L hRb.2 ft s rs cols s' k h,
      facts_kept L pp (runBehind_keep owedOf L hOw.2) hLa.2 ft s rs cols s' k h⟩⟩
  obtain ⟨r, x, a, o, cls, _, _, _, _, hy⟩ := hb₁ ft s rs cols s' k h
  obtain ⟨u, c, c', ⟨e, q, G, hg, _, _, _⟩, _, _⟩ := hy
  obtain ⟨runE, hAtE⟩ := fold_runs L.each L.hear L.order ([], _) (c, e) hg oE hoE
  refine facts_made L pp hp0 hb₁ (claimsInBy_keep owedOf L.each L.hear L.order fun r' hr' => ?_)
    hLa.1 oE hoE runE hAtE (hE runE hAtE) ft s rs cols s' k h
  obtain ⟨o', ho', e'⟩ := List.mem_filterMap.1 hr'
  obtain ⟨run, hrun, rfl⟩ := Option.map_eq_some_iff.1 e'
  exact hOw.1 o' ho' run hrun

variable {β : Type}

/-- **THE TWO BLOCKS AT A LAYERS' LINK.** -/
theorem blocks_layers {l : ℕ} {L : Link S Claim} (hL : SegAt l .layers L) {u : HTailF2}
    {ψ : S → β} {Ok : Q β → Prop} {Fu : S → Prop} {p : OnBytes.Desc.First.K4.Par} {nU : Array ℕ}
    {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : LayersTake L u ψ Ok Fu p nU ent tm4 t3 l3)
    (k3 : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → ∃ G, e₁ = e.putFork G)
    (pp : Where) (hp0 : pp.rows ≠ 0)
    (hb₁ : DrawMoves atS pp [.add (claimsInBy L.each L.hear L.order)] L.batchB) :
    TwoBlocks L pp :=
  two_blocks L pp hp0 hb₁ (fun B R hf => rel_layers R hL A fun o ho run hr n e c e₁ hy => by
      obtain ⟨G, rfl⟩ := k3 o ho run hr n e c e₁ hy
      exact hf e G) (4, "K8.equations") (by rw [(order_at hL).1]; decide) A.ties.tEq

/-- **THE TWO BLOCKS AT AN ATTENTION LINK.** -/
theorem blocks_attention {l : ℕ} {L : Link S Claim} (hL : SegAt l .attention L) {u : HTailF2}
    {ψ : S → β} {Ok : Q β → Prop} {Fu : S → Prop}
    {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : First.Att.P.ParC}
    {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : AttTake L u ψ Ok Fu rd c nU ent tm4 t3 l3)
    (k3 : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run,
      At L o run → ∀ n e c' e₁, run n e = .ok (c', e₁) → ∃ G, e₁ = e.putFork G)
    (pp : Where) (hp0 : pp.rows ≠ 0)
    (hb₁ : DrawMoves atS pp [.add (claimsInBy L.each L.hear L.order)] L.batchB) :
    TwoBlocks L pp :=
  two_blocks L pp hp0 hb₁ (fun B R hf => rel_attention R hL A fun o ho run hr n e c' e₁ hy => by
      obtain ⟨G, rfl⟩ := k3 o ho run hr n e c' e₁ hy
      exact hf e G) (4, "K8.equations") (by rw [(order_at hL).1]; decide) A.ties.tEq

/-- **THE TWO BLOCKS AT THE HEAD's LINK.** -/
theorem blocks_head {l : ℕ} {L : Link S Claim} (hL : SegAt l .head L) {u : HTailF2} {ψ : S → β}
    {Ok : Q β → Prop} {Fu : S → Prop} {h : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ}
    {p : Kinds.Head.Par} {kap : Phi β → Option Kinds.Head.Law.Seen} {nU : Array ℕ}
    {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : HeadTake L u ψ Ok Fu h iU3 l' piece p kap nU ent tm4 t3 l3)
    (k3 : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → ∃ G, e₁ = e.putFork G)
    (pp : Where) (hp0 : pp.rows ≠ 0)
    (hb₁ : DrawMoves atS pp [.add (claimsInBy L.each L.hear L.order)] L.batchB) :
    TwoBlocks L pp :=
  two_blocks L pp hp0 hb₁ (fun B R hf => rel_head R hL A fun o ho run hr n e c e₁ hy => by
      obtain ⟨G, rfl⟩ := k3 o ho run hr n e c e₁ hy
      exact hf e G) (5, "K8.equations") (by rw [(order_at hL).1]; decide) A.ties.tEq

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.fold_runs
#print axioms VerifiableInference.Desc.LinkJoin.two_blocks
#print axioms VerifiableInference.Desc.LinkJoin.blocks_layers
#print axioms VerifiableInference.Desc.LinkJoin.blocks_attention
#print axioms VerifiableInference.Desc.LinkJoin.blocks_head
