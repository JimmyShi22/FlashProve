-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/NumRuns.lean: THE DUTY `MoveNum`
(Johnson/Desc/First/Batch/Law/RowsRide.lean: where a move returns, `numOf` reads the same: the
approximate range proof's structure with its written fields blanked, the list of tables, the plan's
number of claims) AT A LINK's TWO MOVES, AT EACH OF THE THREE SORTS. Theorems.
  `num_wrote`, `num_head`: a run's writing of a ledger with the same plan's number into a layers'
    link's own part, into the head's. `rests_num`: **`RunRests` (RunRel.lean) at "numOf reads the
    same"**: the nine known runs.
  `moveNum_of_keeps`, `moveNum_link`: the duty at the link's two moves from one duty an entry of the
    two orders (`moves_keepL`, JoinKeeps.lean, at the reading `numOf v`).
  `moveNum_layers`, `moveNum_attention`, `moveNum_head`: **the duty at every move of `moves₁ L rl ++
    moves₂ L`**, from the sort's Take and the lookup's runs' share (k3f).
Limits. IMPLICATIONS, as the three Takes are. The lookup's runs' share stays a premise, as in
RunRel.lean. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.RunRel
import Johnson.Desc.First.Link.Law.SizedRides
import Johnson.Desc.First.Link.Law.JoinKeeps
import Johnson.Desc.First.Batch.Law.RowsRide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Wrote Core blockAtC frontAtC_pays backAtC_pays hideRun_core paid_core)
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

variable {α β : Type}

/-- A run's writing of a ledger with the same plan's number into a layers' link's own part. -/
theorem num_wrote (v : HTailF2) {e e₁ : S} {a : First.LayOwn} {G : Fork} (hw : Wrote e a G e₁)
    (hp : G.planClaimsF = a.F.planClaimsF) : numOf v e₁ = numOf v e := by
  obtain ⟨h1, rfl⟩ := hw
  simp [numOf, S.tl?, S.funs?, S.fork?, h1, hp]

/-- The like into the head's. -/
theorem num_head (v : HTailF2) {e : S} {a : First.HeadOwn} {G : Fork} (h1 : e.here = .head a)
    (hp : G.planClaimsF = a.F.planClaimsF) :
    numOf v { e with here := .head { a with F := G } } = numOf v e := by
  by_cases ho : a.opened = true <;> simp [numOf, S.tl?, S.funs?, S.fork?, h1, ho, hp]

/-- **THE NINE KNOWN RUNS.** -/
theorem rests_num (v : HTailF2) : RunRests fun e e₁ => numOf v e₁ = numOf v e where
  refl _ := rfl
  front p r h0 n e c e₁ hr := by
    obtain ⟨a, _, G, _, hw, hc, _, _⟩ := frontAtC_pays h0 hr
    exact num_wrote v hw hc.planClaimsF
  back p r h0 n e c e₁ hr := by
    obtain ⟨a, _, G, _, hw, hc, _, _⟩ := backAtC_pays h0 hr
    exact num_wrote v hw hc.planClaimsF
  free p r h0 e e₁ hr := by
    obtain ⟨a, hw⟩ := k4_freeSlot_wrote h0 hr
    exact num_wrote v hw rfl
  merge n e c e₁ hr := by
    obtain ⟨a, wo, G, h1, _, rfl, _, hrunG⟩ := claim_inv hr
    exact num_head v h1 (hideRun_core hrunG).planClaimsF
  join h iU3 p n e c e₁ hr := by
    obtain ⟨a, i, h1, rfl⟩ := join_hands h iU3 p n e c e₁ hr
    exact num_head v h1 (paid_core _ i).planClaimsF
  eq n e c e₁ hr := k8Run_num v n e e₁ c hr
  ls e e₁ hr := k8LsTail_num v e e₁ hr
  tests nU e e₁ hr := k8Tests_num v nU e e₁ hr

/-- The duty is "the move keeps the reading". -/
theorem moveNum_of_keeps (v : HTailF2) (m : Move S) (h : MoveKeeps (numOf v) m) : MoveNum v m := by
  cases m <;> exact h

/-- **THE DUTY AT A LINK's TWO MOVES, FROM ONE DUTY AN ENTRY.** -/
theorem moveNum_link (v : HTailF2) (L : Link S Claim)
    (rl : List (TermedRun S (α × Option Pub9) Cb.Gl.E))
    (hp : ∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) →
      numOf v e₁ = numOf v e)
    (hq : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      numOf v e₁ = numOf v e) :
    ∀ m ∈ moves₁ L rl ++ moves₂ (α := α) L, MoveNum v m.move :=
  fun m hm => moveNum_of_keeps v m.move (moves_keepL (numOf v) L rl hp hq m hm)

/-- **THE DUTY AT A LAYERS' LINK's TWO MOVES.** -/
theorem moveNum_layers (v : HTailF2) {l : ℕ} {L : Link S Claim}
    (hL : SegAt l .layers L) {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {p : OnBytes.Desc.First.K4.Par} {nU : Array ℕ}
    {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : LayersTake L u ψ Ok Fu p nU ent tm4 t3 l3)
    (k3f : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → numOf v e₁ = numOf v e)
    (rl : List (TermedRun S (α × Option Pub9) Cb.Gl.E)) :
    ∀ m ∈ moves₁ L rl ++ moves₂ (α := α) L, MoveNum v m.move :=
  moveNum_link v L rl (run_layers (rests_num v) hL A k3f).1 (run_layers (rests_num v) hL A k3f).2

/-- **THE DUTY AT AN ATTENTION LINK's TWO MOVES.** -/
theorem moveNum_attention (v : HTailF2) {l : ℕ} {L : Link S Claim}
    (hL : SegAt l .attention L) {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)}
    {c : First.Att.P.ParC} {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : AttTake L u ψ Ok Fu rd c nU ent tm4 t3 l3)
    (k3f : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run,
      At L o run → ∀ n e c' e₁, run n e = .ok (c', e₁) → numOf v e₁ = numOf v e)
    (rl : List (TermedRun S (α × Option Pub9) Cb.Gl.E)) :
    ∀ m ∈ moves₁ L rl ++ moves₂ (α := α) L, MoveNum v m.move :=
  moveNum_link v L rl (run_attention (rests_num v) hL A k3f).1
    (run_attention (rests_num v) hL A k3f).2

/-- **THE DUTY AT THE HEAD's LINK's TWO MOVES.** -/
theorem moveNum_head (v : HTailF2) {l : ℕ} {L : Link S Claim}
    (hL : SegAt l .head L) {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {h : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ} {p : Par}
    {kap : Phi β → Option Seen} {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : HeadTake L u ψ Ok Fu h iU3 l' piece p kap nU ent tm4 t3 l3)
    (k3f : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → numOf v e₁ = numOf v e)
    (rl : List (TermedRun S (α × Option Pub9) Cb.Gl.E)) :
    ∀ m ∈ moves₁ L rl ++ moves₂ (α := α) L, MoveNum v m.move :=
  moveNum_link v L rl (run_head (rests_num v) hL A k3f).1 (run_head (rests_num v) hL A k3f).2

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rests_num
#print axioms VerifiableInference.Desc.LinkJoin.moveNum_link
#print axioms VerifiableInference.Desc.LinkJoin.moveNum_layers
#print axioms VerifiableInference.Desc.LinkJoin.moveNum_attention
#print axioms VerifiableInference.Desc.LinkJoin.moveNum_head
