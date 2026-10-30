-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/K11Run.lean: THE BATCHING KIND's PREMISE ON A RUN OF CLAIMS, PAID AT THE
MERGE's KIND's RUN «the merge» (`headMergeClaim`, Johnson/Desc/First/Fork/MergeKind.lean), AT THE
CARRIED RECORD. Theorems, under named premises on the letters that all kinds share.

Why. As Johnson/Desc/First/Link/Law/K4Run.lean. The run is called behind the batching's draw, in the
head's segment. It makes one plain claim, the one that the merge's sumcheck leaves, and lays that
sumcheck's hiding coefficients (shown 0, factor −1) under a window of free slots (`claim_inv`,
Johnson/Top/H0/MergeLaw/Run.lean).

What is said.
  `get_head`: what the batching's lens reads behind the run's writing. `valsMerge`, `k11_plainOk`,
    `k11_runOk`: **`PlainOk` and `RunOk` of the run**: one claim; its value is that of `wo.p.rowForm
    wo.fvp {}` in the world that the snapshot's ledger names
    (Johnson/Desc/First/Link/Law/K4Values.lean), wo: what the merge has left in the record.

The premises, on the shared letters: hπ: π reads what the merge has left out of φ. hkeep: the run's
writing (the head's ledger alone) leaves φ as it is. hOk: the snapshot's ledger has its arrays at
their sizes; every slot that the form names lies in the sumcheck's own window or is filled in the
snapshot. hFu: at a full state that goes on from q the entries of virtual rows that the form names
are `ent q y`.

Limits. AN IMPLICATION: the four premises are shown of no φ, Ok, Fu. No member; no tooth. Nothing on
soundness.

-/
import Johnson.Top.H0.MergeLaw.Run
import Johnson.Desc.First.Link.Law.K4Values
import Johnson.Desc.First.Batch.Law.PlainRuns
import Johnson.Desc.First.Batch.Law.FitsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K11Run
open OnBytes OnBytes.Model
open OnBytes.PscRun (Later Filled Sized Same hideRun_ok hideRun_keeps)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.MergeLaw (claim_inv)
open Johnson.Desc.First.ForkMerge (headMergeClaim)
open VerifiableInference.Desc.K4Values (refWorld winOf values_ref laid_of_run)

/-- What K9's lens reads behind the run's writing. -/
theorem get_head (e : S) (a9 : K9.Part) (ha : atS.get? e = some a9) (a : HeadOwn)
    (h1 : e.here = .head a) (G : Fork) :
    ∃ a₁, atS.get? { e with here := .head { a with F := G } } = some a₁ ∧ a₁.F = G ∧
      a₁.L = a9.L ∧ a₁.d.st = a9.d.st ∧ a9.F = a.F := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := e
  obtain rfl : here = .head a := h1
  by_cases ho : a.opened = true
  · cases hs : a.slot with
    | none => simp [atS, S.link?, S.fork?, S.tl?, K9.usedOf, ho, hs] at ha
    | some n =>
      simp only [atS, S.link?, S.fork?, S.tl?, K9.usedOf, ho, hs, if_true, Option.bind_eq_bind,
        Option.bind_some, Option.pure_def, Option.some.injEq] at ha
      subst ha
      simp [atS, S.link?, S.fork?, S.tl?, K9.usedOf, ho]
  · simp [atS, S.link?, ho] at ha

/-- A ledger that differs at most in what lies under the slots has the same sums. (So
`K9L.core_of_same`, which stands in a file of members: Batch/Law/MemberLate.lean.) -/
theorem core_same {F G : Fork} (h : Same F G) : core G = core F := by
  unfold Same at h
  rw [h]
  rfl

variable {α K : Type} [Field K] (ρ : Reading K)

/-- The value of the run's one claim. -/
def valsMerge (π : α → Option WsForkOut) (ent : α × Option Pub9 → Bound K → ℕ → ℕ → ℕ → K)
    (q : α × Option Pub9) (y : Bound K) : List K :=
  match π q.1, q.2 with
  | some wo, some u =>
    [(wo.p.rowForm wo.fvp {}).value ρ (refWorld ρ u.F [winOf wo.p] (ent q y) y)]
  | _, _ => []

/-- **PlainOk OF K11's RUN "the merge", AT THE REAL RECORD.** -/
theorem k11_plainOk (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)
    (π : α → Option WsForkOut)
    (hπ : ∀ s a, s.here = .head a → π (φ s) = a.wo)
    (hkeep : ∀ (s : S) (a : HeadOwn) (G : Fork), s.here = .head a →
      φ { s with here := .head { a with F := G } } = φ s)
    (hOk : ∀ q wo u, Ok q → π q.1 = some wo → q.2 = some u → Sized u.F ∧
      ∀ x ∈ (wo.p.rowForm wo.fvp {}).slots.toList,
        K4Values.InWin (winOf wo.p) x.1 ∨ Filled u.F x.1)
    (ent : α × Option Pub9 → Bound K → ℕ → ℕ → ℕ → K)
    (hFu : ∀ q wo t b y, Fx9 φ Ok q t → Fu t → atS.get? t = some b → π q.1 = some wo →
      ∀ x ∈ (wo.p.rowForm wo.fvp {}).ents.toList,
        (worldAt ρ b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx) :
    PlainOk ρ atS (O9 φ Ok Fu) (Fx9 φ Ok) headMergeClaim (valsMerge ρ π ent) (fun _ => 1) := by
  intro q front e a9 c e₁ hf hg ha hs hrun
  obtain ⟨a, wo, G, h1, hwo, rfl, rfl, hrunG⟩ := claim_inv hrun
  obtain ⟨a₁, ha₁, f1, f2, f3, f4⟩ := get_head e a9 ha a h1 G
  have hq1 : π q.1 = some wo := by rw [← hf.2.1, hπ e a h1, hwo]
  have hf0 := hf
  obtain ⟨hok, _, u, b0, hu, hb0, gu⟩ := hf
  obtain rfl : a9 = b0 := Option.some.inj (ha.symm.trans hb0)
  obtain ⟨hsz, hsl⟩ := hOk q wo u hok hq1 hu
  have hUF : Later u.F a.F := by rw [← f4]; exact gu.1
  have hFs : Sized a.F := hUF.sized hsz
  obtain ⟨hsame, _, _, _⟩ := hideRun_ok a.F G _ _ _ hFs hrunG
  have hl : Later a.F G := hideRun_keeps hrunG
  have htr : G.trees = a.F.trees := by
    unfold Same at hsame
    rw [hsame]
  have hpl : G.planClaimsF = a.F.planClaimsF := by
    unfold Same at hsame
    rw [hsame]
  have hLS : G.LS = a.F.LS ∧ G.ns = a.F.ns := by
    unfold Same at hsame
    constructor <;> rw [hsame]
  have hgo : GoesOn (pubOf a9) a₁ :=
    ⟨by rw [f1]; show Later a9.F G; rw [f4]; exact hl,
      by rw [f1, hpl]; show _ = a9.F.planClaimsF; rw [f4],
      by rw [f1, htr]; show _ = a9.F.trees.map LinkJoin.look; rw [f4],
      by rw [f2]; rfl, by rw [f2]; rfl, f3⟩
  have hmore : more9 φ e { e with here := .head { a with F := G } } :=
    ⟨hkeep e a G h1, fun a' ha' => by
      have ea : a' = a9 := Option.some.inj (ha'.symm.trans ha)
      rw [ea]
      exact ⟨a₁, ha₁, hgo⟩⟩
  obtain ⟨a0, ha0, g1, _⟩ := hg
  obtain rfl : a9 = a0 := Option.some.inj (ha.symm.trans ha0)
  have hfx1 := fx_of_more φ Ok q e _ hf0 hmore
  refine ⟨a₁, ha₁, by rw [f1, f4]; exact core_same hsame, by rw [f1, htr, f4],
    ⟨a₁, ha₁, by rw [f2]; exact g1, by rw [f1, hLS.1, hLS.2, ← f4]; exact hs⟩, hmore, hfx1, rfl,
    fun x hx => ?_, fun t b y ht hfull hb => ?_⟩
  · obtain rfl := List.mem_singleton.1 hx
    rfl
  · obtain ⟨b', hb', gb⟩ := ht.2.1.2 a₁ ha₁
    obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
    have hGB : Later G b.F := by
      have := gb.1
      rwa [show (pubOf a₁).F = G from f1] at this
    have hfx : Fx9 φ Ok q t := fx_of_more φ Ok q _ t hfx1 ht.2.1
    simp only [valsMerge, hq1, hu]
    exact values_ref ρ [wo.p.rowForm wo.fvp {}] b.L u.F b.F [winOf wo.p] (ent q y) y
      (hUF.trans (hl.trans hGB))
      (fun w hw => by
        obtain rfl := List.mem_singleton.1 hw
        exact laid_of_run hFs hrunG hGB)
      (fun f hf' x hx => by
        obtain rfl := List.mem_singleton.1 hf'
        exact (hsl x hx).imp (fun k => ⟨_, List.mem_singleton.2 rfl, k⟩) id)
      (fun f hf' x hx => by
        obtain rfl := List.mem_singleton.1 hf'
        exact hFu q wo t b y hfx hfull hb hq1 x hx)

/-- **RunOk OF K11's RUN "the merge".** -/
theorem k11_runOk (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)
    (π : α → Option WsForkOut)
    (hπ : ∀ s a, s.here = .head a → π (φ s) = a.wo)
    (hkeep : ∀ (s : S) (a : HeadOwn) (G : Fork), s.here = .head a →
      φ { s with here := .head { a with F := G } } = φ s)
    (hOk : ∀ q wo u, Ok q → π q.1 = some wo → q.2 = some u → Sized u.F ∧
      ∀ x ∈ (wo.p.rowForm wo.fvp {}).slots.toList,
        K4Values.InWin (winOf wo.p) x.1 ∨ Filled u.F x.1)
    (ent : α × Option Pub9 → Bound K → ℕ → ℕ → ℕ → K)
    (hFu : ∀ q wo t b y, Fx9 φ Ok q t → Fu t → atS.get? t = some b → π q.1 = some wo →
      ∀ x ∈ (wo.p.rowForm wo.fvp {}).ents.toList,
        (worldAt ρ b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx) :
    RunOk ρ atS (O9 φ Ok Fu) (Fx9 φ Ok) headMergeClaim (plainTm (valsMerge ρ π ent))
      (fun _ => 1) :=
  runOk_of_plain ρ atS (O9 φ Ok Fu) (Fx9 φ Ok) headMergeClaim _ _ (part_of_more φ)
    (k11_plainOk ρ φ Ok Fu π hπ hkeep hOk ent hFu)

end VerifiableInference.Desc.K11Run

#print axioms VerifiableInference.Desc.K11Run.get_head
#print axioms VerifiableInference.Desc.K11Run.core_same
#print axioms VerifiableInference.Desc.K11Run.k11_plainOk
#print axioms VerifiableInference.Desc.K11Run.k11_runOk
