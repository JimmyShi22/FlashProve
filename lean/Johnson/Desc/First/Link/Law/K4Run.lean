-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/K4Run.lean: THE BATCHING KIND's PREMISE ON A RUN OF CLAIMS, PAID AT THE
LAYERS' KIND's TWO RUNS «front» AND «back», AT THE CARRIED RECORD. Theorems, under named premises on
the letters that all kinds share.

Why. The batching kind's law (Johnson/Desc/First/Batch/Law/) asks of every run of claims `RunOk`:
the run keeps the ledger's sums, the state behind it goes on from what was fixed before the draw
(q), and the claims' values, read at any later full state, are a polynomial's terms named by q and
the data. For a run of plain claims that is `PlainOk` (PlainRuns.lean). K4's two runs are called
behind the draw and write into the ledger. This file pays `PlainOk` and `RunOk` for them, at the
typed block `blockAtC p` (Johnson/Desc/First/K4/AtC.lean).

What is said.
  `get_wrote`: what the batching's lens reads behind the writing of a run of K4's. `core_of_Core`,
    `k4_frame`: what such a run pays beside the values: the sums stay; the arrays' frame stays;
    «good»; «more»; «goes on from q».
  `valsBack`, `k4_back_plainOk`, `k4_back_runOk`: **the run «back»**: four plain claims; their
    values are those of `backForms o` in the world that the snapshot's ledger names
    (Johnson/Desc/First/Link/Law/K4Values.lean). `valsFront`, `lenFront`, `k4_front_plainOk`,
    `k4_front_runOk`: **the run «front»**.

The premises, on the shared letters φ (what of the state is fixed), Ok (what is asked of the fixed
part), Fu («full»): hπ: π reads the layers' own heard record out of φ. hkeep: a run's writing (the
ledger; the rows owed) leaves φ as it is. hOk: the snapshot's ledger has its arrays at their sizes;
every slot that a form names lies in the run's own window or is filled in the snapshot; for «front»,
the end values' slots are filled there. hFu: at a full state that goes on from q, the entries of
virtual rows that the forms name are `ent q y`: ent stands in front of the state.

Limits. AN IMPLICATION: hπ, hkeep, hOk, hFu ARE SHOWN OF NO φ, Ok, Fu: no closed choice of the
shared letters exists yet. hOk's clause on the slots is the layers' kind's own (held by
reading there; no theorem). No member; no tooth. The discipline on the exponents is not here (a run
of plain claims stands under its own numbers: `plain_inWin`). Nothing on soundness.

-/
import Johnson.Desc.First.K4.RunsAtC
import Johnson.Desc.First.Link.Law.K4Values
import Johnson.Desc.First.Batch.Law.PlainRuns
import Johnson.Desc.First.Batch.Law.FitsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K4Run
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9L
open OnBytes.Model.Layer (Own)
open OnBytes.PscRun (Later Filled Sized)
open OnBytes.Desc.First.K4 (Par blockAtC claimOf Wrote Core frontAtC backAtC frontAtC_pays
  backAtC_pays frontOf frontLen formsBack formsFrontWith formsFrontNoRows formsFront)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.K4Values (refWorld winOf backForms frontForms frontWins back_values
  front_values)

/-- What K9's lens reads behind the writing of a run of K4's. -/
theorem get_wrote (e e₁ : S) (a9 : K9.Part) (ha : atS.get? e = some a9) (a : LayOwn) (G : Fork)
    (hw : Wrote e a G e₁) :
    ∃ a₁, atS.get? e₁ = some a₁ ∧ a₁.F = G ∧ a₁.L = a9.L ∧ a₁.d.st = a9.d.st ∧ a9.F = a.F := by
  obtain ⟨h1, rfl⟩ := hw
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := e
  obtain rfl : here = .lay a := h1
  obtain rfl := Option.some.inj ha
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem core_of_Core {F G : Fork} (h : Core F G) : core G = core F := by
  simp only [core, sums, h.trees, h.LS, h.c0, h.ns, h.theta, h.nClaim, h.planClaimsF]

variable {α K : Type} [Field K] (ρ : Reading K)

/-- **What a run of K4's pays beside the values**, at the real record. -/
theorem k4_frame (φ : S → α) (Ok : α × Option Pub9 → Prop)
    (hkeep : ∀ s a G s', Wrote s a G s' → φ s' = φ s)
    (q : α × Option Pub9) (e e₁ : S) (a9 : K9.Part) (a : LayOwn) (G : Fork)
    (hf : Fx9 φ Ok q e) (hg : good9 e) (ha : atS.get? e = some a9) (hs : a9.F.LS.size = a9.F.ns)
    (hw : Wrote e a G e₁) (hc : Core a.F G) (hl : Later a.F G) :
    ∃ a₁, atS.get? e₁ = some a₁ ∧ a₁.F = G ∧ a9.F = a.F ∧ core a₁.F = core a9.F ∧
      treesFrame a₁.F.trees = treesFrame a9.F.trees ∧ good9 e₁ ∧ more9 φ e e₁ ∧ Fx9 φ Ok q e₁ := by
  obtain ⟨a₁, ha₁, f1, f2, f3, f4⟩ := get_wrote e e₁ a9 ha a G hw
  have hgo : GoesOn (pubOf a9) a₁ :=
    ⟨by rw [f1]; show Later a9.F G; rw [f4]; exact hl,
      by rw [f1, hc.planClaimsF]; show _ = a9.F.planClaimsF; rw [f4],
      by rw [f1, hc.trees]; show _ = a9.F.trees.map LinkJoin.look; rw [f4],
      by rw [f2]; rfl, by rw [f2]; rfl, f3⟩
  have hmore : more9 φ e e₁ := ⟨hkeep e a G e₁ hw, fun a' ha' => by
    have ea : a' = a9 := Option.some.inj (ha'.symm.trans ha)
    rw [ea]
    exact ⟨a₁, ha₁, hgo⟩⟩
  obtain ⟨a0, ha0, g1, _⟩ := hg
  have ea0 : a0 = a9 := Option.some.inj (ha0.symm.trans ha)
  subst ea0
  refine ⟨a₁, ha₁, f1, f4, by rw [f1, f4]; exact core_of_Core hc, by rw [f1, hc.trees, f4],
    ⟨a₁, ha₁, by rw [f2]; exact g1, by rw [f1, hc.LS, hc.ns, ← f4]; exact hs⟩, hmore,
    fx_of_more φ Ok q e _ hf hmore⟩

/-! ## The run "back" -/

/-- The values of the run "back": of what was heard (π of the fixed part's first half), the
snapshot's ledger, the entries as given, and the data. -/
def valsBack (π : α → Option Own) (ent : α × Option Pub9 → Bound K → ℕ → ℕ → ℕ → K)
    (q : α × Option Pub9) (y : Bound K) : List K :=
  match π q.1, q.2 with
  | some o, some u =>
    (backForms o).map fun f => f.value ρ (refWorld ρ u.F [winOf o.wo.toWsMerged.p] (ent q y) y)
  | _, _ => []

/-- **PlainOk OF K4's RUN "back", AT THE REAL RECORD.** -/
theorem k4_back_plainOk (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p : Par)
    (run : Nat → S → Except String (List Claim × S))
    (hr : (blockAtC p).claims.lookup "back" = some run) (π : α → Option Own)
    (hπ : ∀ s a, s.here = .lay a → π (φ s) = a.own)
    (hkeep : ∀ s a G s', Wrote s a G s' → φ s' = φ s)
    (hOk : ∀ q o u, Ok q → π q.1 = some o → q.2 = some u → Sized u.F ∧
      ∀ f ∈ backForms o, ∀ x ∈ f.slots.toList,
        K4Values.InWin (winOf o.wo.toWsMerged.p) x.1 ∨ Filled u.F x.1)
    (ent : α × Option Pub9 → Bound K → ℕ → ℕ → ℕ → K)
    (hFu : ∀ q o t b y, Fx9 φ Ok q t → Fu t → atS.get? t = some b → π q.1 = some o →
      ∀ f ∈ backForms o, ∀ x ∈ f.ents.toList,
        (worldAt ρ b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx) :
    PlainOk ρ atS (O9 φ Ok Fu) (Fx9 φ Ok) run (valsBack ρ π ent) (fun _ => 4) := by
  intro q front e a9 c e₁ hf hg ha hs hrun
  obtain ⟨a, o, fs, G, ho, hfb, rfl, hw⟩ := backAtC hr hrun
  obtain ⟨a', o', G', ho', hw', hc, hl, hlen⟩ := backAtC_pays hr hrun
  obtain rfl : a = a' := by
    have := hw.1.symm.trans hw'.1
    injection this
  obtain rfl : G = G' := by
    have h2 := hw.2.symm.trans hw'.2
    have h3 := congrArg (fun s : S => s.fork?) h2
    exact Option.some.inj h3
  obtain ⟨a₁, ha₁, f1, f4, k1, k2, k3, k4, k5⟩ :=
    k4_frame φ Ok hkeep q e e₁ a9 a G hf hg ha hs hw hc hl
  refine ⟨a₁, ha₁, k1, k2, k3, k4, k5, hlen, fun x hx => ?_,
    fun t b y ht hfull hb => ?_⟩
  · obtain ⟨f, _, rfl⟩ := List.mem_map.1 hx
    rfl
  · have hq1 : π q.1 = some o := by rw [← hf.2.1, hπ e a hw.1, ho]
    obtain ⟨hok, _, u, b0, hu, hb0, gu⟩ := hf
    obtain rfl : a9 = b0 := Option.some.inj (ha.symm.trans hb0)
    obtain ⟨hsz, hsl⟩ := hOk q o u hok hq1 hu
    obtain ⟨b', hb', gb⟩ := ht.2.1.2 a₁ ha₁
    obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
    have hUF : Later u.F a.F := by rw [← f4]; exact gu.1
    have hGB : Later G b.F := by
      have := gb.1
      rwa [show (pubOf a₁).F = G from f1] at this
    have hfx : Fx9 φ Ok q t := fx_of_more φ Ok q e₁ t k5 ht.2.1
    simp only [valsBack, hq1, hu]
    exact back_values ρ b.L (ent q y) y hfb (hUF.sized hsz) hUF hGB hsl
      (hFu q o t b y hfx hfull hb hq1)

/-- **RunOk OF K4's RUN "back".** -/
theorem k4_back_runOk (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p : Par)
    (run : Nat → S → Except String (List Claim × S))
    (hr : (blockAtC p).claims.lookup "back" = some run) (π : α → Option Own)
    (hπ : ∀ s a, s.here = .lay a → π (φ s) = a.own)
    (hkeep : ∀ s a G s', Wrote s a G s' → φ s' = φ s)
    (hOk : ∀ q o u, Ok q → π q.1 = some o → q.2 = some u → Sized u.F ∧
      ∀ f ∈ backForms o, ∀ x ∈ f.slots.toList,
        K4Values.InWin (winOf o.wo.toWsMerged.p) x.1 ∨ Filled u.F x.1)
    (ent : α × Option Pub9 → Bound K → ℕ → ℕ → ℕ → K)
    (hFu : ∀ q o t b y, Fx9 φ Ok q t → Fu t → atS.get? t = some b → π q.1 = some o →
      ∀ f ∈ backForms o, ∀ x ∈ f.ents.toList,
        (worldAt ρ b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx) :
    RunOk ρ atS (O9 φ Ok Fu) (Fx9 φ Ok) run (plainTm (valsBack ρ π ent)) (fun _ => 4) :=
  runOk_of_plain ρ atS (O9 φ Ok Fu) (Fx9 φ Ok) run _ _ (part_of_more φ)
    (k4_back_plainOk ρ φ Ok Fu p run hr π hπ hkeep hOk ent hFu)

/-! ## The run "front" -/

/-- The plain function of the run "front" is `formsFrontWith` at "the lookup does not state its own
claims". -/
theorem frontOf_eq (p : Par) : frontOf p = formsFrontWith (!p.k3Runs) p.P p.g := by
  unfold frontOf
  cases p.k3Runs <;> rfl

/-- The values of the run "front". -/
def valsFront (p : Par) (π : α → Option Own) (ent : α × Option Pub9 → Bound K → ℕ → ℕ → ℕ → K)
    (q : α × Option Pub9) (y : Bound K) : List K :=
  match π q.1, q.2 with
  | some o, some u =>
    match frontForms (!p.k3Runs) p.P p.g o u.F with
    | some l => l.map fun f => f.value ρ (refWorld ρ u.F (frontWins o) (ent q y) y)
    | none => []
  | _, _ => []

/-- How many claims it makes. -/
def lenFront (p : Par) (π : α → Option Own) (q : α × Option Pub9) : ℕ :=
  match π q.1 with
  | some o => frontLen (!p.k3Runs) p.g o
  | none => 0

/-- **PlainOk OF K4's RUN "front", AT THE REAL RECORD.** -/
theorem k4_front_plainOk (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p : Par)
    (run : Nat → S → Except String (List Claim × S))
    (hr : (blockAtC p).claims.lookup "front" = some run) (π : α → Option Own)
    (hπ : ∀ s a, s.here = .lay a → π (φ s) = a.own)
    (hkeep : ∀ s a G s', Wrote s a G s' → φ s' = φ s)
    (hOk : ∀ q o u, Ok q → π q.1 = some o → q.2 = some u → Sized u.F ∧
      (∀ i, i < 4 * p.P.y.NI → Filled u.F (o.H.tV.sEnd + i)) ∧
      ∀ l, frontForms (!p.k3Runs) p.P p.g o u.F = some l → ∀ f ∈ l, ∀ x ∈ f.slots.toList,
        (∃ w ∈ frontWins o, K4Values.InWin w x.1) ∨ Filled u.F x.1)
    (ent : α × Option Pub9 → Bound K → ℕ → ℕ → ℕ → K)
    (hFu : ∀ q o u t b y, Fx9 φ Ok q t → Fu t → atS.get? t = some b → π q.1 = some o →
      q.2 = some u → ∀ l, frontForms (!p.k3Runs) p.P p.g o u.F = some l → ∀ f ∈ l,
      ∀ x ∈ f.ents.toList,
        (worldAt ρ b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx) :
    PlainOk ρ atS (O9 φ Ok Fu) (Fx9 φ Ok) run (valsFront ρ p π ent) (lenFront p π) := by
  intro q front e a9 c e₁ hf hg ha hs hrun
  obtain ⟨a, o, fs, G, ho, hfb, rfl, hw⟩ := frontAtC hr hrun
  obtain ⟨a', o', G', ho', hw', hc, hl, hlen⟩ := frontAtC_pays hr hrun
  obtain rfl : a = a' := by
    have := hw.1.symm.trans hw'.1
    injection this
  obtain rfl : o = o' := Option.some.inj (ho.symm.trans ho')
  obtain rfl : G = G' := by
    have h2 := hw.2.symm.trans hw'.2
    have h3 := congrArg (fun s : S => s.fork?) h2
    exact Option.some.inj h3
  obtain ⟨a₁, ha₁, f1, f4, k1, k2, k3, k4, k5⟩ :=
    k4_frame φ Ok hkeep q e e₁ a9 a G hf hg ha hs hw hc hl
  have hq1 : π q.1 = some o := by rw [← hf.2.1, hπ e a hw.1, ho]
  refine ⟨a₁, ha₁, k1, k2, k3, k4, k5, by
    rw [hlen]
    simp only [lenFront, hq1], fun x hx => ?_, fun t b y ht hfull hb => ?_⟩
  · obtain ⟨f, _, rfl⟩ := List.mem_map.1 hx
    rfl
  · obtain ⟨hok, _, u, b0, hu, hb0, gu⟩ := hf
    obtain rfl : a9 = b0 := Option.some.inj (ha.symm.trans hb0)
    obtain ⟨hsz, hsh, hsl⟩ := hOk q o u hok hq1 hu
    obtain ⟨b', hb', gb⟩ := ht.2.1.2 a₁ ha₁
    obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
    have hUF : Later u.F a.F := by rw [← f4]; exact gu.1
    have hGB : Later G b.F := by
      have := gb.1
      rwa [show (pubOf a₁).F = G from f1] at this
    have hfx : Fx9 φ Ok q t := fx_of_more φ Ok q e₁ t k5 ht.2.1
    rw [frontOf_eq] at hfb
    obtain ⟨l, hl', hv⟩ := front_values ρ b.L (ent q y) y hfb (hUF.sized hsz) hUF hGB hsh hsl
      (hFu q o u t b y hfx hfull hb hq1 hu)
    simp only [valsFront, hq1, hu, hl']
    exact hv

/-- **RunOk OF K4's RUN "front".** -/
theorem k4_front_runOk (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p : Par)
    (run : Nat → S → Except String (List Claim × S))
    (hr : (blockAtC p).claims.lookup "front" = some run) (π : α → Option Own)
    (hπ : ∀ s a, s.here = .lay a → π (φ s) = a.own)
    (hkeep : ∀ s a G s', Wrote s a G s' → φ s' = φ s)
    (hOk : ∀ q o u, Ok q → π q.1 = some o → q.2 = some u → Sized u.F ∧
      (∀ i, i < 4 * p.P.y.NI → Filled u.F (o.H.tV.sEnd + i)) ∧
      ∀ l, frontForms (!p.k3Runs) p.P p.g o u.F = some l → ∀ f ∈ l, ∀ x ∈ f.slots.toList,
        (∃ w ∈ frontWins o, K4Values.InWin w x.1) ∨ Filled u.F x.1)
    (ent : α × Option Pub9 → Bound K → ℕ → ℕ → ℕ → K)
    (hFu : ∀ q o u t b y, Fx9 φ Ok q t → Fu t → atS.get? t = some b → π q.1 = some o →
      q.2 = some u → ∀ l, frontForms (!p.k3Runs) p.P p.g o u.F = some l → ∀ f ∈ l,
      ∀ x ∈ f.ents.toList,
        (worldAt ρ b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx) :
    RunOk ρ atS (O9 φ Ok Fu) (Fx9 φ Ok) run (plainTm (valsFront ρ p π ent)) (lenFront p π) :=
  runOk_of_plain ρ atS (O9 φ Ok Fu) (Fx9 φ Ok) run _ _ (part_of_more φ)
    (k4_front_plainOk ρ φ Ok Fu p run hr π hπ hkeep hOk ent hFu)

end VerifiableInference.Desc.K4Run

#print axioms VerifiableInference.Desc.K4Run.get_wrote
#print axioms VerifiableInference.Desc.K4Run.k4_frame
#print axioms VerifiableInference.Desc.K4Run.k4_back_plainOk
#print axioms VerifiableInference.Desc.K4Run.k4_front_plainOk
#print axioms VerifiableInference.Desc.K4Run.core_of_Core
#print axioms VerifiableInference.Desc.K4Run.frontOf_eq
#print axioms VerifiableInference.Desc.K4Run.k4_back_runOk
#print axioms VerifiableInference.Desc.K4Run.k4_front_runOk
