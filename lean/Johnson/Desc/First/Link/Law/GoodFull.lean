-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/GoodFull.lean: `OwesFull.hend` (LinkOwes.lean): BEHIND THE LAST MOVE OF
A LINK's TWO ROWS THE STATE IS GOOD AND FULL, WITH «FULL» CLOSED: `FullAt nU t` := t STANDS BEHIND A
YES OF THE SMALLNESS TEST's RUN OF SELF TESTS. Theorems on the moves, at the first chain's record.

Why. The batching kind's law reads the claims' values at a «full» state: one behind which no weight
of a virtual row turns. `Fu` was a letter. The last run of every sort of link's order behind the
batching is «K8.tests»: it lays the weights and tests them. So «behind its yes» is what a full state
is; whatever the kinds' laws take of a full state is then a sentence on a yes of that one run.

What is said.
  `FullAt nU t`. `good_ledger`: «good» (a part is there; the draw has run; a coefficient for each
    slot) passes to a record whose part has the same link's record and a ledger with the same
    coefficients and number of slots. `rests_good`: **«good in front gives good behind» at a yes of
    each of the nine known runs** (RunRel.lean). `good_add`: and over the adding. `ran_last`: the
    record behind a chain of yeses stands behind a yes of the last entry's run. `hend_of`: **`hend`
    at `Fu := FullAt nU`**, from: every run of both orders keeps «good»; the order behind the
    batching ends in an entry whose run stands under the run of self tests.

Limits. `hend` alone. WHAT THE KINDS' LAWS TAKE OF A FULL STATE (the ten fields on Fu of the three
Takes) IS NOT PAID HERE: at `FullAt` each becomes a sentence on the ledger that the run of self
tests leaves. The runs' duty is a premise: RunRel.lean pays it at each sort from `rests_good`, the
lookup's runs' share aside. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.RunRel
import Johnson.Desc.First.Link.Law.LaidAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Wrote Core frontAtC_pays backAtC_pays hideRun_core paid_core)
open VerifiableInference.Desc.First.MergeLaw (claim_inv)
open VerifiableInference.Desc.First.TailClaims.Law (eq_side)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K4Run
open VerifiableInference.Desc.K11Run (get_head)
open VerifiableInference.Desc.Kinds.Head.Law (join_hands)
open VerifiableInference.Desc.JoinAtBlocks

/-- **A full state: it stands behind a yes of the smallness test's run of self tests.** -/
def FullAt (nU : Array ℕ) (t : S) : Prop := ∃ e, k8Tests nU e = .ok t

/-- «Good» passes to a record whose part has the same link's record and a ledger with the same
coefficients and number of slots. -/
theorem good_ledger {e e₁ : S} {a a₁ : K9.Part} (ha : atS.get? e = some a)
    (ha₁ : atS.get? e₁ = some a₁) (hL : a₁.L = a.L) (hS : a₁.F.LS = a.F.LS)
    (hn : a₁.F.ns = a.F.ns) (hg : good9 e) : good9 e₁ := by
  obtain ⟨a0, ha0, g1, g2⟩ := hg
  obtain rfl : a0 = a := Option.some.inj (ha0.symm.trans ha)
  exact ⟨a₁, ha₁, by rw [hL]; exact g1, by rw [hS, hn]; exact g2⟩

/-- What a run of the layers' own kind writes, with the ledger's core kept. -/
theorem good_wrote {e e₁ : S} {a : First.LayOwn} {G : Fork} (hw : Wrote e a G e₁)
    (hc : Core a.F G) (hg : good9 e) : good9 e₁ := by
  have ⟨a9, ha, _⟩ := hg
  obtain ⟨a₁, ha₁, f1, f2, _, f4⟩ := get_wrote e e₁ a9 ha a G hw
  exact good_ledger ha ha₁ f2 (by rw [f1, f4]; exact hc.LS) (by rw [f1, f4]; exact hc.ns) hg

/-- A writing of the head's ledger, with the ledger's core kept. -/
theorem good_head {e : S} {a : First.HeadOwn} {G : Fork} (h1 : e.here = .head a)
    (hc : Core a.F G) (hg : good9 e) : good9 { e with here := .head { a with F := G } } := by
  have ⟨a9, ha, _⟩ := hg
  obtain ⟨a₁, ha₁, f1, f2, _, f4⟩ := get_head e a9 ha a h1 G
  exact good_ledger ha ha₁ f2 (by rw [f1, f4]; exact hc.LS) (by rw [f1, f4]; exact hc.ns) hg

/-- **«Good in front gives good behind» at a yes of each of the nine known runs.** -/
theorem rests_good : RunRests fun e e₁ => good9 e → good9 e₁ where
  refl _ := id
  front p r h0 n e c e₁ hr := by
    obtain ⟨a, _, G, _, hw, hc, _, _⟩ := frontAtC_pays h0 hr
    exact good_wrote hw hc
  back p r h0 n e c e₁ hr := by
    obtain ⟨a, _, G, _, hw, hc, _, _⟩ := backAtC_pays h0 hr
    exact good_wrote hw hc
  free p r h0 e e₁ hr := by
    obtain ⟨a, hw⟩ := k4_freeSlot_wrote h0 hr
    exact good_wrote hw (Core.refl _)
  merge n e c e₁ hr := by
    obtain ⟨a, wo, G, h1, _, rfl, _, hrunG⟩ := claim_inv hr
    exact good_head h1 (hideRun_core hrunG)
  join h iU3 p n e c e₁ hr := by
    obtain ⟨a, i, h1, rfl⟩ := join_hands h iU3 p n e c e₁ hr
    exact good_head h1 (paid_core _ _)
  eq n e c e₁ hr hg := by
    obtain ⟨F, tl, funs, tl', F1, hF, _, _, he, rfl⟩ := k8Run_ok n e e₁ c hr
    have ⟨a9, ha, _⟩ := hg
    obtain ⟨a₁, ha₁, f1, f2, _, _, _, hF'⟩ := get_put e a9 ha tl' F1
    obtain rfl : F = a9.F := Option.some.inj (hF.symm.trans hF')
    exact good_ledger ha ha₁ f2 (by rw [f1]; exact (eq_side he).LS)
      (by rw [f1]; exact (eq_side he).ns) hg
  ls e e₁ hr hg := by
    obtain ⟨F, tl, _, _, rfl⟩ := k8LsTail_ok e e₁ hr
    have ⟨a9, ha, _⟩ := hg
    obtain ⟨a₁, ha₁, f1, f2, _⟩ := get_putTl e a9 ha _
    exact good_ledger ha ha₁ f2 (by rw [f1]) (by rw [f1]) hg
  tests nU e e₁ hr hg := by
    obtain ⟨F, tl, g, hF, _, _, _, _, rfl⟩ := k8Tests_ok nU e e₁ hr
    have ⟨a9, ha, _⟩ := hg
    obtain ⟨a₁, ha₁, f1, f2, _, _, _, hF'⟩ := get_put e a9 ha tl _
    obtain rfl : F = a9.F := Option.some.inj (hF.symm.trans hF')
    exact good_ledger ha ha₁ f2 (by rw [f1]; exact (coef_side tl g _).2.2.2.2.2.1)
      (by rw [f1]; exact (coef_side tl g _).2.1) hg

/-- «Good» over the adding. -/
theorem good_add (e : S) (b : K9.Part) (G : Fork) (c : List Claim) (hb : atS.get? e = some b)
    (hG : addAll b.F c = some G) (hg : good9 e) : good9 (atS.set e { b with F := G }) := by
  obtain ⟨b0, hb0, g1, g2⟩ := hg
  obtain rfl : b0 = b := Option.some.inj (hb0.symm.trans hb)
  obtain ⟨_, _, e2, _⟩ := addAll_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ c b0.F G g2 hG
  obtain ⟨b', hb', k1, k2, _⟩ := atS_reads e { b0 with F := G } (by rw [hb]; rfl)
  exact ⟨b', hb', by rw [k2]; exact g1, by rw [k1]; exact e2⟩

/-- The record behind a chain of yeses stands behind a yes of the last entry's run. -/
theorem ran_last (bs : List (Block S Claim)) (o : ℕ × String) :
    ∀ (pre : List (ℕ × String)) (e e₁ : S), Ran bs (pre ++ [o]) e e₁ →
      ∃ run x, ((bs[o.1]?).bind fun b => b.after.lookup o.2) = some run ∧ run x = .ok e₁
  | [], e, e₁, h => by
    cases h with
    | cons _ _ run _ e' _ hl hr ht =>
      cases ht
      exact ⟨run, e, hl, hr⟩
  | _ :: pre, e, e₁, h => by
    cases h with
    | cons _ _ run _ e' _ hl hr ht => exact ran_last bs o pre e' e₁ ht

variable {α : Type}

/-- **hend, AT Fu := FullAt nU.** -/
theorem hend_of (L : Link S Claim) (nU : Array ℕ)
    (rl : List (TermedRun S (α × Option Pub9) Cb.Gl.E))
    (hp : ∀ o ∈ L.order, ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) →
      good9 e → good9 e₁)
    (hq : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      good9 e → good9 e₁)
    (pre : List (ℕ × String)) (oT : ℕ × String) (hord : L.orderAfter = pre ++ [oT])
    (hT : ∀ run, AtAfter L oT run → UnderAfter run (k8Tests nU)) :
    ∀ s s' cls, good9 s →
      MovesYes atS ((moves₁ L rl ++ moves₂ (α := α) L).map (·.move)) s s' cls →
      good9 s' ∧ FullAt nU s' := by
  intro s s' cls hg hy
  obtain ⟨u, c, c', ⟨e, q, G, hgat, hqe, hG, rfl⟩, ⟨u', c₂, c₃, ⟨hrun, _⟩, ⟨rfl, _⟩, _⟩, _⟩ := hy
  have hran := afterIn_ran L.hear L.orderAfter _ _ (Link.afterIn_of_runBehind hrun)
  have g1 : good9 e := gather_holds good9 (fun _ => []) [] (runsIn L.hear L.order)
    (fun r' hr' => by
      obtain ⟨o', ho', e'⟩ := List.mem_filterMap.1 hr'
      obtain ⟨run, hrun', rfl⟩ := Option.map_eq_some_iff.1 e'
      exact hp o' ho' run hrun') ([], s) (c, e)
    (fold_gstep L.each L.hear L.order ([], s) (c, e) hgat) hg
  have g2 := good_add e q G c hqe hG g1
  refine ⟨ran_holds good9 L.hear L.orderAfter _ _ hran hq g2, ?_⟩
  rw [hord] at hran
  obtain ⟨run, x, hl, hx⟩ := ran_last L.hear oT pre _ _ hran
  exact ⟨x, hT run hl x _ hx⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rests_good
#print axioms VerifiableInference.Desc.LinkJoin.good_add
#print axioms VerifiableInference.Desc.LinkJoin.ran_last
#print axioms VerifiableInference.Desc.LinkJoin.hend_of
