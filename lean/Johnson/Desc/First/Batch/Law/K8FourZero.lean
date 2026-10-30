-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Law/K8FourZero.lean
(kind K9's soundness lemma; toward the two items of the sort "worth" that the batching's row
closes): THEOREM: WHERE THE FOUR VALUES THAT THE LAW's TERMS NAME (vals4, Law/K8Four.lean) ARE 0,
THE FIRST FOUR CLAIMS OF THE APPROXIMATE RANGE PROOF's RUN "K8.equations" ARE WORTH 0 IN THE
BATCHING's OWN WORLD AT EVERY LATER FULL STATE, IN THE BATCHING's OWN MEASURE.
Why. The batching's law hands out, in front: every term's coefficient is 0; at this run's first four
terms these coefficients are vals4: values in the world that the ledger IN FRONT OF THE DRAW names.
The exchange of the four claims for what the lookup on the digits puts out
(k3Out_at_world, Johnson/Desc/First/K8/Four/AtWorld.lean) asks: the first four claims of the run's
list are worth 0 in `worldAt` at the ledger in which the rows' weights are laid, by `claimValue`.
This file passes from the one to the other.
  four_values_full   the four claims' values at a later full state ARE vals4, one by one.
  four_zero_full     **so where vals4 is 0 throughout, each of the four is worth 0 there.**
  four_zero_coefAll  the same where "full" is "behind a yes of the run of self tests": the ledger is
                the library's coefAll tlX g Fc: THE PREMISE hz OF k3Out_at_world, TO THE LETTER.
THE HYPOTHESES: those of k8_four (Law/K8Four.lean): h-pi, hkeep, hOk4, hFu4 (the entries' half:
taken as given there and here).
Not claimed: the exchange itself; its other premises; that any state is full. Nothing on soundness.

-/
import Johnson.Desc.First.Batch.Law.K8Four
import Johnson.Desc.First.Batch.Law.K8CoefAll
import Johnson.Desc.First.Batch.BlindK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.PscRun (Later Sized Filled paid_later)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.K4Values (refWorld winOf LaidAt laid_of_run)

variable {α : Type}

/-- **The four claims' values at a later full state are the law's four values.** -/
theorem four_values_full (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (u : HTailF2)
    (π : α → Option HTailF2 × Option (Array HFun))
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?))
    (hkeep : ∀ s tl tl' F1, s.tl? = some tl → blank u tl' = blank u tl →
      φ ((s.putTl tl').putFork F1) = φ s)
    (ent : α × Option Pub9 → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (hOk4 : ∀ q v tlb g, Ok q → q.2 = some v → (π q.1).1 = some tlb → tlb.heard = some g →
      Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g.leaves) x.1 ∨ Filled v.F x.1)
    (hFu4 : ∀ q t b y tlb g, Fx9 φ Ok q t → Fu t → atS.get? t = some b →
      (π q.1).1 = some tlb → tlb.heard = some g → ∀ cl ∈ four8 tlb g,
      (∀ x ∈ cl.form.ents.toList, (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx =
        ent q y x.tree x.row x.idx) ∧
      ∀ r ∈ cl.runs.toList, ∀ i < r.n,
        (worldAt Reading.gl b.L b.F y).entry r.tree r.row (r.first + i) =
          ent q y r.tree r.row (r.first + i))
    (q : α × Option Pub9) (front : ℕ) (e : S) (a : K9.Part) (c : List Claim) (e₁ : S)
    (hf : Fx9 φ Ok q e) (ha : atS.get? e = some a) (hr : k8Run.2 front e = .ok (c, e₁)) (t : S)
    (y : Bound GE8) (b : K9.Part) (ht : laterK atS (O9 (K := GE8) φ Ok Fu) e₁ t) (hfull : Fu t)
    (hb : atS.get? t = some b) :
    (c.take 4).map (claimValue Reading.gl (worldAt Reading.gl b.L b.F y)) = vals4 π ent q y := by
  obtain ⟨F, tl, funs, tl', F1, hF, htl, hfu, he, rfl⟩ := k8Run_ok front e e₁ c hr
  obtain ⟨a₁, ha₁, f1, _, _, _, _, hF'⟩ := get_put e a ha tl' F1
  have eF : F = a.F := Option.some.inj (hF.symm.trans hF')
  subst eF
  obtain ⟨g, Fa, hg, h4, hrun, hF1⟩ := take_four he
  have hmore := k8_goes φ u hkeep _ e a tl tl' funs F1 c ha htl he
  have hft : Fx9 φ Ok q t :=
    fx_of_more φ Ok q _ t (fx_of_more φ Ok q e _ hf hmore) ht.2.1
  have hft' := hft
  obtain ⟨b0, hb0, gb⟩ := ht.2.1.2 a₁ ha₁
  have eb0 : b0 = b := Option.some.inj (hb0.symm.trans hb)
  subst eb0
  have hq1 : (π q.1).1 = some (blank u tl) := by
    rw [← hf.2.1, hπ, htl]
    rfl
  obtain ⟨hok, _, v, a0, hv, ha0, gv⟩ := hf
  have ea0 : a0 = a := Option.some.inj (ha0.symm.trans ha)
  subst ea0
  obtain ⟨_, _, v', b', hv', hb', gv'⟩ := hft
  have ev : v' = v := Option.some.inj (hv'.symm.trans hv)
  have eb : b' = b0 := Option.some.inj (hb'.symm.trans hb)
  subst ev eb
  obtain ⟨hsz, hslots⟩ := hOk4 q v' (blank u tl) g hok hv hq1 hg
  rw [four8_blank] at hslots
  have hsa : Sized a0.F := gv.1.sized hsz
  have hlb : Later F1 b'.F := by
    have := gb.1
    rwa [show (pubOf a₁).F = F1 from f1] at this
  have hlaid : LaidAt b'.F (winOf g.leaves) :=
    laid_of_run ((paid_later a0.F g.owedJoin).sized hsa) hrun
      ((by rw [hF1]; exact paid_later Fa g.owedPlanes : Later Fa F1).trans hlb)
  have hvals : vals4 π ent q y = (four8 tl g).map (claimValue Reading.gl
      (refWorld Reading.gl v'.F [winOf g.leaves] (ent q y) y)) := by
    have hg' : (blank u tl).heard = some g := hg
    simp only [vals4, hq1, hv, hg']
    rw [four8_blank]
  have h5 := hFu4 q t b' y (blank u tl) g hft' hfull hb hq1 hg
  rw [four8_blank] at h5
  rw [h4, hvals]
  exact List.map_congr_left fun cl hcl =>
    claim_ref Reading.gl cl b'.L v'.F b'.F [winOf g.leaves] (ent q y) y gv'.1
      (fun w hw => by
        rw [List.mem_singleton] at hw
        rw [hw]
        exact hlaid)
      (fun x hx => (hslots cl hcl x hx).imp (fun h => ⟨_, List.mem_singleton.2 rfl, h⟩) id)
      (h5 cl hcl).1 (h5 cl hcl).2

/-- A list of values that is a list of zeros, member by member. -/
theorem zero_of_map {β K : Type} [Zero K] (f : β → K) (l : List β) (vs : List K)
    (h : l.map f = vs) (h0 : ∀ v ∈ vs, v = 0) : ∀ k ∈ l, f k = 0 := fun k hk =>
  h0 _ (h ▸ List.mem_map.2 ⟨k, hk, rfl⟩)

/-- **Where the law's four values are 0, each of the four claims is worth 0 at every later full
state, in the batching's own world and measure.** -/
theorem four_zero_full (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (u : HTailF2)
    (π : α → Option HTailF2 × Option (Array HFun))
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?))
    (hkeep : ∀ s tl tl' F1, s.tl? = some tl → blank u tl' = blank u tl →
      φ ((s.putTl tl').putFork F1) = φ s)
    (ent : α × Option Pub9 → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (hOk4 : ∀ q v tlb g, Ok q → q.2 = some v → (π q.1).1 = some tlb → tlb.heard = some g →
      Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g.leaves) x.1 ∨ Filled v.F x.1)
    (hFu4 : ∀ q t b y tlb g, Fx9 φ Ok q t → Fu t → atS.get? t = some b →
      (π q.1).1 = some tlb → tlb.heard = some g → ∀ cl ∈ four8 tlb g,
      (∀ x ∈ cl.form.ents.toList, (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx =
        ent q y x.tree x.row x.idx) ∧
      ∀ r ∈ cl.runs.toList, ∀ i < r.n,
        (worldAt Reading.gl b.L b.F y).entry r.tree r.row (r.first + i) =
          ent q y r.tree r.row (r.first + i))
    (q : α × Option Pub9) (front : ℕ) (e : S) (a : K9.Part) (c : List Claim) (e₁ : S)
    (hf : Fx9 φ Ok q e) (ha : atS.get? e = some a) (hr : k8Run.2 front e = .ok (c, e₁)) (t : S)
    (y : Bound GE8) (b : K9.Part) (ht : laterK atS (O9 (K := GE8) φ Ok Fu) e₁ t) (hfull : Fu t)
    (hb : atS.get? t = some b) (h0 : ∀ v ∈ vals4 π ent q y, v = 0) :
    ∀ k ∈ c.take 4, claimValue Reading.gl (worldAt Reading.gl b.L b.F y) k = 0 :=
  zero_of_map _ _ _
    (four_values_full φ Ok Fu u π hπ hkeep ent hOk4 hFu4 q front e a c e₁ hf ha hr t y b ht hfull
      hb) h0

/-- **The same where the full state stands behind a yes of the run of self tests**: the ledger is
the library's, in which the rows' weights are laid. -/
theorem four_zero_coefAll (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (u : HTailF2)
    (π : α → Option HTailF2 × Option (Array HFun))
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?))
    (hkeep : ∀ s tl tl' F1, s.tl? = some tl → blank u tl' = blank u tl →
      φ ((s.putTl tl').putFork F1) = φ s)
    (ent : α × Option Pub9 → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (hOk4 : ∀ q v tlb g, Ok q → q.2 = some v → (π q.1).1 = some tlb → tlb.heard = some g →
      Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g.leaves) x.1 ∨ Filled v.F x.1)
    (hFu4 : ∀ q t b y tlb g, Fx9 φ Ok q t → Fu t → atS.get? t = some b →
      (π q.1).1 = some tlb → tlb.heard = some g → ∀ cl ∈ four8 tlb g,
      (∀ x ∈ cl.form.ents.toList, (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx =
        ent q y x.tree x.row x.idx) ∧
      ∀ r ∈ cl.runs.toList, ∀ i < r.n,
        (worldAt Reading.gl b.L b.F y).entry r.tree r.row (r.first + i) =
          ent q y r.tree r.row (r.first + i))
    (q : α × Option Pub9) (front : ℕ) (e : S) (a : K9.Part) (c : List Claim) (e₁ : S)
    (hf : Fx9 φ Ok q e) (ha : atS.get? e = some a) (hr : k8Run.2 front e = .ok (c, e₁)) (t : S)
    (y : Bound GE8) (b : K9.Part) (ht : laterK atS (O9 (K := GE8) φ Ok Fu) e₁ t) (hfull : Fu t)
    (hb : atS.get? t = some b) (h0 : ∀ v ∈ vals4 π ent q y, v = 0) (nU : Array ℕ) (e' : S)
    (hT : k8Tests nU e' = .ok t) :
    ∃ Fc tlX g, e'.fork? = some Fc ∧ e'.tl? = some tlX ∧ tlX.heard = some g ∧
      b.F = Fo.coefAll tlX g Fc ∧
      ∀ k ∈ c.take 4,
        claimValue Reading.gl (worldAt Reading.gl b.L (Fo.coefAll tlX g Fc) y) k = 0 := by
  obtain ⟨Fc, tlX, g, h1, h2, h3, _, h5⟩ := k8_tests_coefAll nU e' t hT
  have eF : b.F = Fo.coefAll tlX g Fc := Option.some.inj ((K9.get_fork t b hb).symm.trans h5)
  refine ⟨Fc, tlX, g, h1, h2, h3, eF, ?_⟩
  rw [← eF]
  exact four_zero_full φ Ok Fu u π hπ hkeep ent hOk4 hFu4 q front e a c e₁ hf ha hr t y b ht hfull
    hb h0

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.four_values_full
#print axioms VerifiableInference.Desc.K9L.zero_of_map
#print axioms VerifiableInference.Desc.K9L.four_zero_full
#print axioms VerifiableInference.Desc.K9L.four_zero_coefAll
