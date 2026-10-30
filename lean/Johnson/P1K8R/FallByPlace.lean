-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/FallByPlace.lean: THE SMALLNESS TEST: THE CHANCE OF Johnson/P1K8R/FallAtRunRows.lean
SAID BY PLACE: THE HONEST SIDE's OWN `chainFall` (Johnson/Desc/ProofFile/Honest/Fall.lean), AT THE
FIRST CHAIN, SAYS A FALL AT THE PLACE OF THE MEMBER WITHOUT A ROUND BEHIND A SEGMENT's BATCHING.
LEMMAS; NONE OF THE LIBRARY's GOALS. Nothing on completeness, soundness or hiding. An assembly: no
new argument.

  `chainFall_at`   general: where `chainFall` says (a, w), `frontsOf` has an entry at the place a at
      which `fallOf` says w
  **`fall_by_place`**   IF THE PUBLIC TEST `rowsFitB` SAYS YES AT ALL 25 SEGMENTS (`RowsAsked Z`):
      the premises of `fall_at_run_rows`; for every list fs of falls such that (htest) whatever fs
      says at quietPlace l o, at a state s, gives that `selfUnits` says no at s: the chance, over
      the list of challenges, that the run returns and `chainFall` at fs, at the first chain and the
      run's first view, says a fall at quietPlace l o, is at most nU[2] * (p.rows - 1) * w / (the
      number of round j's challenges)
  **`chainFall_quiet`**   in the goals' scope: a fall that `chainFall` says at quietPlace l o, at
      whatever list of falls and view, is said by `fallOf` at entry K + 1 of `frontsOf`: the state
      in front of that member
  **`fall_by_place_cut`**   the same bound AT EVERY LIST OF FALLS, without (htest), for the event
      cut by the test: `chainFall` says a fall at quietPlace l o, and `selfUnits` says no at the
      state at which it is said: the term that a sum over the tests of a fall wants; the bound is
      `fall_at_run_rows`' own: the clauses on `chainFall` and `fallOf` only make the event smaller
  `unitsFall`, `unitsFall_test`   a fall at that place whose test is just that `selfUnits` says no:
      the list of that one fall meets (htest)
By: `fall_at_run_rows` · `frontsOf_reach₀` (Johnson/Desc/ProofFile/Honest/K8/FrontsReach.lean) ·
`quiet_place` (Johnson/P1K8R/PlacesAtFlat.lean).
Limits. The first chain's arm alone: not `fallAt` whole. ONE OF THE SEVEN TESTS of `k8ShareFall`
(Johnson/Desc/ProofFile/Honest/K8/Falls.lean): that fall's own list does not meet (htest). No stated
share is held against the bound. For the rest those of FallAtRunRows.lean.
-/
import Johnson.P1K8R.FallAtRunRows
import Johnson.P1K8R.PlacesAtFlat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9Asks (RowsAsked)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws RunC runC frontsOf chainFall fallOf Fall Odds)
open ProofFile.Honest.K8 (frontAt rnds batchPlace quietPlace)
open scoped ENNReal

/-- Where `chainFall` says something. -/
theorem chainFall_at {T Cl : Type} (fs : List (Fall T)) (ft : Nat) (bs : List (Block T Cl)) (s : T)
    (v : Fmt.View) (a : Place) (w : String) (h : chainFall fs ft bs s v = some (a, w)) :
    ∃ (n : Nat) (e : Place × T × List Fmt.Drawn),
      (frontsOf ft bs s v.rounds v.opened)[n]? = some e ∧ e.1 = a ∧
        fallOf fs a e.2.1 e.2.2 = some w := by
  unfold chainFall at h
  obtain ⟨e, he, hf⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 he
  obtain ⟨u, hu, hp⟩ := Option.map_eq_some_iff.1 hf
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
  exact ⟨n, e, hn, rfl, hu⟩

/-- A fall at the member without a round whose test is that `selfUnits` says no. -/
def unitsFall (link o : Nat) (nU : Array Nat) (share : Odds) : Fall S :=
  { place := quietPlace link o
    test := fun s _ => if zeroUnitAt nU s then some "the smallness test: a unit's weight is 0"
      else none
    share := share }

theorem unitsFall_test (link o : Nat) (nU : Array Nat) (share : Odds) (s : S)
    (ds : List Fmt.Drawn) (w : String)
    (h : fallOf [unitsFall link o nU share] (quietPlace link o) s ds = some w) :
    zeroUnitAt nU s = true := by
  unfold fallOf at h
  obtain ⟨f, hf, ht⟩ := List.exists_of_findSome?_eq_some h
  obtain rfl : f = unitsFall link o nU share := by
    have := (List.mem_filter.1 hf).1
    simpa using this
  by_contra hz
  simp only [unitsFall, if_neg hz] at ht
  cases ht

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- **A fall that `chainFall` says at the quiet member's place is said at entry K + 1.** -/
theorem chainFall_quiet (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    (fs : List (Fall S)) (z : ProofFile.InstPub) (v : Fmt.View) (u : String)
    (h : chainFall fs 0 c.blocksInOrder (ProofFile.startS Z z) v =
      some (quietPlace l (if l = 24 then 1 else 0), u)) :
    ∃ e : Place × S × List Fmt.Drawn,
      (frontsOf 0 c.blocksInOrder (ProofFile.startS Z z) v.rounds v.opened)[14 * l +
                       (if l = 24 then 11 else 9) + 1]? = some e ∧
      fallOf fs (quietPlace l (if l = 24 then 1 else 0)) e.2.1 e.2.2 = some u := by
  obtain ⟨n, e, hn, hpl, hfall⟩ := chainFall_at fs 0 c.blocksInOrder _ _ _ u h
  have hre := (ProofFile.Honest.K8.frontsOf_reach₀ 0 c.blocksInOrder (ProofFile.startS Z) z _ _ n e hn).2
  rw [hpl] at hre
  obtain rfl := quiet_place hS hR O hl hre
  exact ⟨e, hn, hfall⟩

/-- **The chance, by place.** -/
theorem fall_by_place (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    {W₀ Rc Ky Tr X₀ X' : Type} (Bk : ProverCoinCounts) (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X') (w₀ : W₀)
    (rc : Rc) (x : ProofFile.Inst) (k : Coins Bk)
    {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} [∀ i, Fintype (A i)]
    [∀ i, Nonempty (A i)] (j : ι) (el : A j → Cb.Gl.E) (w : ℕ)
    (hw : ∀ y, Prob.cnt (fun a => el a = y) ≤ w) (shows : (∀ i, A i) → Draws)
    (hj : ∀ f a, (shows (Function.update f j a)).first.take
        (rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9)))) =
      (shows f).first.take (rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9)))))
    (hshow : ∀ f dr, (shows f).first[rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9)))]? =
      some dr → dr.elems = [Slice.ofE (el (f j))]) :
    ∃ (p : K9.Where) (X : LinkH), IM.k9At Z l = some p ∧ Bs.G₀.built.toList[l]? = some X ∧
      ∀ fs : List (Fall S),
        (∀ s ds u, fallOf fs (quietPlace l (if l = 24 then 1 else 0)) s ds = some u →
          zeroUnitAt (ProofFile.k8NU Bs.G₀ X) s = true) →
        Prob.pr (Prob.unif (∀ i, A i)) {f | ∃ (r : RunC (descAt Z A₂ B₂ c)) (u : String),
          runC (descAt Z A₂ B₂ c) Bk H w₀ rc x k (shows f) = .ok r ∧
          chainFall fs 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound r.run.views.1) =
            some (quietPlace l (if l = 24 then 1 else 0), u)} ≤
        (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) * w : ℕ) : ℝ≥0∞) / Fintype.card (A j) := by
  obtain ⟨p, X, hp, hX, h⟩ := fall_at_run_rows hE hS hR O hl Bk H w₀ rc x k j el w hw shows hj hshow
  refine ⟨p, X, hp, hX, fun fs htest => (Prob.pr_mono _ fun f hf => ?_).trans h⟩
  obtain ⟨r, u, hr, hc⟩ := hf
  obtain ⟨e, hn, hfall⟩ := chainFall_quiet hS hR O hl fs x.pub _ u hc
  exact ⟨r, e, hr, hn, htest _ _ u hfall⟩

/-- **The same with the event cut by the test, at every list of falls.** -/
theorem fall_by_place_cut (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    {W₀ Rc Ky Tr X₀ X' : Type} (Bk : ProverCoinCounts) (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X') (w₀ : W₀)
    (rc : Rc) (x : ProofFile.Inst) (k : Coins Bk)
    {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} [∀ i, Fintype (A i)]
    [∀ i, Nonempty (A i)] (j : ι) (el : A j → Cb.Gl.E) (w : ℕ)
    (hw : ∀ y, Prob.cnt (fun a => el a = y) ≤ w) (shows : (∀ i, A i) → Draws)
    (hj : ∀ f a, (shows (Function.update f j a)).first.take
        (rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9)))) =
      (shows f).first.take (rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9)))))
    (hshow : ∀ f dr, (shows f).first[rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9)))]? =
      some dr → dr.elems = [Slice.ofE (el (f j))]) :
    ∃ (p : K9.Where) (X : LinkH), IM.k9At Z l = some p ∧ Bs.G₀.built.toList[l]? = some X ∧
      ∀ fs : List (Fall S),
        Prob.pr (Prob.unif (∀ i, A i)) {f | ∃ (r : RunC (descAt Z A₂ B₂ c)) (u : String)
            (e' : Place × S × List Fmt.Drawn),
          runC (descAt Z A₂ B₂ c) Bk H w₀ rc x k (shows f) = .ok r ∧
          chainFall fs 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound r.run.views.1) =
            some (quietPlace l (if l = 24 then 1 else 0), u) ∧
          (frontsOf 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound r.run.views.1).rounds
            (withEmptySealRound r.run.views.1).opened)[14 * l + (if l = 24 then 11 else 9) + 1]? =
              some e' ∧
          fallOf fs (quietPlace l (if l = 24 then 1 else 0)) e'.2.1 e'.2.2 = some u ∧
          zeroUnitAt (ProofFile.k8NU Bs.G₀ X) e'.2.1 = true} ≤
        (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) * w : ℕ) : ℝ≥0∞) / Fintype.card (A j) := by
  obtain ⟨p, X, hp, hX, h⟩ := fall_at_run_rows hE hS hR O hl Bk H w₀ rc x k j el w hw shows hj hshow
  refine ⟨p, X, hp, hX, fun fs => (Prob.pr_mono _ fun f hf => ?_).trans h⟩
  obtain ⟨r, u, e', hr, -, hn, -, hz⟩ := hf
  exact ⟨r, e', hr, hn, hz⟩

end

end P1K8

#print axioms P1K8.chainFall_at
#print axioms P1K8.unitsFall_test
#print axioms P1K8.chainFall_quiet
#print axioms P1K8.fall_by_place
#print axioms P1K8.fall_by_place_cut
#print axioms P1K8.unitsFall
