-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverOwn.lean: `localDebts_sorts` (Honest/Law/CoverSorts.lean)
with the frame's own marks paid inside, and with a reached state handed to whoever proves its
hypothesis `hP`. That theorem bounds all gated sub-protocols of one chain. It takes one list of
marks. Some marks come from the sub-protocols' owners. The marks `fitMarks`
(Honest/Law/CoverFit.lean) are the frame's own: one for each sub-protocol, which speaks if the
challenges are none that its rounds can draw. Here the list is the owners' marks followed by
`fitMarks`.

What this changes. The hypotheses on marks (`hseat`, `hM`, `hp₁`, `hp₂`) speak of the owners' marks
alone. The hypothesis `hP` may use that the verifier's state just before a sub-protocol that has a
round is reached by the steps of the sub-protocols under `below` (`ver_reach_below`,
Honest/Law/CoverBelow.lean). The silence of `fitMarks` gives what that lemma asks of the challenges
(`fit_of_silent`).

  1  `fitMark_at`   a mark of `fitMarks` at a sub-protocol's place is that sub-protocol's
  2  `hsil_own`, `hM_own`, `sum_own`   the three hypotheses on marks, from the owners' marks alone
  3  `hP_reach`   the hypothesis `hP`, from a form that may use the reached state
  4  `localDebts_own`   `localDebts_sorts` with these four laid in

Limits.
  * `hnd` (no two gated sub-protocols stand at one place) is a hypothesis. At a description whose
    tests on the plan accept, `places_nodup` (Honest/Law/Cuts.lean) gives it for each whole chain.
  * `hC` (what the kit of challenges shows fits its round) and `hz` are hypotheses. `kit_two`
    (Honest/Law/KitTwo.lean) proves `hC` at one kit.
  * `hq0` asks that the number laid for a mark of `fitMarks` is 0.
  * The hypotheses of `localDebts_sorts` on which sub-protocol has a round (`H`, `hlast`, `hend`,
    `hmr`) stay as they are.
  * The reached state is handed over just before a sub-protocol that has a round.
  * `hX`, `hs` and `hft` are hypotheses. `hX` asks that every start of the walk comes from the state
    `start (zp base)`, at some columns handed: it fits a file's first chain, not the second where an
    earlier chain can reject (see Honest/Law/CoverPay.lean).
  * The lemmas are applied to no description here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverSorts
import Johnson.Desc.ProofFile.Honest.Law.CoverFitAt
import Johnson.Desc.ProofFile.Honest.Law.CoverBelow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

variable {S Cl W Y : Type}

/-! ## 1 Whose mark -/

/-- A mark of `fitMarks` that stands at the place of a sub-protocol `b` of the list is the mark of
`b`, if no two sub-protocols of the list stand at one place. -/
theorem fitMark_at (bs : List (Block S Cl)) (hnd : (bs.map (·.place)).Nodup) {b : Block S Cl}
    (hb : b ∈ bs) {mk : Mark} (hmk : mk ∈ fitMarks bs) (hp : mk.place = b.place) :
    mk = ⟨b.place,
      fun _ own => if drawsFit b.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hmk
  have e : c = b := List.inj_on_of_nodup_map hnd hc hb hp
  rw [e]

/-! ## 2 The hypotheses on marks -/

/-- Where no owner's mark may stand, no mark of the whole list speaks at a typed message. -/
theorem hsil_own (C : CK)
    (hC : ∀ e k (c : C.Ch e k), H2K.Fit.FitsDrawn e k (C.dr e k c) ∧
      (∀ z ∈ (C.dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
      ((C.dr e k c).digest = none ∨ k = .sealed))
    (bs : List (Block S Cl)) (ds : List RDT)
    (hfit : List.Forall₂ KindFits ds (bs.flatMap (·.rounds)))
    (hz : ∀ b ∈ bs, ∀ z ∈ b.rounds, z.entry.drawNZ ≤ z.entry.drawE)
    (hnd : (bs.map (·.place)).Nodup) (hm : List Mark) (seatM : Place → Bool)
    (hseat : ∀ mk ∈ hm, seatM mk.place = true) :
    ∀ A b B, bs = A ++ b :: B → seatM b.place = false →
      ∀ fr (ρ : Iop.Rho (uLT C ((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length))),
      markOf (hm ++ fitMarks bs) b.place fr (drawnT C _ ρ) = none := by
  intro A b B e hs fr ρ
  have hb : b ∈ bs := by
    rw [e]
    exact List.mem_append_right _ List.mem_cons_self
  refine markOf_none_of _ _ _ _ fun mk hmk hp => ?_
  rcases List.mem_append.1 hmk with h1 | h1
  · have h2 := hseat mk h1
    rw [hp, hs] at h2
    cases h2
  · rw [fitMark_at bs hnd hb h1 hp]
    exact if_pos (fit_at_member C hC ds A B b (e ▸ hfit) (hz b hb) ρ)

/-- The bounds for the marks at a sub-protocol's place, from the owners' bounds alone. -/
theorem hM_own (C : CK)
    (hC : ∀ e k (c : C.Ch e k), H2K.Fit.FitsDrawn e k (C.dr e k c) ∧
      (∀ z ∈ (C.dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
      ((C.dr e k c).digest = none ∨ k = .sealed))
    (bs : List (Block S Cl)) (hz : ∀ b ∈ bs, ∀ z ∈ b.rounds, z.entry.drawNZ ≤ z.entry.drawE)
    (hnd : (bs.map (·.place)).Nodup) (hm : List Mark)
    (PM : Block S Cl → List Fmt.Drawn → Prop) (qM : Block S Cl → Mark → ℝ≥0∞)
    (hM : ∀ A b b' B, bs = A ++ b :: b' :: B →
      ∀ mk ∈ hm.filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) (qM b mk)) :
    ∀ A b b' B, bs = A ++ b :: b' :: B →
      ∀ mk ∈ (hm ++ fitMarks bs).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) (qM b mk) := by
  intro A b b' B e mk hmk dsb hd
  have hb : b ∈ bs := by
    rw [e]
    exact List.mem_append_right _ List.mem_cons_self
  rw [List.filter_append] at hmk
  rcases List.mem_append.1 hmk with h1 | h1
  · exact hM A b b' B e mk h1 dsb hd
  · obtain ⟨h2, h3⟩ := List.mem_filter.1 h1
    rw [fitMark_at bs hnd hb h2 (eq_of_beq h3)]
    exact fitMark_debt C b dsb (fun ρ => drawsFit_typed C hC _ _ hd (hz b hb) ρ) _ _

/-- The numbers of the marks at a sub-protocol's place add up to the owners' numbers. -/
theorem sum_own (bs : List (Block S Cl)) (hnd : (bs.map (·.place)).Nodup) (hm : List Mark)
    (qM : Block S Cl → Mark → ℝ≥0∞)
    (hq0 : ∀ b ∈ bs, qM b ⟨b.place,
      fun _ own => if drawsFit b.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ = 0)
    {b : Block S Cl} (hb : b ∈ bs) :
    (((hm ++ fitMarks bs).filter fun m => m.place == b.place).map (qM b)).sum =
      ((hm.filter fun m => m.place == b.place).map (qM b)).sum := by
  have h0 : (((fitMarks bs).filter fun m => m.place == b.place).map (qM b)).sum = 0 := by
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨mk, hmk, rfl⟩ := List.mem_map.1 hx
    obtain ⟨h2, h3⟩ := List.mem_filter.1 hmk
    rw [fitMark_at bs hnd hb h2 (eq_of_beq h3)]
    exact hq0 b hb
  rw [List.filter_append, List.map_append, List.sum_append, h0, add_zero]

/-! ## 3 The reached state -/

/-- The hypothesis `hP` of `localDebts_sorts`, from a form `hP'` whose last premise hands over the
reached state. `start`, `zp`: every start of the chain's walk has the verifier's state
`start (zp base)`. `hs`: the words of the stored columns are below the prime. -/
theorem hP_reach (all bs rest : List (Block S Cl)) (fs : List (Fall S)) (ms : List Mark)
    (skip : Nat) (X : List Fmt.Drawn → ChainAt S Cl W Y) (hall : all = bs ++ rest)
    (hsub : ∀ mk ∈ fitMarks bs, mk ∈ ms) {Pb : Type} (start : Pb → S)
    (zp : List Fmt.Drawn → Pb)
    (hX : ∀ base a, (X base).start = some a → ∃ (m₀ : Option (Mid W Y)) (front : List OpenedColumn),
      m₀.isSome = true ∧ ChainProgress.start (X base).lay all m₀ (some (start (zp base))) front = .ok a)
    (hs : ∀ base i x u, (X base).lay.stored i x = some u → ∀ a ∈ u, a < fieldPrimeWord)
    {ft : Nat} (hft : ∀ base, (X base).lay.firstTree = ft) (seatF : Place → Bool)
    (P : Block S Cl → List Fmt.Drawn → S → Prop)
    (hP' : ∀ A b b' B, bs = A ++ b :: b' :: B → seatF b.place = true → b.rounds ≠ [] →
      ∀ fr a z s', skip ≤ fr.length →
      (fr.drop skip).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy all fs (X (fr.take skip)) (0 + (A.flatMap (·.rounds)).length) (fr.drop skip) = false →
      silentQ ms skip bs (0 + A.length) fr → (X (fr.take skip)).start = some a →
      walk (X (fr.take skip)).lay
        ((X (fr.take skip)).steps.take (0 + (A.flatMap (·.rounds)).length)) (fr.drop skip) a =
        .ok z →
      z.ver = some s' →
      (b.rounds ≠ [] → Reach ft (all.map below) start A.length (zp (fr.take skip), s')) →
      P b fr s') :
    ∀ A b b' B, bs = A ++ b :: b' :: B → seatF b.place = true → b.rounds ≠ [] →
      ∀ fr a z s', skip ≤ fr.length →
      (fr.drop skip).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy all fs (X (fr.take skip)) (0 + (A.flatMap (·.rounds)).length) (fr.drop skip) = false →
      silentQ ms skip bs (0 + A.length) fr → (X (fr.take skip)).start = some a →
      walk (X (fr.take skip)).lay
        ((X (fr.take skip)).steps.take (0 + (A.flatMap (·.rounds)).length)) (fr.drop skip) a =
        .ok z →
      z.ver = some s' → P b fr s' := by
  intro A b b' B e hsF hr0 fr a z s' h1 h2 h3 h4 y1 y2 hv
  refine hP' A b b' B e hsF hr0 fr a z s' h1 h2 h3 h4 y1 y2 hv fun hr => ?_
  obtain ⟨m₀, _, hm, ha⟩ := hX _ a y1
  have hA : bs.take (0 + A.length) = A := by
    rw [e, Nat.zero_add]
    exact List.take_left' rfl
  have hd := fit_of_silent bs ms hsub skip (0 + A.length) fr (by rw [hA, h2, Nat.zero_add]) h4
  rw [hA] at hd
  have hall' : all = A ++ b :: (b' :: B ++ rest) := by
    rw [hall, e, List.append_assoc, List.cons_append]
  rw [hall'] at ha ⊢
  have h := ver_reach_below (X (fr.take skip)).lay (hs _) start (zp (fr.take skip)) A b
    (b' :: B ++ rest) (List.length_pos_of_ne_nil hr) m₀ hm ha y2 hd hv
  rw [hft] at h
  exact h

/-! ## 4 Laid in -/

set_option maxHeartbeats 1000000 in
/-- `localDebts_sorts` at the owners' marks `hm` followed by `fitMarks bs`. -/
theorem localDebts_own (C : CK)
    (hC : ∀ e k (c : C.Ch e k), H2K.Fit.FitsDrawn e k (C.dr e k c) ∧
      (∀ z ∈ (C.dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
      ((C.dr e k c).digest = none ∨ k = .sealed))
    (all bs rest : List (Block S Cl)) (fs : List (Fall S)) (hm : List Mark) (skip : Nat)
    (X : List Fmt.Drawn → ChainAt S Cl W Y) (p : Nat → ℝ≥0∞) (tail : List Fmt.Drawn)
    {Pb : Type} (start : Pb → S) (zp : List Fmt.Drawn → Pb)
    (hX : ∀ base a, (X base).start = some a → ∃ (m₀ : Option (Mid W Y)) (front : List OpenedColumn),
      m₀.isSome = true ∧ ChainProgress.start (X base).lay all m₀ (some (start (zp base))) front = .ok a)
    (hs : ∀ base i x u, (X base).lay.stored i x = some u → ∀ a ∈ u, a < fieldPrimeWord)
    (hall : all = bs ++ rest) (ds : List RDT)
    (hfit : List.Forall₂ KindFits ds (bs.flatMap (·.rounds)))
    (hz : ∀ b ∈ bs, ∀ z ∈ b.rounds, z.entry.drawNZ ≤ z.entry.drawE)
    (hnd : (bs.map (·.place)).Nodup) (seatF seatM : Place → Bool)
    (hfs : ∀ f ∈ fs, seatF f.place = true) (hseat : ∀ mk ∈ hm, seatM mk.place = true)
    (H : ∀ (P : List (Block S Cl)) (c d : Block S Cl) (Q : List (Block S Cl)),
      all = P ++ c :: d :: Q → seatF d.place = true → d.rounds = [] →
      c.rounds ≠ [] ∧ seatF c.place = true)
    (hrest : ∀ d ∈ rest, seatF d.place = false)
    (hlast : ∀ A b, bs = A ++ [b] → b.rounds = [] → tail = [])
    (hend : ∀ A b, bs = A ++ [b] →
      ¬ (seatM b.place = true ∨ (seatF b.place = true ∧ b.rounds ≠ [])))
    (hmr : ∀ b ∈ bs, seatM b.place = true → b.rounds ≠ [])
    {ft : Nat} (hft : ∀ base, (X base).lay.firstTree = ft)
    (PM : Block S Cl → List Fmt.Drawn → Prop) (qM : Block S Cl → Mark → ℝ≥0∞)
    (hq0 : ∀ b ∈ bs, qM b ⟨b.place,
      fun _ own => if drawsFit b.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ = 0)
    (hM : ∀ A b b' B, bs = A ++ b :: b' :: B →
      ∀ mk ∈ hm.filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) (qM b mk))
    (hPM : ∀ A b b' B, bs = A ++ b :: b' :: B →
      ∀ fr, skip ≤ fr.length → (fr.drop skip).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy all fs (X (fr.take skip)) (0 + (A.flatMap (·.rounds)).length) (fr.drop skip) = false →
      silentQ (hm ++ fitMarks bs) skip bs (0 + A.length) fr → PM b fr)
    (P : Block S Cl → List Fmt.Drawn → S → Prop) (qF : Block S Cl → Fall S → ℝ≥0∞)
    (reps : Block S Cl → List (Fall S))
    (hF : ∀ A b b' B, bs = A ++ b :: b' :: B → seatF b.place = true → b.rounds ≠ [] →
      ∀ g ∈ reps b, ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      FallDebt C g ft b (b' :: B ++ rest) dsb [] (P b) (qF b g))
    (hin : ∀ A b b' B, bs = A ++ b :: b' :: B → seatF b.place = true → b.rounds ≠ [] →
      ∀ f ∈ fs, (∃ d ∈ groupOf b (b' :: B ++ rest), f.place = d.place) →
      ∃ g ∈ reps b, ∀ fr s' own, P b fr s' →
        localFall [f] ft (b :: (b' :: B ++ rest)) s' own →
        localFall [g] ft (b :: (b' :: B ++ rest)) s' own)
    (hP' : ∀ A b b' B, bs = A ++ b :: b' :: B → seatF b.place = true → b.rounds ≠ [] →
      ∀ fr a z s', skip ≤ fr.length →
      (fr.drop skip).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy all fs (X (fr.take skip)) (0 + (A.flatMap (·.rounds)).length) (fr.drop skip) = false →
      silentQ (hm ++ fitMarks bs) skip bs (0 + A.length) fr →
      (X (fr.take skip)).start = some a →
      walk (X (fr.take skip)).lay
        ((X (fr.take skip)).steps.take (0 + (A.flatMap (·.rounds)).length)) (fr.drop skip) a =
        .ok z →
      z.ver = some s' →
      (b.rounds ≠ [] → Reach ft (all.map below) start A.length (zp (fr.take skip), s')) →
      P b fr s')
    (hp₁ : ∀ A b b' B, bs = A ++ b :: b' :: B → seatF b.place = true → b.rounds ≠ [] →
      ((hm.filter fun m => m.place == b.place).map (qM b)).sum + ((reps b).map (qF b)).sum ≤
        p (0 + A.length))
    (hp₂ : ∀ A b b' B, bs = A ++ b :: b' :: B → seatF b.place = false →
      ((hm.filter fun m => m.place == b.place).map (qM b)).sum ≤ p (0 + A.length)) :
    LocalDebts C all fs (hm ++ fitMarks bs) skip X p tail
      (silentQ (hm ++ fitMarks bs) skip bs) bs 0 0 ds := by
  have hmem : ∀ A b b' B, bs = A ++ b :: b' :: B → b ∈ bs := fun A b b' B e => by
    rw [e]
    exact List.mem_append_right _ List.mem_cons_self
  refine localDebts_sorts C all bs rest fs (hm ++ fitMarks bs) skip X p tail
    (fun base a h => ?_) hall ds hfit seatF seatM hfs
    (hsil_own C hC bs ds hfit hz hnd hm seatM hseat) H hrest hlast hend hmr hft PM qM
    (hM_own C hC bs hz hnd hm PM qM hM) hPM P qF reps hF hin
    (hP_reach all bs rest fs (hm ++ fitMarks bs) skip X hall
      (fun mk h => List.mem_append_right _ h) start zp hX hs hft seatF P hP')
    (fun A b b' B e hsF hr => ?_) (fun A b b' B e hsF => ?_)
  · obtain ⟨m₀, _, h1, h2⟩ := hX base a h
    exact ⟨m₀, _, _, h1, h2⟩
  · rw [sum_own bs hnd hm qM hq0 (hmem A b b' B e)]
    exact hp₁ A b b' B e hsF hr
  · rw [sum_own bs hnd hm qM hq0 (hmem A b b' B e)]
    exact hp₂ A b b' B e hsF

end ProofFile.Honest

#print axioms ProofFile.Honest.fitMark_at
#print axioms ProofFile.Honest.hsil_own
#print axioms ProofFile.Honest.hM_own
#print axioms ProofFile.Honest.sum_own
#print axioms ProofFile.Honest.hP_reach
#print axioms ProofFile.Honest.localDebts_own
