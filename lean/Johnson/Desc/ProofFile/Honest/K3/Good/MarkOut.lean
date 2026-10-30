-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/MarkOut.lean: the kind "lookup" (K3): what the lookup owes for
its second mark (`markOut`, Honest/K3/Good/Mark.lean: for other kinds' slots and entries).
Conditional: the frame's `MarkDebt` (Honest/Law/CoverJoin.lean) at the number of that mark's events
times a letter kap. Definitions; theorems. None of the library's goals.

Terms. Honest/K3/GLOSSARY.md: see there mark (in the frame's sense), spot, event, sample, good
samples, share, kit and window. In this file: a is the lookup's place and f its face. C is a kit,
dsb the data of the rounds of the lookup's member, kap a letter for a share.

What is shown.
  `mean_eq`, `mean_le`: a bound at every cut bounds the share of a set of pairs.
  `chal_le`: of one round's messages: the bits of the test of work cancel.
  `inner_le`: the measure of an event on all rounds is at most p, if at every fixing of the other
    rounds at most the share p of one round's challenges meet it.
  `leafBad`, `outEvents`, `goodOut_eq`, `outEvents_length`: the second test's events: the last one;
    those on one round's sample; the test written by the two; their number.
  `LeafFew`, `FewOut`: the hypotheses on the kit.
  `markOut_le`, `markOut_debt`: the bound, written out and at the frame's own name.
Helpers: `head_fibre_le`, `one_of_out`, `leaf_le`.
The test `goodK3Out` (Honest/K3/GoodDraws.lean) asks two things. Its spots' elements are neither 0
nor 1: events on one round's sample each, as the first mark's. And one factor is not 0: the factor
of the planes' value in the leaves' claim, which reads the shift, alpha and the leaves' point, which
is sampled later. That last event reads several rounds. It is bounded at one round, at every fixing
of all other rounds, those behind it too.

Hypotheses that remain. Neither is shown in this file.
  `hc`: `CanAll C f dsb` (Honest/K3/Good/MarkShare.lean).
  `hf`: `FewOut C f dsb kap`: `FewAt` at each event of `outEvents f`, and `LeafFew`: there is a
    round of whose challenges, at every fixing of all other rounds, at most the share kap make the
    factor 0 or give it a word at or above the prime (`leafBad`).
In the theorems on the way. `h`: (in `mean_le`, `head_fibre_le`, `inner_le`) the bound p at every
cut, or at every fixing; (in `leaf_le`) `LeafFew`.

Imported. Honest/K3/Good/MarkDebt.lean imports Honest/Law/CoverJoin.lean.
Follows. `mean_eq` and `mean_le` are the frame's (Honest/Law/SharesMean.lean [not in this library]):
statements and proofs are taken over from there,
sign for sign, because that file stands on others that this one does not need.

Users. Honest/K3/Good/MarksHead.lean imports this file; the head of Honest/K3/Good/MarkDebt.lean
names `markOut_debt`.

Limits. At kap = 1 or more the clauses on the share hold of themselves, and the bound says
nothing. kap is a letter. `LeafFew` names no round: it asks that there be one; it is meant of
alpha's. It asks its bound at every two lists in front and behind, of which the first has the right
length: also at lists that no kit shows; the proof of `inner_le` spends it at what the kit shows
alone. No instance of these hypotheses is exhibited in this file. In particular no instance of
`FewOut` is exhibited, at the synthetic kit of Honest/K3/Good/MarkToy.lean either (its head says
so). What this mark's silence gives is not stated in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.MarkDebt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open Prob
open scoped ENNReal
open OnBytes (E okE isZeroE)
open VerifiableInference.Desc (Place)
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)
open Iop (GChal)

/-! ## 1 One round, at every fixing of the others -/

/-- The share of a set of pairs is the mean of its cuts' measures. -/
theorem mean_eq {A K : Type} [Fintype A] [Nonempty A] [Fintype K] [Nonempty K] (E : Set (A × K)) :
    pr (unif (A × K)) E = expect (unif K) fun k => pr (unif A) {a | (a, k) ∈ E} := by
  rw [unif_prod, ← map_swap_prod (unif K) (unif A), pr_map, pr_prod]
  rfl

/-- A bound at every cut bounds the share. -/
theorem mean_le {A K : Type} [Fintype A] [Nonempty A] [Fintype K] [Nonempty K] (E : Set (A × K))
    (p : ℝ≥0∞) (h : ∀ k, pr (unif A) {a | (a, k) ∈ E} ≤ p) : pr (unif (A × K)) E ≤ p := by
  rw [mean_eq]
  exact expect_le_of_forall_le _ fun k _ => h k

/-- Of one round's messages, the measure of those that show what Q says is at most `shareAt`. -/
theorem chal_le (C : CK) (d : RDT) (Q : Fmt.Drawn → Prop) :
    pr (unif (TypedOracleCompiler.Run.PQ.roundS C d.toRD).up.Chal)
      {c | Q (C.dr d.entry d.kind (GChal.old (b := d.entry.work) c))} ≤ shareAt C d Q := by
  have hc : Prob.cnt (fun c : GChal d.entry.work (C.Ch d.entry d.kind) =>
      Q (C.dr d.entry d.kind (GChal.old c))) ≤
      Prob.cnt (fun c : C.Ch d.entry d.kind => Q (C.dr d.entry d.kind c)) * 2 ^ d.entry.work :=
    Prob.cnt_comp_le (GChal.old (b := d.entry.work)) (gchal_fib d.entry.work)
      (fun c => Q (C.dr d.entry d.kind c))
  have hh : pr (unif (TypedOracleCompiler.Run.PQ.roundS C d.toRD).up.Chal)
      {c | Q (C.dr d.entry d.kind (GChal.old (b := d.entry.work) c))} ≤ _ :=
    pr_unif_le_of_cnt_le hc
  refine hh.trans (le_of_eq ?_)
  have hcard : (Fintype.card (TypedOracleCompiler.Run.PQ.roundS C d.toRD).up.Chal : ℝ≥0∞) =
      (Nat.card (C.Ch d.entry d.kind) : ℝ≥0∞) * ((2 ^ d.entry.work : ℕ) : ℝ≥0∞) := by
    rw [← Nat.cast_mul, ← gchal_card, Nat.card_eq_fintype_card]
  unfold shareAt
  rw [hcard, Nat.cast_mul]
  have h2 : ((2 ^ d.entry.work : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_ne_zero (by positivity)).ne'
  have h3 : ((2 ^ d.entry.work : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  exact ENNReal.mul_div_mul_right _ _ h2 h3

/-- The first of several rounds, at every fixing of those behind it. -/
theorem head_fibre_le (r : Iop.Round) (s : Iop.Shape) (T : Set (r.Chal × Iop.Rho s)) (p : ℝ≥0∞)
    (h : ∀ u : Iop.Rho s, pr (unif r.Chal) {c | (c, u) ∈ T} ≤ p) :
    Iop.prRho (s := r :: s) T ≤ p := mean_le T p h

/-- **One round, at every fixing of all others.** Here P is an event on all that the rounds show. -/
theorem inner_le (C : CK) (a : List RDT) (d : RDT) (b : List RDT) (P : List Fmt.Drawn → Prop)
    (p : ℝ≥0∞)
    (h : ∀ pre post : List Fmt.Drawn, pre.length = a.length →
      shareAt C d (fun R => P (pre ++ R :: post)) ≤ p) :
    Iop.prRho {ρ : Iop.Rho (uLT C (a ++ d :: b)) | P (drawnT C (a ++ d :: b) ρ)} ≤ p := by
  have hT : ∀ x : Iop.Rho (uLT C a),
      Iop.prRho {y : Iop.Rho (uLT C (d :: b)) | P (drawnT C a x ++ drawnT C (d :: b) y)} ≤ p := by
    intro x
    refine head_fibre_le (TypedOracleCompiler.Run.PQ.roundS C d.toRD).up (uLT C b) _ p fun u => ?_
    exact (chal_le C d fun R => P (drawnT C a x ++ R :: drawnT C b u)).trans
      (h (drawnT C a x) (drawnT C b u) (drawnT_len C a x))
  have h2 := fibre_le C a (d :: b) ∅
    (fun x => {y : Iop.Rho (uLT C (d :: b)) | P (drawnT C a x ++ drawnT C (d :: b) y)})
    {ρ : Iop.Rho (uLT C (a ++ d :: b)) | P (drawnT C (a ++ d :: b) ρ)} 0 p
    (Iop.prRho_empty _ fun _ hx => hx)
    (fun x y hxy _ => by
      have h3 : P (drawnT C (a ++ d :: b) (joinR C a (d :: b) x y)) := hxy
      rw [drawn_join] at h3
      exact h3)
    (fun x _ => hT x)
  rwa [zero_add] at h2

/-! ## 2 The second test's events -/

/-- The factor of the planes' value in the leaves' claim is 0, or has a word at or above the prime.
-/
def leafBad (f : LFace) (ds : List Fmt.Drawn) : Bool :=
  let p := ptsOf f 0 ds
  let x := f.leaf p.theta p.alpha (leavesR f 0 ds)
  !(okE x && !isZeroE x)

/-- The events on one round's sample. -/
def outEvents (f : LFace) : List Event := (spotsOut f).flatMap eventsAtSpot

theorem goodOut_eq (f : LFace) (ds : List Fmt.Drawn) :
    goodK3Out f ds = ((spotsOut f).all (Spot.fine f ds) && !leafBad f ds) := by
  unfold goodK3Out leafBad
  simp only [Bool.not_not]

theorem one_of_out (f : LFace) : ∀ p ∈ spotsOut f, p.one = true := by
  intro p hp
  unfold spotsOut at hp
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_singleton] at hp
  rcases hp with ((⟨x, -, (⟨l, -, rfl⟩ | rfl)⟩ | ⟨l, -, rfl⟩) | ⟨l, -, rfl⟩) <;> rfl

/-- With the last event the list is as long as Honest/K3/GoodDraws.lean counts. -/
theorem outEvents_length (f : LFace) : (outEvents f).length + 1 = eventsOut f := by
  unfold outEvents eventsOut
  rw [length_flat]
  have h : ∀ l : List Spot, (∀ p ∈ l, p.one = true) →
      (l.map fun p => if p.one then 2 else 1).sum = 2 * l.length := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons p l ih =>
      intro hl
      rw [List.map_cons, List.sum_cons, ih fun q hq => hl q (List.mem_cons_of_mem _ hq),
        hl p List.mem_cons_self, List.length_cons]
      simp only [if_true]
      omega
  rw [h _ (one_of_out f)]

/-! ## 3 The hypotheses and the bound -/

/-- **There is a round of whose challenges, at every fixing of all other rounds, at most the share
kap make the factor 0 or give it a word at or above the prime** (`leafBad`). -/
def LeafFew (C : CK) (f : LFace) (dsb : List RDT) (kap : ℝ≥0∞) : Prop :=
  ∃ (a : List RDT) (d : RDT) (b : List RDT), dsb = a ++ d :: b ∧
    ∀ pre post : List Fmt.Drawn, pre.length = a.length →
      shareAt C d (fun R => leafBad f (pre ++ R :: post) = true) ≤ kap

/-- The hypotheses on the kit for the second mark. -/
def FewOut (C : CK) (f : LFace) (dsb : List RDT) (kap : ℝ≥0∞) : Prop :=
  (∀ e ∈ outEvents f, FewAt C f dsb kap e) ∧ LeafFew C f dsb kap

theorem leaf_le (C : CK) (f : LFace) (dsb : List RDT) (kap : ℝ≥0∞) (h : LeafFew C f dsb kap) :
    Iop.prRho {ρ : Iop.Rho (uLT C dsb) | leafBad f (drawnT C dsb ρ) = true} ≤ kap := by
  obtain ⟨a, d, b, rfl, hs⟩ := h
  exact inner_le C a d b (fun ds => leafBad f ds = true) kap hs

/-- **What the lookup owes for its second mark**, written out. -/
theorem markOut_le (C : CK) (a : Place) (f : LFace) (dsb : List RDT) (kap : ℝ≥0∞)
    (hc : CanAll C f dsb) (hf : FewOut C f dsb kap) (fr : List Fmt.Drawn) :
    Iop.prRho {ρ : Iop.Rho (uLT C dsb) |
        ((markOut a f).test fr (drawnT C dsb ρ)).isSome = true} ≤ (eventsOut f : ℝ≥0∞) * kap := by
  rw [← outEvents_length, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  refine le_trans (pr_mono _ ?_) (le_trans (pr_union_le _ _ _)
    (add_le_add (events_le C f dsb kap (outEvents f) hf.1) (leaf_le C f dsb kap hf.2)))
  intro ρ hρ
  have h1 : ((markOut a f).test fr (drawnT C dsb ρ)).isSome = true := hρ
  have hg : goodK3Out f (drawnT C dsb ρ) = false := by
    cases hq : goodK3Out f (drawnT C dsb ρ) with
    | false => rfl
    | true =>
      have h0 : ((markOut a f).test fr (drawnT C dsb ρ)).isSome = false := by
        unfold markOut
        simp [hq]
      rw [h0] at h1
      cases h1
  rw [goodOut_eq] at hg
  cases hl : leafBad f (drawnT C dsb ρ) with
  | true => exact Or.inr hl
  | false =>
    rw [hl] at hg
    have hs : (spotsOut f).all (Spot.fine f (drawnT C dsb ρ)) = false := by simpa using hg
    obtain ⟨p, hp, hq⟩ := notFine_of_all hs
    obtain ⟨e, he, hh⟩ := event_of_notFine (ok_value f _ (hc ρ) p) hq
    exact Or.inl ⟨e, List.mem_flatMap.2 ⟨p, hp, he⟩, hh⟩

/-- **At the frame's own name.** -/
theorem markOut_debt (C : CK) (a : Place) (f : LFace) (dsb : List RDT) (kap : ℝ≥0∞)
    (hc : CanAll C f dsb) (hf : FewOut C f dsb kap) :
    MarkDebt C (markOut a f) dsb (fun _ => True) ((eventsOut f : ℝ≥0∞) * kap) :=
  fun fr _ => markOut_le C a f dsb kap hc hf fr

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.mean_eq
#print axioms ProofFile.Honest.K3.Good.mean_le
#print axioms ProofFile.Honest.K3.Good.chal_le
#print axioms ProofFile.Honest.K3.Good.head_fibre_le
#print axioms ProofFile.Honest.K3.Good.inner_le
#print axioms ProofFile.Honest.K3.Good.goodOut_eq
#print axioms ProofFile.Honest.K3.Good.one_of_out
#print axioms ProofFile.Honest.K3.Good.outEvents_length
#print axioms ProofFile.Honest.K3.Good.leaf_le
#print axioms ProofFile.Honest.K3.Good.markOut_le
#print axioms ProofFile.Honest.K3.Good.markOut_debt
