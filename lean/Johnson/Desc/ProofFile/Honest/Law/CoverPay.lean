-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverPay.lean: WHAT THE FRAME ITSELF PAYS OF A CHAIN's DEBTS.
`debt_join` (Honest/Law/CoverJoin.lean) takes a premise hfront: how the walk stands in front of the
member, and what the owners are handed. Here: (1) how it stands: `front_stand`: in front of a member
with a round the members still to do are that member and those behind it, and no round is laid for
it; `front_open`: in front of any border the member that is being played has more rounds than are
laid for it; (2) THE ZEROS: `debt_zero`: at a member with a round at whose place no mark speaks at
any typed message of its rounds, and at whose group no fall sits; `debt_zero_quiet`: at a member
WITHOUT a round at whose place no mark speaks so: `DebtAt` at Q := `silentQ`, at any number; (3) THE
STOPS' MARKS STAND AT EVERY MEMBER: at one without a half, or whose half never stops, they never
speak (`stopMarks_none`, `stop_noHalf`): so the zeros can be had with the stops laid as marks; and
where the marks hold the stops' marks, `silentQ` gives `stopQ` (Honest/Law/CoverStops.lean): no part
in front has stopped.

WHAT THIS IS. Lemmas on our own walk and definitions; the zeros are on the library's own measure.
None of the library's goals.

  1  `front_stand`, `front_open`
  2  `debt_zero`, `debt_zero_rest`, `debt_zero_quiet`
  3  `stopMarks_none`, `stop_noHalf`, `marksQuiet_stops`, `stopQ_of_silent`

hX: what a chain's walk starts from is a start of the frame's own (`ChainProgress.start`), with the prover's
run in hand, FROM SOME STATE OF THE VERIFIER's, at some columns handed. At a file's first and shared
chain `at₁_starts` and `at₂_starts` (Honest/Law/CoverAll.lean) pay it: these chains name their first
state outright. NOT AT THE SECOND CHAIN WHERE AN EARLIER CHAIN CAN REJECT: there `door₃`
(Honest/Walk.lean) is `none` and the walk still starts, with no verifier's state and no place that
refused, which no start from a state gives; `at₃_starts` takes as a premise that the state is there.
So the three zeros, and what calls them (Honest/Law/CoverSparse.lean, CoverSeated.lean,
CoverSorts.lean, CoverOwn.lean), do not serve there as they stand. The second chain's debts are paid
without them (`localDebts_noFall`, Honest/Law/CoverNoFall.lean; `falls_first`,
Honest/Law/CoverEnd.lean). For this file's lemmas that limit is one of the premise's form: `hm` and
the state `s₀` stand in no end of this file; `hm` is spent only to turn `start_tied`'s `if`
(`front_stand`, `front_open`), and `walk_tied` and `tied_at` stand at any `Option S`. No front or
zero is stated here without them.

Limits. `debt_zero` stands where no fixed challenge stands behind the member's own; at a chain's
last gated member `debt_zero_rest` serves, which asks that no fall sits at ANY member from there on.
This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverJoin
import Johnson.Desc.ProofFile.Honest.Law.CoverStops

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

variable {S Cl V W Y : Type}

/-! ## 1 How the walk stands in front -/

/-- **In front of a member with a round.** pre: the members in front of b; t: those behind it. -/
theorem front_stand (L : Lay) (all pre t : List (Block S Cl)) (b : Block S Cl) {a z : ChainProgress S Cl W Y}
    {s₀ : S} {m₀ : Option (Mid W Y)} {ss' : List (Step W Y)} {dA : List Fmt.Drawn}
    {front : List OpenedColumn} (hm : m₀.isSome = true) (ha : ChainProgress.start L all m₀ (some s₀) front = .ok a)
    (hb : all = pre ++ b :: t) (hpos : 0 < b.rounds.length) (hz : walk L ss' dA a = .ok z)
    (hl : ss'.length = (pre.flatMap (·.rounds)).length) : z.todo = b :: t ∧ z.own = [] := by
  obtain ⟨t0, o0, l0⟩ := start_tied L all m₀ (some s₀) ha
  rw [if_pos hm] at t0
  obtain ⟨t1, o1, l1⟩ := walk_tied L all (some s₀) _ _ a z t0 o0 hz
  exact tied_at L all pre t b (some s₀) t1 o1 hb hpos
    (by rw [l1, l0, hl, List.length_nil, Nat.zero_add])

/-- **In front of any border** the walk is open. -/
theorem front_open (L : Lay) (all : List (Block S Cl)) {a z : ChainProgress S Cl W Y} {s₀ : S}
    {m₀ : Option (Mid W Y)} {ss' : List (Step W Y)} {dA : List Fmt.Drawn}
    {front : List OpenedColumn} (hm : m₀.isSome = true) (ha : ChainProgress.start L all m₀ (some s₀) front = .ok a)
    (hz : walk L ss' dA a = .ok z) : z.Open := by
  obtain ⟨t0, o0, -⟩ := start_tied L all m₀ (some s₀) ha
  rw [if_pos hm] at t0
  exact (walk_tied L all (some s₀) _ _ a z t0 o0 hz).2.1

/-! ## 2 The zeros -/

section
variable (C : CK) (all : List (Block S Cl)) (fs : List (Fall S)) (ms : List Mark) (skip : Nat)
  (X : List Fmt.Drawn → ChainAt S Cl W Y) (p : Nat → ℝ≥0∞)
  (hX : ∀ base a, (X base).start = some a → ∃ (m₀ : Option (Mid W Y)) (s₀ : S) (front : List OpenedColumn),
    m₀.isSome = true ∧ ChainProgress.start (X base).lay all m₀ (some s₀) front = .ok a)
include hX

/-- **NOTHING SITS HERE: 0: a member with a round.** -/
theorem debt_zero (bs pre t : List (Block S Cl)) {b : Block S Cl} {j n : Nat} {dsb : List RDT}
    {last : Bool} (hj : bs[j]? = some b) (hn : n = ((bs.take j).flatMap (·.rounds)).length)
    (hlen : dsb.length = b.rounds.length) (hb : all = pre ++ b :: t)
    (hpre : (pre.flatMap (·.rounds)).length = n) (hpos : 0 < b.rounds.length)
    (hmk : ∀ fr (ρ : Iop.Rho (uLT C dsb)), markOf ms b.place fr (drawnT C dsb ρ) = none)
    (hfl : ∀ d ∈ groupOf b t, ∀ f ∈ fs, f.place ≠ d.place) :
    DebtAt C all fs ms skip X p (silentQ ms skip bs) b j n dsb [] last := by
  intro fr h1 h2 h3 h4
  refine ⟨zero_of_not C dsb _ (fun ρ hρ => ?_) _, fun _ ρ hm _ =>
    silentQ_step ms skip bs hj fr _ h1 (by rw [h2, hn]) (by rw [drawnT_len, hlen]) h4 hm⟩
  rcases hρ with hm | ⟨a, z, s', y1, y2, y3, y4⟩
  · rw [hmk] at hm
    cases hm
  · obtain ⟨m₀, s₀, _, g1, g2⟩ := hX _ a y1
    have hw := walk_len _ _ _ _ _ y2
    obtain ⟨e1, e2⟩ := front_stand _ all pre t b g1 g2 hb hpos y2 (by rw [← hw, h2, hpre])
    refine runFall_group e1 ?_ hfl y4
    rw [e2, List.append_nil, drawnT_len, hlen, List.length_nil, Nat.zero_add]

/-- **NOTHING SITS FROM HERE ON: 0**: a member with a round at which, and behind which, no fall of
the list sits: at whatever fixed challenges tl stand behind its own: so at a chain's last gated
member too. -/
theorem debt_zero_rest (bs pre t : List (Block S Cl)) {b : Block S Cl} {j n : Nat}
    {dsb : List RDT} {tl : List Fmt.Drawn} {last : Bool} (hj : bs[j]? = some b)
    (hn : n = ((bs.take j).flatMap (·.rounds)).length) (hlen : dsb.length = b.rounds.length)
    (hb : all = pre ++ b :: t) (hpre : (pre.flatMap (·.rounds)).length = n)
    (hpos : 0 < b.rounds.length)
    (hmk : ∀ fr (ρ : Iop.Rho (uLT C dsb)), markOf ms b.place fr (drawnT C dsb ρ) = none)
    (hfl : ∀ d ∈ b :: t, ∀ f ∈ fs, f.place ≠ d.place) :
    DebtAt C all fs ms skip X p (silentQ ms skip bs) b j n dsb tl last := by
  intro fr h1 h2 h3 h4
  refine ⟨zero_of_not C dsb _ (fun ρ hρ => ?_) _, fun _ ρ hm _ =>
    silentQ_step ms skip bs hj fr _ h1 (by rw [h2, hn]) (by rw [drawnT_len, hlen]) h4 hm⟩
  rcases hρ with hm | ⟨a, z, s', y1, y2, y3, z', ps, cs, -, -, -, y4⟩
  · rw [hmk] at hm
    cases hm
  · obtain ⟨m₀, s₀, _, g1, g2⟩ := hX _ a y1
    have hw := walk_len _ _ _ _ _ y2
    obtain ⟨e1, -⟩ := front_stand _ all pre t b g1 g2 hb hpos y2 (by rw [← hw, h2, hpre])
    rw [e1, chainFall_none fs _ (b :: t) hfl] at y4
    cases y4

/-- **NOTHING SITS HERE: 0: a member without a round.** -/
theorem debt_zero_quiet (bs : List (Block S Cl)) {b : Block S Cl} {j n : Nat} {dsb : List RDT}
    {last : Bool} (hj : bs[j]? = some b) (hn : n = ((bs.take j).flatMap (·.rounds)).length)
    (hlen : dsb.length = b.rounds.length) (hr : b.rounds = [])
    (hmk : ∀ fr (ρ : Iop.Rho (uLT C dsb)), markOf ms b.place fr (drawnT C dsb ρ) = none) :
    DebtAt C all fs ms skip X p (silentQ ms skip bs) b j n dsb [] last := by
  intro fr h1 h2 h3 h4
  refine ⟨zero_of_not C dsb _ (fun ρ hρ => ?_) _, fun _ ρ hm _ =>
    silentQ_step ms skip bs hj fr _ h1 (by rw [h2, hn]) (by rw [drawnT_len, hlen]) h4 hm⟩
  rcases hρ with hm | ⟨a, z, s', y1, y2, y3, y4⟩
  · rw [hmk] at hm
    cases hm
  · obtain ⟨m₀, s₀, _, g1, g2⟩ := hX _ a y1
    have ho := front_open _ all g1 g2 y2
    have hext : (drawnT C dsb ρ ++ []).length = 0 := by
      rw [List.append_nil, drawnT_len, hlen, hr]
      rfl
    cases ht : z.todo with
    | nil => exact runFall_nil ht y4
    | cons c t' =>
      refine runFall_short ht ?_ y4
      rw [hext, Nat.add_zero]
      exact ho c t' ht

end

/-! ## 3 The silence gives «no part in front has stopped» -/

section
variable (v : Option V) (hs : List (Placed V W Y)) (skip : Nat)
  (loc₀ : List Fmt.Drawn → List Fmt.Drawn) (sh : Place → Odds)

/-- **The stops' marks at a place never speak where the members of that place have no half, or one
that never stops**; with further marks ms of which none stands there. So the zeros' premise hmk can
be had with the stops laid as marks. -/
theorem stopMarks_none (all : List (Block S Cl)) (ms : List Mark) (a : Place)
    (h : ∀ c ∈ all, c.place = a → ∀ loc own, chainStopAt v [c] hs loc own = none)
    (hms : ∀ m ∈ ms, m.place ≠ a) (fr own : List Fmt.Drawn) :
    markOf (stopMarks v hs skip loc₀ sh all ++ ms) a fr own = none := by
  cases hc : markOf (stopMarks v hs skip loc₀ sh all ++ ms) a fr own with
  | none => rfl
  | some _ =>
    exfalso
    obtain ⟨mk, hmk, ht⟩ := markOf_mem (ms := stopMarks v hs skip loc₀ sh all ++ ms) (a := a)
      (fr := fr) (own := own) (by rw [hc]; rfl)
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hmk
    rcases List.mem_append.1 h1 with g | g
    · obtain ⟨c, hcA, rfl⟩ := List.mem_map.1 g
      have ht' : ((chainStopAt v [c] hs (loc₀ (fr.take skip) ++ fr.drop skip) own).map
        fun _ => "a part stops").isSome = true := ht
      rw [h c hcA (eq_of_beq h2)] at ht'
      cases ht'
    · exact hms mk g (eq_of_beq h2)

/-- A member at whose place no half stands: nothing stops. -/
theorem stop_noHalf (c : Block S Cl) (hn : (hs.find? fun g => g.place == c.place) = none)
    (loc own : List Fmt.Drawn) : chainStopAt v [c] hs loc own = none := by
  unfold chainStopAt
  rw [hn]
  rfl

/-- all: the list of which the stops' marks are made; A: members of it. base: the challenges in
front of the chain; f: the chain's own in front of A; r: A's own. -/
theorem marksQuiet_stops (all : List (Block S Cl)) (ms : List Mark) (base : List Fmt.Drawn)
    (hbase : base.length = skip) : ∀ (A : List (Block S Cl)) (f r : List Fmt.Drawn),
    (∀ c ∈ A, c ∈ all) →
    marksQuiet (stopMarks v hs skip loc₀ sh all ++ ms) A (base ++ f) r = true →
    chainStopAt v A hs (loc₀ base ++ f) r = none
  | [], _, _, _, _ => rfl
  | c :: A, f, r, hA, h => by
    have h' : ((markOf (stopMarks v hs skip loc₀ sh all ++ ms) c.place (base ++ f)
        (r.take c.rounds.length)).isNone &&
      marksQuiet (stopMarks v hs skip loc₀ sh all ++ ms) A
        (base ++ f ++ r.take c.rounds.length) (r.drop c.rounds.length)) = true := h
    rw [Bool.and_eq_true] at h'
    obtain ⟨h1, h2⟩ := h'
    have s1 := stop_silent v hs skip loc₀ sh all ms (hA c List.mem_cons_self) (base ++ f)
      (r.take c.rounds.length) (by
        cases hm : markOf (stopMarks v hs skip loc₀ sh all ++ ms) c.place (base ++ f)
          (r.take c.rounds.length) with
        | none => rfl
        | some _ =>
          rw [hm] at h1
          cases h1)
    rw [← hbase, List.take_left' rfl, List.drop_left' rfl] at s1
    rw [List.append_assoc] at h2
    have s2 := marksQuiet_stops all ms base hbase A (f ++ r.take c.rounds.length)
      (r.drop c.rounds.length) (fun d hd => hA d (List.mem_cons_of_mem _ hd)) h2
    have e : chainStopAt v (c :: A) hs (loc₀ base ++ f) r =
        (chainStopAt v [c] hs (loc₀ base ++ f) (r.take c.rounds.length)).or
          (chainStopAt v A hs (loc₀ base ++ f ++ r.take c.rounds.length)
            (r.drop c.rounds.length)) := by
      have e0 := chainStopAt_append v hs [c] A (loc₀ base ++ f) r
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at e0
      exact e0
    rw [e, s1, List.append_assoc, s2]
    rfl

/-- **Where the marks hold the stops' marks, the silence says that no part in front has
stopped.** -/
theorem stopQ_of_silent (bs : List (Block S Cl)) (ms : List Mark) (j : Nat) (fr : List Fmt.Drawn)
    (hsk : skip ≤ fr.length)
    (h : silentQ (stopMarks v hs skip loc₀ sh bs ++ ms) skip bs j fr) :
    stopQ v hs skip loc₀ bs j fr := by
  unfold silentQ at h
  unfold stopQ
  have h' := marksQuiet_stops v hs skip loc₀ sh bs ms (fr.take skip)
    (by rw [List.length_take, Nat.min_eq_left hsk]) (bs.take j) [] (fr.drop skip)
    (fun c hc => List.mem_of_mem_take hc) (by rw [List.append_nil]; exact h)
  rw [List.append_nil] at h'
  exact h'

end

end ProofFile.Honest

#print axioms ProofFile.Honest.front_stand
#print axioms ProofFile.Honest.front_open
#print axioms ProofFile.Honest.debt_zero
#print axioms ProofFile.Honest.debt_zero_rest
#print axioms ProofFile.Honest.debt_zero_quiet
#print axioms ProofFile.Honest.stopMarks_none
#print axioms ProofFile.Honest.stop_noHalf
#print axioms ProofFile.Honest.marksQuiet_stops
#print axioms ProofFile.Honest.stopQ_of_silent
