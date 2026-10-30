-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverLocal.lean: FROM A CANONICAL GATE's TEST TO AN EVENT AT ONE
MEMBER: NARROW AND WIDE. `runFall`, THE NARROW EVENT: the walk on from the stand in front of a
member, over that member's Steps at its own challenges, returns, and the members still to do meet a
fall from the verifier's state s' ON WHAT THAT WALK HAS LAID AND FILLED SINCE. `localFall`, THE WIDE
EVENT: THERE ARE rounds with these challenges, and columns, at which they meet a fall from s': no
walk, no prover, no coin and no input is in it: a sentence on the description's own steps and the
falls' tests. The narrow gives the wide (`run_local`). Where a canonical gate
(Honest/Law/CoverChain.lean) speaks anew of a fall, the wide event holds (`speaks_local`; the
narrow: `speaks_at`, Honest/Law/CoverHeld.lean).

WHAT THIS IS. A definition, and lemmas on the frame's own walk. No measure is in this file. None of
the library's goals.

  0  `walk_shows`   a walk lays each round with the challenge that it is handed
  1  `tied_at`   in front of a member with a round the walk has asked just the members in front
  2  `runFall`, `localFall`, `run_local`, `speaks_local`   the two events

OVER WHOSE LEMMAS. `walk_shows` (a walk lays each round with the challenge that it is handed) has
the statement of `walk_drawn` (Honest/K8/FrontsStep.lean, other authors', who had it first) and of
`walk_laid_drawn` (Honest/WalkHeard.lean), which is its proof here; the name stays for its callers.
From `localFall` the same authors' frontsOf_zero | frontsOf_step lead on to «the member's own step
returns t, and a member without a round behind it falls at t»: the form of their counts and of other
authors'.

Limits. THE WIDE EVENT CAN BE UNMEETABLE BUT BY 1: it runs over ALL rounds and columns with these
challenges. For a fall seated at the member itself that is idle (its test reads s' and the
challenges). For a fall at a member without a round behind it: «the member's step returns t at SOME
rounds and columns, and the test speaks at t»: where the member's rounds state no item and open
nothing that is what the run does; AT A MEMBER WHOSE ROUNDS SEND ITEMS THAT ITS STEP LAYS INTO THE
STATE the wide event picks the items, and may hold at every challenge: there the narrow event is the
one to bound. Nothing says that s' meets a thread's sentence. This file proves nothing about
soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverNew
import Johnson.Desc.ProofFile.Honest.Law.RunMid
import Johnson.Desc.ProofFile.Honest.Law.RunAtFile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl W Y : Type}

/-! ## 1 In front of a member with a round -/

/-- **A walk lays each round with the challenge that it is handed.** -/
theorem walk_shows (L : Lay) : ∀ (l : List (Step W Y)) (d : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y), walk L l d z = .ok z' →
    z'.laid.map (·.drawn) = z.laid.map (·.drawn) ++ d :=
  walk_laid_drawn L

/-- **In front of a member with a round the walk has asked just the members in front of it**, and
has laid no round for it. -/
theorem tied_at (L : Lay) (bs pre t : List (Block S Cl)) (b : Block S Cl) (v₀ : Option S)
    {z : ChainProgress S Cl W Y} (ht : ChainProgress.Tied L bs v₀ z.todo z) (ho : z.Open)
    (hb : bs = pre ++ b :: t) (hpos : 0 < b.rounds.length)
    (hl : z.laid.length = (pre.flatMap (·.rounds)).length) : z.todo = b :: t ∧ z.own = [] := by
  obtain ⟨done, front, e1, e2, e3, -, -⟩ := ht
  have hlen : front.length + z.own.length = (pre.flatMap (·.rounds)).length := by
    rw [← hl, e2, List.length_append]
  rw [hb] at e1
  rcases List.append_eq_append_iff.1 e1 with ⟨a', ha, hb'⟩ | ⟨c', hc, hd⟩
  · -- done = pre ++ a'
    cases a' with
    | nil =>
      rw [List.append_nil] at ha
      rw [List.nil_append] at hb'
      refine ⟨hb'.symm, ?_⟩
      rw [ha] at e3
      exact List.eq_nil_of_length_eq_zero (by omega)
    | cons x a'' =>
      exfalso
      rw [List.cons_append] at hb'
      obtain ⟨hx, -⟩ := List.cons.inj hb'
      subst hx
      rw [ha, List.flatMap_append, List.length_append, List.flatMap_cons,
        List.length_append] at e3
      omega
  · -- pre = done ++ c'
    cases c' with
    | nil =>
      rw [List.append_nil] at hc
      rw [List.nil_append] at hd
      refine ⟨hd, ?_⟩
      rw [← hc] at e3
      exact List.eq_nil_of_length_eq_zero (by omega)
    | cons x c'' =>
      exfalso
      rw [List.cons_append] at hd
      have h1 := ho x _ hd
      rw [hc, List.flatMap_append, List.length_append, List.flatMap_cons,
        List.length_append] at hlen
      omega

/-! ## 2 The local event -/

/-- **The narrow event.** z: the walk's stand in front; ss': the Steps from there on; ext: their
challenges. The walk on from z returns, and the members that z has still to do meet a fall from s'
on the rounds that z has laid for the first of them and those laid since, and on the columns filled
since. -/
def runFall (fs : List (Fall S)) (L : Lay) (ss' : List (Step W Y)) (z : ChainProgress S Cl W Y) (s' : S)
    (ext : List Fmt.Drawn) : Prop :=
  ∃ (z' : ChainProgress S Cl W Y) (ps : List Played) (cs : List OpenedColumn), walk L ss' ext z = .ok z' ∧
    z'.laid = z.laid ++ ps ∧ z'.cols = z.cols ++ cs ∧
    (chainFall fs L.firstTree z.todo s' ⟨roundsOf (z.own ++ ps), cs⟩).isSome = true

/-- **The wide event**: there are rounds with the challenges own, and columns, at which the members
todo meet a fall from the state s'. -/
def localFall (fs : List (Fall S)) (ft : Nat) (todo : List (Block S Cl)) (s' : S)
    (own : List Fmt.Drawn) : Prop :=
  ∃ (rs : List Fmt.RoundView) (cols : List OpenedColumn), rs.map (·.drawn) = own ∧
    (chainFall fs ft todo s' ⟨rs, cols⟩).isSome = true

/-- **The narrow event gives the wide one.** -/
theorem run_local {fs : List (Fall S)} {L : Lay} {ss' : List (Step W Y)} {z : ChainProgress S Cl W Y}
    {s' : S} {ext : List Fmt.Drawn} (h : runFall fs L ss' z s' ext) :
    localFall fs L.firstTree z.todo s' (z.own.map (·.drawn) ++ ext) := by
  obtain ⟨z', ps, cs, hw, g2, -, g4⟩ := h
  refine ⟨roundsOf (z.own ++ ps), cs, ?_, g4⟩
  have hdw := walk_shows L _ _ z z' hw
  rw [g2, List.map_append] at hdw
  have h3 := List.append_cancel_left hdw
  rw [← h3]
  unfold roundsOf
  rw [List.map_map, List.map_append]
  rfl

/-- **Where a canonical gate speaks anew of a fall, the wide event holds.** a: the chain's start.
n: the rounds in front of the member b; k: how far the gate walks on. dr: the chain's challenges.
`front`: whatever columns the start was handed; the end does not read it. -/
theorem speaks_local (fs : List (Fall S)) (bs pre t : List (Block S Cl)) (b : Block S Cl)
    {X : ChainAt S Cl W Y} {a : ChainProgress S Cl W Y} {s₀ : S} {m₀ : Option (Mid W Y)}
    (hs : X.start = some a) (h0 : X.s₀ = some s₀) (hm : m₀.isSome = true)
    {front : List OpenedColumn} (ha : ChainProgress.start X.lay bs m₀ (some s₀) front = .ok a)
    (hb : bs = pre ++ b :: t)
    (hpos : 0 < b.rounds.length) (k : Nat) (dr : List Fmt.Drawn)
    (hd : (pre.flatMap (·.rounds)).length + k ≤ dr.length)
    (hss : (pre.flatMap (·.rounds)).length + k ≤ X.steps.length)
    (f0 : fellBy bs fs X (pre.flatMap (·.rounds)).length dr = false)
    (f1 : fellBy bs fs X ((pre.flatMap (·.rounds)).length + k) dr = true) :
    ∃ z s', walk X.lay (X.steps.take (pre.flatMap (·.rounds)).length)
        (dr.take (pre.flatMap (·.rounds)).length) a = .ok z ∧ z.ver = some s' ∧
      localFall fs X.lay.firstTree (b :: t) s'
        ((dr.drop (pre.flatMap (·.rounds)).length).take k) := by
  obtain ⟨N, hN⟩ : ∃ N, N = (pre.flatMap (·.rounds)).length := ⟨_, rfl⟩
  rw [← hN] at hd hss f0 f1 ⊢
  -- the longer walk returns, and goes through the shorter one
  cases hw' : walk X.lay (X.steps.take (N + k)) (dr.take (N + k)) a with
  | error e =>
    unfold fellBy at f1
    rw [hs, h0] at f1
    simp only at f1
    rw [hw'] at f1
    cases f1
  | ok z' =>
    have e1 : X.steps.take (N + k) = X.steps.take N ++ (X.steps.drop N).take k := List.take_add
    have e2 : dr.take (N + k) = dr.take N ++ (dr.drop N).take k := List.take_add
    have hw'' := hw'
    rw [e1, e2] at hw''
    obtain ⟨z, hz, hzz⟩ := walk_append_ok _ _ _ _ a z' (by
      rw [List.length_take, List.length_take]
      omega) hw''
    rw [fellBy_ok bs fs hs h0 hz] at f0
    rw [fellBy_ok bs fs hs h0 hw'] at f1
    obtain ⟨t0, o0, l0⟩ := start_tied X.lay bs m₀ (some s₀) ha
    rw [if_pos hm] at t0
    obtain ⟨t1, o1, l1⟩ := walk_tied X.lay bs (some s₀) _ _ a z t0 o0 hz
    have hl : z.laid.length = (pre.flatMap (·.rounds)).length := by
      rw [l1, l0, List.length_nil, Nat.zero_add, List.length_take, ← hN]
      omega
    obtain ⟨q1, q2⟩ := tied_at X.lay bs pre t b (some s₀) t1 o1 hb hpos hl
    have f0' : chainFall fs X.lay.firstTree bs s₀ ⟨roundsOf z.laid, z.cols⟩ = none := by
      cases hc : chainFall fs X.lay.firstTree bs s₀ ⟨roundsOf z.laid, z.cols⟩ with
      | none => rfl
      | some _ =>
        rw [hc] at f0
        cases f0
    obtain ⟨s', ps, cs, g1, g2, -, g4⟩ := new_fall fs X.lay bs s₀ t1 hzz f0' f1
    refine ⟨z, s', hz, g1, roundsOf ps, cs, ?_, ?_⟩
    · have hdw := walk_shows X.lay _ _ z z' hzz
      rw [g2, List.map_append] at hdw
      have h3 := List.append_cancel_left hdw
      rw [← h3]
      unfold roundsOf
      rw [List.map_map]
      rfl
    · rw [q1, q2, List.nil_append] at g4
      exact g4

end ProofFile.Honest

#print axioms ProofFile.Honest.walk_shows
#print axioms ProofFile.Honest.tied_at
#print axioms ProofFile.Honest.run_local
#print axioms ProofFile.Honest.speaks_local
#print axioms ProofFile.Honest.runFall
#print axioms ProofFile.Honest.localFall
