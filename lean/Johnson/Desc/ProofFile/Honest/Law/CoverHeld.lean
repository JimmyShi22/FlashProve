-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverHeld.lean: FROM BOUNDS A MEMBER TO `GatesHeld` AT ONE CHAIN's
CANONICAL GATES. `falls_held_canon` (Honest/Law/CoverFile.lean) leaves `GatesHeld` at gates whose
tests ask walks over fronts. Here that is paid from bounds on events at ONE member each: «a mark at
this place speaks, or: the walk over the rounds in front holds a verifier's state s', and, walking
on over this member's Steps at its own challenges, the members still to do meet a fall from s' on
what is laid since» (`runFall`, Honest/Law/CoverLocal.lean: the narrow event). Each bound is asked
only at fronts BY WHICH THE RUN HAS MET NO FALL and which a letter Q lets in. A bound on the wide
event (`localWide`: the mark, or the walk over the front and then `localFall`, in which no walk,
prover, coin or input stands) pays too (`bound_of_wide`).

WHAT THIS IS. Definitions (premises' forms), and a conditional lemma on our own walk and the
library's own measure (`Iop.prRho`). The kit C is a letter. None of the library's goals.

Q: A LETTER THAT IS CARRIED DOWN THE CHAIN: whatever is to be known of a front at which no earlier
gate has spoken (that the marks in front are silent; lengths). It holds at the chain's start, and
goes on past a member whose mark is silent and by whose last round the run has met no fall: both are
premises.

MET FOR NOTHING. A number of 1 somewhere. Q := False at the start. Where the walk over a front
refuses, or holds no verifier's state, no fall is met anew: only the mark is counted there.

  1  `speaks_at`   where `fellBy` turns from false to true: at any number of rounds
  2  `localAt`, `localWide`, `localAt_wide`, `bound_of_wide`, `LocalDebts`   the events at a member;
     the debts, one a member
  3  `test_local`, `canon_held`   the law

Limits. One chain. That the chain's start has met no fall is a premise. So is `hX`: every start of
the chain's walk comes from `ChainProgress.start` with the prover's run in hand, from the chain's own first
state s₀ where the chain has one (`(X base).s₀ = some s₀`: of another start nothing is asked), at
some columns handed (which ones is not asked: no end here reads them). Nothing says that s' meets a
thread's sentence: whoever pays a debt takes that from the thread. ONE BOUND A MEMBER, ON ALL THE
LIST's FALLS AND MARKS THERE TOGETHER: nothing here splits the event by falls, nor into «at the
member» and «at a member without a round behind it»; the debts go down the list by recursion: in
this file there is no form for one member alone (`DebtAt`, Honest/Law/CoverSplit.lean, is one); and
here no lemma pays «nothing sits here: 0» (`fallDebt_none`, Honest/Law/CoverJoin.lean, and the zeros
of Honest/Law/CoverPay.lean do). This file proves nothing about soundness, completeness, hiding or
any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverLocal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

variable {S Cl W Y : Type}

/-! ## 1 Where `fellBy` turns -/

/-- As `speaks_local`, at any number N of rounds, in the walk's own letters: THE NARROW EVENT. -/
theorem speaks_at (fs : List (Fall S)) (bs : List (Block S Cl)) {X : ChainAt S Cl W Y}
    {a : ChainProgress S Cl W Y} {s₀ : S} {m₀ : Option (Mid W Y)} (hs : X.start = some a)
    (h0 : X.s₀ = some s₀) (hm : m₀.isSome = true)
    {front : List OpenedColumn} (ha : ChainProgress.start X.lay bs m₀ (some s₀) front = .ok a) (N k : Nat)
    (dr : List Fmt.Drawn)
    (hd : N + k ≤ dr.length) (f0 : fellBy bs fs X N dr = false)
    (f1 : fellBy bs fs X (N + k) dr = true) :
    ∃ z s', walk X.lay (X.steps.take N) (dr.take N) a = .ok z ∧ z.ver = some s' ∧
      runFall fs X.lay ((X.steps.drop N).take k) z s' ((dr.drop N).take k) := by
  cases hw' : walk X.lay (X.steps.take (N + k)) (dr.take (N + k)) a with
  | error e =>
    unfold fellBy at f1
    rw [hs, h0] at f1
    simp only at f1
    rw [hw'] at f1
    cases f1
  | ok z' =>
    have hlen := walk_len _ _ _ _ _ hw'
    rw [List.length_take, List.length_take] at hlen
    have e1 : X.steps.take (N + k) = X.steps.take N ++ (X.steps.drop N).take k := List.take_add
    have e2 : dr.take (N + k) = dr.take N ++ (dr.drop N).take k := List.take_add
    have hw'' := hw'
    rw [e1, e2] at hw''
    obtain ⟨z, hz, hzz⟩ := walk_append_ok _ _ _ _ a z' (by
      rw [List.length_take, List.length_take]
      omega) hw''
    rw [fellBy_ok bs fs hs h0 hz] at f0
    rw [fellBy_ok bs fs hs h0 hw'] at f1
    obtain ⟨t0, o0, -⟩ := start_tied X.lay bs m₀ (some s₀) ha
    rw [if_pos hm] at t0
    obtain ⟨t1, -, -⟩ := walk_tied X.lay bs (some s₀) _ _ a z t0 o0 hz
    have f0' : chainFall fs X.lay.firstTree bs s₀ ⟨roundsOf z.laid, z.cols⟩ = none := by
      cases hc : chainFall fs X.lay.firstTree bs s₀ ⟨roundsOf z.laid, z.cols⟩ with
      | none => rfl
      | some _ =>
        rw [hc] at f0
        cases f0
    obtain ⟨s', ps, cs, g1, g2, g3, g4⟩ := new_fall fs X.lay bs s₀ t1 hzz f0' f1
    exact ⟨z, s', hz, g1, z', ps, cs, hzz, g2, g3, g4⟩

/-! ## 2 The events at a member; the debts -/

section
variable (C : CK) (all : List (Block S Cl)) (fs : List (Fall S)) (ms : List Mark) (skip : Nat)
  (X : List Fmt.Drawn → ChainAt S Cl W Y) (p : Nat → ℝ≥0∞) (tail : List Fmt.Drawn)
  (Q : Nat → List Fmt.Drawn → Prop)

/-- **The event at a member.** fr: all challenges in front, those in front of the chain first; n:
how many of them are the chain's. own: the member's own. ext: own, and at the last gate the fixed
challenges behind it. -/
def localAt (b : Block S Cl) (fr : List Fmt.Drawn) (n : Nat) (own ext : List Fmt.Drawn) : Prop :=
  (markOf ms b.place fr own).isSome = true ∨
    ∃ a z s', (X (fr.take skip)).start = some a ∧
      walk (X (fr.take skip)).lay ((X (fr.take skip)).steps.take n) (fr.drop skip) a = .ok z ∧
      z.ver = some s' ∧
      runFall fs (X (fr.take skip)).lay (((X (fr.take skip)).steps.drop n).take ext.length) z s'
        ext

/-- The same with the wide event. -/
def localWide (b : Block S Cl) (fr : List Fmt.Drawn) (n : Nat) (own ext : List Fmt.Drawn) :
    Prop :=
  (markOf ms b.place fr own).isSome = true ∨
    ∃ a z s', (X (fr.take skip)).start = some a ∧
      walk (X (fr.take skip)).lay ((X (fr.take skip)).steps.take n) (fr.drop skip) a = .ok z ∧
      z.ver = some s' ∧
      localFall fs (X (fr.take skip)).lay.firstTree z.todo s' (z.own.map (·.drawn) ++ ext)

theorem localAt_wide {b : Block S Cl} {fr : List Fmt.Drawn} {n : Nat} {own ext : List Fmt.Drawn}
    (h : localAt fs ms skip X b fr n own ext) : localWide fs ms skip X b fr n own ext := by
  rcases h with h | ⟨a, z, s', h1, h2, h3, h4⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, z, s', h1, h2, h3, run_local h4⟩

/-- **A bound on the wide event pays.** f: own ↦ ext. -/
theorem bound_of_wide (b : Block S Cl) (fr : List Fmt.Drawn) (n : Nat) (ds : List RDT)
    (f : List Fmt.Drawn → List Fmt.Drawn) (q : ℝ≥0∞)
    (h : Iop.prRho {ρ : Iop.Rho (uLT C ds) |
      localWide fs ms skip X b fr n (drawnT C ds ρ) (f (drawnT C ds ρ))} ≤ q) :
    Iop.prRho {ρ : Iop.Rho (uLT C ds) |
      localAt fs ms skip X b fr n (drawnT C ds ρ) (f (drawnT C ds ρ))} ≤ q :=
  le_trans (pr_mono _ fun _ hρ => localAt_wide fs ms skip X hρ) h

/-- **The debts, one a member**: at every front by which the run has met no fall and which Q lets
in: the event at the member has, over the member's own rounds' messages, at most the member's number
as its measure; and Q goes on past a member whose mark is silent and by whose last round the run has
met no fall. -/
def LocalDebts : List (Block S Cl) → Nat → Nat → List RDT → Prop
  | [], _, _, _ => True
  | [b], j, n, ds => ∀ fr, skip ≤ fr.length → (fr.drop skip).length = n →
      fellBy all fs (X (fr.take skip)) n (fr.drop skip) = false → Q j fr →
      Iop.prRho {ρ : Iop.Rho (uLT C (ds.take b.rounds.length)) |
        localAt fs ms skip X b fr n (drawnT C _ ρ) (drawnT C _ ρ ++ tail)} ≤ p j
  | b :: b' :: bs, j, n, ds =>
    (∀ fr, skip ≤ fr.length → (fr.drop skip).length = n →
      fellBy all fs (X (fr.take skip)) n (fr.drop skip) = false → Q j fr →
      Iop.prRho {ρ : Iop.Rho (uLT C (ds.take b.rounds.length)) |
        localAt fs ms skip X b fr n (drawnT C _ ρ) (drawnT C _ ρ)} ≤ p j ∧
      ∀ ρ : Iop.Rho (uLT C (ds.take b.rounds.length)),
        (markOf ms b.place fr (drawnT C _ ρ)).isSome = false →
        fellBy all fs (X (fr.take skip)) (n + b.rounds.length)
          (fr.drop skip ++ drawnT C _ ρ) = false →
        Q (j + 1) (fr ++ drawnT C _ ρ)) ∧
    LocalDebts (b' :: bs) (j + 1) (n + b.rounds.length) (ds.drop b.rounds.length)

/-! ## 3 The law -/

variable (hX : ∀ base a s₀, (X base).start = some a → (X base).s₀ = some s₀ →
  ∃ (m₀ : Option (Mid W Y)) (front : List OpenedColumn), m₀.isSome = true ∧
    ChainProgress.start (X base).lay all m₀ (some s₀) front = .ok a)
include hX

/-- Where a gate's test speaks of a fall, at a front by which none was met. -/
theorem test_local (fr : List Fmt.Drawn) (n k : Nat) (ext : List Fmt.Drawn)
    (hn : (fr.drop skip).length = n) (hk : ext.length = k)
    (f0 : fellBy all fs (X (fr.take skip)) n (fr.drop skip) = false)
    (f1 : fellBy all fs (X (fr.take skip)) (n + k) (fr.drop skip ++ ext) = true) :
    ∃ a z s', (X (fr.take skip)).start = some a ∧
      walk (X (fr.take skip)).lay ((X (fr.take skip)).steps.take n) (fr.drop skip) a = .ok z ∧
      z.ver = some s' ∧
      runFall fs (X (fr.take skip)).lay (((X (fr.take skip)).steps.drop n).take ext.length) z s'
        ext := by
  cases hs : (X (fr.take skip)).start with
  | none =>
    unfold fellBy at f1
    rw [hs] at f1
    cases f1
  | some a =>
    cases h0 : (X (fr.take skip)).s₀ with
    | none =>
      unfold fellBy at f1
      rw [hs, h0] at f1
      cases f1
    | some s₀ =>
      obtain ⟨m₀, _, hm, ha⟩ := hX _ a s₀ hs h0
      have t1 : (fr.drop skip ++ ext).take n = fr.drop skip := List.take_left' hn
      have t2 : (fr.drop skip ++ ext).drop n = ext := List.drop_left' hn
      have f0' : fellBy all fs (X (fr.take skip)) n (fr.drop skip ++ ext) = false := by
        rw [fellBy_take all fs _ n (fr.drop skip ++ ext) (fr.drop skip)
          (by rw [t1, ← hn, List.take_length])]
        exact f0
      obtain ⟨z, s', hz, hv, hl⟩ := speaks_at fs all hs h0 hm ha n k (fr.drop skip ++ ext)
        (by rw [List.length_append, hn, hk]) f0' f1
      rw [t1] at hz
      rw [t2, ← hk, List.take_length] at hl
      exact ⟨a, z, s', rfl, hz, hv, hl⟩

/-- **FROM BOUNDS A MEMBER TO `GatesHeld` AT THE CANONICAL GATES.** -/
theorem canon_held : ∀ (bs : List (Block S Cl)) (j n : Nat) (ds : List RDT)
    (fr : List Fmt.Drawn), ds.length = (bs.flatMap (·.rounds)).length → skip ≤ fr.length →
    (fr.drop skip).length = n → fellBy all fs (X (fr.take skip)) n (fr.drop skip) = false →
    Q j fr → LocalDebts C all fs ms skip X p tail Q bs j n ds →
    GatesHeld C (coverGates all fs ms skip X p tail bs j n ds) fr
  | [], _, _, _, _, _, _, _, _, _, _ => trivial
  | [b], j, n, ds, fr, hl, hsk, hn, f0, hq, hD => by
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hl
    have hm : (ds.take b.rounds.length).length = b.rounds.length := by
      rw [List.length_take]
      omega
    refine ⟨le_trans (pr_mono _ ?_) (hD fr hsk hn f0 hq), fun _ _ => trivial⟩
    intro ρ hρ
    have hρ' : ((markOf ms b.place fr (drawnT C _ ρ)).isSome ||
        fellBy all fs (X (fr.take skip)) (n + b.rounds.length + tail.length)
          (fr.drop skip ++ drawnT C _ ρ ++ tail)) = true := hρ
    rw [Bool.or_eq_true] at hρ'
    rcases hρ' with g | g
    · exact Or.inl g
    · rw [Nat.add_assoc, List.append_assoc] at g
      exact Or.inr (test_local all fs skip X hX fr n _ _ hn
        (by rw [List.length_append, drawnT_len, hm]) f0 g)
  | b :: b' :: bs, j, n, ds, fr, hl, hsk, hn, f0, hq, hD => by
    rw [List.flatMap_cons, List.length_append] at hl
    have hm : (ds.take b.rounds.length).length = b.rounds.length := by
      rw [List.length_take]
      omega
    obtain ⟨hD1, hD2⟩ := hD
    obtain ⟨hb, hnext⟩ := hD1 fr hsk hn f0 hq
    refine ⟨le_trans (pr_mono _ ?_) hb, fun ρ hρ => ?_⟩
    · intro ρ hρ
      have hρ' : ((markOf ms b.place fr (drawnT C _ ρ)).isSome ||
          fellBy all fs (X (fr.take skip)) (n + b.rounds.length)
            (fr.drop skip ++ drawnT C _ ρ)) = true := hρ
      rw [Bool.or_eq_true] at hρ'
      rcases hρ' with g | g
      · exact Or.inl g
      · exact Or.inr (test_local all fs skip X hX fr n _ _ hn (by rw [drawnT_len, hm]) f0 g)
    · have hρ' : ((markOf ms b.place fr (drawnT C _ ρ)).isSome ||
          fellBy all fs (X (fr.take skip)) (n + b.rounds.length)
            (fr.drop skip ++ drawnT C _ ρ)) = false := hρ
      rw [Bool.or_eq_false_iff] at hρ'
      have d1 : (fr ++ drawnT C (ds.take b.rounds.length) ρ).drop skip =
          fr.drop skip ++ drawnT C (ds.take b.rounds.length) ρ :=
        List.drop_append_of_le_length hsk
      have d2 : (fr ++ drawnT C (ds.take b.rounds.length) ρ).take skip = fr.take skip :=
        List.take_append_of_le_length hsk
      exact canon_held (b' :: bs) (j + 1) (n + b.rounds.length) (ds.drop b.rounds.length) _
        (by rw [List.length_drop]; omega)
        (by rw [List.length_append]; omega)
        (by rw [d1, List.length_append, hn, drawnT_len, hm])
        (by rw [d1, d2]; exact hρ'.2) (hnext ρ hρ'.1 hρ'.2) hD2

end

end ProofFile.Honest

#print axioms ProofFile.Honest.speaks_at
#print axioms ProofFile.Honest.localAt_wide
#print axioms ProofFile.Honest.bound_of_wide
#print axioms ProofFile.Honest.test_local
#print axioms ProofFile.Honest.canon_held
#print axioms ProofFile.Honest.localAt
#print axioms ProofFile.Honest.localWide
#print axioms ProofFile.Honest.LocalDebts
