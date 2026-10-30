-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/RunsFwdPlanes.lean: one of the eighteen fields of `RunsPass`
(KeepAtMerge.lean): what the reader of the run "planes" answers in front of the merge's accepting
step it answers behind it (`Fwd`, Johnson/Desc/Reads/FormsPass.lean). Definitions, and theorems with
their proofs.

How. "planes" is the one run of the nine that writes under slots: it fills the slots of the hiding
polynomial of the sumcheck over the leaves, and then lays a mark on a debt. Its three forms do not
read the ledger: they are made of what the lookup has heard and of the calling kind's forms.
  (1) `Carries w x`: a flat function x whose value, and what it leaves of the tape, do not hang on
      the ledger, and which lays w of the ledger in front: wherever x returns at one ledger it
      returns the same value at every ledger at which w returns. It goes through "then" and through
      a fold; so it holds of the run's flat function (`all_carries`), at w := that one write, then
      the mark.
  (2) The write returns behind the merge: its stretch ends at or below the next free number in front
      (`leaves_below`, RunsLate.lean), it is free in front because the write returned there, and the
      merge turns no mark below that number (`merge_below_next`, LedgerBehind.lean).
  (3) What the run reads beside: the ledger's list of debts (`merge_owed`); what was heard; the
      output head's readers of the planes' matrix, which read the reads' tables and the arrays'
      list: the merge leaves both (`planeReaders_stay`).
  (4) The late slots are a function of what was heard (`late_hideRun`,
      Johnson/Top/H/Keep/K3Late.lean).

Main names:
  `Carries`, `carries_pure`, `carries_must`, `carries_need`, `carries_change`, `carries_bind`,
    `blind_bind`, `bind_blind`, `carries_fold`.
  `planesAt_carries`, `leavesRow_carries`, `planeClaims_carries`, `all_carries`.
  `planes_moves`: `Moves` (RunsFwdLook.lean) of the run, between two states, under what (2), (3) and
    (4) want. `write_behind`: (2). `planeReaders_stay`: (3).
  `fwd_planes`: THE FIELD, from: the segment is there; `RunIs` at "planes"; the merge's accepting
    step; in front of it the table's test `ledgerB`, the lookup arguments' public test behind the
    lookup on the calls, `leavesLenB` (RunsLate.lean) and `speaksAt` (RunsAre.lean). BY READING
    ONE PREMISE MORE THAN IS NEEDED: that public test accepts only where a ledger is open and passes
    `sizedB` (Johnson/Desc/First/Look/K3Borders.lean), the three comparisons of `ledgerB`
    (Johnson/Desc/First/FillKeeper.lean). No lemma here says so: `ledgerB` is taken beside it
    because the lemmas beneath take it, and its user has both.
  `carries_fails`: a negative test: a flat function that returns the ledger's next free number
    does not have `Carries`.

Limits. NO EXAMPLE IN LEAN: the premises are shown together at no segment and no state; no accepting
step of the merge is exhibited. AN EVALUATION, NO THEOREM: over another state of the library, at one
honest full-size run over synthetic weights, the terms of `speaksAt` at "planes" and of
`leavesLenB`, typed out, have been seen to accept at the state in front of the merge, and the own
reader's answers at "planes" in front of the merge and behind it were one (3 forms, 44 late slots).
`RunIs`, `ledgerB` and `lookOutC` have not been evaluated there. IDLE CASES: the field asks nothing
where the reader answers nothing in front. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.RunsFwdLook
import Johnson.Top.H.Keep.K3Start

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes OnBytes.Model
open OnBytes.K.Kc (Fl Tape)
open OnBytes.PscRun (Sized Filled Later SlotsOwed)
open Fo.Tp (bind_ok pure_ok must_ok get_ok change_ok)
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Reads.Pass (Fwd)
open VerifiableInference.Desc.K9 (statesOfLink readerOf lateOf readersAt)
open VerifiableInference.Desc.First.Look (K3Data lookOutC planesAtF leavesRowOwn planeClaimsOwn
  planesAddedF)
open VerifiableInference.Desc.Kinds.Head (asClaim callerReaders planesAt)
open VerifiableInference.OnPublicFiles (lateG late_hideRun lvLen fork_putFork named_bind
        own_write_returns)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-! ## Flat functions whose value does not hang on the ledger -/

section
variable {α β : Type}

/-- The value of x, and what it leaves of the tape, do not hang on the ledger; the ledger behind is
w of the ledger in front. -/
def Carries (w : Fork → Option Fork) (x : Fl α) : Prop :=
  ∀ F c a G c', x F c = .ok ((a, G), c') →
    w F = some G ∧ ∀ F' G', w F' = some G' → x F' c = .ok ((a, G'), c')

theorem carries_pure (a : α) : Carries some (pure a : Fl α) := by
  intro F c a' G c' h
  have e := (pure_ok a F c _).1 h
  simp only [Prod.mk.injEq] at e
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
  refine ⟨rfl, fun F' G' hw => ?_⟩
  obtain rfl := Option.some.inj hw
  exact (pure_ok _ _ _ _).2 rfl

theorem carries_must (b : Bool) : Carries some (Fl.must b) := by
  intro F c a' G c' h
  obtain ⟨hb, e⟩ := (must_ok b F c _).1 h
  simp only [Prod.mk.injEq] at e
  obtain ⟨⟨-, rfl⟩, rfl⟩ := e
  refine ⟨rfl, fun F' G' hw => ?_⟩
  obtain rfl := Option.some.inj hw
  exact (must_ok _ _ _ _).2 ⟨hb, rfl⟩

theorem carries_need (o : Option α) : Carries some (Fl.need o) := by
  intro F c a' G c' h
  obtain ⟨a, ho, e⟩ := (get_ok o F c _).1 h
  simp only [Prod.mk.injEq] at e
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
  refine ⟨rfl, fun F' G' hw => ?_⟩
  obtain rfl := Option.some.inj hw
  exact (get_ok _ _ _ _).2 ⟨_, ho, rfl⟩

theorem carries_change (w : Fork → Option Fork) : Carries w (Fl.change w) := by
  intro F c a' G c' h
  obtain ⟨G0, hw0, e⟩ := (change_ok w F c _).1 h
  simp only [Prod.mk.injEq] at e
  obtain ⟨⟨-, rfl⟩, rfl⟩ := e
  exact ⟨hw0, fun F' G' hw => (change_ok _ _ _ _).2 ⟨G', hw, rfl⟩⟩

theorem carries_bind {w₁ w₂ : Fork → Option Fork} {x : Fl α} {f : α → Fl β} (hx : Carries w₁ x)
    (hf : ∀ a, Carries w₂ (f a)) : Carries (fun F => (w₁ F).bind w₂) (x >>= f) := by
  intro F c b G c' h
  obtain ⟨a, G1, c1, h1, h2⟩ := (bind_ok x f F c _).1 h
  obtain ⟨k1, k2⟩ := hx F c a G1 c1 h1
  obtain ⟨m1, m2⟩ := hf a G1 c1 b G c' h2
  refine ⟨?_, fun F' G' hw => ?_⟩
  · show (w₁ F).bind w₂ = some G
    rw [k1]
    exact m1
  · obtain ⟨G1', p1, p2⟩ := Option.bind_eq_some_iff.1 hw
    exact (bind_ok x f F' c _).2 ⟨a, G1', c1, k2 F' G1' p1, m2 G1' G' p2⟩

/-- In front of x a function that leaves the ledger. -/
theorem blind_bind {w : Fork → Option Fork} {x : Fl α} {f : α → Fl β} (hx : Carries some x)
    (hf : ∀ a, Carries w (f a)) : Carries w (x >>= f) := carries_bind hx hf

/-- Behind x functions that leave the ledger. -/
theorem bind_blind {w : Fork → Option Fork} {x : Fl α} {f : α → Fl β} (hx : Carries w x)
    (hf : ∀ a, Carries some (f a)) : Carries w (x >>= f) := by
  intro F c b G c' h
  obtain ⟨a, G1, c1, h1, h2⟩ := (bind_ok x f F c _).1 h
  obtain ⟨k1, k2⟩ := hx F c a G1 c1 h1
  obtain ⟨m1, m2⟩ := hf a G1 c1 b G c' h2
  obtain rfl := Option.some.inj m1
  exact ⟨k1, fun F' G' hw => (bind_ok x f F' c _).2 ⟨a, G', c1, k2 F' G' hw, m2 G' G' rfl⟩⟩

theorem carries_fold (step : β → α → Fl β) (hs : ∀ s a, Carries some (step s a)) :
    ∀ (l : List α) (s : β), Carries some (l.foldlM step s)
  | [], s => by
    rw [List.foldlM_nil]
    exact carries_pure s
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact blind_bind (hs s a) fun s' => carries_fold step hs l s'

/-- A negative test: a flat function that returns the ledger's next free number does not have the
property, whatever w. -/
theorem carries_fails (w : Fork → Option Fork) : ¬ Carries w (Fl.ask fun F => some F.next) := by
  intro H
  obtain ⟨k1, k2⟩ := H {} [] 0 {} [] rfl
  have h2 : w { next := 1 } = some { next := 1 } :=
    (H { next := 1 } [] 1 { next := 1 } [] rfl).1
  have h3 := k2 { next := 1 } { next := 1 } h2
  have h4 : (some ((1 : ℕ), ({ next := 1 } : Fork), ([] : Tape))) =
      some ((0 : ℕ), ({ next := 1 } : Fork), ([] : Tape)) := h3
  have h5 := congrArg (fun x : ℕ × Fork × Tape => x.1) (Option.some.inj h4)
  exact absurd h5 (by decide)

end

/-! ## The flat function of "planes" -/

/-- The one write of "planes". -/
def leavesWrite (g : Forest.Heard) (F : Fork) : Option Fork :=
  F.hideRun g.leaves.first (Array.replicate (lvLen g) zeroE) (subE zeroE oneE)

theorem planesAt_carries (g : Forest.Heard) (lm e : ℕ) (bit : ℕ → ℕ → Option Aff) :
    Carries some (planesAtF g lm e fun e col => Fl.need (bit e col)) := by
  unfold planesAtF
  exact carries_fold _ (fun f col => blind_bind (carries_need _) fun x => carries_pure _) _ _

theorem leavesRow_carries (g : Forest.Heard) (S0 : E) (kept : Aff) :
    Carries (leavesWrite g) (leavesRowOwn g.leaves S0 kept) := by
  unfold leavesRowOwn
  exact blind_bind (carries_must _) fun _ => bind_blind (carries_change _) fun _ => carries_pure _

theorem planeClaims_carries (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → Option Aff)
    (pin : ℕ → Option Aff) :
    Carries (leavesWrite g)
      (planeClaimsOwn g lm (fun e col => Fl.need (bit e col)) fun col => Fl.need (pin col)) := by
  unfold planeClaimsOwn
  exact blind_bind (carries_must _) fun _ =>
    blind_bind (planesAt_carries g lm 0 bit) fun at0 =>
    blind_bind (planesAt_carries g lm 1 bit) fun at1 =>
    blind_bind (carries_fold _ (fun f col => blind_bind (carries_need _) fun x => carries_pure _)
      _ _) fun count =>
    bind_blind (leavesRow_carries g _ _) fun row => carries_pure _

/-- **The run's flat function**: the three forms do not hang on the ledger; the ledger behind is the
one write, then the mark on the debt. -/
theorem all_carries (g : Forest.Heard) (lm : ℕ) (r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)) :
    Carries (fun F => (leavesWrite g F).bind fun H => some (H.paid g.owedPlanes))
      ((do
        let fs ← planeClaimsOwn g lm (fun e col => Fl.need (r.1 e col))
          fun col => Fl.need (r.2 col)
        planesAddedF g
        pure fs) : Fl (Array Aff)) :=
  carries_bind (planeClaims_carries g lm r.1 r.2) fun fs =>
    bind_blind (carries_change _) fun _ => carries_pure fs

/-! ## The run between two states -/

/-- **`Moves` of "planes"**, under: what the lookups' runs read stays; the calling kind's readers
answer at s' what they answer at s; both ledgers have their sizes; the write returns at s'. -/
theorem planes_moves (lm : ℕ) (readers : K3.Readers S) {s s' : S} (st : LookStays s s')
    (hrd : ∀ r, readers s = some r → readers s' = some r)
    (hsz : ∀ F, s.fork? = some F → Sized F) (hsz' : ∀ F, s'.fork? = some F → Sized F)
    (hw : ∀ F F' g H, s.fork? = some F → s'.fork? = some F' → s.lookHeard? = some g →
      leavesWrite g F = some H → ∃ H', leavesWrite g F' = some H') :
    Moves (K3.planesRun (K3.seatCalls asClaim) lm readers) s s' := by
  intro z F G h0 hF hG
  unfold K3.planesRun at h0
  rw [named_bind] at h0
  obtain ⟨F1, e1, h0⟩ := h0
  rw [named_bind] at h0
  obtain ⟨g, e2, h0⟩ := h0
  rw [VerifiableInference.OnPublicFiles.need_bind] at h0
  obtain ⟨hu, h0⟩ := h0
  rw [named_bind] at h0
  obtain ⟨r, e3, h0⟩ := h0
  dsimp only at h0
  rw [named_bind] at h0
  obtain ⟨⟨fs, G1, u⟩, e4, h0⟩ := h0
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans e1)
  obtain ⟨k1, k2⟩ := all_carries g lm r F [] fs G1 u e4
  obtain ⟨H, hH, eH⟩ := Option.bind_eq_some_iff.1 k1
  obtain rfl : H.paid g.owedPlanes = G1 := Option.some.inj eH
  have ez : z = (fs.toList.map asClaim, s.putFork (H.paid g.owedPlanes)) :=
    (Except.ok.inj h0).symm
  obtain ⟨F', hF', ht, ho⟩ := st.fork F hF
  obtain ⟨H', hH'⟩ := hw F F' g H hF hF' e2 hH
  have eG : G = H.paid g.owedPlanes := by
    rw [ez] at hG
    exact (Option.some.inj ((fork_putFork s F _ hF).symm.trans hG)).symm
  have run' : K3.planesRun (K3.seatCalls asClaim) lm readers 0 s' =
      .ok (fs.toList.map asClaim, s'.putFork (H'.paid g.owedPlanes)) := by
    unfold K3.planesRun
    rw [named_bind]
    refine ⟨F', hF', ?_⟩
    rw [named_bind]
    refine ⟨g, st.calls.trans e2, ?_⟩
    rw [VerifiableInference.OnPublicFiles.need_bind]
    refine ⟨?_, ?_⟩
    · unfold K3.unpaid at hu ⊢
      rw [ho]
      exact hu
    · rw [named_bind]
      refine ⟨r, hrd r e3, ?_⟩
      dsimp only
      rw [named_bind]
      refine ⟨(fs, H'.paid g.owedPlanes, u), k2 F' _ ?_, rfl⟩
      show (leavesWrite g F').bind _ = _
      rw [hH']
      rfl
  refine ⟨_, F', H'.paid g.owedPlanes, run', ?_, hF', fork_putFork s' F' _ hF', by rw [ez],
    by rw [ht], ?_⟩
  · show (s'.putFork _).out.reply = _
    rw [out_putFork]
  · have a1 : lateG F' (H'.paid g.owedPlanes) = lateG F' H' := rfl
    have a2 : lateG F (H.paid g.owedPlanes) = lateG F H := rfl
    rw [eG, ← lateG_is, ← lateG_is, a1, a2, late_hideRun (hsz' F' hF') hH',
      late_hideRun (hsz F hF) hH]

/-! ## Across the merge -/

/-- **The write returns behind the merge.** -/
theorem write_behind (P : HeadMergeP) {a b : S} {rs : List Fmt.RoundView}
    (hy : headMergeDecide P a rs = .ok b) {F F' : Fork} {g : Forest.Heard} {H : Fork}
    (hF : a.fork? = some F) (hF' : b.fork? = some F') (hS : Sized F)
    (hb : g.leaves.first + lvLen g ≤ F.next) (hpos : 0 < lvLen g)
    (hH : leavesWrite g F = some H) : ∃ H', leavesWrite g F' = some H' := by
  obtain ⟨x, x', hx, hx', rfl, hG, hl, -, -⟩ := merge_forks P hy hF
  obtain rfl : x'.F = F' := Option.some.inj (hG.symm.trans hF')
  obtain ⟨-, -, hin, -⟩ := OnBytes.PscRun.hideRun_ok x.F H _ _ _ hS hH
  rw [Array.size_replicate] at hin
  refine own_write_returns (hl.sized hS) ⟨Nat.le_trans hb hl.next, fun j h1 h2 hf => ?_⟩ ?_
  · have e : g.leaves.first + (j - g.leaves.first) = j := by omega
    have h3 := (hin (j - g.leaves.first) (by omega)).2.1
    rw [e] at h3
    exact h3 ((merge_below_next P hy hx hx' hS j (by omega)).1 hf)
  · rw [hl.ns]
    have := (hin (lvLen g - 1) (by omega)).1
    omega

/-- **The output head's readers of the planes' matrix answer the same behind the merge.** -/
theorem planeReaders_stay (P : HeadMergeP) {a b : S} {rs : List Fmt.RoundView}
    (hy : headMergeDecide P a rs = .ok b) (hled : ledgerB a = true) (iU3 : ℕ) :
    callerReaders (planesAt iU3) b = callerReaders (planesAt iU3) a := by
  obtain ⟨F0, hF0, hS⟩ := sized_of_ledgerB hled
  obtain ⟨y, -, hy1, -, rfl, -⟩ := merge_forks P hy hF0
  obtain ⟨x, x', hx, hx', -, ex, -⟩ := isLocal P a rs b hy
  obtain rfl : y = x := by
    rw [hx] at hy1
    exact (Here.head.inj hy1).symm
  have eo : x'.opened = y.opened := by rw [ex]
  have et : x'.t = y.t := by rw [ex]
  have etr : x'.F.trees = y.F.trees := merge_trees P hy hx hx' hS
  have e : planesAt iU3 b = planesAt iU3 a := by
    unfold planesAt
    simp only [S.fork?, hx, hx', eo]
    cases y.opened with
    | false => rfl
    | true =>
      show (x'.t.bind fun tt => (x'.F.trees[iU3]?).bind fun tr =>
          if tr.K == 0 then none else some (Kinds.Head.planeEntry tt.tab iU3 tr.K)) =
        y.t.bind fun tt => (y.F.trees[iU3]?).bind fun tr =>
          if tr.K == 0 then none else some (Kinds.Head.planeEntry tt.tab iU3 tr.K)
      rw [et, etr]
  unfold callerReaders
  rw [e]

/-- **WHAT THE READER OF "planes" ANSWERS IN FRONT OF THE MERGE's ACCEPTING STEP IT ANSWERS BEHIND
IT.** -/
theorem fwd_planes {lk : ℕ → Option (Link S Claim)} {X : OnBytes.Model.Verify.Public} {mH m : ℕ}
    {l : Link S Claim} (hlk : lk m = some l) {iU3 lm : ℕ}
    (hr : RunIs l 2 "planes"
      (K3.planesRun (K3.seatCalls asClaim) lm (callerReaders (planesAt iU3))))
    (d : K3Data) (P : HeadMergeP) {a b : S} {rs : List Fmt.RoundView}
    (hy : headMergeDecide P a rs = .ok b) (hled : ledgerB a = true)
    (hout : lookOutC d m false a = true) (hlen : leavesLenB a = true)
    (hs : speaksAt l 2 "planes" a = true) : Fwd (readersAt lk X mH m) 2 "planes" a b := by
  obtain ⟨F0, hF0, hS⟩ := sized_of_ledgerB hled
  have hS' : ∀ F, b.fork? = some F → Sized F := fun F hF => by
    obtain ⟨x, x', -, -, rfl, hG, hl, -, -⟩ := merge_forks P hy hF0
    obtain rfl : x'.F = F := Option.some.inj (hG.symm.trans hF)
    exact hl.sized hS
  refine fwd_speaking hlk (by decide) hr (planes_moves lm _ (stays_merge P hy hled)
    (fun r h => by rw [planeReaders_stay P hy hled iU3]; exact h)
    (fun F hF => by rw [← Option.some.inj (hF0.symm.trans hF)]; exact hS) hS'
    fun F F' g H hF hF' hg hH => ?_) hs
  have hb := (leaves_below d m hF hg hout hlen).1
  have hpos : 0 < lvLen g := by
    unfold leavesLenB at hlen
    rw [hg] at hlen
    simp only [Option.any_some, beq_iff_eq] at hlen
    omega
  exact write_behind P hy hF hF' (by rw [← Option.some.inj (hF0.symm.trans hF)]; exact hS) hb hpos
    hH

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.carries_pure
#print axioms VerifiableInference.Desc.First.MergeLaw.carries_must
#print axioms VerifiableInference.Desc.First.MergeLaw.carries_need
#print axioms VerifiableInference.Desc.First.MergeLaw.carries_change
#print axioms VerifiableInference.Desc.First.MergeLaw.carries_bind
#print axioms VerifiableInference.Desc.First.MergeLaw.blind_bind
#print axioms VerifiableInference.Desc.First.MergeLaw.bind_blind
#print axioms VerifiableInference.Desc.First.MergeLaw.carries_fold
#print axioms VerifiableInference.Desc.First.MergeLaw.carries_fails
#print axioms VerifiableInference.Desc.First.MergeLaw.planesAt_carries
#print axioms VerifiableInference.Desc.First.MergeLaw.leavesRow_carries
#print axioms VerifiableInference.Desc.First.MergeLaw.planeClaims_carries
#print axioms VerifiableInference.Desc.First.MergeLaw.all_carries
#print axioms VerifiableInference.Desc.First.MergeLaw.planes_moves
#print axioms VerifiableInference.Desc.First.MergeLaw.write_behind
#print axioms VerifiableInference.Desc.First.MergeLaw.planeReaders_stay
#print axioms VerifiableInference.Desc.First.MergeLaw.fwd_planes
