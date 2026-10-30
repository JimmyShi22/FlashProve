-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/SilentPlanes.lean: THE LOOKUP's RUN "planes"
(Johnson/Desc/First/Look/K3Runs.lean: planesRun) ACCEPTS, at the calls' seat with true claims: from
what it reads of the verifier's state. And what its accept asks of the ledger, as ONE structure that
rides past a hearing. Definitions, statements and proofs.

  foldlM_need_some, planesAtF_some   a fold that reads one form of the caller's a step returns where
                   every form is there (the way back of Law/PlanesValue.lean's foldlM_need).
  andThen_at       one step of a flat program, where its first half returns.
  leavesRowOwn_some, planeClaimsOwn_some   the three claims on the planes are made.
  planesRun_answers   MAIN: the run accepts, with its claims and the state that it returns.
  LeavesReady g F  what the run asks of what was heard and of the ledger (and what "join" asks):
                   the sumcheck over the leaves begun, a challenge a variable, its claim not made;
                   its hiding polynomial's slots free, below the number of slots and below the next
                   free number; the debts on the planes and on the join unpaid.
  LeavesReady.takes   it rides past a hearing that takes fresh numbers alone and keeps what is owed.

WHAT IT IS NOT. Implications. THAT THE LOOKUP LEAVES LeavesReady IS NOT SHOWN HERE (by reading:
K3LeftAt, K3LeftStatement.lean, has it). Nothing on what the claims are worth. Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.Desc.Kinds.Law.PlanesValue
import Johnson.Desc.First.Look.LookPlanesOwn
import Johnson.Desc.First.Look.K3Runs
import Johnson.Stored.HeadAddsAtS
import Johnson.Desc.Kinds.Law.TablesAnswer
import Johnson.Desc.Kinds.Law.Takes
import Johnson.Desc.Part.MaskedSumReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc (need named)
open VerifiableInference.Desc.First.Look (planesAtF planeClaimsOwn leavesRowOwn planesAddedF)
open Planes

/-- A fold of steps each of which reads one form of the caller's RETURNS where every form is there:
the ledger and the tape stay; the value is the plain fold. -/
theorem foldlM_need_some (r : Nat → Option Aff) (step : Aff → Nat → Aff → Aff) (F : Fork)
    (t : Tape) : ∀ (l : List Nat) (a : Aff), (∀ c ∈ l, (r c).isSome = true) →
      (l.foldlM (fun (f : Aff) col => (do
        let x ← Fl.need (r col)
        pure (step f col x) : Fl Aff)) a) F t =
        some (l.foldl (fun f col => step f col ((r col).getD {})) a, F, t)
  | [], _, _ => rfl
  | c :: l, a, h => by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (h c List.mem_cons_self)
    rw [List.foldlM_cons, List.foldl_cons, hx]
    have ih := foldlM_need_some r step F t l (step a c x) fun d hd =>
      h d (List.mem_cons_of_mem _ hd)
    simpa [bind, Fl.andThen, Fl.need, pure, Fl.ret] using ih

/-- planesAtF returns where the caller's forms are there below the planes' number of columns. -/
theorem planesAtF_some (g : Forest.Heard) (lm e : Nat) (r : Nat → Nat → Option Aff) (F : Fork)
    (t : Tape) (h : ∀ col, col < nCols g lm → (r e col).isSome = true) :
    planesAtF g lm e (fun e col => Fl.need (r e col)) F t =
      some (atForm g lm e fun e col => (r e col).getD {}, F, t) :=
  foldlM_need_some (r e) (fun f col x => Aff.addMul f x (colWeight g lm e col)) F t _ _
    fun c hc => h c (List.mem_range.1 hc)

/-- One step of a flat program, where its first half returns. -/
theorem andThen_at {α β : Type} (x : Fl α) (f : α → Fl β) (F G : Fork) (t u : Tape) (a : α)
    (h : x F t = some (a, G, u)) : Fl.andThen x f F t = f a G u := by
  unfold Fl.andThen
  rw [h]

/-- The claim that the sumcheck over the leaves leaves: it is made where the sumcheck was begun and
has a challenge a variable, and the hiding polynomial's slots can be filled. -/
theorem leavesRowOwn_some (p : Psc) (S0 : E) (kept : Aff) (F G : Fork) (t : Tape)
    (hfl : (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size) = true)
    (hrun : F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G) :
    leavesRowOwn p S0 kept F t = some (p.rowForm S0 kept, G, t) := by
  unfold leavesRowOwn
  simp [bind, Fl.andThen, Fl.must, Fl.change, pure, Fl.ret, hfl, hrun]

/-- **The three claims on the planes are made.** -/
theorem planeClaimsOwn_some (g : Forest.Heard) (lm : Nat) (r1 : Nat → Nat → Option Aff)
    (r2 : Nat → Option Aff) (F G : Fork) (t : Tape)
    (hok : First.Look.planesOk g.shape lm = true)
    (h1 : ∀ e col, col < nCols g lm → (r1 e col).isSome = true)
    (h2 : ∀ col, col < nCols g lm → (r2 col).isSome = true)
    (hfl : (!g.leaves.rowMade && g.leaves.started && !g.leaves.vars.isEmpty &&
      g.leaves.r.size == g.leaves.vars.size) = true)
    (hrun : F.hideRun g.leaves.first (Array.replicate g.leaves.walk.1.length zeroE)
      (subE zeroE oneE) = some G) :
    planeClaimsOwn g lm (fun e col => Fl.need (r1 e col)) (fun col => Fl.need (r2 col)) F t =
      some (planeForms g lm (fun e col => (r1 e col).getD {}) (fun col => (r2 col).getD {}), G,
        t) := by
  have c0 := planesAtF_some g lm 0 r1 F t (h1 0)
  have c1 := planesAtF_some g lm 1 r1 F t (h1 1)
  have c2 := foldlM_need_some r2 (fun f _ x => f + x) F t (List.range (nCols g lm))
    (Aff.ofConst (negE (ofF (2 ^ g.shape.v - g.shape.padding).toUInt64)))
    fun c hc => h2 c (List.mem_range.1 hc)
  have c3 := leavesRowOwn_some g.leaves oneE
    (Aff.scale (atForm g lm 0 fun e col => (r1 e col).getD {}) g.leavesA) F G t hfl hrun
  unfold planeClaimsOwn
  show Fl.andThen (Fl.must (First.Look.planesOk g.shape lm)) (fun _ =>
    Fl.andThen (planesAtF g lm 0 _) fun at0 => Fl.andThen (planesAtF g lm 1 _) fun at1 =>
    Fl.andThen _ fun count =>
    Fl.andThen (leavesRowOwn g.leaves oneE (Aff.scale at0 g.leavesA)) fun lr =>
    Fl.ret #[lr, Aff.slot g.sBit - at1, count]) F t = _
  refine (andThen_at _ _ F F t t () (by simp [Fl.must, hok])).trans ?_
  refine (andThen_at _ _ F F t t _ c0).trans ?_
  refine (andThen_at _ _ F F t t _ c1).trans ?_
  refine (andThen_at _ _ F F t t _ c2).trans ?_
  exact (andThen_at _ _ F G t t _ c3).trans rfl

/-- **THE LOOKUP's RUN "planes" ACCEPTS**, at the calls' seat with true claims: a sub-proof is open;
the lookup was heard; its debt on the planes is unpaid; the caller's readers answer at every column;
the sumcheck over the leaves is ready and its hiding polynomial's slots can be filled. -/
theorem planesRun_answers (lm : Nat) (readers : K3.Readers First.S) (n : Nat) (s : First.S)
    (F G : Fork) (g : Forest.Heard) (r : (Nat → Nat → Option Aff) × (Nat → Option Aff))
    (hF : s.fork? = some F) (hg : s.lookHeard? = some g)
    (hun : K3.unpaid F g.owedPlanes = true) (hr : readers s = some r)
    (hok : First.Look.planesOk g.shape lm = true)
    (h1 : ∀ e col, col < nCols g lm → (r.1 e col).isSome = true)
    (h2 : ∀ col, col < nCols g lm → (r.2 col).isSome = true)
    (hfl : (!g.leaves.rowMade && g.leaves.started && !g.leaves.vars.isEmpty &&
      g.leaves.r.size == g.leaves.vars.size) = true)
    (hrun : F.hideRun g.leaves.first (Array.replicate g.leaves.walk.1.length zeroE)
      (subE zeroE oneE) = some G) :
    K3.planesRun (K3.seatCalls asClaim) lm readers n s =
      .ok ((planeForms g lm (fun e col => (r.1 e col).getD {})
        fun col => (r.2 col).getD {}).toList.map asClaim, s.putFork (G.paid g.owedPlanes)) := by
  have c := planeClaimsOwn_some g lm r.1 r.2 F G [] hok h1 h2 hfl hrun
  have hall : (Fl.andThen (planeClaimsOwn g lm (fun e col => Fl.need (r.1 e col))
      fun col => Fl.need (r.2 col)) fun fs =>
      Fl.andThen (planesAddedF g) fun _ => Fl.ret fs) F [] =
      some (planeForms g lm (fun e col => (r.1 e col).getD {}) (fun col => (r.2 col).getD {}),
        G.paid g.owedPlanes, []) :=
    (andThen_at _ _ F G [] [] _ c).trans rfl
  have hF' : (K3.seatCalls asClaim).fork s = some F := hF
  have hg' : (K3.seatCalls asClaim).heard s = some g := hg
  have e : (do
      let fs ← planeClaimsOwn g lm (fun e col => Fl.need (r.1 e col)) fun col => Fl.need (r.2 col)
      planesAddedF g
      pure fs : Fl (Array Aff)) F [] =
      some (planeForms g lm (fun e col => (r.1 e col).getD {}) (fun col => (r.2 col).getD {}),
        G.paid g.owedPlanes, []) := hall
  unfold K3.planesRun
  simp only [hF', hg', hun, hr, named_at_some, need_at_true, bind_at_ok, e]
  rfl

/-- **WHAT THE LOOKUP's TWO LATER RUNS WANT OF THE LEDGER AND OF WHAT WAS HEARD**: the sumcheck over
the leaves was begun, has a challenge a variable, and its claim is not yet made; the slots of its
hiding polynomial's coefficients are free, below the ledger's number of slots and below its next
free number; the debts on the planes and on the join are unpaid. -/
structure LeavesReady (g : Forest.Heard) (F : Fork) : Prop where
  flags : (!g.leaves.rowMade && g.leaves.started && !g.leaves.vars.isEmpty &&
    g.leaves.r.size == g.leaves.vars.size) = true
  free : Part.MaskedSum.FreeIn F g.leaves.first (g.leaves.first + g.leaves.walk.1.length)
  below : g.leaves.first + g.leaves.walk.1.length ≤ F.next
  planes : K3.unpaid F g.owedPlanes = true
  join : K3.unpaid F g.owedJoin = true

/-- **It rides past a hearing that takes fresh numbers alone and keeps what is owed.** -/
theorem LeavesReady.takes {g : Forest.Heard} {F G : Fork} {n : Nat} (h : LeavesReady g F)
    (T : Takes F G n) (ho : G.owed = F.owed) : LeavesReady g G := by
  have hs : G.gotF.size = G.ns := T.touch.sized.2.2
  refine ⟨h.flags, ⟨by rw [T.touch.ns]; exact h.free.1, hs, fun j h1 h2 => ?_⟩,
    by rw [T.next]; exact Nat.le_trans h.below (Nat.le_add_right _ _), ?_, ?_⟩
  · have hb := h.below
    have hj : j < F.next := by omega
    have e := (T.touch.out j (Or.inl hj)).2.2
    have hF0 := h.free.2.2 j h1 h2
    have hjF : j < F.gotF.size := by
      rw [h.free.2.1]
      have := h.free.1
      omega
    have hjG : j < G.gotF.size := by
      rw [hs, T.touch.ns, ← h.free.2.1]
      exact hjF
    have nF : ¬ OnBytes.PscRun.Filled F j := by
      unfold OnBytes.PscRun.Filled
      simp only [Array.getD, hjF, dif_pos] at hF0 ⊢
      rw [hF0]
      simp
    have nG : ¬ OnBytes.PscRun.Filled G j := fun q => nF (e.1 q)
    unfold OnBytes.PscRun.Filled at nG
    simp only [Array.getD, hjG, dif_pos] at nG ⊢
    simpa using nG
  · unfold K3.unpaid
    rw [ho]
    exact h.planes
  · unfold K3.unpaid
    rw [ho]
    exact h.join

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.planesRun_answers
#print axioms VerifiableInference.Desc.Kinds.Head.Law.LeavesReady.takes
