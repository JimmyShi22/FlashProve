-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/RunsStillAtS.lean: THE BATCHING KIND's PREMISE ON A RUN OF CLAIMS (RunOk,
Johnson/Desc/First/Batch/Law/Gather.lean) AT THE OUTPUT HEAD's OWN THREE RUNS "norm", "policy",
"logits", AT THE CARRIED RECORD: by the tool for runs that leave the record as it is
(Johnson/Desc/First/Link/Law/StillRun.lean), under named premises on the letters that all kinds
share. Statements and proofs. The load lies in Law/RunsStill.lean.

  rests_seen     the head's letter for the free field of the one closed reader of the record
                 (Johnson/Desc/First/Link/Law/PhiAll.lean): seenOf: what the head's readers see
                 beside the ledger: it rests under the five writings behind the draw.
  fsK6           the forms of a run, read off what is fixed in front: off a projection of the
                 shared reader, and off the snapshot's ledger.
  K6Promise      THE NAMED PREMISE ON THE SHARED PROMISE Ok: wherever Ok holds of a fixed part that
                 shows z and whose snapshot's ledger is U: K6Ready z U (Law/RunsStill.lean).
  k6_still       Still of each of the three runs.
  k6_door        the door's duty, which the link's law asks of every run beside RunOk.
  k6_hOk         the tool's premise on slots: every slot that a form names is filled in the
                 snapshot.
  k6_runOk       MAIN: RunOk of each of the three runs.

WHAT IT IS NOT. AN IMPLICATION. OWED: (1) K6Promise: it comes due where Ok is closed: that in front
of the batching's draw the head's letters in front are read, that the seat reads back as heard what
the head's own hearing returned, and that the ledger there is later than the one which that hearing
left (NOTHING ON THE READS: Law/RunsStill.lean): the head's own block at its border
(Law/K6PromiseBorder.lean), and every block between, which must keep it. (2) hFu: at a full
state that goes on, the entries of virtual rows that the forms name are a function of the fixed part
and the data: one payer for all kinds: not ours alone. (3) The run "join" is not here: it marks an
owed claim as added, so it does not leave the record as it is. (4) The runs are those of the kind's
block at true claims (kind asClaim (seatAt h iU3) l piece p): that the seated block's runs of these
names are these is Law/SeatedBridge.lean's tested_claims and the text of kindWithJoin: not called
here. No member. Nothing on soundness.
LETTERS. No letter stands under "there is" in the tops. Under "for all": kap: the projection: pinned
by hkap at every record. ent: hFu alone reads it. l, piece: the block's place: the runs do not read
them.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RunsStill
import Johnson.Desc.First.Link.Law.StillRun
import Johnson.Desc.First.Link.Law.PhiMore
import Johnson.Desc.First.Batch.BlindK3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork Aff Reading HTailF2)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.StillRun

/-- **The head's letter rests under the writings behind the draw.** -/
theorem rests_seen (u : HTailF2) : PhiAll.Rests u seenOf where
  fork := fun s F => by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here with
    | head x => by_cases ho : x.opened = true <;> simp [seenOf, S.putFork, ho]
    | _ => simp [seenOf, S.putFork]
  set := fun s a => by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here with
    | head x => by_cases ho : x.opened = true <;> simp [seenOf, atS, S.putLink, S.putFork, ho]
    | _ => simp [seenOf, atS, S.putLink, S.putFork]
  tl := fun s tl tl' _ _ => by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here with
    | head x => by_cases ho : x.opened = true <;> simp [seenOf, S.putTl, ho]
    | _ => simp [seenOf, S.putTl]
  wrote := fun s a G s' h => by
    obtain ⟨h1, rfl⟩ := h
    simp [seenOf, h1]
  head := fun s a G h => by
    simp [seenOf, h]

section At

variable {α : Type} (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Par)

/-- The forms of a run, read off what is fixed in front. kap: what the shared reader shows of what
the head's readers see. -/
noncomputable def fsK6 (kap : α → Option Seen) (name : String) (q : α × Option Pub9) :
    Option (List Aff) :=
  match kap q.1, q.2 with
  | some z, some u => formsOf h iU3 p name z u.F
  | _, _ => none

/-- **THE NAMED PREMISE ON THE SHARED PROMISE.** -/
def K6Promise (kap : α → Option Seen) (Ok : α × Option Pub9 → Prop) : Prop :=
  ∀ q z u, Ok q → kap q.1 = some z → q.2 = some u → K6Ready h iU3 p z u.F

variable (φ : S → α) (Ok : α × Option Pub9 → Prop) (kap : α → Option Seen)
  (hkap : ∀ e, kap (φ e) = seenOf e) (hP : K6Promise h iU3 p kap Ok)

include hkap hP in
/-- **EACH OF THE THREE RUNS LEAVES THE RECORD AS IT IS, AND ITS FORMS ARE READ OFF WHAT IS FIXED.**
-/
theorem k6_still (l piece : Nat) (name : String) (run : Nat → S → Except String (List Claim × S))
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run) :
    Still φ Ok run (fsK6 h iU3 p kap name) where
  hands := fun n e c e₁ hr =>
    k6_same h iU3 l piece p (name, run) (lookup_mem _ _ _ hrun) n e (c, e₁) hr
  forms := fun q n e c e₁ hf hr => by
    obtain ⟨hok, hq, u, b, hu, hb, hL, _, hK, _⟩ := hf
    obtain ⟨z, hz⟩ := seen_of_run h iU3 p l piece name run hrun n e e₁ c hr
    have hk : kap q.1 = some z := by rw [← hq, hkap, hz]
    have hF : e.fork? = some b.F := K9.get_fork e b hb
    obtain ⟨_, fs, h1, h2⟩ := still_core h iU3 p l piece name run hrun hz hF hL
      (LinkJoin.widths_of_looks _ _ hK)
      (hP q z u hok hk hu) n c e₁ hr
    refine ⟨fs, ?_, h2⟩
    unfold fsK6
    rw [hk, hu]
    exact h1

omit hkap hP in
/-- **The door's duty of each of the three runs**: the record is the same. Under no premise. -/
theorem k6_door (l piece : Nat) (name : String) (run : Nat → S → Except String (List Claim × S))
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run) (n : Nat)
    (e : S) (c : List Claim) (e₁ : S) (hr : run n e = .ok (c, e₁)) : KeepsDoor atS e e₁ := by
  obtain rfl : e₁ = e :=
    k6_same h iU3 l piece p (name, run) (lookup_mem _ _ _ hrun) n e (c, e₁) hr
  exact fun a ha => ⟨a, ha, rfl, rfl⟩

include hP in
/-- **The tool's premise on slots.** -/
theorem k6_hOk (name : String) : ∀ q l u, Ok q → fsK6 h iU3 p kap name q = some l → q.2 = some u →
    ∀ f ∈ l, ∀ x ∈ f.slots.toList, OnBytes.PscRun.Filled u.F x.1 := by
  intro q l u hok hl hu f hf x hx
  unfold fsK6 at hl
  rw [hu] at hl
  cases hk : kap q.1 with
  | none => rw [hk] at hl; cases hl
  | some z =>
    rw [hk] at hl
    exact still_filled h iU3 p name (hP q z u hok hk hu) l hl f hf x hx

variable {K : Type} [Field K] (ρ : Reading K)

include hkap hP in
/-- **RunOk OF EACH OF THE THREE RUNS.** -/
theorem k6_runOk (Fu : S → Prop) (l piece : Nat) (name : String)
    (run : Nat → S → Except String (List Claim × S))
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run)
    (ent : α × Option Pub9 → Bound K → Nat → Nat → Nat → K)
    (hFu : ∀ q l t b y, Fx9 φ Ok q t → Fu t → atS.get? t = some b →
      fsK6 h iU3 p kap name q = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList,
        (worldAt ρ b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx) :
    RunOk ρ atS (O9 φ Ok Fu) (Fx9 φ Ok) run
      (plainTm (valsStill ρ (fsK6 h iU3 p kap name) ent)) (lenStill (fsK6 h iU3 p kap name)) :=
  still_runOk ρ φ Ok Fu run _ (k6_still h iU3 p φ Ok kap hkap hP l piece name run hrun)
    (k6_hOk h iU3 p Ok kap hP name) ent hFu

end At

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.rests_seen
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_still
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_door
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_hOk
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_runOk
