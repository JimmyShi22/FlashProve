-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ReaderRides.lean.
WHAT IT DOES NOT SHOW. No soundness. THE RUNS "join" AND "planes" ARE NOT HERE: that the lookup's
own functions answer at the later ledger is another law's. THAT THE READER ANSWERS AT THE FIRST
RECORD: a premise (hR). WHICH RUN STANDS IN THE LINK UNDER THE NAME: premises: hf (it is found), fwd
(where it answers, the kind's own run gives the same answer) and bwd (where the kind's own run
answers and leaves the reply, it gives the same answer): a run in the dress of a guard on the reply
meets both; that the description's run is such a run is not shown here.
LETTERS. No "there is" in the tops.
OBJECT. Desc/First/Batch/ReaderOf.lean's readerOf: "the reader of a run is the run itself", at one
of the output head's three own runs ("norm", "policy", "logits"), at the seat
Stored/HeadSeatAt.lean.
USER. Whoever carries the sentence "the forms that this run states are worth 0" from one border to
the next: it asks that the reader gives ONE answer at both records.
WHAT IT IS. WHERE ONE RECORD GOES ON FROM ANOTHER AS FAR AS THE OUTPUT HEAD's READERS SEE (Alike,
Law/RunsFixed.lean) AND THE LEDGER's ARRAYS KEEP THEIR NUMBERS OF ROWS, THE READER's ANSWER AT THE
FIRST IS ITS ANSWER AT THE SECOND: the same forms, no late slot.
  k6_run_answers    the kind's own run answers wherever the letters are read and the run is there.
  ownRow_same       the reader's test on an entry reads the arrays' numbers of rows alone.
  reader_rides_own  the statement.

-/
import Mathlib
import Johnson.Desc.First.Batch.ReaderOf
import Johnson.Desc.Kinds.Law.K06Runs
import Johnson.Desc.Kinds.Law.HeadRunsCarry
import Johnson.Desc.Kinds.Law.RunsFixed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (readerOf lateOf ownRow RunOf)

/-- **The kind's own run answers** wherever the letters are read and the run is there; at the seat
at
S it leaves the record. -/
theorem k6_run_answers (h : Model.Head.Shape) (iU3 l piece : Nat) (p : Par) (name : String)
    (run : Nat → S → Except String (List Claim × S))
    (h1 : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run) (n : Nat) (s : S)
    (g : Given) (b : Behind) (x : Places) (fs : List Form)
    (hv : lettersAt p (seatAt h iU3) s = .ok (g, b, x))
    (hfs : ((fun (_ : Given) (_ : Behind) (_ : Places) => claims) g b x).lookup name = some fs) :
    run n s = .ok (fs.map asClaim, s) := by
  have h1' : (runsBy ["norm", "policy", "logits"] (fun _ _ _ => claims)
      (fun g _ _ => g.calls.map fun c => keyVector key c.1 c.2) asClaim p
      (seatAt h iU3)).lookup name = some run := h1
  unfold runsBy at h1'
  have hr := lookup_map_self _ _ _ _ h1'
  subst hr
  simp only [bind, Except.bind, pure, Except.pure, hv, named, hfs]
  split <;> rfl

/-- The reader's test on an entry reads the arrays' numbers of rows alone. -/
theorem ownRow_same {F G : Fork} (hr : G.trees.map (·.R) = F.trees.map (·.R)) (x : Ent) :
    ownRow G x = ownRow F x := by
  have e : (G.trees[x.tree]?).map (·.R) = (F.trees[x.tree]?).map (·.R) := by
    rw [← Array.getElem?_map, ← Array.getElem?_map, hr]
  unfold ownRow
  cases hG : G.trees[x.tree]? <;> cases hF : F.trees[x.tree]? <;> rw [hG, hF] at e <;>
    simp_all

/-- **THE READER's ANSWER RIDES**, at one of the head's three own runs. -/
theorem reader_rides_own (h : Model.Head.Shape) (iU3 l piece : Nat) (p : Par)
    {states : Nat → List (RunOf S)} {b : Nat} {name : String}
    {run run' : Nat → S → Except String (List Claim × S)}
    (hf : (states b).find? (fun r => r.1 == name) = some (name, run))
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run')
    (fwd : ∀ k t y, run k t = .ok y → run' k t = .ok y)
    (bwd : ∀ k t y, run' k t = .ok y → y.2.out.reply = t.out.reply → run k t = .ok y)
    {e s' : S} (a : Alike e s') {F F' : Fork} (hF : e.fork? = some F) (hF' : s'.fork? = some F')
    (hrow : F'.trees.map (·.R) = F.trees.map (·.R)) {R : K9.Read}
    (hR : readerOf states b name e = some R) : readerOf states b name s' = some R := by
  unfold readerOf at hR ⊢
  rw [hf] at hR ⊢
  simp only [Option.bind_some] at hR ⊢
  cases hr : run 0 e with
  | error m => rw [hr] at hR; cases hR
  | ok z =>
    rw [hr, hF] at hR
    simp only at hR
    have hr' := fwd 0 e z hr
    obtain ⟨g, bh, x, fs, k1, k2, k3⟩ :=
      k6_run_spec asClaim (seatAt h iU3) l piece p name run' 0 e z.2 z.1 hrun hr'
    have hz : z.2 = e := k6_same h iU3 l piece p (name, run') (lookup_mem _ _ _ hrun) 0 e z hr'
    have k1' := letters_alike h iU3 p a (g, bh, x) k1
    have hs' : run 0 s' = .ok (fs.map asClaim, s') :=
      bwd 0 s' _ (k6_run_answers h iU3 l piece p name run' hrun 0 s' g bh x fs k1' k2) rfl
    rw [hs', hF']
    simp only
    rw [hz, hF] at hR
    rw [hF']
    simp only [Option.bind_some] at hR ⊢
    have late0 : ∀ G : Fork, lateOf G G = [] := by
      intro G
      unfold lateOf
      rw [List.filterMap_eq_nil_iff]
      intro j _
      cases G.gotF.getD j false <;> rfl
    rw [late0] at hR ⊢
    rw [k3] at hR
    have ht : ((fs.map asClaim).all fun c => c.runs.isEmpty && c.eqFirst.isNone &&
        c.form.ents.all (ownRow F')) = ((fs.map asClaim).all fun c => c.runs.isEmpty &&
        c.eqFirst.isNone && c.form.ents.all (ownRow F)) := by
      congr 1
      funext c
      congr 1
      congr 1
      funext x
      exact ownRow_same hrow x
    rw [ht]
    exact hR

end VerifiableInference.Desc.Kinds.Head.Law
