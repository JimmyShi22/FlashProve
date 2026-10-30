-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6SilentRides.lean: THE LAST JOINS AROUND Law/K6SilentCode.lean's k6Silent.
EQUATIONS OF OPTIONS.
(1) THE READER's ANSWER AT "join" RIDES from a record to one that is Alike, with the same rows and
    the same owed claims (the like of Law/ReaderRides.lean's reader_rides_own, for the fourth run);
(2) silent_is_run: k6Silent BEHIND THE OUTPUT HEAD's OWN BLOCK IS THE RUN ITSELF BEHIND THE SENDING
    OF THE READS AND THE READS' QUIET STEP: readerOf ... s' = k6Silent ... s, at all four of the
    head's runs: silent together, or one answer; and so the table's readers give ONE ANSWER at the
    two records (readers_one).
Statements and proofs, over Law/SilentIsRun.lean (there
the two records are Alike each to the other) and what it imports.

  K6Back           THE WAY BACK, A NAMED PREMISE beside Law/K6Silent.lean's K6States: where the
                   kind's own run answers and leaves the heard reply, the run that stands at the
                   link's block gives that answer.
  lookHeard_alike, reader_rides_join, silent_is_run, readers_one   as above.
  withTables_laid  where the quiet step's own tables are laid already, withTables leaves the record.

WHAT IT IS NOT. Implications. K6States and K6Back are premises (at the guarded block: other
files' to show). The two blocks are K1's commitAtS and ReadsQuiet.head by their own decide, not
the place as the link holds it. "planes": nothing. readers_one asks that no tables are laid at
the earlier record (no payer here). Nothing on soundness.
LETTERS. No letter stands under "there is" in the tops.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K6Stated
import Johnson.Desc.Kinds.Law.K6FormsInT
import Johnson.Desc.Kinds.Law.SilentIsRun
import Johnson.Desc.Kinds.Law.HeardAt
import Johnson.Desc.First.StateLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff)
open VerifiableInference.Desc (Block Claim Link)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K1 (commitAtS)
open VerifiableInference.Desc.K9 (readerOf lateOf ownRow RunOf)

/-! ## 1 "join" rides -/

/-- What the lookup has heard is the same at records that are Alike. -/
theorem lookHeard_alike {e s' : S} (a : Alike e s') : s'.lookHeard? = e.lookHeard? := by
  obtain ⟨o, o', e1, e2, _, _, _, e6, e7, _⟩ := a
  unfold S.lookHeard?
  rw [e1, e2]
  show (if o'.opened then o'.lookHeard else none) = if o.opened then o.lookHeard else none
  rw [e6, e7]

/-- **THE READER's ANSWER RIDES, AT "join".** -/
theorem reader_rides_join (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Par)
    {states : Nat → List (RunOf S)} {b : Nat} {run : Nat → S → Except String (List Claim × S)}
    (hf : (states b).find? (fun r => r.1 == "join") = some ("join", run))
    (fwd : ∀ k t y, run k t = .ok y →
      K3.joinRun (K3.seatCalls asClaim) (callerKeys p (seatAt h iU3)) k t = .ok y)
    (bwd : ∀ k t y, K3.joinRun (K3.seatCalls asClaim) (callerKeys p (seatAt h iU3)) k t = .ok y →
      y.2.out.reply = t.out.reply → run k t = .ok y)
    {e s' : S} (a : Alike e s') {F F' : Fork} (hF : e.fork? = some F) (hF' : s'.fork? = some F')
    (hrow : F'.trees.map (·.R) = F.trees.map (·.R)) (howed : F'.owed = F.owed) {R : K9.Read}
    (hR : readerOf states b "join" e = some R) : readerOf states b "join" s' = some R := by
  unfold readerOf at hR ⊢
  rw [hf] at hR ⊢
  simp only [Option.bind_some] at hR ⊢
  cases hr : run 0 e with
  | error m => rw [hr] at hR; cases hR
  | ok z =>
    rw [hr, hF] at hR
    simp only at hR
    obtain ⟨F0, g, KF, j1, j2, j3, j4, j5, rfl⟩ := (join_iff _ 0 e z).1 (fwd 0 e z hr)
    obtain rfl : F = F0 := Option.some.inj (hF.symm.trans j1)
    have k4 : callerKeys p (seatAt h iU3) s' = some KF := by
      unfold callerKeys at j4 ⊢
      obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp j4
      have hl : lettersAt p (seatAt h iU3) e = .ok v := by
        cases hl : lettersAt p (seatAt h iU3) e with
        | error m => rw [hl] at hv; cases hv
        | ok w =>
          rw [hl] at hv
          exact congrArg Except.ok (Option.some.inj hv)
      rw [letters_alike h iU3 p a v hl]
      rfl
    have k3 : K3.unpaid F' g.owedJoin = true := by
      unfold K3.unpaid at j3 ⊢
      rw [howed]
      exact j3
    have hs' : run 0 s' = .ok ([asClaim (Came.joinForm g KF)], s'.putFork (F'.paid g.owedJoin)) :=
      bwd 0 s' _ ((join_iff _ 0 s' _).2 ⟨F', g, KF, hF', (lookHeard_alike a).trans j2, k3, k4, j5,
        rfl⟩) (congrArg (·.reply) (out_putFork s' _))
    rw [hs', hF']
    simp only
    rw [S.fork_putFork e F _ hF] at hR
    rw [S.fork_putFork s' F' _ hF']
    simp only [Option.bind_some] at hR ⊢
    rw [lateOf_got F (F.paid g.owedJoin) rfl] at hR
    rw [lateOf_got F' (F'.paid g.owedJoin) rfl]
    have ht : ([asClaim (Came.joinForm g KF)].all fun c => c.runs.isEmpty && c.eqFirst.isNone &&
        c.form.ents.all (ownRow F')) = ([asClaim (Came.joinForm g KF)].all fun c =>
        c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (ownRow F)) := by
      congr 1
      funext c
      congr 1
      congr 1
      funext x
      exact ownRow_same hrow x
    rw [ht]
    exact hR

/-! ## 2 silent_is_run -/

section Rides

variable (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Par) (l piece : Nat)

/-- **THE WAY BACK**: where the kind's own run answers and leaves the heard reply, the run that
stands at the link's hearing block number b under that name gives that answer. -/
structure K6Back (states : Nat → List (RunOf S)) (b : Nat) : Prop where
  own : ∀ name run run', (states b).find? (fun r => r.1 == name) = some (name, run) →
    (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run' →
    ∀ k t y, run' k t = .ok y → y.2.out.reply = t.out.reply → run k t = .ok y
  join : ∀ run, (states b).find? (fun r => r.1 == "join") = some ("join", run) →
    ∀ k t y, K3.joinRun (K3.seatCalls asClaim) (callerKeys p (seatAt h iU3)) k t = .ok y →
      y.2.out.reply = t.out.reply → run k t = .ok y

variable {h iU3 p l piece}

/-- **k6Silent BEHIND THE HEAD's OWN BLOCK IS THE RUN ITSELF BEHIND THE SENDING OF THE READS AND THE
READS' QUIET STEP: AN EQUATION OF OPTIONS**, at all four runs: where the one answers, the other
gives that answer; where the one is silent, so is the other. -/
theorem silent_is_run {states : Nat → List (RunOf S)} {b : Nat}
    (KS : K6States h iU3 p l piece states b) (KB : K6Back h iU3 p l piece states b)
    {Cl : Type} {Q : K1.Par} {link moment : Nat} {arrays : Option (List Nat)}
    {P : K8.ReadsQuiet.PH} {s s1 s' : S} {a : HeadOwn} {rs rs' : List Fmt.RoundView}
    {gs gs' : List (List (Nat × List UInt64))} (ha : s.here = .head a)
    (h1 : (commitAtS (Cl := Cl) Q link moment arrays).decide s rs gs = .ok s1)
    (h2 : (K8.ReadsQuiet.head P).decide s1 rs' gs' = .ok s') (name : String) (hn : K6Name name) :
    readerOf states b name s' = k6Silent P states b name s := by
  obtain ⟨cov, x, tt, o', hop, g2, g3, g4, g5, g6, g6', g7, g8⟩ := reads_laid_alike ha h1 h2
  have he : withTables P s = some { s with here := .head { a with t := some tt } } :=
    (withTables_iff P s _).2 ⟨a, cov, x, tt, ha, hop, g2, g3, g4, rfl⟩
  have hk : k6Silent P states b name s =
      readerOf states b name { s with here := .head { a with t := some tt } } := by
    unfold k6Silent
    rw [he]
    rfl
  rw [hk]
  by_cases hj : name = "join"
  · subst hj
    obtain ⟨run, hfj, fwd⟩ := KS.join
    have hop' : o'.opened = true := by
      obtain ⟨o, o2, e1, e2, _, _, _, e6, _⟩ := g6
      rw [g5] at e2
      injection e2 with e2
      injection e1 with e1
      rw [e2, e6, ← e1]
      exact hop
    have hF : ({ s with here := .head { a with t := some tt } } : S).fork? = some a.F := by
      unfold S.fork?
      simp [hop]
    have hF' : s'.fork? = some o'.F := by
      unfold S.fork?
      rw [g5]
      simp [hop']
    cases h3 : readerOf states b "join" { s with here := .head { a with t := some tt } } with
    | some R => exact reader_rides_join h iU3 p hfj fwd (KB.join run hfj) g6 hF hF' g7 g8 h3
    | none =>
      cases h4 : readerOf states b "join" s' with
      | none => rfl
      | some R =>
        have := reader_rides_join h iU3 p hfj fwd (KB.join run hfj) g6' hF' hF g7.symm g8.symm h4
        rw [h3] at this
        cases this
  · have hn' : name = "norm" ∨ name = "policy" ∨ name = "logits" := by
      rcases hn with q | q | q | q
      · exact Or.inl q
      · exact Or.inr (Or.inl q)
      · exact Or.inr (Or.inr q)
      · exact absurd q hj
    obtain ⟨run, run', hf, hrun, fwd⟩ := KS.own name hn'
    exact rides_of_laid h iU3 l piece p hf hrun fwd (KB.own name run run' hf hrun) hop g5 g6 g6' g7

/-- Where the quiet step's own tables are laid already, withTables lays them again: the record is
as it was. -/
theorem withTables_laid {P : K8.ReadsQuiet.PH} {t : S} {o : HeadOwn}
    {cov : OnBytes.Model.Head.Covered} {x : OnBytes.Model.Head.Heard}
    {tt : OnBytes.Model.Head.Tables} (ho : t.here = .head o) (hop : o.opened = true)
    (hc : t.covered P.h.T P.h.V = .ok cov) (hx : o.x = some x)
    (ht : K8.ReadsQuiet.tables P.h P.L P.hp cov x = .ok tt) (hto : o.t = some tt) :
    withTables P t = some t := by
  refine (withTables_iff P t t).2 ⟨o, cov, x, tt, ho, hop, hc, hx, ht, ?_⟩
  have e1 : ({ o with t := some tt } : HeadOwn) = o := by
    rw [← hto]
  rw [e1, ← ho]

/-- **ONE ANSWER AT THE TWO RECORDS**, at the table's own filling of the readers: where no tables
are laid at the earlier record. (Whether k6Silent answers there is not asked.) -/
theorem readers_one (Lk : Link S Claim) {b : Nat}
    (KS : K6States h iU3 p l piece (K9.statesOfLink Lk) b)
    (KB : K6Back h iU3 p l piece (K9.statesOfLink Lk) b)
    {Cl : Type} {Q : K1.Par} {link moment : Nat} {arrays : Option (List Nat)}
    {P : K8.ReadsQuiet.PH} (small : S → Option K9.Read) {s s1 s' : S} {o : HeadOwn}
    {rs rs' : List Fmt.RoundView} {gs gs' : List (List (Nat × List UInt64))}
    (ho : s.here = .head o) (hno : o.t = none)
    (h1 : (commitAtS (Cl := Cl) Q link moment arrays).decide s rs gs = .ok s1)
    (h2 : (K8.ReadsQuiet.head P).decide s1 rs' gs' = .ok s') (name : String) (hn : K6Name name) :
    (K9.readersOfLink ⟨small, k6Silent P (K9.statesOfLink Lk)⟩ Lk).forms b name s' =
      (K9.readersOfLink ⟨small, k6Silent P (K9.statesOfLink Lk)⟩ Lk).forms b name s := by
  rw [readers_silent h iU3 p l piece b Lk KS P small s o ho hno name hn]
  have hne : (name == "K8.equations") = false := by
    rcases hn with rfl | rfl | rfl | rfl <;> decide
  have e := silent_is_run KS KB ho h1 h2 name hn
  show (if name == "K8.equations" then small s'
    else match readerOf (K9.statesOfLink Lk) b name s' with
      | some R => some R
      | Option.none => k6Silent P (K9.statesOfLink Lk) b name s') = _
  rw [hne]
  cases h3 : readerOf (K9.statesOfLink Lk) b name s' with
  | some R =>
    rw [← e, h3]
    rfl
  | none =>
    rw [← e, h3]
    obtain ⟨cov, x, tt, o', hop, g2, g3, g4, g5, g6, _, _, _⟩ := reads_laid_alike ho h1 h2
    obtain ⟨oa, ob, e1, e2, ex, _, et, eo, _, er, eq, _, _⟩ := g6
    rw [g5] at e2
    injection e2 with e2
    injection e1 with e1
    subst e2
    subst e1
    have hc : s'.covered P.h.T P.h.V = .ok cov := by
      rw [← g2]
      unfold S.covered S.replyTok? S.coveredAt
      rw [er, eq]
    show k6Silent P (K9.statesOfLink Lk) b name s' = none
    unfold k6Silent
    rw [withTables_laid g5 (eo.trans hop) hc (ex.trans g3) g4 et]
    exact h3

end Rides

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.reader_rides_join
#print axioms VerifiableInference.Desc.Kinds.Head.Law.silent_is_run
#print axioms VerifiableInference.Desc.Kinds.Head.Law.readers_one
