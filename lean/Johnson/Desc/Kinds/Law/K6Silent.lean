-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
tablesAt, withTables, k6Silent MOVED, TO THE LETTER, INTO Law/K6SilentCode.lean (code
alone; no law; no Mathlib), for the harnesses. What this head says of them holds there.
Johnson/Desc/Kinds/Law/K6Silent.lean: FOR THE TABLE OF JOINTS' BORDER RIGHT BEHIND THE OUTPUT HEAD's
OWN BLOCK (in front of the sending of the reads):
(1) A FILLING OF THE LETTER "silent" (the reader of a run where the run itself is silent:
    Johnson/Desc/First/Batch/ReadersOfLink.lean: LinkHoles): the run itself, at the record WITH THE
    TABLES OF READS LAID AS THE READS' QUIET STEP WILL LAY THEM;
(2) what that reader answers at the head's four runs;
(3) FROM THE TABLE's ITEM formsT AT THESE FOUR RUNS, AT ONE RECORD, TO K6Out (Law/RowPins.lean: the
    fifth premise of the head's law).
Definitions, statements and proofs.

WHY. At that border the head's runs refuse: they read the places of the reads' tables off the
record's field t, which is laid one block later. But the tables are a function of public numbers, of
the request's words, of the heard reply and of what the head's own rounds heard
(Johnson/Desc/K8/ReadsQuiet.lean: tables): all of which lie in the record behind the head's yes.

  tablesAt P s     the tables that the reads' quiet step makes at the record s: its own text's three
                   readers and its own function, in its order.
  withTables P s   the record with these tables laid in t, nothing else turned.
  k6Silent P states   THE FILLING: block b, run name, record s: the run itself (readerOf) at
                   withTables P s.
  lateOf_got       a run that fills no slot has no late slot.
  withTables_iff   what withTables lays, both ways, by the quiet step's own readers and function.
  withTables_spec, front_withTables, back_withTables, fork_withTables   what withTables turns: t
                   alone. seg_fork: the ledger of the open segment's part is the record's.
  K6States         which runs stand at the link's hearing block number b under the four names: A
                   NAMED PREMISE, in the form "where it answers, the kind's own run answers the
                   same": so a run in a guard's dress is admitted.
  K6Name, join_iff   the four names; where "join" answers, both ways.
  readers_silent   where no tables are laid the link's readers ask "silent" at the four names.
  reader_own, reader_join   what the run's reader answers at the head's four runs: the forms at the
                   letters that are read at the record; no late slot.
  k6Out_of_items   MAIN: see its docstring.

WHAT IT IS NOT. AN IMPLICATION. ASSUMED, BY NAME:
  hRd       at this record the table's readers answer as k6Silent does, AT THE FOUR NAMES:
            readers_silent pays it at the table's own readersOfLink, where
            NO TABLES ARE LAID at the record (o.t = none): THAT is a fact on the record with no
            payer
  K6States  other files' to show: the walked runs are the kind's
  hT        K6HeardAt at the record (Law/K6PromiseBorder.lean: k6_border pays it from the yes)
  hmask     the stated data's mask row is the components', AT THE ENTRIES IN USE (below the number
  of
            the ledger's factors; beyond it the factor is 0 and nothing reads the row)
  hA        the stated data's cells of the reads' array are, below each read's length, the reads in
            truth of the components' cells: WITH hmask A SPECIFICATION OF THE TABLE's LETTER
            Stated.at1 AND OF THE READER OF THE COMPONENTS: paid by nobody
  hWt       WeightAt (Law/MergeClaimAt.lean): the sentence on the weights
  hbare     the lookup's last claim names no entry
  hok       the tests on the plan
That k6Silent answers at a real record is shown by nothing here. That its answer is the run's own
one block later: not here. The planes' three forms: the filling covers them (it is general in block
and name); nothing is proved of them. Nothing on soundness.
LETTERS. No letter stands under "there is" in the top. In hA: e, v: under "for all", pinned by
withTables P s = some e and lettersAt ... e = .ok v. b: the block's number in the link's list of
hearing blocks (at the head's link: 3); piece: the place's piece (4).

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K6Claims
import Johnson.Desc.Kinds.Law.K6SilentCode
import Johnson.Desc.First.Batch.ReadersOfLink
import Johnson.Desc.Sound.FormsQ

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff Reading World)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (Block Claim Link)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K9 (Readers readerOf lateOf segAt? RunOf)
open VerifiableInference.Desc.Sound (Stated formsTQ worldOwn dataQ slotW)
open Norm (lt ls d lPd T S2)

/-! ## 1 The filling -/

-- tablesAt, withTables, k6Silent: Law/K6SilentCode.lean (code alone).

/-! ## 2 Tools -/

theorem lateOf_got (F G : Fork) (h : G.gotF = F.gotF) : lateOf F G = [] := by
  unfold lateOf
  rw [List.filterMap_eq_nil_iff]
  intro j _
  rw [h]
  cases F.gotF.getD j false <;> rfl

theorem withTables_spec {P : K8.ReadsQuiet.PH} {s e : S} (h : withTables P s = some e) :
    ∃ (a : HeadOwn) (tt : OnBytes.Model.Head.Tables), s.here = .head a ∧
      e = { s with here := .head { a with t := some tt } } := by
  unfold withTables at h
  cases hh : s.here with
  | head a =>
    rw [hh] at h
    obtain ⟨tt, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨a, tt, rfl, rfl⟩
  | _ => rw [hh] at h; cases h

/-- **What withTables lays, both ways**: the reads' quiet step's own three readers and its own
function, by name. -/
theorem withTables_iff (P : K8.ReadsQuiet.PH) (s e : S) :
    withTables P s = some e ↔ ∃ (a : HeadOwn) (cov : OnBytes.Model.Head.Covered)
      (x : OnBytes.Model.Head.Heard) (tt : OnBytes.Model.Head.Tables), s.here = .head a ∧
      a.opened = true ∧ s.covered P.h.T P.h.V = .ok cov ∧ a.x = some x ∧
      K8.ReadsQuiet.tables P.h P.L P.hp cov x = .ok tt ∧
      e = { s with here := .head { a with t := some tt } } := by
  constructor
  · intro h
    unfold withTables at h
    cases hh : s.here with
    | head a =>
      rw [hh] at h
      obtain ⟨tt, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      unfold tablesAt at ht
      rw [hh] at ht
      by_cases ho : a.opened = true
      · simp only [ho, if_true] at ht
        obtain ⟨cov, hc, h2⟩ := Option.bind_eq_some_iff.mp ht
        obtain ⟨x, hx, h3⟩ := Option.bind_eq_some_iff.mp h2
        refine ⟨a, cov, x, tt, rfl, ho, ?_, hx, ?_, rfl⟩
        · cases hcv : s.covered P.h.T P.h.V with
          | error m => rw [hcv] at hc; cases hc
          | ok c' =>
            rw [hcv] at hc
            exact congrArg Except.ok (Option.some.inj hc)
        · cases htb : K8.ReadsQuiet.tables P.h P.L P.hp cov x with
          | error m => rw [htb] at h3; cases h3
          | ok t' =>
            rw [htb] at h3
            exact congrArg Except.ok (Option.some.inj h3)
      · simp [ho] at ht
    | _ => rw [hh] at h; cases h
  · rintro ⟨a, cov, x, tt, ha, ho, hc, hx, ht, rfl⟩
    have h1 : tablesAt P s = some tt := by
      unfold tablesAt
      rw [ha]
      simp only [ho, if_true, hc, hx, ht, Except.toOption, Option.bind_some]
    unfold withTables
    rw [ha]
    simp only [h1, Option.map_some]

theorem front_withTables {P : K8.ReadsQuiet.PH} {s e : S} (h : withTables P s = some e) :
    AlikeFront s e := by
  obtain ⟨a, tt, ha, rfl⟩ := withTables_spec h
  exact ⟨a, _, ha, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Later.refl _⟩

theorem back_withTables {P : K8.ReadsQuiet.PH} {s e : S} (h : withTables P s = some e) :
    AlikeFront e s := by
  obtain ⟨a, tt, ha, rfl⟩ := withTables_spec h
  exact ⟨_, a, rfl, ha, rfl, rfl, rfl, rfl, rfl, rfl, Later.refl _⟩

theorem fork_withTables {P : K8.ReadsQuiet.PH} {s e : S} (h : withTables P s = some e) :
    e.fork? = s.fork? ∧ e.lookHeard? = s.lookHeard? := by
  obtain ⟨a, tt, ha, rfl⟩ := withTables_spec h
  unfold S.fork? S.lookHeard?
  rw [ha]
  exact ⟨rfl, rfl⟩

/-- The ledger of the open segment's part is the record's. -/
theorem seg_fork {s : S} {a : K9.Part} (h : segAt? s = some a) : s.fork? = some a.F := by
  have h' : (do
    let L ← s.link?
    let F ← s.fork?
    let tl ← s.tl?
    pure ({ owed := K9.owedOf s, used := (K9.usedOf s).getD 0, laid := K9.laidOf tl, L := L, F := F,
            d := { st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } } :
      K9.Part)) = some a := h
  cases h1 : s.link? with
  | none => rw [h1] at h'; cases h'
  | some L =>
    cases h2 : s.fork? with
    | none => rw [h1, h2] at h'; cases h'
    | some F =>
      cases h3 : s.tl? with
      | none => rw [h1, h2, h3] at h'; cases h'
      | some tl =>
        rw [h1, h2, h3] at h'
        have e5 := Option.some.inj h'
        rw [← e5]

/-- The names of the head's four runs. -/
def K6Name (name : String) : Prop :=
  name = "norm" ∨ name = "policy" ∨ name = "logits" ∨ name = "join"

/-- **Where "join" answers, both ways**: a sub-proof is open; the lookup has heard; the debt is not
yet marked; the caller's keys are there; one form and one weight a call. -/
theorem join_iff (keys : S → Option (Array Aff)) (n : Nat) (s : S) (y : List Claim × S) :
    K3.joinRun (K3.seatCalls asClaim) keys n s = .ok y ↔
      ∃ (F : Fork) (g : OnBytes.Model.Forest.Heard) (KF : Array Aff), s.fork? = some F ∧
        s.lookHeard? = some g ∧ K3.unpaid F g.owedJoin = true ∧ keys s = some KF ∧
        (KF.size == g.shape.calls.size && g.e.size == g.shape.calls.size) = true ∧
        y = ([asClaim (Came.joinForm g KF)], s.putFork (F.paid g.owedJoin)) := by
  constructor
  · intro hy
    unfold K3.joinRun at hy
    simp only [bind, Except.bind] at hy
    cases hF : (K3.seatCalls asClaim).fork s with
    | none => simp [hF, named] at hy
    | some F =>
      cases hg : (K3.seatCalls asClaim).heard s with
      | none => simp [hF, hg, named] at hy
      | some g =>
        simp only [hF, hg, named] at hy
        cases hu : K3.unpaid F g.owedJoin with
        | false => simp [hu, need] at hy
        | true =>
          simp only [hu, need, if_true] at hy
          cases hK : keys s with
          | none => simp [hK] at hy
          | some KF =>
            simp only [hK] at hy
            cases hj : First.Look.joinF g KF F [] with
            | none => simp [hj] at hy
            | some x =>
              simp only [hj] at hy
              obtain ⟨hb, hG, _, hx⟩ := (Came.joinF_spec g KF F x.2.1 [] x.2.2 x.1).mp hj
              refine ⟨F, g, KF, hF, hg, hu, rfl, hb, ?_⟩
              rw [← Except.ok.inj hy, ← hx, ← hG]
              rfl
  · rintro ⟨F, g, KF, hF, hg, hu, hK, hb, rfl⟩
    have hj : First.Look.joinF g KF F [] = some (Came.joinForm g KF, F.paid g.owedJoin, []) :=
      (Came.joinF_spec g KF F _ [] [] _).mpr ⟨hb, rfl, rfl, rfl⟩
    have hF' : (K3.seatCalls asClaim).fork s = some F := hF
    have hg' : (K3.seatCalls asClaim).heard s = some g := hg
    unfold K3.joinRun
    simp only [bind, Except.bind, hF', hg', named, hu, need, if_true, hK, hj]
    rfl

section Readers

variable (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Par) (l piece : Nat)

/-- **Which runs stand at the link's hearing block number b under the four names**: each is there,
and where it answers, the kind's own run of that name gives the same answer. (So a run in a guard's
dress is admitted. The way back, which the law that the reader's answer rides wants, is that law's
own
premise, not this structure's.) -/
structure K6States (states : Nat → List (RunOf S)) (b : Nat) : Prop where
  own : ∀ name, name = "norm" ∨ name = "policy" ∨ name = "logits" → ∃ run run',
    (states b).find? (fun r => r.1 == name) = some (name, run) ∧
      (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run' ∧
      ∀ k t y, run k t = .ok y → run' k t = .ok y
  join : ∃ run, (states b).find? (fun r => r.1 == "join") = some ("join", run) ∧
    ∀ k t y, run k t = .ok y →
      K3.joinRun (K3.seatCalls asClaim) (callerKeys p (seatAt h iU3)) k t = .ok y

variable {h iU3 p l piece}

/-- What the run's reader answers at one of the head's three own runs. -/
theorem reader_own {states : Nat → List (RunOf S)} {b : Nat}
    (K : K6States h iU3 p l piece states b)
    (name : String) (hn : name = "norm" ∨ name = "policy" ∨ name = "logits") (e : S) (R : K9.Read)
    (hR : readerOf states b name e = some R) :
    ∃ v fs, lettersAt p (seatAt h iU3) e = .ok v ∧ (claimsSeat v).lookup name = some fs ∧
      R.forms = fs ∧ R.late = [] := by
  obtain ⟨run, run', hf, hrun, hans⟩ := K.own name hn
  unfold readerOf at hR
  rw [hf] at hR
  simp only [Option.bind_some] at hR
  cases hr : run 0 e with
  | error m => rw [hr] at hR; cases hR
  | ok z =>
    rw [hr] at hR
    cases hF : e.fork? with
    | none => rw [hF] at hR; cases hR
    | some F =>
      rw [hF] at hR
      simp only at hR
      obtain ⟨G, hG, h2⟩ := Option.bind_eq_some_iff.mp hR
      have hr' := hans 0 e z hr
      obtain ⟨g, bh, x, fs, k1, k2, k3⟩ :=
        k6_run_spec asClaim (seatAt h iU3) l piece p name run' 0 e z.2 z.1 hrun hr'
      have hz : z.2 = e := k6_same h iU3 l piece p (name, run') (lookup_mem _ _ _ hrun) 0 e z hr'
      rw [hz, hF] at hG
      obtain rfl := Option.some.inj hG
      split at h2
      · obtain rfl := Option.some.inj h2
        refine ⟨(g, bh, x), fs, k1, k2, ?_, lateOf_got _ _ rfl⟩
        show z.1.map (·.form) = fs
        rw [k3, List.map_map]
        exact List.map_id _
      · cases h2

/-- What the run's reader answers at "join". -/
theorem reader_join {states : Nat → List (RunOf S)} {b : Nat}
    (K : K6States h iU3 p l piece states b)
    (e : S) (R : K9.Read) (hR : readerOf states b "join" e = some R) :
    ∃ v gk, lettersAt p (seatAt h iU3) e = .ok v ∧ e.lookHeard? = some gk ∧
      R.forms = [Came.joinForm gk (keyVectorsAt v)] ∧ R.late = [] := by
  obtain ⟨run, hfj, hans⟩ := K.join
  unfold readerOf at hR
  rw [hfj] at hR
  simp only [Option.bind_some] at hR
  cases hr0 : run 0 e with
  | error m => rw [hr0] at hR; cases hR
  | ok z =>
    rw [hr0] at hR
    have hr := hans 0 e z hr0
    cases hF : e.fork? with
    | none => rw [hF] at hR; cases hR
    | some F =>
      rw [hF] at hR
      simp only at hR
      obtain ⟨G, hG, h2⟩ := Option.bind_eq_some_iff.mp hR
      obtain ⟨F', gk, KF, j1, j2, j3, j4, _⟩ := join_spec _ 0 e z.1 z.2 hr
      obtain ⟨a, i, a1, a2⟩ := join_hands h iU3 p 0 e z.1 z.2 hr
      have hgot : G.gotF = F.gotF := by
        unfold S.fork? at hF hG
        rw [a2] at hG
        rw [a1] at hF
        by_cases ho : a.opened = true
        · simp only [ho, if_true, Option.some.injEq] at hF hG
          rw [← hF, ← hG]
          rfl
        · simp [ho] at hF
      unfold callerKeys at j3
      obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp j3
      have hl : lettersAt p (seatAt h iU3) e = .ok v := by
        cases hl : lettersAt p (seatAt h iU3) e with
        | error m => rw [hl] at hv; cases hv
        | ok w =>
          rw [hl] at hv
          exact congrArg Except.ok (Option.some.inj hv)
      split at h2
      · obtain rfl := Option.some.inj h2
        refine ⟨v, gk, hl, j2, ?_, lateOf_got _ _ hgot⟩
        show z.1.map (·.form) = _
        rw [j4]
        rfl
      · cases h2

end Readers

/-- **WHERE NO TABLES ARE LAID THE LINK's READERS ASK "silent" AT THE HEAD's FOUR RUNS**: so hRd of
k6Out_of_items holds at the table's own filling of the readers, whatever its first hole holds. -/
theorem readers_silent (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Par) (l piece b : Nat)
    (Lk : Link S Claim) (K : K6States h iU3 p l piece (K9.statesOfLink Lk) b)
    (P : K8.ReadsQuiet.PH) (small : S → Option K9.Read) (s : S) (o : HeadOwn)
    (ho : s.here = .head o) (ht : o.t = none) (name : String) (hn : K6Name name) :
    (K9.readersOfLink ⟨small, k6Silent P (K9.statesOfLink Lk)⟩ Lk).forms b name s =
      k6Silent P (K9.statesOfLink Lk) b name s := by
  have hne : (name == "K8.equations") = false := by
    rcases hn with rfl | rfl | rfl | rfl <;> decide
  have hno : ∀ v, lettersAt p (seatAt h iU3) s ≠ .ok v := by
    intro v hv
    obtain ⟨_, x, _, _, k3, _⟩ := lettersAt_ok h iU3 p hv
    unfold seatAt at k3
    dsimp only at k3
    split at k3
    · rename_i o' F' ho' _
      rw [ho] at ho'
      obtain rfl : o = o' := by injection ho'
      rw [ht] at k3
      simp at k3
    · cases k3
  have hnone : readerOf (K9.statesOfLink Lk) b name s = none := by
    cases hR : readerOf (K9.statesOfLink Lk) b name s with
    | none => rfl
    | some R =>
      exfalso
      rcases hn with h1 | h1 | h1 | h1
      · obtain ⟨v, _, hv, _⟩ := reader_own K name (Or.inl h1) s R hR
        exact hno v hv
      · obtain ⟨v, _, hv, _⟩ := reader_own K name (Or.inr (Or.inl h1)) s R hR
        exact hno v hv
      · obtain ⟨v, _, hv, _⟩ := reader_own K name (Or.inr (Or.inr h1)) s R hR
        exact hno v hv
      · subst h1
        obtain ⟨v, _, hv, _⟩ := reader_join K s R hR
        exact hno v hv
  show (if name == "K8.equations" then small s
    else match readerOf (K9.statesOfLink Lk) b name s with
      | some R => some R
      | Option.none => k6Silent P (K9.statesOfLink Lk) b name s) = _
  rw [hne, hnone]
  rfl

/-! ## 3 From the table's items to K6Out -/

/-- **FROM formsT AT THE HEAD's FOUR RUNS, AT ONE RECORD, TO K6Out: AN IMPLICATION.** s: the record
behind the head's own block; rdW: the witness's messages; d: the components. The four runs are TWO
of
the four items that the table's row opens there: "own" (as three runs) and "join". ASSUMED BESIDE
THEM: K6States; hRd (the readers answer as k6Silent does, at the four names); the tests on the plan;
K6HeardAt at s (its first two clauses ARE two conjuncts of K6Out); hmask and hA (the stated data's
mask row and cells of the reads' array against the components); WeightAt (a conjunct of K6Out, word
for word); that the lookup's last claim names no entry. It would go through for any laying of t:
that
the tables are the quiet step's is spent by the law that the reader's answer rides, not here. -/
theorem k6Out_of_items (W : OnBytes.Model.Verify.Public) (P : K8.ReadsQuiet.PH) (l piece b : Nat)
    (states : Nat → List (RunOf S))
    (K : K6States W.hS (readsOf W) (parOf W.hS (workOf W)) l piece states b)
    (Rd : Readers) (St : Stated) (own : List (Nat × Nat)) (s : S) (rdW : Nat × Nat → Sound.MsgQ)
    (d : Pinned) (a : K9.Part) (ha : segAt? s = some a)
    (hRd : ∀ name, K6Name name → Rd.forms b name s = k6Silent P states b name s)
    (hok : (parOf W.hS (workOf W)).ok = true)
    (hT : K6HeardAt W.hS (readsOf W) (parOf W.hS (workOf W)) s)
    (hmask : ∀ j, j < a.F.mf.size → (St.at1 s (dataQ own a rdW)).mask j = rd (d.2 j))
    (hA : ∀ e v, withTables P s = some e →
      lettersAt (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) e = .ok v →
      (letI := v.1
       letI := v.2.1
       EntriesAlike (worldOwn a [] (St.at1 s (dataQ own a rdW)))
         (worldE ((seatAt W.hS (readsOf W)).ledger s) d.2 noEnt)
         v.2.2.final (normReadsAtCells d.1) v.2.2.head (readsAt d.1.toCells)))
    (hWt : WeightAt W s d.1.toCells d.2)
    (hbare : ∀ gk, s.lookHeard? = some gk → gk.cEnd.ents = #[])
    (hn : formsTQ Rd St own b "norm" s rdW) (hp : formsTQ Rd St own b "policy" s rdW)
    (hl : formsTQ Rd St own b "logits" s rdW) (hj : formsTQ Rd St own b "join" s rdW) :
    K6Out W s d := by
  obtain ⟨g, H, F0, G, rs, hg, hH, hW0, hh, hLt⟩ := hT
  obtain ⟨Fa, Fb, lr, hNorm, _, _, _, _, _⟩ := Came.hear_parts hW0 hh
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h4, _, _⟩ := norm_parts hW0 hNorm
  have h6 : OnBytes.okE (H.1.P.getD 6 {}).var.const = true := batch_okConst h4 6
  have hB := heardBare_of_hear hW0 hh
  -- what an item says
  have item : ∀ name, K6Name name → formsTQ Rd St own b name s rdW → ∃ e R,
      withTables P s = some e ∧
      readerOf states b name e = some R ∧ ∀ f ∈ R.forms,
        f.value Reading.gl (worldOwn a R.late (St.at1 s (dataQ own a rdW))) = 0 := by
    rintro name hnm ⟨a', R, ha', hR, _, hf⟩
    obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
    rw [hRd name hnm] at hR
    obtain ⟨e, he, hR'⟩ := Option.bind_eq_some_iff.mp hR
    exact ⟨e, R, he, hR', fun f hm => (hf f hm).2⟩
  obtain ⟨e, Rn, he, hRn, zn⟩ := item "norm" (Or.inl rfl) hn
  obtain ⟨e2, Rp, he2, hRp, zp⟩ := item "policy" (Or.inr (Or.inl rfl)) hp
  obtain rfl : e = e2 := Option.some.inj (he.symm.trans he2)
  obtain ⟨e3, Rl, he3, hRl, zl⟩ := item "logits" (Or.inr (Or.inr (Or.inl rfl))) hl
  obtain rfl : e = e3 := Option.some.inj (he.symm.trans he3)
  obtain ⟨e4, Rj, he4, hRj, zj⟩ := item "join" (Or.inr (Or.inr (Or.inr rfl))) hj
  obtain rfl : e = e4 := Option.some.inj (he.symm.trans he4)
  obtain ⟨v, fsn, hv, ln, en, tn⟩ := reader_own K "norm" (Or.inl rfl) e Rn hRn
  obtain ⟨v2, fsp, hv2, lp, ep, tp⟩ := reader_own K "policy" (Or.inr (Or.inl rfl)) e Rp hRp
  obtain rfl : v = v2 := Except.ok.inj (hv.symm.trans hv2)
  obtain ⟨v3, fsl, hv3, ll, el, tl⟩ := reader_own K "logits" (Or.inr (Or.inr rfl)) e Rl hRl
  obtain rfl : v = v3 := Except.ok.inj (hv.symm.trans hv3)
  obtain ⟨v4, gk, hv4, hgke, ej, tj⟩ := reader_join K e Rj hRj
  obtain rfl : v = v4 := Except.ok.inj (hv.symm.trans hv4)
  rw [tn, en] at zn
  rw [tp, ep] at zp
  rw [tl, el] at zl
  rw [tj, ej] at zj
  -- the letters at e are the record's own
  have hse := front_withTables he
  obtain ⟨H', x, k1, k2, _, k4⟩ := lettersAt_ok W.hS (readsOf W) (parOf W.hS (workOf W)) hv
  have e1 : (Except.ok v.1 : Except String Given) = .ok g := by
    rw [← k1, given_front W.hS (readsOf W) _ hse, hg]
  obtain rfl := Except.ok.inj e1
  have e2 := heard_front W.hS (readsOf W) hse H hH
  rw [k2] at e2
  obtain rfl := Option.some.inj e2
  have eH : (v.2.1.norm, v.2.1.final, v.2.1.head) = H' := by rw [k4]
  have hgk : s.lookHeard? = some gk := by rw [← (fork_withTables he).2]; exact hgke
  -- the part's ledger is the record's
  have hF : (seatAt W.hS (readsOf W)).ledger s = a.F := by
    show s.fork?.getD {} = a.F
    rw [seg_fork ha]
    rfl
  have hslot : ∀ j, (worldOwn a [] (St.at1 s (dataQ own a rdW))).slot j =
      (worldE ((seatAt W.hS (readsOf W)).ledger s) d.2 noEnt).slot j := by
    intro j
    rw [worldE_eq, hF]
    show slotW a.F [] _ j = _
    rw [Sound.slotW_ledger a.F [] _ j rfl]
    show _ =
      Reading.gl.val (a.F.vp.getD j zeroE) - Reading.gl.val (a.F.mf.getD j zeroE) * rd (d.2 j)
    by_cases hj : j < a.F.mf.size
    · rw [hmask j hj]
    · have e0 : a.F.mf.getD j zeroE = zeroE := by
        simp [Array.getD, hj]
      rw [e0, Reading.gl.zero, zero_mul, zero_mul]
  obtain ⟨hd, hJ⟩ := sizes_of_plan _ _ e v.1 hok k1
  subst eH
  refine k6Out_of_claims W s d v.1 _ (v.2.2.final, v.2.2.head) gk
    (worldOwn a [] (St.at1 s (dataQ own a rdW))) hg hH hgk h6
    (k6Exchange_of_entries v.1 _ (v.2.2.final, v.2.2.head) d.1 _ _ hslot (hA e v he hv) hB hd hJ)
    hWt (fun name fs hlk f hf => ?_) (zj _ List.mem_cons_self) ?_
  · have hlk' : (claimsSeat v).lookup name = some fs := hlk
    by_cases n1 : name = "norm"
    · subst n1
      rw [ln] at hlk'
      obtain rfl := Option.some.inj hlk'
      exact zn f hf
    · by_cases n2 : name = "policy"
      · subst n2
        rw [lp] at hlk'
        obtain rfl := Option.some.inj hlk'
        exact zp f hf
      · by_cases n3 : name = "logits"
        · subst n3
          rw [ll] at hlk'
          obtain rfl := Option.some.inj hlk'
          exact zl f hf
        · exfalso
          have b1 : (name == "norm") = false := by simpa using n1
          have b2 : (name == "policy") = false := by simpa using n2
          have b3 : (name == "logits") = false := by simpa using n3
          unfold claimsSeat claims at hlk'
          simp only [List.lookup_cons, List.lookup_nil, b1, b2, b3] at hlk'
          cases hlk'
  · unfold vW
    refine value_agree0 Reading.gl _ _ gk.cEnd (fun y _ => hslot y.1) fun y hy => ?_
    rw [hbare gk hgk] at hy
    simp at hy

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.reader_own
#print axioms VerifiableInference.Desc.Kinds.Head.Law.reader_join
#print axioms VerifiableInference.Desc.Kinds.Head.Law.withTables_iff
#print axioms VerifiableInference.Desc.Kinds.Head.Law.join_iff
#print axioms VerifiableInference.Desc.Kinds.Head.Law.readers_silent
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6Out_of_items
