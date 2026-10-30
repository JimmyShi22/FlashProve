-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/GatherFold.lean: THE TWO PREMISES ON THE GATHERER (`GatherKeeps`, `KeysSame`:
Honest/K9/LedgerOf.lean), CUT RUN BY RUN: what each kind owes of ITS OWN runs of claims, and the fold over
the frame's gatherer (`claimsInBy`, Johnson/Desc/Block.lean). Statements and proofs ON THE VERIFIER's TEXT;
no prover is in this file, and no goal is stated.

  `Kept t e`        where K9's lens answers at t it answers at e, with the same core of the ledger
                    (`LedgerCore`, Honest/K9/LedgerOf.lean)
  `RunKeeps run`    WHAT A KIND OWES OF A RUN (1): wherever the run returns, `Kept` from the state in front to
                    the state behind
  `RunTwin R run`   WHAT A KIND OWES OF A RUN (2), at a relation R between two states ("the same but for what
                    hangs on chi"; the caller's): from two states in R, handed the same number, where both
                    return: the claims' keys are the same, and the states behind are in R again
  `claimsRunOf bs o`      the run that an order's entry names
  `step_ok`         a yes of the frame's one step (`claimsInStep`), taken apart
  `gather_keeps`    **every named run keeps ⟹ `GatherKeeps` of the whole gatherer**
  `gather_twin`     **every named run is a twin at R ⟹ from two states in R the whole gatherer yields claims
                    with the same keys, and states in R**
  `runsLaw_of_runs` so `RunsLaw`, from: the runs' two debts · R holds behind the draw at any two challenges · R
                    keeps the merge's slot
  `Ran`, `gather_ran`   **THE THREAD**: the gatherer's list IS the runs' lists in a row, and the runs ran one behind
                    the other FROM THE GATHERER's OWN STATE: each at the state that the one in front left, at
                    the number of claims made so far
  `ran_inv`         an invariant rides along the thread: so a kind may say its share of its run AT THE STATES AT
                    WHICH THE INVARIANT HOLDS, not at every state. ONE invariant for all places: "the run in front
                    has written X" cannot be said by it, and the number handed is forgotten: whoever needs
                    these takes `Ran` itself
  `gather_kept`     every named run keeps ⟹ `Kept` from the gatherer's state to the state behind it (so the lens
                    answers there)
  `slotsLive_of_gather`   so the Bool `K9H.slotsLive` at the gatherer's own list, out of the runs' shares ALONG
                    THAT THREAD (`K9H.slotsLive_of_runs`, Johnson/Desc/K9/Honest/SlotsJoin.lean)
  `slotsLive_of_inv`   **THE PLUG FOR THE KINDS' SHARES**: each kind says its share of its own run, at every number and
                    every state at which an invariant holds that all runs hand on
  `RunUnder`, `RunKeeps.under`, `RunTwin.under`   both debts pass to a run that only refuses more: so from a kind's own
                    run to the run that stands in the description's list, which its makers have wrapped
  `start_of_view`   K9's own share of "R holds behind the draw at any two challenges", at R := "the same view"
  `twin_of_view`    A ONE-STATE ROAD TO `RunTwin`: view : S → α says what of a state does not hang on chi, and R is
                    "the same view". A run whose claims' keys, and whose state's view behind, are functions of
                    the number handed and of the view in front, is a twin at that R. So a kind need not speak
                    of two states. WHICH VIEW SERVES ALL KINDS' RUNS OF A SEGMENT IS NOT SAID HERE: until one
                    is named, a kind can pay this debt at a view of its own choice only

WHAT IS NOT CLAIMED. That any kind's run pays either debt. The link's test behind each run (`each`) cannot
turn the state, by type. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.LedgerOf
import Johnson.Desc.K9.Honest.SlotsJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim claimsInBy claimsInStep named)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (atS Where mergeOf drawAlone)

/-- Where the lens answers in front it answers behind, with the same core. -/
def Kept (t e : S) : Prop :=
  ∀ a, atS.get? t = some a → ∃ a', atS.get? e = some a' ∧ LedgerCore a a'

theorem Kept.refl (t : S) : Kept t t := fun a ha => ⟨a, ha, LedgerCore.refl a⟩

theorem Kept.trans {t u e : S} (h1 : Kept t u) (h2 : Kept u e) : Kept t e := by
  intro a ha
  obtain ⟨b, hb, c1⟩ := h1 a ha
  obtain ⟨c, hc, c2⟩ := h2 b hb
  exact ⟨c, hc, c1.trans c2⟩

abbrev ClaimsRun : Type := Nat → S → Except String (List Claim × S)

/-- **A kind's first debt of a run.** -/
def RunKeeps (run : ClaimsRun) : Prop := ∀ n t z, run n t = .ok z → Kept t z.2

/-- **A kind's second debt of a run**, at a relation between two states. -/
def RunTwin (R : S → S → Prop) (run : ClaimsRun) : Prop :=
  ∀ n t t' z z', R t t' → run n t = .ok z → run n t' = .ok z' →
    z.1.map slotKey = z'.1.map slotKey ∧ R z.2 z'.2

/-- A run that only refuses more than another: every yes of it is a yes of the other, with the same return. SO
STAND THE RUNS OF THE DESCRIPTION's OWN LIST, WHICH ITS MAKERS HAVE WRAPPED, UNDER THE KINDS' OWN. -/
def RunUnder (run' run : ClaimsRun) : Prop := ∀ n t z, run' n t = .ok z → run n t = .ok z

/-- Both debts pass to a run that only refuses more. -/
theorem RunKeeps.under {run' run : ClaimsRun} (h : RunKeeps run) (hu : RunUnder run' run) : RunKeeps run' :=
  fun n t z hz => h n t z (hu n t z hz)

theorem RunTwin.under {R : S → S → Prop} {run' run : ClaimsRun} (h : RunTwin R run)
    (hu : RunUnder run' run) : RunTwin R run' :=
  fun n t t' z z' hR hz hz' => h n t t' z z' hR (hu n t z hz) (hu n t' z' hz')

/-- The run that an order's entry names. -/
def claimsRunOf (bs : List (Block S Claim)) (o : Nat × String) : Option ClaimsRun :=
  (bs[o.1]?).bind fun b => b.claims.lookup o.2

/-- A yes of the frame's one step, taken apart. -/
theorem step_ok (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (x y : List Claim × S) (o : Nat × String)
    (h : claimsInStep each bs x o = .ok y) :
    ∃ run z, claimsRunOf bs o = some run ∧ run x.1.length x.2 = .ok z ∧ y = (x.1 ++ z.1, z.2) := by
  unfold claimsInStep at h
  obtain ⟨run, hr, h⟩ := bind_ok (x := named (o.2 ++ ": no such run") (claimsRunOf bs o)) h
  have hr' : claimsRunOf bs o = some run := by
    unfold named at hr
    cases hq : claimsRunOf bs o with
    | none => rw [hq] at hr; exact nomatch hr
    | some r => rw [hq] at hr; exact congrArg some (Except.ok.inj hr)
  cases hz : run x.1.length x.2 with
  | error m => simp only [hz] at h; exact nomatch h
  | ok z =>
    simp only [hz] at h
    cases he : each o z.1 z.2 with
    | error m => simp only [he] at h; exact nomatch h
    | ok u =>
      simp only [he] at h
      exact ⟨run, z, hr', hz, (Except.ok.inj h).symm⟩

/-- The gatherer's fold's step. -/
def gatherStep (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (acc : Except String (List Claim × S)) (o : Nat × String) :
    Except String (List Claim × S) :=
  acc.bind fun x => claimsInStep each bs x o

/-- The fold, from any answer so far. -/
theorem fold_ok (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) : ∀ (order : List (Nat × String))
    (acc : Except String (List Claim × S)) (y : List Claim × S),
    order.foldl (gatherStep each bs) acc = .ok y →
      ∃ x, acc = .ok x
  | [], acc, y, h => ⟨y, h⟩
  | o :: l, acc, y, h => by
    rw [List.foldl_cons] at h
    obtain ⟨x', hx'⟩ := fold_ok each bs l _ y h
    obtain ⟨x, hx, _⟩ := bind_ok hx'
    exact ⟨x, hx⟩

theorem fold_keeps (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) : ∀ (order : List (Nat × String)),
    (∀ o ∈ order, ∀ run, claimsRunOf bs o = some run → RunKeeps run) →
    ∀ (x y : List Claim × S),
    order.foldl (gatherStep each bs) (.ok x) = .ok y →
      Kept x.2 y.2
  | [], _, x, y, h => by
    have e : x = y := Except.ok.inj h
    rw [e]
    exact Kept.refl _
  | o :: l, hk, x, y, h => by
    rw [List.foldl_cons] at h
    obtain ⟨x', hx'⟩ := fold_ok each bs l _ y h
    rw [hx'] at h
    obtain ⟨run, z, hr, hz, e⟩ := step_ok each bs x x' o hx'
    have k1 : Kept x.2 x'.2 := by
      rw [e]
      exact hk o List.mem_cons_self run hr _ _ z hz
    exact k1.trans (fold_keeps each bs l (fun o' ho' => hk o' (List.mem_cons_of_mem _ ho')) x' y h)

/-- **Every named run keeps ⟹ the gatherer keeps.** -/
theorem gather_keeps (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (order : List (Nat × String))
    (hk : ∀ o ∈ order, ∀ run, claimsRunOf bs o = some run → RunKeeps run) :
    GatherKeeps (claimsInBy each bs order) := by
  intro t cls e a a' hg ha ha'
  obtain ⟨b, hb, hc⟩ := fold_keeps each bs order hk ([], t) (cls, e) hg a ha
  have eb : b = a' := Option.some.inj (hb.symm.trans ha')
  rw [← eb]
  exact hc

theorem fold_twin (R : S → S → Prop) (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) : ∀ (order : List (Nat × String)),
    (∀ o ∈ order, ∀ run, claimsRunOf bs o = some run → RunTwin R run) →
    ∀ (x x' y y' : List Claim × S), x.1.map slotKey = x'.1.map slotKey → R x.2 x'.2 →
    order.foldl (gatherStep each bs) (.ok x) = .ok y →
    order.foldl (gatherStep each bs) (.ok x') = .ok y' →
      y.1.map slotKey = y'.1.map slotKey ∧ R y.2 y'.2
  | [], _, x, x', y, y', hk, hR, h, h' => by
    have e : x = y := Except.ok.inj h
    have e' : x' = y' := Except.ok.inj h'
    rw [← e, ← e']
    exact ⟨hk, hR⟩
  | o :: l, ht, x, x', y, y', hk, hR, h, h' => by
    rw [List.foldl_cons] at h h'
    obtain ⟨u, hu⟩ := fold_ok each bs l _ y h
    obtain ⟨u', hu'⟩ := fold_ok each bs l _ y' h'
    rw [hu] at h
    rw [hu'] at h'
    obtain ⟨run, z, hr, hz, e⟩ := step_ok each bs x u o hu
    obtain ⟨run', z', hr', hz', e'⟩ := step_ok each bs x' u' o hu'
    have er : run = run' := Option.some.inj (hr.symm.trans hr')
    subst er
    have el : x.1.length = x'.1.length := by
      have := congrArg List.length hk
      simpa using this
    rw [← el] at hz'
    obtain ⟨k, r⟩ := ht o List.mem_cons_self run hr _ _ _ z z' hR hz hz'
    refine fold_twin R each bs l (fun o' ho' => ht o' (List.mem_cons_of_mem _ ho')) u u' y y'
      ?_ ?_ h h'
    · rw [e, e']
      simp only [List.map_append, hk, k]
    · rw [e, e']
      exact r

/-- **Every named run is a twin ⟹ so is the gatherer.** -/
theorem gather_twin (R : S → S → Prop)
    (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (order : List (Nat × String))
    (ht : ∀ o ∈ order, ∀ run, claimsRunOf bs o = some run → RunTwin R run)
    (t t' : S) (y y' : List Claim × S) (hR : R t t')
    (h : claimsInBy each bs order t = .ok y) (h' : claimsInBy each bs order t' = .ok y') :
    y.1.map slotKey = y'.1.map slotKey ∧ R y.2 y'.2 :=
  fold_twin R each bs order ht ([], t) ([], t') y y' rfl hR h h'

/-- **THE THREAD OF THE RUNS**: from the state t, with n claims made so far, the runs that the order names have
run one behind the other: each at the state that the one in front left and at the number of claims made so
far; ls: their lists; e: the state behind the last. -/
def Ran (bs : List (Block S Claim)) : List (Nat × String) → Nat → S → List (List Claim) → S → Prop
  | [], _, t, [], e => e = t
  | o :: os, n, t, l :: ls, e =>
    ∃ run u, claimsRunOf bs o = some run ∧ run n t = .ok (l, u) ∧ Ran bs os (n + l.length) u ls e
  | _, _, _, _, _ => False

/-- The fold's thread, from any list so far. -/
theorem fold_ran (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) : ∀ (order : List (Nat × String)) (x y : List Claim × S),
    order.foldl (gatherStep each bs) (.ok x) = .ok y →
      ∃ ls : List (List Claim), y.1 = x.1 ++ ls.flatten ∧ Ran bs order x.1.length x.2 ls y.2
  | [], x, y, h => by
    have e : x = y := Except.ok.inj h
    exact ⟨[], by rw [e]; simp, by rw [e]; rfl⟩
  | o :: l, x, y, h => by
    rw [List.foldl_cons] at h
    obtain ⟨u, hu⟩ := fold_ok each bs l _ y h
    rw [hu] at h
    obtain ⟨run, z, hr, hz, e⟩ := step_ok each bs x u o hu
    obtain ⟨ls, h1, h2⟩ := fold_ran each bs l u y h
    refine ⟨z.1 :: ls, ?_, run, z.2, hr, hz, ?_⟩
    · rw [h1, e, List.flatten_cons, List.append_assoc]
    · rw [e] at h2
      simpa [List.length_append] using h2

/-- **The gatherer's list is the runs' lists in a row, and the runs ran in one thread from the gatherer's own
state.** -/
theorem gather_ran (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (order : List (Nat × String)) (t : S) (y : List Claim × S)
    (h : claimsInBy each bs order t = .ok y) :
    ∃ ls : List (List Claim), y.1 = ls.flatten ∧ Ran bs order 0 t ls y.2 := by
  obtain ⟨ls, h1, h2⟩ := fold_ran each bs order ([], t) y h
  exact ⟨ls, by rw [h1]; rfl, h2⟩

/-- Along the thread an invariant rides: I holds at the state in front, and every named run hands it on: then
each list is the answer of its run AT A STATE AT WHICH I HOLDS. -/
theorem ran_inv (bs : List (Block S Claim)) (I : S → Prop) : ∀ (order : List (Nat × String)) (n : Nat)
    (t : S) (ls : List (List Claim)) (e : S),
    (∀ o ∈ order, ∀ run, claimsRunOf bs o = some run → ∀ n t z, I t → run n t = .ok z → I z.2) →
    I t → Ran bs order n t ls e →
      List.Forall₂ (fun o l => ∃ run n u z, claimsRunOf bs o = some run ∧ I u ∧ run n u = .ok z ∧ z.1 = l)
        order ls ∧ I e
  | [], _, t, [], e, _, hI, h => by
    have e1 : e = t := h
    exact ⟨List.Forall₂.nil, by rw [e1]; exact hI⟩
  | [], _, _, _ :: _, _, _, _, h => h.elim
  | _ :: _, _, _, [], _, _, _, h => h.elim
  | o :: os, n, t, l :: ls, e, hk, hI, h => by
    obtain ⟨run, u, hr, hz, hrest⟩ := h
    have hu : I u := hk o List.mem_cons_self run hr n t (l, u) hI hz
    obtain ⟨h1, h2⟩ := ran_inv bs I os (n + l.length) u ls e
      (fun o' ho' => hk o' (List.mem_cons_of_mem _ ho')) hu hrest
    exact ⟨List.Forall₂.cons ⟨run, n, t, (l, u), hr, hI, hz, rfl⟩ h1, h2⟩

/-- Every named run keeps ⟹ from the gatherer's state to the state behind it: `Kept`. -/
theorem gather_kept (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (order : List (Nat × String))
    (hk : ∀ o ∈ order, ∀ run, claimsRunOf bs o = some run → RunKeeps run)
    (t : S) (y : List Claim × S) (h : claimsInBy each bs order t = .ok y) : Kept t y.2 :=
  fold_keeps each bs order hk ([], t) y h

/-- **The Bool `slotsLive` at the gatherer's own list**, out of the runs' shares ALONG THE THREAD FROM THE
GATHERER's OWN STATE: of the lists that the runs answer there: each slot below n but the merge's is live in one
of them, plain in all; the merge's slot is named in none. -/
theorem slotsLive_of_gather (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (order : List (Nat × String)) (t : S) (y : List Claim × S)
    (h : claimsInBy each bs order t = .ok y) (n : Nat) (merge : Option Nat)
    (shares : ∀ ls : List (List Claim), Ran bs order 0 t ls y.2 →
      (∀ j < n, merge ≠ some j → ∃ l ∈ ls, VerifiableInference.Desc.K9H.liveAt l j = true) ∧
      (∀ j < n, merge ≠ some j → ∀ l ∈ ls, VerifiableInference.Desc.K9H.plainAt l j = true) ∧
      (∀ j < n, merge = some j → ∀ l ∈ ls, VerifiableInference.Desc.K9H.unnamedAt l j = true)) :
    VerifiableInference.Desc.K9H.slotsLive n merge y.1 = true := by
  obtain ⟨ls, h1, h2⟩ := gather_ran each bs order t y h
  obtain ⟨a, b, c⟩ := shares ls h2
  rw [h1]
  exact VerifiableInference.Desc.K9H.slotsLive_of_runs n merge ls a b c

theorem forall₂_left {α β : Type} {P : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ P l l' → ∀ a ∈ l, ∃ b ∈ l', P a b
  | _, _, .nil, _, h => nomatch h
  | _, _, .cons hp ht, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self, hp⟩
    · obtain ⟨b, hb, hP⟩ := forall₂_left ht a h
      exact ⟨b, List.mem_cons_of_mem _ hb, hP⟩

theorem forall₂_right {α β : Type} {P : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ P l l' → ∀ b ∈ l', ∃ a ∈ l, P a b
  | _, _, .nil, _, h => nomatch h
  | _, _, .cons hp ht, b, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self, hp⟩
    · obtain ⟨a, ha, hP⟩ := forall₂_right ht b h
      exact ⟨a, List.mem_cons_of_mem _ ha, hP⟩

/-- **THE PLUG FOR THE KINDS' SHARES**: I: an invariant that holds at the gatherer's state and that every named run
hands on. EACH KIND SAYS ITS SHARE OF ITS OWN RUN, AT EVERY NUMBER AND EVERY STATE WITH I: for each slot below n
but the merge's SOME entry of the order is named whose run's list has the slot live; every run's list is plain
at each such slot; no run's list names the merge's slot. Then the Bool holds of the gatherer's own list. -/
theorem slotsLive_of_inv (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (order : List (Nat × String)) (t : S) (y : List Claim × S)
    (h : claimsInBy each bs order t = .ok y) (n : Nat) (merge : Option Nat) (I : S → Prop) (hI : I t)
    (hand : ∀ o ∈ order, ∀ run, claimsRunOf bs o = some run → ∀ n t z, I t → run n t = .ok z → I z.2)
    (live : ∀ j < n, merge ≠ some j → ∃ o ∈ order, ∀ run, claimsRunOf bs o = some run →
      ∀ m u z, I u → run m u = .ok z → VerifiableInference.Desc.K9H.liveAt z.1 j = true)
    (plain : ∀ j < n, merge ≠ some j → ∀ o ∈ order, ∀ run, claimsRunOf bs o = some run →
      ∀ m u z, I u → run m u = .ok z → VerifiableInference.Desc.K9H.plainAt z.1 j = true)
    (unnamed : ∀ j < n, merge = some j → ∀ o ∈ order, ∀ run, claimsRunOf bs o = some run →
      ∀ m u z, I u → run m u = .ok z → VerifiableInference.Desc.K9H.unnamedAt z.1 j = true) :
    VerifiableInference.Desc.K9H.slotsLive n merge y.1 = true := by
  refine slotsLive_of_gather each bs order t y h n merge fun ls hR => ?_
  have hF := (ran_inv bs I order 0 t ls y.2 hand hI hR).1
  refine ⟨fun j hj hm => ?_, fun j hj hm l hl => ?_, fun j hj hm l hl => ?_⟩
  · obtain ⟨o, ho, hlive⟩ := live j hj hm
    obtain ⟨l, hl, run, m, u, z, hr, hu, hz, e⟩ := forall₂_left hF o ho
    exact ⟨l, hl, by rw [← e]; exact hlive run hr m u z hu hz⟩
  · obtain ⟨o, ho, run, m, u, z, hr, hu, hz, e⟩ := forall₂_right hF l hl
    rw [← e]
    exact plain j hj hm o ho run hr m u z hu hz
  · obtain ⟨o, ho, run, m, u, z, hr, hu, hz, e⟩ := forall₂_right hF l hl
    rw [← e]
    exact unnamed j hj hm o ho run hr m u z hu hz

/-- **A one-state road to `RunTwin`.** -/
theorem twin_of_view {α : Type} (view : S → α) (run : ClaimsRun)
    (keys : Nat → α → List (Option Nat × List (Nat × E))) (next : Nat → α → α)
    (h : ∀ n t z, run n t = .ok z → z.1.map slotKey = keys n (view t) ∧ view z.2 = next n (view t)) :
    RunTwin (fun t t' => view t = view t') run := by
  intro n t t' z z' hR hz hz'
  obtain ⟨k, v⟩ := h n t z hz
  obtain ⟨k', v'⟩ := h n t' z' hz'
  have hR' : view t = view t' := hR
  exact ⟨by rw [k, k', hR'], by show view z.2 = view z'.2; rw [v, v', hR']⟩

/-- K9's OWN SHARE OF "R HOLDS BEHIND THE DRAW AT ANY TWO CHALLENGES", at R := "the same view": by `draw_is` it is one
equation on the state in front: the view does not see the ledger's field theta. -/
theorem start_of_view {α : Type} (view : S → α) (p : Where) (s : S) (a : VerifiableInference.Desc.K9.Part)
    (ha : atS.get? s = some a)
    (hv : ∀ x x', view (atS.set s (drawnPart p a x)) = view (atS.set s (drawnPart p a x')))
    (x x' : E) (t t' : S)
    (h : (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t)
    (h' : (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x'⟩] [] = .ok t') : view t = view t' := by
  rw [draw_is p s t x a ha h, draw_is p s t' x' a ha h']
  exact hv x x'

/-- **`RunsLaw` out of the runs' two debts.** -/
theorem runsLaw_of_runs (p : Where) (s : S) (R : S → S → Prop)
    (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (order : List (Nat × String))
    (hk : ∀ o ∈ order, ∀ run, claimsRunOf bs o = some run → RunKeeps run)
    (ht : ∀ o ∈ order, ∀ run, claimsRunOf bs o = some run → RunTwin R run)
    (start : ∀ x x' t t', (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t →
      (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x'⟩] [] = .ok t' → R t t')
    (merge : ∀ e e', R e e' → mergeOf e = mergeOf e') :
    RunsLaw p (claimsInBy each bs order) s := by
  refine runsLaw_of p _ s (gather_keeps each bs order hk) ?_
  intro x x' y y' hy hy'
  obtain ⟨t, hd, hg, _⟩ := gathered_split p _ s x y hy
  obtain ⟨t', hd', hg', _⟩ := gathered_split p _ s x' y' hy'
  obtain ⟨k, r⟩ := gather_twin R each bs order ht t t' _ _ (start x x' t t' hd hd') hg hg'
  exact ⟨k, merge _ _ r⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.step_ok
#print axioms ProofFile.Honest.K9.gather_keeps
#print axioms ProofFile.Honest.K9.gather_twin
#print axioms ProofFile.Honest.K9.runsLaw_of_runs
#print axioms ProofFile.Honest.K9.gather_ran
#print axioms ProofFile.Honest.K9.ran_inv
#print axioms ProofFile.Honest.K9.gather_kept
#print axioms ProofFile.Honest.K9.slotsLive_of_gather
#print axioms ProofFile.Honest.K9.slotsLive_of_inv
#print axioms ProofFile.Honest.K9.RunKeeps.under
#print axioms ProofFile.Honest.K9.RunTwin.under
#print axioms ProofFile.Honest.K9.start_of_view
#print axioms ProofFile.Honest.K9.twin_of_view
#print axioms ProofFile.Honest.K9.fold_keeps
#print axioms ProofFile.Honest.K9.fold_twin
#print axioms ProofFile.Honest.K9.Kept
#print axioms ProofFile.Honest.K9.Kept.refl
#print axioms ProofFile.Honest.K9.Kept.trans
#print axioms ProofFile.Honest.K9.ClaimsRun
#print axioms ProofFile.Honest.K9.RunKeeps
#print axioms ProofFile.Honest.K9.RunTwin
#print axioms ProofFile.Honest.K9.RunUnder
#print axioms ProofFile.Honest.K9.claimsRunOf
#print axioms ProofFile.Honest.K9.gatherStep
#print axioms ProofFile.Honest.K9.fold_ok
#print axioms ProofFile.Honest.K9.Ran
#print axioms ProofFile.Honest.K9.fold_ran
#print axioms ProofFile.Honest.K9.forall₂_left
#print axioms ProofFile.Honest.K9.forall₂_right
