-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/GoodLaw/Runs.lean: what the output head's four runs of claims owe
to "every sent scalar stands in a claim", in the clause forms of `slotsLive_of_inv`
(Honest/K9/GatherFold.lean). Definitions, statements and proofs ON THE VERIFIER's TEXT; no prover is
in this file, and no goal is stated. Whose: part 4's.

WHAT IT IS NOT. THAT THE INVARIANT HOLDS AT THE GATHERER's STATE IS NOT SHOWN: it holds behind the
head's own step (`k6_border_good`) and is handed on by whoever shows `AlikeFront`; that every
sub-protocol and every run between does so is owed by their writers. ONE DEBT OF THE LOOKUP's SIDE
stands in `k6_border_good` as a premise: the form in which its key side ended names slots below the
head's first. A file that has not landed pays most of it (the lookup's side's
Honest/K3/Law/Thread/CEndBelow.lean, `cEnd_below`; its statement was read, the file is not imported
here: where the lookup's hearing returns from a ledger F to G, every slot that this form names lies
from F.next on and below G.next); what then stays is that G.next is at most b: the ledger only grows
between the lookup's member and the head's. `K6On` has a clause near it (`CEndFilled`,
Johnson/Desc/Kinds/Law/RowFront.lean: each slot that this form names is filled in the ledger in
front), which is not it. b AND e ARE NO WRITTEN NUMBERS: in `k6_border_good` b is the ledger's next
slot at the state in front of the step: which written number that is, is not said here.
`k6_border_good` speaks of the sub-protocol `blockOf`: from a member of the IOP as written in Lean,
with the seat's tests and the makers' guards around it, to that sub-protocol nothing is called here
(that is GoodLaw/AtHead.lean's `good_at_member`). In `k6_border_good` the samples are those of the
step's rounds with the sealed digests struck; the tests read elements alone. THE WINDOW's LAST SLOT
is covered by no clause here: that none of the four runs names it is a reading (which slot it is:
GoodLaw/Window.lean's `sV_of_good`). That the merge's slot lies behind the window is a premise of
`clauses_fit`. From the kind's own runs to the runs in the own list of the IOP as written in Lean:
by `RunUnder`, a premise of `clauses_fit` (Johnson/Desc/Kinds/Law/SeatedRuns.lean has the seated
sub-protocol's runs; of the guards nothing is called here: that is GoodLaw/RunsUnder.lean's
`runs_under_at_head`). Nothing on the batching element, and nothing on how often the tests reject.

  `K6GoodAt h iU3 p b e s`   THE INVARIANT, a predicate on states: the head's own hearing is read
                    back at s; its first slot is b, the slot behind its last is e; the lookup's
                    point on the positions has lt coordinates; `goodAll` accepts its rounds'
                    samples; and the form in which the lookup's key side ended names slots below b
                    alone
  `k6GoodAt_front`, `k6GoodAt_keeps`   who hands it on: whoever shows `AlikeFront`; a sub-protocol
                    with `KeepsK6`
  `k6_border_good`  **it holds behind every accepting step of the head's sub-protocol**, with both
                    ends of the window written out: the ledger's next slot in front of the step, and
                    `headWindow` p more; where `goodK6` and `goodK6Nz` accept the step's own
                    samples; under `K6On` on the state in front and `Canonical` on the rounds, as
                    `k6_border` has them
  `run_live`, `run_plain`, `run_unnamed`, `run_same`   **the four clauses of the runs "norm",
                    "policy", "logits"**
  `join_plain`, `join_unnamed`, `join_hands`   **three clauses of the run "join"** (it need keep no
                    slot alive)
  `k6GoodAt_head`, `join_merge`   a state with the invariant stands in the head's segment; "join"
                    does not turn the slot of the merge's end value
  `clauses_four`    **the four clauses over the whole order, handed out**, at ANY invariant that
                    gives `K6GoodAt`, with every other sub-protocol's clauses as premises: nothing
                    is asked of a state, and no acceptance of the gatherer
  `clauses_fit`     `clauses_four` laid into `slotsLive_of_inv`

GROUND THAT HAS NOT YET LANDED IN THE LIBRARY: Honest/K9/GatherFold.lean (sha256) with
what it imports, and the ground of GoodLaw/Coef.lean.
Nothing on any property.

-/
import Johnson.Desc.Kinds.Law.RunsStill
import Johnson.Desc.Kinds.Law.SeatedRuns
import Johnson.Desc.Kinds.Law.FromGiven
import Johnson.Desc.Kinds.Law.K6Claims
import Johnson.Desc.ProofFile.Honest.K9.GatherFold
import Johnson.Desc.Kinds.Law.KeysHave
import Johnson.Desc.Kinds.Law.K06HonestWhole
import Johnson.Desc.Kinds.Law.HeardBack
import Johnson.Desc.Kinds.Law.WeightTwinAt
import Johnson.Desc.ProofFile.Honest.K6.GoodLaw.Tie

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace ProofFile.Honest.K6.GoodLaw

section
open OnBytes (E okE)
open OnBytes.Model (Fork)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head (HeardAll Given asClaim seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (WellLaid SlotsIn AlikeFront)
open VerifiableInference.Desc.K9H (liveAt plainAt unnamedAt)

/-- How many of the sub-protocol's scalars stand in front of the last sumcheck's. -/
def headBeforeLogits (p : Head.Par) : Nat := 35 + 6 * headLt p + 2 * headLPd p

/-- How many scalars the sub-protocol sends: so many slots has its window. -/
def headWindow (p : Head.Par) : Nat := 41 + 8 * headLt p + 4 * headLPd p

/-- A list of plain claims is plain at every slot: each claim takes its own number. -/
theorem plain_all (fs : List Form) (j : Nat) : plainAt (fs.map asClaim) j = true := by
  unfold VerifiableInference.Desc.K9H.plainAt
  rw [List.all_eq_true]
  intro cl hcl
  obtain ⟨f, _, rfl⟩ := List.mem_map.1 hcl
  rfl

theorem unnamed_of_slotsIn {lo hi : Nat} (fs : List Form) (hs : ∀ f ∈ fs, SlotsIn lo hi f) (j : Nat)
    (hj : j < lo ∨ hi ≤ j) : unnamedAt (fs.map asClaim) j = true := by
  unfold VerifiableInference.Desc.K9H.unnamedAt
  rw [List.all_eq_true]
  intro cl hcl
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hcl
  unfold VerifiableInference.Desc.K9H.unnamedIn
  rw [List.all_eq_true]
  intro x hx
  have h2 := hs f hf x hx
  have hne : x.1 ≠ j := by omega
  simpa using hne

section Forms
variable [Head.Sizes] [Head.Policy] [Head.Request] [Head.Token] [FinalNorm.In] [Head.In]

/-- Outside the stretch of slots that the hearing took, no form of the three runs names a slot. -/
theorem forms_unnamed [FinalNorm.Reads] [Head.Reads] {F G : Fork} {rs : List Fmt.RoundView} {H : HeardAll}
    (hW : WellLaid F) (h : Head.hear F rs = some (H, G, []))
    (hN : ∀ r i, (FinalNorm.entry r i).slots = #[]) (hR : ∀ r i, (Head.entry r i).slots = #[]) :
    letI : Norm.Heard := H.1
    letI : FinalNorm.Heard := H.2.1
    letI : Head.Heard := H.2.2
    ∀ name fs, Head.claims.lookup name = some fs → ∀ j, (j < F.next ∨ G.next ≤ j) →
      unnamedAt (fs.map asClaim) j = true := by
  letI : Norm.Heard := H.1
  letI : FinalNorm.Heard := H.2.1
  letI : Head.Heard := H.2.2
  intro name fs hl j hj
  exact unnamed_of_slotsIn fs (Head.Law.forms_slotsIn hW h hN hR name fs hl) j hj

end Forms

section Runs
variable (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Head.Par)

/-- **THE INVARIANT.** `K6HeardAt` (Johnson/Desc/Kinds/Law/K6Claims.lean: the head's own hearing is
read back at the state), with four clauses more on that hearing, which name no state: its first slot
is b; the slot behind its last is e; the lookup's point on the positions has lt coordinates; the
three tests on its rounds' samples accept. And THE LOOKUP's DEBT: the form that the lookup's key
side ended in names slots below b alone. -/
def K6GoodAt (b e : Nat) (s : S) : Prop :=
  (∃ (g : Given) (H : HeardAll) (F0 G : Fork) (rs : List Fmt.RoundView),
    Head.given p (seatAt h iU3) s = .ok g ∧ (seatAt h iU3).heard s = some H ∧ WellLaid F0 ∧
    Head.hear F0 rs = some (H, G, []) ∧ Later G ((seatAt h iU3).ledger s) ∧
    F0.next = b ∧ G.next = e ∧ (FinalNorm.zt).size = Norm.lt ∧
    goodAll p (rs.map (·.drawn)) = true) ∧
  ∀ gl, s.lookHeard? = some gl → SlotsIn 0 b gl.cEnd

/-- It gives `K6HeardAt`. -/
theorem K6GoodAt.heardAt {b e : Nat} {s : S} (k : K6GoodAt h iU3 p b e s) :
    Head.Law.K6HeardAt h iU3 p s := by
  obtain ⟨⟨g, H, F0, G, rs, hg, hH, hW, hh, hL, _⟩, _⟩ := k
  exact ⟨g, H, F0, G, rs, hg, hH, hW, hh, hL⟩

theorem lookHeard_front {s s' : S} (a : AlikeFront s s') : s'.lookHeard? = s.lookHeard? := by
  obtain ⟨o, o', ho, ho', _, _, eo, el, _⟩ := a
  unfold S.lookHeard?
  rw [ho, ho']
  simp only [eo, el]

/-- **WHOEVER SHOWS `AlikeFront` (Johnson/Desc/Kinds/Law/RunsFixedFront.lean) FROM ONE STATE TO
ANOTHER HANDS THE INVARIANT ON.** -/
theorem k6GoodAt_front {b e : Nat} {s s' : S} (a : AlikeFront s s')
    (k : K6GoodAt h iU3 p b e s) : K6GoodAt h iU3 p b e s' := by
  obtain ⟨⟨g, H, F0, G, rs, hg, hH, hW, hh, hL, c1, c2, c3, c4⟩, hk⟩ := k
  refine ⟨⟨g, H, F0, G, rs, (Head.Law.given_front h iU3 p a).trans hg,
    Head.Law.heard_front h iU3 a H hH, hW, hh, hL.trans (Head.Law.ledger_front h iU3 a), c1, c2, c3,
    c4⟩, fun gl hgl => hk gl ?_⟩
  rw [← lookHeard_front a]
  exact hgl

/-- A sub-protocol that keeps what `KeepsK6` (Johnson/Desc/Kinds/Law/K6Claims.lean) names keeps the
invariant. -/
theorem k6GoodAt_keeps {Cl : Type} {b e : Nat} (bl : Block S Cl) (hb : Head.Law.KeepsK6 bl)
    (firstTree : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn) (s' : S)
    (n : Nat) (hs : bl.step firstTree s rs cols = .ok (s', n)) (k : K6GoodAt h iU3 p b e s) :
    K6GoodAt h iU3 p b e s' := by
  refine k6GoodAt_front h iU3 p (hb firstTree s rs cols s' n ?_ hs) k
  obtain ⟨⟨_, H, _, _, _, _, hH, _⟩, _⟩ := k
  cases hh : s.here with
  | head o => exact ⟨o, rfl⟩
  | _ =>
    exfalso
    have hN : (seatAt h iU3).heard s = none := by
      show (match s.here with
        | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
          Head.allOf o.F x (some (Head.keptOf q x.wpl.sL))
        | _ => none) = none
      rw [hh]
    rw [hN] at hH
    cases hH

abbrev Run : Type := Nat → S → Except String (List Claim × S)

/-- Where one of the three runs returns at a state with the invariant: its claims are the plain
claims of the forms at the letters of the good hearing. -/
theorem run_at (l piece b e : Nat) (name : String) (run : Run)
    (hrun : (Head.kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run)
    (m : Nat) (u : S) (z : List Claim × S) (hI : K6GoodAt h iU3 p b e u) (hz : run m u = .ok z) :
    ∃ (g : Given) (H : HeardAll) (x : FinalNorm.Reads × Head.Reads) (F0 G : Fork)
      (rs : List Fmt.RoundView) (fs : List Form),
      headLt p = Norm.lt ∧ headLPd p = Norm.lPd ∧ WellLaid F0 ∧
      Head.hear F0 rs = some (H, G, []) ∧ F0.next = b ∧ G.next = e ∧
      (FinalNorm.zt).size = Norm.lt ∧ goodAll p (rs.map (·.drawn)) = true ∧
      (∀ r i, (x.1.entry r i).slots = #[]) ∧ (∀ r i, (x.2.entry r i).slots = #[]) ∧
      ((fun (_ : Given) (_ : Head.Behind) (_ : Head.Places) => Head.claims) g
        ⟨H.1, H.2.1, H.2.2⟩ ⟨x.1, x.2⟩).lookup name = some fs ∧ z.1 = fs.map asClaim := by
  obtain ⟨⟨g, H, F0, G, rs, hg, hH, hW, hh, _, hb, he, hzt, good⟩, _⟩ := hI
  obtain ⟨g', b', x', fs, h1, h2, h3⟩ :=
    Head.Law.k6_run_spec asClaim (seatAt h iU3) l piece p name run m u z.2 z.1 hrun hz
  obtain ⟨H', x, e1, e2, e3, e4⟩ := Head.Law.lettersAt_ok h iU3 p h1
  rw [hH] at e2
  obtain rfl := Option.some.inj e2
  have hg1 : (Except.ok g : Except String Given) = .ok g' := hg.symm.trans e1
  obtain rfl := Except.ok.inj hg1
  simp only [Prod.mk.injEq, true_and] at e4
  obtain ⟨rfl, rfl⟩ := e4
  obtain ⟨hN, hR⟩ := Head.Law.reads_bare h iU3 e3
  have hp : p.sizes = g.sizes := by
    obtain ⟨_, _, _, _, _, hgg⟩ := Head.Law.Came.given_ok p (seatAt h iU3) u g hg
    rw [hgg]
  have hlt : headLt p = Norm.lt := by
    unfold headLt
    rw [hp]
    rfl
  have hlPd : headLPd p = Norm.lPd := by
    unfold headLPd
    rw [hp]
  exact ⟨g, H, x, F0, G, rs, fs, hlt, hlPd, hW, hh, hb, he, hzt, good, hN, hR, h2, h3⟩

/-- **LIVE**: at a state with the invariant the run "norm" has every slot of the window in front of
the last sumcheck's live, the run "logits" the others but the last. -/
theorem run_live (l piece b e : Nat) (name : String) (run : Run)
    (hrun : (Head.kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run)
    (j : Nat)
    (hj : (name = "norm" ∧ b ≤ j ∧ j < b + headBeforeLogits p) ∨
      (name = "logits" ∧ b + headBeforeLogits p ≤ j ∧ j + 1 < e)) :
    ∀ m u z, K6GoodAt h iU3 p b e u → run m u = .ok z → liveAt z.1 j = true := by
  intro m u z hI hz
  obtain ⟨g, H, x, F0, G, rs, fs, hlt, hlPd, hW, hh, rfl, rfl, hzt, good, hN, hR, h2, h3⟩ :=
    run_at h iU3 p l piece b e name run hrun m u z hI hz
  letI := g
  letI : FinalNorm.Reads := x.1
  letI : Head.Reads := x.2
  have T := forms_live p hlt hlPd hW hh hN hR hzt good
  rw [h3]
  rcases hj with ⟨rfl, j1, j2⟩ | ⟨rfl, j1, j2⟩
  · obtain rfl : _ = fs := Option.some.inj h2
    exact T.1 j j1 j2
  · obtain rfl : _ = fs := Option.some.inj h2
    exact T.2 j j1 j2

/-- **PLAIN**: every claim of the three runs takes its own number. -/
theorem run_plain (l piece : Nat) (name : String) (run : Run)
    (hrun : (Head.kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run) (j : Nat) :
    ∀ m u z, run m u = .ok z → plainAt z.1 j = true := by
  intro m u z hz
  obtain ⟨_, _, _, fs, _, _, h3⟩ :=
    Head.Law.k6_run_spec asClaim (seatAt h iU3) l piece p name run m u z.2 z.1 hrun hz
  rw [h3]
  exact plain_all fs j

/-- **UNNAMED**: outside the window the three runs name no slot. -/
theorem run_unnamed (l piece b e : Nat) (name : String) (run : Run)
    (hrun : (Head.kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run) (j : Nat)
    (hj : j < b ∨ e ≤ j) :
    ∀ m u z, K6GoodAt h iU3 p b e u → run m u = .ok z → unnamedAt z.1 j = true := by
  intro m u z hI hz
  obtain ⟨g, H, x, F0, G, rs, fs, _, _, hW, hh, rfl, rfl, _, _, hN, hR, h2, h3⟩ :=
    run_at h iU3 p l piece b e name run hrun m u z hI hz
  letI := g
  letI : FinalNorm.Reads := x.1
  letI : Head.Reads := x.2
  rw [h3]
  exact forms_unnamed hW hh hN hR name fs h2 j hj

/-- **HANDED ON**, in a stronger form: the three runs leave the state as it is. -/
theorem run_same (l piece : Nat) (name : String) (run : Run)
    (hrun : (Head.kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run) :
    ∀ m u z, run m u = .ok z → z.2 = u := fun m u z hz =>
  Head.Law.k6_same h iU3 l piece p (name, run) (Head.Law.lookup_mem _ _ _ hrun) m u z hz

/-- "join" hands the invariant on: it marks one owed claim in the ledger as added. -/
theorem join_hands (b e : Nat) (keys : S → Option (Array OnBytes.Model.Aff)) :
    ∀ m u z, K6GoodAt h iU3 p b e u →
      VerifiableInference.Desc.K3.joinRun (VerifiableInference.Desc.K3.seatCalls asClaim) keys m u
        = .ok z → K6GoodAt h iU3 p b e z.2 := by
  intro m u z hI hz
  obtain ⟨F, g, hF, _, e2⟩ := Head.Law.k6_join keys m u z hz
  refine k6GoodAt_front h iU3 p ?_ hI
  rw [e2]
  unfold S.fork? at hF
  cases hh : u.here with
  | head o =>
    rw [hh] at hF
    by_cases ho : o.opened = true
    · simp only [ho, if_true, Option.some.injEq] at hF
      have hput : u.putFork (F.paid g.owedJoin) =
          { u with here := .head { o with F := F.paid g.owedJoin } } := by
        unfold S.putFork
        simp only [hh, ho, if_true]
      rw [hput]
      refine ⟨o, { o with F := F.paid g.owedJoin }, hh, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      show Later o.F (F.paid g.owedJoin)
      rw [hF]
      exact OnBytes.PscRun.paid_later F _
    · simp [ho] at hF
  | _ =>
    exfalso
    obtain ⟨⟨_, H, _, _, _, _, hH, _⟩, _⟩ := hI
    have hN : (seatAt h iU3).heard u = none := by
      show (match u.here with
        | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
          Head.allOf o.F x (some (Head.keptOf q x.wpl.sL))
        | _ => none) = none
      rw [hh]
    rw [hN] at hH
    cases hH

end Runs

end

section
open OnBytes (E okE zeroE)
open OnBytes.Model (Fork Aff)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head (HeardAll Given asClaim seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (WellLaid SlotsIn AlikeFront)
open VerifiableInference.Desc.K9H (liveAt plainAt unnamedAt)

/-- Rounds whose words are below the prime: so are their samples'. -/
theorem drawsOk_of_canonical {rs : List Fmt.RoundView} (h : Head.Law.Canonical rs) :
    drawsOk (rs.map (·.drawn)) = true := by
  unfold drawsOk
  rw [List.all_eq_true]
  intro d hd
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hd
  rw [List.all_eq_true]
  intro x hx
  unfold elemsOf at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  exact (h r hr).2 y hy

theorem getD_has {P : Form → Prop} (l : List Form) (hl : ∀ f ∈ l, P f) (c : Nat)
    (hc : c < l.toArray.size) (d : Form) : P (l.toArray.getD c d) := by
  have hc' : c < l.length := by simpa using hc
  have e : l.toArray.getD c d = l[c] := by simp [Array.getD, hc']
  rw [e]
  exact hl _ (List.getElem_mem hc')

section Runs
variable (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Head.Par)

/-- At this seat an entry of the read "wide" names no slot. -/
theorem reads_wide {s : S} {x : FinalNorm.Reads × Head.Reads}
    (e : (seatAt h iU3).reads s = some x) : ∀ i, (x.1.wide i).slots = #[] := by
  unfold seatAt at e
  dsimp only at e
  split at e
  · obtain ⟨tt, _, e1⟩ := Option.bind_eq_some_iff.mp e
    obtain ⟨tr, _, e2⟩ := Option.bind_eq_some_iff.mp e1
    split at e2
    · cases e2
    · have e3 := Option.some.inj e2
      subst e3
      exact fun _ => rfl
  · cases e

/-- Where "join" returns: its one claim is the plain claim of the lookup's formula on the caller's
key vectors. -/
theorem join_claims (keys : S → Option (Array Aff)) (m : Nat) (u : S) (z : List Claim × S)
    (hz : VerifiableInference.Desc.K3.joinRun (VerifiableInference.Desc.K3.seatCalls asClaim) keys
      m u = .ok z) :
    ∃ (g : OnBytes.Model.Forest.Heard) (KF : Array Aff), u.lookHeard? = some g ∧
      keys u = some KF ∧ z.1 = [asClaim (Head.Law.Came.joinForm g KF)] := by
  unfold VerifiableInference.Desc.K3.joinRun at hz
  simp only [bind, Except.bind] at hz
  cases hF : (VerifiableInference.Desc.K3.seatCalls asClaim).fork u with
  | none => simp [hF, VerifiableInference.Desc.named] at hz
  | some F =>
    cases hg : (VerifiableInference.Desc.K3.seatCalls asClaim).heard u with
    | none => simp [hF, hg, VerifiableInference.Desc.named] at hz
    | some g =>
      simp only [hF, hg, VerifiableInference.Desc.named] at hz
      split at hz
      · cases hz
      · split at hz
        · cases hz
        · rename_i KF hKF
          split at hz
          · cases hz
          · rename_i x hx
            have hx' : VerifiableInference.Desc.First.Look.joinF g KF F [] = some x := by
              cases hj : VerifiableInference.Desc.First.Look.joinF g KF F [] with
              | none => simp [hj] at hx
              | some x' =>
                simp [hj] at hx
                rw [hx]
            obtain ⟨_, _, _, hf⟩ := (Head.Law.Came.joinF_spec g KF F x.2.1 [] x.2.2 x.1).mp hx'
            have e := Except.ok.inj hz
            have hK : keys u = some KF := by
              cases hk : keys u with
              | none => simp [hk] at hKF
              | some K' =>
                simp [hk] at hKF
                rw [hKF]
            refine ⟨g, KF, hg, hK, ?_⟩
            rw [← e, ← hf]
            rfl

/-- The claim of "join" takes its own number. -/
theorem join_plain (keys : S → Option (Array Aff)) (j : Nat) :
    ∀ m u z, VerifiableInference.Desc.K3.joinRun (VerifiableInference.Desc.K3.seatCalls asClaim)
      keys m u = .ok z → plainAt z.1 j = true := by
  intro m u z hz
  obtain ⟨g, KF, _, _, e⟩ := join_claims keys m u z hz
  rw [e]
  exact plain_all [Head.Law.Came.joinForm g KF] j

/-- From the slot behind the window on, the claim of "join" names no slot. -/
theorem join_unnamed (b e j : Nat) (hj : e ≤ j) :
    ∀ m u z, K6GoodAt h iU3 p b e u →
      VerifiableInference.Desc.K3.joinRun (VerifiableInference.Desc.K3.seatCalls asClaim)
        (Head.callerKeys p (seatAt h iU3)) m u = .ok z → unnamedAt z.1 j = true := by
  intro m u z hI hz
  obtain ⟨gl, KF, hgl, hK, ez⟩ := join_claims _ m u z hz
  obtain ⟨⟨g, H, F0, G, rs, hg, hH, hW, hh, _, rfl, rfl, _, _⟩, hLook⟩ := hI
  have hle : F0.next ≤ G.next := by
    have := (Head.Law.hear_takes (⟨hW.2.1, hW.2.2, hW.1⟩ : OnBytes.PscRun.Sized F0) hh).next
    omega
  unfold Head.callerKeys at hK
  obtain ⟨v, hv, hKF⟩ := Option.map_eq_some_iff.mp hK
  obtain ⟨g', b', x'⟩ := v
  have hl : Head.lettersAt p (seatAt h iU3) u = .ok (g', b', x') := by
    cases hx : Head.lettersAt p (seatAt h iU3) u with
    | error w => rw [hx] at hv; cases hv
    | ok w =>
      rw [hx] at hv
      exact congrArg Except.ok (Option.some.inj hv)
  obtain ⟨H', x, e1, e2, e3, e4⟩ := Head.Law.lettersAt_ok h iU3 p hl
  rw [hH] at e2
  obtain rfl := Option.some.inj e2
  have hg1 : (Except.ok g : Except String Given) = .ok g' := hg.symm.trans e1
  obtain rfl := Except.ok.inj hg1
  simp only [Prod.mk.injEq, true_and] at e4
  obtain ⟨rfl, rfl⟩ := e4
  obtain ⟨hN, hR⟩ := Head.Law.reads_bare h iU3 e3
  have hw := reads_wide h iU3 e3
  rw [ez]
  refine unnamed_of_slotsIn (lo := 0) (hi := G.next) [Head.Law.Came.joinForm gl KF] ?_ j (Or.inr hj)
  intro f hf
  obtain rfl : f = Head.Law.Came.joinForm gl KF := by simpa using hf
  refine Head.Law.joinForm_has (Head.Law.kept_slotsIn 0 G.next) gl KF ?_
    ((hLook gl hgl).mono (Nat.le_refl _) hle)
  intro c hc
  subst hKF
  letI := g
  letI : FinalNorm.Reads := x.1
  letI : Head.Reads := x.2
  have hks := Head.Law.keys_slotsIn hW hh hN hR hw
  refine getD_has _ (fun f hf => ?_) c hc _
  obtain ⟨cc, _, rfl⟩ := List.mem_map.1 hf
  exact (hks cc.1 cc.2).mono (Nat.zero_le _) (Nat.le_refl _)

end Runs

/-- **THE BORDER: BEHIND EVERY ACCEPTING STEP OF THE HEAD's SUB-PROTOCOL THE INVARIANT HOLDS**,
where the two tests on the step's own rounds' samples accept. After `k6_border`
(Johnson/Desc/Kinds/Law/K6Claims.lean), with its witnesses shown. b is the sub-protocol without the
seat's tests and the makers' guards (`blockOf`, Johnson/Stored/HeadSeatAt.lean). The premises `K6On`
(Johnson/Desc/Kinds/Law/RowPins.lean) on the state in front and `Canonical`
(Johnson/Desc/Kinds/HeadLaw.lean) on the rounds are those of `k6_border`. The window's two ends are
written out: the ledger's next slot in front, and `headWindow` more; which written number the first
is, is not said here. hLook is a debt of the lookup's side. -/
theorem k6_border_good (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit)
    (hb : Head.blockOf W l = some b) (firstTree : Nat) (s : S) (rs : List Fmt.RoundView)
    (cols : List VerifiableInference.Desc.OpenedColumn) (s' : S) (n : Nat) (hOn : Head.Law.K6On W s)
    (hcan : Head.Law.Canonical rs) (hstep : b.step firstTree s rs cols = .ok (s', n))
    (gd : goodK6 (Head.parOf W.hS (Head.Law.workOf W))
      ((rs.map VerifiableInference.Desc.noDigest).map (·.drawn)) = true)
    (nz : goodK6Nz (Head.parOf W.hS (Head.Law.workOf W))
      ((rs.map VerifiableInference.Desc.noDigest).map (·.drawn)) = true)
    (hLook : ∀ gl, s'.lookHeard? = some gl →
      SlotsIn 0 ((seatAt W.hS (Head.Law.readsOf W)).ledger s).next gl.cEnd) :
    K6GoodAt W.hS (Head.Law.readsOf W) (Head.parOf W.hS (Head.Law.workOf W))
      ((seatAt W.hS (Head.Law.readsOf W)).ledger s).next
      (((seatAt W.hS (Head.Law.readsOf W)).ledger s).next +
        headWindow (Head.parOf W.hS (Head.Law.workOf W))) s' := by
  obtain ⟨gs, hd⟩ := Head.Law.Came.step_decide firstTree b s rs cols s' n hstep
  obtain ⟨iU3, hu, hbb⟩ := Option.map_eq_some_iff.mp hb
  have hr : Head.Law.readsOf W = iU3 := by
    unfold Head.Law.readsOf
    rw [hu]
    rfl
  subst hbb
  have hWL : WellLaid ((seatAt W.hS (Head.Law.readsOf W)).ledger s) := hOn.1
  rw [hr] at hWL hLook ⊢
  have hd' : (Head.blockAt W.hS iU3 (Head.Law.workOf W) l).decide s
      (rs.map VerifiableInference.Desc.noDigest) gs = .ok s' := hd
  obtain ⟨g, H, F, w, s1, s2, hg, hh, e1, e2, hs'⟩ :=
    Head.Law.decide_hears_at W.hS iU3 (Head.Law.workOf W) l s s'
      (rs.map VerifiableInference.Desc.noDigest) gs hd'
  obtain ⟨b1, b2, b3, _⟩ := Head.Law.seatBack_at W.hS iU3 (Head.Law.workOf W) s g
    (rs.map VerifiableInference.Desc.noDigest) [] F H w s1 s2 hg hWL
    (Head.Law.Came.canonical_noDigest hcan) hh e1 e2
  have good : goodAll (Head.parOf W.hS (Head.Law.workOf W))
      ((rs.map VerifiableInference.Desc.noDigest).map (·.drawn)) = true := by
    unfold goodAll
    rw [drawsOk_of_canonical (Head.Law.Came.canonical_noDigest hcan), gd, nz]
    rfl
  have hzt : (FinalNorm.zt).size = Norm.lt :=
    Head.Law.Came.zt_size_at W (by rw [hr]; exact hg) hOn.2.1
  have hp : (Head.parOf W.hS (Head.Law.workOf W)).sizes = g.sizes := by
    obtain ⟨_, _, _, _, _, hgg⟩ := Head.Law.Came.given_ok _ (seatAt W.hS iU3) s g hg
    rw [hgg]
  have hlt : headLt (Head.parOf W.hS (Head.Law.workOf W)) = Norm.lt := by
    unfold headLt
    rw [hp]
    rfl
  have hlPd : headLPd (Head.parOf W.hS (Head.Law.workOf W)) = Norm.lPd := by
    unfold headLPd
    rw [hp]
  have nG := (Head.Law.hear_takes_plan
    (⟨hWL.2.1, hWL.2.2, hWL.1⟩ : OnBytes.PscRun.Sized ((seatAt W.hS iU3).ledger s)) hzt hh).next
  refine ⟨⟨g, H, _, F, rs.map VerifiableInference.Desc.noDigest, ?_, ?_, hWL, hh, ?_, rfl, ?_, hzt,
    good⟩, hLook⟩
  · rw [hs']
    exact b3.trans hg
  · rw [hs']
    exact b2
  · rw [hs', b1]
    exact Later.refl _
  · rw [nG]
    unfold headWindow
    rw [hlt, hlPd]

/-- A state with the invariant stands in the head's segment. -/
theorem k6GoodAt_head {h : OnBytes.Model.Head.Shape} {iU3 : Nat} {p : Head.Par} {b e : Nat} {s : S}
    (k : K6GoodAt h iU3 p b e s) : ∃ o, s.here = .head o := by
  obtain ⟨⟨_, H, _, _, _, _, hH, _⟩, _⟩ := k
  cases hh : s.here with
  | head o => exact ⟨o, rfl⟩
  | _ =>
    exfalso
    have hN : (seatAt h iU3).heard s = none := by
      show (match s.here with
        | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
          Head.allOf o.F x (some (Head.keptOf q x.wpl.sL))
        | _ => none) = none
      rw [hh]
    rw [hN] at hH
    cases hH

/-- "join" does not turn the slot of the merge's end value (`K9.mergeOf`,
Johnson/Desc/First/Batch/AtS.lean). -/
theorem join_merge (keys : S → Option (Array Aff)) (m : Nat) (u : S) (z : List Claim × S)
    (hz : VerifiableInference.Desc.K3.joinRun (VerifiableInference.Desc.K3.seatCalls asClaim) keys
      m u = .ok z) :
    VerifiableInference.Desc.K9.mergeOf z.2 = VerifiableInference.Desc.K9.mergeOf u := by
  obtain ⟨F, g, _, _, e2⟩ := Head.Law.k6_join keys m u z hz
  rw [e2]
  unfold VerifiableInference.Desc.K9.mergeOf S.putFork
  cases hh : u.here with
  | head o =>
    by_cases ho : o.opened = true
    · simp [ho]
    · simp [hh, ho]
  | _ => simp [hh]

/-- **THE FOUR CLAUSES, HANDED OUT**: handed on, live, plain and unnamed, over the whole order, in
the forms in which `slotsLive_of_inv` (Honest/K9/GatherFold.lean) asks them, at a list of
sub-protocols whose runs at number 3 only reject more than the kind's three runs and "join"
(`RunUnder`, same file: so under the guards that the makers of the IOP as written in Lean lay around
a sub-protocol). I: ANY invariant that gives `K6GoodAt`: so the other sub-protocols' conditions on
their own samples can stand in it beside ours. Paid here, at the four entries (3, ..): live, plain
and unnamed; handed on by the three runs, which leave the state as it is. Premises: that "join"
hands I on (`join_hands` pays the share of `K6GoodAt`, `join_merge` that of the merge's slot); every
other entry's four clauses; that the merge's slot lies behind the window; that the order names (3,
"norm") and (3, "logits"). Nothing is asked of a state here, and no acceptance of the gatherer: so
whoever wants the four at every challenge has them. -/
theorem clauses_four (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Head.Par) (l b e : Nat)
    (bs : List (Block S Claim)) (order : List (Nat × String)) (n : Nat)
    (merge : Option Nat) (I : S → Prop) (hIK : ∀ u, I u → K6GoodAt h iU3 p b e u)
    (hm : ∀ j, merge = some j → e ≤ j)
    (ho : (3, "norm") ∈ order ∧ (3, "logits") ∈ order)
    (hb3 : ∀ name run', K9.claimsRunOf bs (3, name) = some run' →
      (name ≠ "join" ∧ ∃ run,
        (Head.kind asClaim (seatAt h iU3) l 4 p).claims.lookup name = some run ∧
        K9.RunUnder run' run) ∨
      (name = "join" ∧ K9.RunUnder run' (VerifiableInference.Desc.K3.joinRun
        (VerifiableInference.Desc.K3.seatCalls asClaim) (Head.callerKeys p (seatAt h iU3)))))
    (joinI : ∀ m u z, I u → VerifiableInference.Desc.K3.joinRun
      (VerifiableInference.Desc.K3.seatCalls asClaim) (Head.callerKeys p (seatAt h iU3)) m u
        = .ok z → I z.2)
    (handElse : ∀ o ∈ order, o.1 ≠ 3 → ∀ run, K9.claimsRunOf bs o = some run → ∀ n t z,
      I t → run n t = .ok z → I z.2)
    (liveElse : ∀ j < n, merge ≠ some j → ¬ (b ≤ j ∧ j + 1 < e) → ∃ o ∈ order, ∀ run,
      K9.claimsRunOf bs o = some run → ∀ m u z, I u → run m u = .ok z → liveAt z.1 j = true)
    (plainElse : ∀ j < n, merge ≠ some j → ∀ o ∈ order, o.1 ≠ 3 → ∀ run,
      K9.claimsRunOf bs o = some run → ∀ m u z, I u → run m u = .ok z → plainAt z.1 j = true)
    (unnamedElse : ∀ j < n, merge = some j → ∀ o ∈ order, o.1 ≠ 3 → ∀ run,
      K9.claimsRunOf bs o = some run → ∀ m u z, I u → run m u = .ok z →
        unnamedAt z.1 j = true) :
    (∀ o ∈ order, ∀ run, K9.claimsRunOf bs o = some run → ∀ k t z,
      I t → run k t = .ok z → I z.2) ∧
    (∀ j < n, merge ≠ some j → ∃ o ∈ order, ∀ run, K9.claimsRunOf bs o = some run →
      ∀ k u z, I u → run k u = .ok z → liveAt z.1 j = true) ∧
    (∀ j < n, merge ≠ some j → ∀ o ∈ order, ∀ run, K9.claimsRunOf bs o = some run →
      ∀ k u z, I u → run k u = .ok z → plainAt z.1 j = true) ∧
    (∀ j < n, merge = some j → ∀ o ∈ order, ∀ run, K9.claimsRunOf bs o = some run →
      ∀ k u z, I u → run k u = .ok z → unnamedAt z.1 j = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro o hoo run hr m u z hu hz
    by_cases h3 : o.1 = 3
    · obtain ⟨o1, name⟩ := o
      obtain rfl : o1 = 3 := h3
      rcases hb3 name run hr with ⟨_, r0, hr0, hu0⟩ | ⟨_, hu0⟩
      · rw [run_same h iU3 p l 4 name r0 hr0 m u z (hu0 m u z hz)]
        exact hu
      · exact joinI m u z hu (hu0 m u z hz)
    · exact handElse o hoo h3 run hr m u z hu hz
  · intro j hj hmj
    by_cases hw : b ≤ j ∧ j + 1 < e
    · by_cases hl : j < b + headBeforeLogits p
      · refine ⟨(3, "norm"), ho.1, fun run hr m u z hu hz => ?_⟩
        rcases hb3 "norm" run hr with ⟨_, r0, hr0, hu0⟩ | ⟨hc, _⟩
        · exact run_live h iU3 p l 4 b e "norm" r0 hr0 j (Or.inl ⟨rfl, hw.1, hl⟩) m u z
            (hIK u hu) (hu0 m u z hz)
        · exact absurd hc (by decide)
      · refine ⟨(3, "logits"), ho.2, fun run hr m u z hu hz => ?_⟩
        rcases hb3 "logits" run hr with ⟨_, r0, hr0, hu0⟩ | ⟨hc, _⟩
        · exact run_live h iU3 p l 4 b e "logits" r0 hr0 j (Or.inr ⟨rfl, by omega, hw.2⟩) m u z
            (hIK u hu) (hu0 m u z hz)
        · exact absurd hc (by decide)
    · exact liveElse j hj hmj hw
  · intro j hj hmj o hoo run hr m u z hu hz
    by_cases h3 : o.1 = 3
    · obtain ⟨o1, name⟩ := o
      obtain rfl : o1 = 3 := h3
      rcases hb3 name run hr with ⟨_, r0, hr0, hu0⟩ | ⟨_, hu0⟩
      · exact run_plain h iU3 p l 4 name r0 hr0 j m u z (hu0 m u z hz)
      · exact join_plain _ j m u z (hu0 m u z hz)
    · exact plainElse j hj hmj o hoo h3 run hr m u z hu hz
  · intro j hj hmj o hoo run hr m u z hu hz
    by_cases h3 : o.1 = 3
    · obtain ⟨o1, name⟩ := o
      obtain rfl : o1 = 3 := h3
      rcases hb3 name run hr with ⟨_, r0, hr0, hu0⟩ | ⟨_, hu0⟩
      · exact run_unnamed h iU3 p l 4 b e name r0 hr0 j (Or.inr (hm j hmj)) m u z (hIK u hu)
          (hu0 m u z hz)
      · exact join_unnamed h iU3 p b e j (hm j hmj) m u z (hIK u hu) (hu0 m u z hz)
    · exact unnamedElse j hj hmj o hoo h3 run hr m u z hu hz

/-- **THE FOUR CLAUSES, LAID INTO `slotsLive_of_inv`**: `clauses_four`, with I at the gatherer's
state and an acceptance of the gatherer there. -/
theorem clauses_fit (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Head.Par) (l b e : Nat)
    (each : Nat × String → List Claim → S → Except String Unit)
    (bs : List (Block S Claim)) (order : List (Nat × String)) (t : S) (y : List Claim × S)
    (hy : VerifiableInference.Desc.claimsInBy each bs order t = .ok y) (n : Nat)
    (merge : Option Nat) (I : S → Prop) (hIK : ∀ u, I u → K6GoodAt h iU3 p b e u) (hI : I t)
    (hm : ∀ j, merge = some j → e ≤ j)
    (ho : (3, "norm") ∈ order ∧ (3, "logits") ∈ order)
    (hb3 : ∀ name run', K9.claimsRunOf bs (3, name) = some run' →
      (name ≠ "join" ∧ ∃ run,
        (Head.kind asClaim (seatAt h iU3) l 4 p).claims.lookup name = some run ∧
        K9.RunUnder run' run) ∨
      (name = "join" ∧ K9.RunUnder run' (VerifiableInference.Desc.K3.joinRun
        (VerifiableInference.Desc.K3.seatCalls asClaim) (Head.callerKeys p (seatAt h iU3)))))
    (joinI : ∀ m u z, I u → VerifiableInference.Desc.K3.joinRun
      (VerifiableInference.Desc.K3.seatCalls asClaim) (Head.callerKeys p (seatAt h iU3)) m u
        = .ok z → I z.2)
    (handElse : ∀ o ∈ order, o.1 ≠ 3 → ∀ run, K9.claimsRunOf bs o = some run → ∀ n t z,
      I t → run n t = .ok z → I z.2)
    (liveElse : ∀ j < n, merge ≠ some j → ¬ (b ≤ j ∧ j + 1 < e) → ∃ o ∈ order, ∀ run,
      K9.claimsRunOf bs o = some run → ∀ m u z, I u → run m u = .ok z → liveAt z.1 j = true)
    (plainElse : ∀ j < n, merge ≠ some j → ∀ o ∈ order, o.1 ≠ 3 → ∀ run,
      K9.claimsRunOf bs o = some run → ∀ m u z, I u → run m u = .ok z → plainAt z.1 j = true)
    (unnamedElse : ∀ j < n, merge = some j → ∀ o ∈ order, o.1 ≠ 3 → ∀ run,
      K9.claimsRunOf bs o = some run → ∀ m u z, I u → run m u = .ok z →
        unnamedAt z.1 j = true) :
    VerifiableInference.Desc.K9H.slotsLive n merge y.1 = true := by
  obtain ⟨c1, c2, c3, c4⟩ := clauses_four h iU3 p l b e bs order n merge I hIK hm ho hb3 joinI
    handElse liveElse plainElse unnamedElse
  exact K9.slotsLive_of_inv each bs order t y hy n merge I hI c1 c2 c3 c4

end

#print axioms plain_all
#print axioms unnamed_of_slotsIn
#print axioms forms_unnamed
#print axioms K6GoodAt.heardAt
#print axioms lookHeard_front
#print axioms k6GoodAt_front
#print axioms k6GoodAt_keeps
#print axioms run_at
#print axioms run_live
#print axioms run_plain
#print axioms run_unnamed
#print axioms run_same
#print axioms join_hands
#print axioms drawsOk_of_canonical
#print axioms getD_has
#print axioms reads_wide
#print axioms join_claims
#print axioms join_plain
#print axioms join_unnamed
#print axioms k6_border_good
#print axioms k6GoodAt_head
#print axioms join_merge
#print axioms clauses_four
#print axioms clauses_fit

end ProofFile.Honest.K6.GoodLaw
