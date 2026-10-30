-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/Falls.lean: CONDITIONAL: the two falls of the layers' own
rounds (kind K4; `k4Fall`, `k4FreeSlotFall`, Honest/K4/Part.lean) in the form `FallDebt`
(Honest/Law/CoverJoin.lean). A fall is a test on the verifier's state and a member's challenges,
laid at a place; `FallDebt` is a sentence that bounds the measure of one member's typed challenges
at which there are rounds with these challenges, and columns, such that the members from that one on
meet the fall. Statements and proofs.

Limits. THESE ARE BOUNDS ON THE MEASURE OF CHALLENGES AT WHICH A TEST SPEAKS: no run, no prover, no
coin and no input is in them; THAT A TEST IS THE VERIFIER's OWN Bool AT THE STATE AT WHICH THE
VERIFIER ASKS IT IS NOT SHOWN HERE. For the second fall that matters: K4's run on the free slots is
asked behind another kind's run in the same member, and the fall's test reads the state in front of
that member. NO NUMBER IS EVALUATED OR STATED: every bound q is a variable. MET FOR NOTHING: every
sentence here at q of 1 or more; both sentences in `FallDebt` at P := fun _ _ => False;
`k4_freeSlot_debt` at f := the fall itself; `k4_freeSlot_k9` has a premise that is never met at
Q.hp.used = 0. FOR THE FIRST FALL the count is a premise: `ZeroAtRound C d q`: at ONE round's typed
challenges those that show 0 as their first sampled element have at most the measure q. It hangs on
the kit C of typed challenges and on d's entry and kind, and is shown at no kit and no d here:
whoever shows it names what it needs of d (that the round samples one element, with no mark, no
position and no matrix entry, and its kind); NOTHING HERE TIES d TO THE ROUND OF ANY DESCRIPTION. C
IS ANY KIT: challenges that do not fit the rounds' declarations, or whose words are not below the
prime, are counted by neither fall: the first fall's test compares words as they are. FOR THE SECOND
FALL nothing is counted: where its test speaks, the condition of the batching's own test on the free
slots (`freeSlotOk`, Johnson/Desc/First/Door/Sums.lean) is false at K4's number of slots, at the
same ledger and the same merge slot (`k4_freeSlot_k9`: this is what is handed in);
`k4_freeSlot_debt` is a fallback: it follows from the sentence of ANOTHER fall f at the same place
whose test speaks wherever this one does, with the same q: WHOEVER LAYS BOTH FALLS INTO ONE LIST
COUNTS ONE EVENT TWICE. That such a fall f stands in any list, that its test is the Bool of
`k4_freeSlot_k9`, and that the batching's number of filled slots is K4's, is not shown. That the two
conditions agree at a layers' state is also proved for the batching's honest side
(Honest/K9/Quiet.lean, not in this tree: `k4Free_eq`, `k4Free_of_slotsFree`, `k4Share_silent`). NOT
STATED HERE, AND OWED: that where the member's own step accepts, the second fall's test is silent.
The stated shares (`Fall.share`) are read by nothing here. No property is claimed.

  `zeroFirst R`        a challenge's first sampled element is 0; false where it has none.
  `ZeroAtRound C d q`  the premise's form: one round.
  `K4ZeroCount C Q ds q`  the same event at the rounds ds of K4's member, at the round in which the
      second token sumcheck begins.
  `k4CoinZero_nil`, `k4CoinZero_at`, `fronts_nil_draws`   the first fall's test at no challenge, and
      as `zeroFirst`; with no round left a member is handed no challenge.
  `k4_zeroCount_cut`, `k4_zeroCount`   from one round to the member's rounds.
  `k4_coinZero_debt`   **the first fall's sentence**, at every P, ft and t, at no fixed challenge
      behind (tl = []).
  `freeSlot_same`, `k4_freeSlot_k9`   **where the second fall's test speaks, the batching's own
      condition is false.**
  `k4_freeSlot_debt`   the second fall's sentence, from that of a fall whose test speaks wherever
      this one does: a fallback.
-/
import Johnson.Desc.ProofFile.Honest.K4.Part
import Johnson.Desc.ProofFile.Honest.Law.CoverSeat
import Johnson.Desc.First.Batch.TestsAtS
import Johnson.Desc.First.K4.SeatS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open Prob
open scoped ENNReal
open OnBytes (E isZeroE oneE)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block Place OpenedColumn)

variable {S Cl : Type}

/-- A challenge's first sampled element is 0. False where it has no element: as `k4CoinZero` reads
it. -/
def zeroFirst (R : Fmt.Drawn) : Bool := isZeroE ((R.elems.head?.map E.ofTriple).getD oneE)

/-- **At one round's typed challenges, those whose first sampled element shows as 0 have at most the
measure q.** A premise's form: nothing is claimed by the definition. -/
def ZeroAtRound (C : CK) (d : RDT) (q : ℝ≥0∞) : Prop :=
  Iop.prRho {ρ : Iop.Rho (uLT C [d]) | ((drawnT C [d] ρ).head?.any zeroFirst) = true} ≤ q

/-- **The first fall's test speaks at no more than the measure q of the member's typed
challenges.** A definition: nothing is claimed by it. -/
def K4ZeroCount (C : CK) (Q : K4Pub) (ds : List RDT) (q : ℝ≥0∞) : Prop :=
  Iop.prRho {ρ : Iop.Rho (uLT C ds) | (k4CoinZero Q (drawnT C ds ρ)).isSome = true} ≤ q

/-- At no challenge the first fall's test is silent. -/
theorem k4CoinZero_nil (Q : K4Pub) : k4CoinZero Q [] = none := by
  unfold k4CoinZero
  rw [List.getElem?_nil]

/-- The first fall's test, as `zeroFirst` at the round in which the second token sumcheck begins. -/
theorem k4CoinZero_at (Q : K4Pub) (own : List Fmt.Drawn) :
    (k4CoinZero Q own).isSome = (own[(starts Q).getD 2 0]?).any zeroFirst := by
  unfold k4CoinZero
  cases own[(starts Q).getD 2 0]? with
  | none => rfl
  | some R =>
    show (if zeroFirst R = true then some _ else (none : Option String)).isSome = zeroFirst R
    cases zeroFirst R <;> rfl

/-- With no round left, every member that is reached is handed no challenge. -/
theorem fronts_nil_draws (ft : Nat) : ∀ (t : List (Block S Cl)) (s : S) (cols : List OpenedColumn),
    ∀ e ∈ frontsOf ft t s [] cols, e.2.2 = []
  | [], _, _, e, he => by simp [frontsOf] at he
  | d :: t, s, cols, e, he => by
    cases hr : d.rounds with
    | cons r l =>
      exfalso
      rw [frontsOf_few ft d t s [] cols (by rw [hr]; exact Nat.succ_pos _)] at he
      cases he
    | nil =>
      have hm : (([] : List Fmt.RoundView).take d.rounds.length).length = d.rounds.length := by
        rw [hr]
        rfl
      cases hs : d.step ft s (([] : List Fmt.RoundView).take d.rounds.length) cols with
      | error w =>
        rw [frontsOf_err ft d t s [] cols w hm hs] at he
        obtain rfl := List.mem_singleton.1 he
        show (([] : List Fmt.RoundView).take d.rounds.length).map (·.drawn) = []
        rw [List.take_nil]
        rfl
      | ok y =>
        obtain ⟨s', k⟩ := y
        rw [frontsOf_ok ft d t s s' k [] cols hm hs] at he
        rcases List.mem_cons.1 he with rfl | he'
        · show (([] : List Fmt.RoundView).take d.rounds.length).map (·.drawn) = []
          rw [List.take_nil]
          rfl
        · rw [List.drop_nil] at he'
          exact fronts_nil_draws ft t s' _ e he'

/-- **From one round to the member's rounds**, these cut at that round. CONDITIONAL on the count at
that round. -/
theorem k4_zeroCount_cut (C : CK) (Q : K4Pub) (pre post : List RDT) (d : RDT)
    (hpre : pre.length = (starts Q).getD 2 0) (q : ℝ≥0∞) (h : ZeroAtRound C d q) :
    K4ZeroCount C Q (pre ++ d :: post) q := by
  have h2 : Iop.prRho {y : Iop.Rho (uLT C ([d] ++ post)) |
      ((drawnT C ([d] ++ post) y).head?.any zeroFirst) = true} ≤ q + 0 := by
    refine fibre_le C [d] post {x | ((drawnT C [d] x).head?.any zeroFirst) = true}
      (fun _ => {_y | False}) _ q 0 h (fun x y hxy hx => hx ?_)
      (fun _ _ => zero_of_not C post (fun _ => False) (fun _ k => k) 0)
    have e : (drawnT C ([d] ++ post) (joinR C [d] post x y)).head? = (drawnT C [d] x).head? := by
      rw [drawn_join]
      have hl := drawnT_len C [d] x
      cases hx' : drawnT C [d] x with
      | nil =>
        rw [hx'] at hl
        cases hl
      | cons a l => rfl
    show ((drawnT C [d] x).head?.any zeroFirst) = true
    rw [← e]
    exact hxy
  have h1 : Iop.prRho {ρ : Iop.Rho (uLT C (pre ++ ([d] ++ post))) |
      (k4CoinZero Q (drawnT C (pre ++ ([d] ++ post)) ρ)).isSome = true} ≤ 0 + (q + 0) := by
    refine fibre_le C pre ([d] ++ post) {_x | False}
      (fun _ => {y | ((drawnT C ([d] ++ post) y).head?.any zeroFirst) = true}) _ 0 (q + 0)
      (zero_of_not C pre (fun _ => False) (fun _ k => k) 0) (fun x y hxy _ => ?_) (fun _ _ => h2)
    have hxy' : (k4CoinZero Q
        (drawnT C (pre ++ ([d] ++ post)) (joinR C pre ([d] ++ post) x y))).isSome = true := hxy
    rw [k4CoinZero_at, drawn_join, ← hpre, ← drawnT_len C pre x,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hxy'
    show ((drawnT C ([d] ++ post) y).head?.any zeroFirst) = true
    rw [List.head?_eq_getElem?]
    exact hxy'
  rw [zero_add, add_zero] at h1
  exact h1

/-- **From one round to the member's rounds.** d: the data of the round in which the second token
sumcheck begins. CONDITIONAL on the count at that round. -/
theorem k4_zeroCount (C : CK) (Q : K4Pub) (ds : List RDT) (d : RDT)
    (hd : ds[(starts Q).getD 2 0]? = some d) (q : ℝ≥0∞) (h : ZeroAtRound C d q) :
    K4ZeroCount C Q ds q := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hd
  have e : ds = ds.take ((starts Q).getD 2 0) ++ ds[(starts Q).getD 2 0] ::
      ds.drop ((starts Q).getD 2 0 + 1) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  rw [e]
  exact k4_zeroCount_cut C Q _ _ _ (by rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]) q h

/-- **THE FIRST FALL's SENTENCE**: at a member b with the rounds' data dsb, at every sentence P on
the challenges and the verifier's state in front, every ft and all members t behind, AT NO FIXED
CHALLENGE BEHIND (the letter tl of `FallDebt` is []). Where b does not stand at K4's place the event
is empty. CONDITIONAL on the count. -/
theorem k4_coinZero_debt (C : CK) (Q : K4Pub) (ft : Nat) (b : Block S Cl) (t : List (Block S Cl))
    (dsb : List RDT) (hlen : dsb.length = b.rounds.length) (q : ℝ≥0∞)
    (h : K4ZeroCount C Q dsb q) (P : List Fmt.Drawn → S → Prop) :
    FallDebt C (k4Fall Q) ft b t dsb [] P q := by
  intro fr s' _
  refine le_trans (pr_mono _ ?_) h
  rintro ρ ⟨rs, cols, h1, h2⟩
  rw [List.append_nil] at h1
  have hl : rs.length = b.rounds.length := by
    have e := congrArg List.length h1
    rw [List.length_map, drawnT_len, hlen] at e
    exact e
  rcases chainFall_cons [k4Fall Q] ft b t s' rs cols h2 with g | ⟨s'', k, -, g⟩
  · rw [← hl, List.take_length, h1] at g
    exact (fallOf_one g).2
  · exfalso
    rw [← hl, List.drop_length] at g
    obtain ⟨e, he, hf⟩ := (chainFall_iff _ _ _ _ _).1 g
    have ht : (k4CoinZero Q e.2.2).isSome = true := (fallOf_one hf).2
    rw [fronts_nil_draws ft t s'' _ e he, k4CoinZero_nil] at ht
    cases ht

/-- K4's condition on the free slots is the batching's, at the merge's slot as an option. The same
law, with this proof, stands among the files of the batching's honest side (`k4Free_eq`). -/
theorem freeSlot_same (n sFv : Nat) (F : OnBytes.Model.Fork) :
    OnBytes.Desc.First.K4.freeSlotOk n sFv F =
      VerifiableInference.Desc.First.Door.freeSlotOk n (some sFv) F := by
  unfold OnBytes.Desc.First.K4.freeSlotOk VerifiableInference.Desc.First.Door.freeSlotOk
  congr 1
  funext j
  have e : (j == sFv) = (some sFv == some j) := by
    by_cases h : j = sFv
    · subst h
      simp
    · have h' : sFv ≠ j := fun e => h e.symm
      simp [h, h']
  rw [e]

/-- **WHAT IS HANDED IN FOR THE SECOND FALL. Where its test speaks, the condition of the batching's
own test on the free slots is false**, at K4's number of slots: at the seat of K4 in the first
chain's state (`seatS`, Johnson/Desc/First/K4/SeatS.lean), and at what the lens of the batching's
tests reads there (`tAtS`, Johnson/Desc/First/Batch/TestsAtS.lean). By reading, and held by no
import: the right side is the Bool of the fall on the free slots that the batching's honest side
lays at the same member, at the number Q.hp.used. -/
theorem k4_freeSlot_k9 (Q : K4Pub) (quiet : Place) (share : Odds)
    (s : VerifiableInference.Desc.First.S) (ds : List Fmt.Drawn)
    (h : ((k4FreeSlotFall OnBytes.Desc.First.K4.seatS Q quiet share).test s ds).isSome = true) :
    (match VerifiableInference.Desc.K9.tAtS.get? s with
      | some a => VerifiableInference.Desc.First.Door.freeSlotOk Q.hp.used a.merge a.F
      | none => true) = false := by
  have h' : ((OnBytes.Desc.First.K4.seatS.own s).bind fun o =>
      if OnBytes.Desc.First.K4.freeSlotOk Q.hp.used o.wo.sFv
          (OnBytes.Desc.First.K4.seatS.fork s) = true
      then (none : Option String) else some _).isSome = true := h
  cases hs : s.here with
  | lay a =>
    have e1 : OnBytes.Desc.First.K4.seatS.own s = a.own := by
      simp only [OnBytes.Desc.First.K4.seatS, hs]
    have e2 : OnBytes.Desc.First.K4.seatS.fork s = a.F := by
      simp only [OnBytes.Desc.First.K4.seatS, hs]
    rw [e1, e2] at h'
    cases ho : a.own with
    | none =>
      rw [ho] at h'
      cases h'
    | some o =>
      rw [ho] at h'
      have hb : OnBytes.Desc.First.K4.freeSlotOk Q.hp.used o.wo.sFv a.F = false := by
        cases hq : OnBytes.Desc.First.K4.freeSlotOk Q.hp.used o.wo.sFv a.F with
        | false => rfl
        | true =>
          have h2 : (if OnBytes.Desc.First.K4.freeSlotOk Q.hp.used o.wo.sFv a.F = true
              then (none : Option String) else some _).isSome = true := h'
          rw [if_pos hq] at h2
          cases h2
      have key : OnBytes.Desc.First.K4.freeSlotOk Q.hp.used o.wo.sFv a.F =
          (match VerifiableInference.Desc.K9.tAtS.get? s with
            | some a => VerifiableInference.Desc.First.Door.freeSlotOk Q.hp.used a.merge a.F
            | none => true) := by
        rw [freeSlot_same]
        simp [VerifiableInference.Desc.K9.tAtS, VerifiableInference.Desc.First.S.fork?,
          VerifiableInference.Desc.First.S.tl?, VerifiableInference.Desc.K9.mergeOf, hs, ho]
      rw [← key]
      exact hb
  | _ =>
    have e1 : OnBytes.Desc.First.K4.seatS.own s = none := by
      simp only [OnBytes.Desc.First.K4.seatS, hs]
    rw [e1] at h'
    cases h'

/-- **The second fall's sentence: A FALLBACK**, from the sentence of a fall f at the same place
whose test speaks wherever this one does, WITH THE SAME q: WHOEVER LAYS BOTH FALLS INTO ONE LIST
COUNTS ONE EVENT TWICE. b: the last member with a round in front of that place. CONDITIONAL on f's
sentence. -/
theorem k4_freeSlot_debt (C : CK) (seat : OnBytes.Desc.First.K4.Seat S) (Q : K4Pub)
    (quiet : Place) (share : Odds) (f : Fall S) (hp : f.place = quiet)
    (hf : ∀ s ds, ((k4FreeSlotFall seat Q quiet share).test s ds).isSome = true →
      (f.test s ds).isSome = true)
    (ft : Nat) (b : Block S Cl) (t : List (Block S Cl)) (dsb : List RDT) (tl : List Fmt.Drawn)
    (P : List Fmt.Drawn → S → Prop) (q : ℝ≥0∞) (h : FallDebt C f ft b t dsb tl P q) :
    FallDebt C (k4FreeSlotFall seat Q quiet share) ft b t dsb tl P q := by
  intro fr s' hP
  refine le_trans (pr_mono _ ?_) (h fr s' hP)
  rintro ρ ⟨rs, cols, h1, h2⟩
  refine ⟨rs, cols, h1, ?_⟩
  obtain ⟨e, he, hg⟩ := (chainFall_iff _ _ _ _ _).1 h2
  refine (chainFall_iff _ _ _ _ _).2 ⟨e, he, ?_⟩
  obtain ⟨hpl, ht⟩ := fallOf_one hg
  have hpl' : f.place = e.1 := hp.trans hpl
  unfold fallOf
  exact (findSome_isSome _ _).2
    ⟨f, List.mem_filter.2 ⟨List.mem_singleton.2 rfl, beq_iff_eq.2 hpl'⟩, hf _ _ ht⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4CoinZero_nil
#print axioms ProofFile.Honest.K4.k4CoinZero_at
#print axioms ProofFile.Honest.K4.fronts_nil_draws
#print axioms ProofFile.Honest.K4.k4_zeroCount_cut
#print axioms ProofFile.Honest.K4.k4_zeroCount
#print axioms ProofFile.Honest.K4.k4_coinZero_debt
#print axioms ProofFile.Honest.K4.freeSlot_same
#print axioms ProofFile.Honest.K4.k4_freeSlot_k9
#print axioms ProofFile.Honest.K4.k4_freeSlot_debt
