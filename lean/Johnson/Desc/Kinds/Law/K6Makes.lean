-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6Makes.lean: WHAT THE OUTPUT HEAD's OWN BLOCK MAKES OF THE TABLE OF JOINTS'
PUBLIC ITEMS: the maker's lemmas for leftOn and for lookIn (the lookup on the digits) at the head's
segment. Statements and proofs.

The table's row of the head's own block asks the item left (what the lookup on the calls left: what
was heard is the end values of a hearing from some ledger, and the ledger in hand is the one behind
that hearing) and makes the item leftOn (the same with "the ledger in hand is LATER than the one
behind that hearing"), and the item lookIn of the lookup on the digits (that lookup's own condition
in front). All are worded by the lookup's files (Johnson/Desc/First/Look/K3LeftItem.lean:
k3LeftItem, k3LeftOnItem; K3LookIn.lean: k3LookIn).

  foLater_of       the two relations "a later ledger": the one with four fields gives the
                   one with three.
  leftOn_of_kept   from k3LeftItem at the verifier's state in front: k3LeftOnItem at a state behind
                   at which what the lookup heard stays, the ledger is later, and is well laid.
  leftOn_below     so behind a yes of the strict reading of the kind's block, under K6On in front.
  blockAt_takes_exact   the head's hearing takes JUST 41 + 8 lt + 4 lPd slots of the ledger, where
                   the first point that the lookup heard has at least lt coordinates
                   (Law/TakesAt.lean had that number as a ceiling).
  lookIn_below     k3LookIn at the digits' parameters behind that yes.

WHAT IT IS NOT. Implications. WHAT lookIn_below ASKS OF THE STATE IN FRONT IS THE PROMISE's, AND OF
THE PLAN: K6On · the heard first point's size (the item lookOut of the lookup on the calls has it) ·
"the next free slot and the head's count give the digits' first slot" (the item callerIn with a test
on the plan: shown at no plan here) · all free from the next slot on, with room (the item
freeAbove) · nothing heard at the digits' seat, and the table of arrays (the item linkFresh) · no
count of rows waits · the open link's number. Which item of the table's row in front gives which is
by reading.
Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.Desc.First.Look.K3LeftItem
import Johnson.Desc.Kinds.Law.K6RecordPaid
import Johnson.Desc.Kinds.Law.KeepsAt
import Johnson.Desc.Kinds.Law.RowPromise
import Johnson.Desc.Kinds.Law.TakesAt
import Johnson.Desc.Kinds.Law.FromGiven
import Johnson.Desc.First.Look.K3LookIn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.OnPublicFiles (k3LeftItem k3LeftOnItem leftOn_of_left leftOn_stays)

/-- The relation with four fields gives the relation with three. -/
theorem foLater_of {F G : Fork} (h : OnBytes.PscRun.Later F G) : _root_.Fo.Later F G :=
  ⟨h.next, h.ns, h.keep⟩

/-- **leftOn, from left in front and what a block keeps.** -/
theorem leftOn_of_kept {p : VerifiableInference.Desc.First.Look.P} {s s' : S} {Fs Ft : Fork}
    (hs : s.fork? = some Fs) (ht : s'.fork? = some Ft) (hh : s'.lookHeard? = s.lookHeard?)
    (hl : OnBytes.PscRun.Later Fs Ft) (hw : WellLaid Ft) (L : k3LeftItem p s) :
    k3LeftOnItem p s' :=
  leftOn_stays hh hs ht (foLater_of hl) ⟨hw.2.1, hw.2.2, hw.1⟩ (leftOn_of_left L)

/-- **THE MAKER's LEMMA FOR leftOn AT THE HEAD's OWN BLOCK.** -/
theorem leftOn_below (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit)
    (hb : blockOf W l = some b) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (Sound.below b).decide s rs gs = .ok s')
    (hOn : K6On W s) (p : VerifiableInference.Desc.First.Look.P) (L : k3LeftItem p s) :
    k3LeftOnItem p s' := by
  obtain ⟨_, hd⟩ := canonical_of_below b s s' rs gs h
  obtain ⟨i, hu, rfl⟩ := Option.map_eq_some_iff.mp hb
  have hL := blockAt_later _ _ _ _ s s' rs gs hd
  obtain ⟨a, F1, X, Q, ha, hop, _, rfl⟩ := Came.decide_record _ _ _ _ hd
  have f1 : s.fork? = some a.F := by
    unfold S.fork?
    rw [ha]
    simp [hop]
  have f2 : ({ s with here := .head { a with F := F1, x := some X, squaresP := some Q } } :
      S).fork? = some F1 := by
    unfold S.fork?
    simp [hop]
  have hh : ({ s with here := .head { a with F := F1, x := some X, squaresP := some Q } } :
      S).lookHeard? = s.lookHeard? := by
    unfold S.lookHeard?
    rw [ha]
  have hL' : OnBytes.PscRun.Later a.F F1 := by
    have e1 : (seatAt W.hS i).ledger s = a.F := by
      show s.fork?.getD {} = _
      rw [f1]
      rfl
    have e2 : (seatAt W.hS i).ledger
        { s with here := .head { a with F := F1, x := some X, squaresP := some Q } } = F1 := by
      show (S.fork? _).getD {} = _
      rw [f2]
      rfl
    rw [e1, e2] at hL
    exact hL
  have hr : readsOf W = i := by
    unfold readsOf
    rw [hu]
    rfl
  have hW : WellLaid a.F := by
    have h0 : WellLaid ((seatAt W.hS (readsOf W)).ledger s) := hOn.1
    rw [hr] at h0
    have e1 : (seatAt W.hS i).ledger s = a.F := by
      show s.fork?.getD {} = _
      rw [f1]
      rfl
    rw [e1] at h0
    exact h0
  exact leftOn_of_kept f1 f2 hh hL' (Came.wellLaid_later hW hL') L

/-- **THE HEAD's HEARING TAKES JUST THE PLAN's NUMBER OF SLOTS** (Law/TakesAt.lean has that number
as a ceiling): where the first point that the lookup heard has at least lt coordinates. -/
theorem blockAt_takes_exact (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hS : OnBytes.PscRun.Sized ((seatAt h iU3).ledger s))
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') (gk : OnBytes.Model.Forest.Heard)
    (hk : s.lookHeard? = some gk)
    (hz : (letI := (parOf h work).sizes
      Norm.lt) ≤ gk.zx.size) :
    Takes ((seatAt h iU3).ledger s) ((seatAt h iU3).ledger s') (takesOf (parOf h work)) := by
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) (parOf h work)
      (seatAt h iU3) s rs = .ok s' := hd
  obtain ⟨g, H, F, left, w, s1, s2, hg, hh, e1, e2, hs'⟩ := decideBy_spec hd'
  rw [hs', seatAt_fit h iU3 s F H w s1 s2 e1 e2]
  have T := hear_takes hS hh
  obtain ⟨z, y, hz', _, _, rfl⟩ := Came.given_ok (parOf h work) _ s g hg
  have hz2 : (seatAt h iU3).lookup s = some (gk.zx, fun c => gk.zk.getD c #[]) := by
    show (s.lookHeard?.map fun g => (g.zx, fun c => g.zk.getD c #[])) = _
    rw [hk]
    rfl
  obtain rfl : z = (gk.zx, fun c => gk.zk.getD c #[]) := Option.some.inj (hz'.symm.trans hz2)
  refine T.cast ?_
  letI := (parOf h work).sizes
  have q := congrArg List.length (Came.toList_last gk.zx Norm.lt)
  rw [Array.length_toList, List.length_drop, Array.length_toList] at q
  have hsz : (Point.last gk.zx Norm.lt).size = Norm.lt := by omega
  show 41 + 4 * Norm.lt + 4 * (Point.last gk.zx Norm.lt).size + 4 * Norm.lPd =
    41 + 8 * Norm.lt + 4 * Norm.lPd
  rw [hsz]
  omega

/-- **THE MAKER's LEMMA FOR lookIn (THE LOOKUP ON THE DIGITS) AT THE HEAD's OWN BLOCK.** In front:
K6On; what the lookup on the calls heard has a first point of at least lt coordinates; the ledger's
next free slot and the head's count give the digits' first slot; from the next slot on all is free,
with room for the digits' lookup; nothing is heard at the digits' seat; no count of rows waits; the
open link has the place's number and the given table of arrays. -/
theorem lookIn_below (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit)
    (hb : blockOf W l = some b) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (Sound.below b).decide s rs gs = .ok s')
    (hOn : K6On W s) (gk : OnBytes.Model.Forest.Heard) (hk : s.lookHeard? = some gk)
    (hz : (letI := (parOf W.hS (workOf W)).sizes
      Norm.lt) ≤ gk.zx.size)
    (p : VerifiableInference.Desc.First.Look.P) (sh : OnBytes.Model.Forest.Shape)
    (hsh : p.shape = some sh) (hdg : p.digits = true) (arrayOf : Array (Nat × String)) (F : Fork)
    (hF : s.fork? = some F) (hfirst : F.next + takesOf (parOf W.hS (workOf W)) = p.first)
    (hroom : p.first + OnBytes.Model.Forest.elems sh ≤ F.ns)
    (hfree : ∀ j, F.next ≤ j → ¬ OnBytes.PscRun.Filled F j)
    (hfresh : (s.tl?.bind (·.heard)).isNone = true)
    (hrows : VerifiableInference.Desc.First.Tape.RowsOwed.noneWaits s.rowsOwed = true)
    (hlink : (s.link?.any fun L => L.link == p.link && L.arrayOf == arrayOf) = true) :
    VerifiableInference.Desc.First.Look.k3LookIn p arrayOf s' = true := by
  obtain ⟨_, hd⟩ := canonical_of_below b s s' rs gs h
  obtain ⟨i, hu, rfl⟩ := Option.map_eq_some_iff.mp hb
  have hr : readsOf W = i := by
    unfold readsOf
    rw [hu]
    rfl
  have hled : (seatAt W.hS i).ledger s = F := by
    show s.fork?.getD {} = _
    rw [hF]
    rfl
  have hW : WellLaid F := by
    have h0 : WellLaid ((seatAt W.hS (readsOf W)).ledger s) := hOn.1
    rw [hr, hled] at h0
    exact h0
  have hS : OnBytes.PscRun.Sized F := ⟨hW.2.1, hW.2.2, hW.1⟩
  have T := blockAt_takes_exact W.hS i (workOf W) l s s' rs gs (by rw [hled]; exact hS) hd gk hk hz
  obtain ⟨a, F1, X, Q, ha, hop, _, rfl⟩ := Came.decide_record _ _ _ _ hd
  have f2 : ({ s with here := .head { a with F := F1, x := some X, squaresP := some Q } } :
      S).fork? = some F1 := by
    unfold S.fork?
    simp [hop]
  have hled2 : (seatAt W.hS i).ledger
      { s with here := .head { a with F := F1, x := some X, squaresP := some Q } } = F1 := by
    show (S.fork? _).getD {} = _
    rw [f2]
    rfl
  rw [hled, hled2] at T
  have htl : ({ s with here := .head { a with F := F1, x := some X, squaresP := some Q } } :
      S).tl? = s.tl? := by
    unfold S.tl?
    rw [ha]
  have hlk : ({ s with here := .head { a with F := F1, x := some X, squaresP := some Q } } :
      S).link? = s.link? := by
    unfold S.link?
    rw [ha]
  have hnext : F1.next = p.first := by rw [T.next, hfirst]
  have hS1 := T.touch.sized
  have hns : F1.ns = F.ns := T.touch.ns
  have hfr : ∀ j, j < OnBytes.Model.Forest.elems sh → F1.gotF.getD (p.first + j) true = false := by
    intro j hj
    have h1 : ¬ OnBytes.PscRun.Filled F1 (p.first + j) := fun hf =>
      hfree (p.first + j) (by omega)
        ((T.touch.out (p.first + j) (Or.inr (by omega))).2.2.1 hf)
    have hin : p.first + j < F1.gotF.size := by
      rw [hS1.2.2, hns]
      omega
    unfold OnBytes.PscRun.Filled at h1
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hin] at h1 ⊢
    simpa using h1
  unfold VerifiableInference.Desc.First.Look.k3LookIn VerifiableInference.Desc.K3.k3OnIn
    VerifiableInference.Desc.K3.heardAt
  rw [hsh, hdg, hlk, hlink, f2]
  simp only [if_true, htl, hfresh, Bool.true_and, Bool.and_true, Option.any_some]
  show (VerifiableInference.Desc.First.Tape.RowsOwed.noneWaits s.rowsOwed &&
    (F1.next == p.first && VerifiableInference.Desc.K3.sizedB F1 &&
      VerifiableInference.Desc.K3.freeB F1 p.first (OnBytes.Model.Forest.elems sh))) = true
  rw [hrows, hnext]
  unfold VerifiableInference.Desc.K3.sizedB VerifiableInference.Desc.K3.freeB
  rw [hS1.1, hS1.2.1, hS1.2.2, hns]
  simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, Bool.not_eq_true']
  exact ⟨hroom, fun j hj => hfr j hj⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.blockAt_takes_exact
#print axioms VerifiableInference.Desc.Kinds.Head.Law.lookIn_below
#print axioms VerifiableInference.Desc.Kinds.Head.Law.leftOn_of_kept
#print axioms VerifiableInference.Desc.Kinds.Head.Law.leftOn_below
