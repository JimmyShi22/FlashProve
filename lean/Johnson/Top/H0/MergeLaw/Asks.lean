--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/MergeLaw/Asks.lean: what a yes of the merge's decision asks: every test of the text
named in a statement. Theorems with their proofs.

Seven tests of the text (Johnson/Desc/First/Fork/MergeKind.lean) stood in no conclusion of the
merge's law: the head's ledger is laid; nothing is owed by the round in front; the numbers of claims
and of slots; each claim's unit is in the layout; each claim's factors fit its unit; the two tests
on the batching round. The law's other statements hold of the text and of a laxer one alike. Here
each test of the text stands in a conclusion of one of the three theorems.

Main names:
  `tape_iff`: the maker of the tape says yes just where the stretch and the list of entries have a
    first member, the two tests on the batching round pass, and the strict maker returns on the
    rest; and what it then gives.
  `decide_iff`: BOTH WAYS: the decision's yes is: the record stands in the head's link; the head's
    ledger is laid; nothing is owed by the round in front; the tape is made; the claim and what the
    head heard are laid; what is heard returns and uses the stretch up; the next free slot is the
    plan's number of slots; and the record behind is the one written out.
  `yes_asks`: ONE STATEMENT with six of these seven, down to those at the head of `mergeHear` at the
    one claim and the two on the batching round. The seventh, on the numbers of claims and of slots,
    is asked by the decision at one claim and one slot, where it is true by the text; in general it
    stands in `hear_tests` (Pinned.lean). `yes_asks` does NOT hold three further tests, which stand
    in `decide_iff` and `tape_iff` alone: the strict maker returns on the rest; what is heard
    returns and uses the stretch up; the next free slot is the plan's number of slots.

Limits. Whether a statement here falls when a test is struck from the text has not been tried. The
test on the batching round's entry is asked at the block's own entry: a closed Boolean, which reads
neither the record nor the rounds. The tests inside the flat routines that `mergeHear` calls are not
listed here: what their yes
holds is `mergeHear_inv` (Hear.lean) and `hear_ended` (Said.lean). `mergeHear` has no statement both
ways. Nothing on soundness or on hiding.

-/
import Johnson.Top.H0.MergeLaw.Pinned

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes (E)
open OnBytes.K.Kc (Tape flatOf)
open OnBytes.Model (RoundName)
open VerifiableInference.Desc (need named)
open VerifiableInference.Desc.First.Look (tapeS)
open VerifiableInference.Desc.First.Door (batchEntryB batchRoundB)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide mergeTapeE mergeHear mergeEntries
  claimFits)

/-- **The maker of the tape, both ways.** -/
theorem tape_iff (rs : List Fmt.RoundView) (es : List Fmt.Entry) (tp : Tape) :
    mergeTapeE rs es = .ok tp ↔
      ∃ r rs' e es' t, rs = r :: rs' ∧ es = e :: es' ∧ batchEntryB e = true ∧
        batchRoundB e r = true ∧ tapeS rs' es' = some t ∧ tp = flatOf r (some e) :: t := by
  constructor
  · intro h
    match rs, es, h with
    | [], _, h => simp [mergeTapeE] at h
    | _ :: _, [], h => simp [mergeTapeE] at h
    | r :: rs, e :: es, h =>
      by_cases h1 : batchEntryB e = true
      · by_cases h2 : batchRoundB e r = true
        · cases ht : tapeS rs es with
          | none => simp [mergeTapeE, need, named, h1, h2, ht, bind, Except.bind] at h
          | some t =>
            simp [mergeTapeE, need, named, h1, h2, ht, bind, Except.bind, pure, Except.pure] at h
            exact ⟨r, rs, e, es, t, rfl, rfl, h1, h2, ht, h.symm⟩
        · simp [mergeTapeE, need, h1, h2, bind, Except.bind] at h
      · simp [mergeTapeE, need, h1, bind, Except.bind] at h
  · rintro ⟨r, rs', e, es', t, rfl, rfl, h1, h2, ht, rfl⟩
    simp [mergeTapeE, need, named, h1, h2, ht, bind, Except.bind, pure, Except.pure]

/-- **The decision, both ways.** -/
theorem decide_iff (P : HeadMergeP) (s s' : S) (rs : List Fmt.RoundView) :
    headMergeDecide P s rs = .ok s' ↔
      ∃ a tp claim x wo F, s.here = .head a ∧ a.opened = true ∧ s.noneWaits = true ∧
        mergeTapeE rs (mergeEntries P.lay.lk 1 P.work) = .ok tp ∧ a.claim = some claim ∧
        a.x = some x ∧ mergeHear P.lay #[claim] #[x.sV] a.F tp = .ok (wo, F, []) ∧
        F.next = P.nMsg ∧
        s' = { s with
          rowsOwed := none
          here := .head { a with wo := some wo, F := { F with planClaimsF := P.nLin }, Fm := a.F,
                                 slot := some F.next } } := by
  constructor
  · intro h
    cases hh : s.here with
    | head a =>
      by_cases ho : a.opened = true
      · by_cases hw : s.noneWaits = true
        · cases ht : mergeTapeE rs (mergeEntries P.lay.lk 1 P.work) with
          | error e => simp [headMergeDecide, hh, ho, hw, ht, need, bind, Except.bind] at h
          | ok t =>
            cases hcl : a.claim with
            | none =>
              simp [headMergeDecide, hh, ho, hw, ht, hcl, need, named, bind, Except.bind] at h
            | some claim =>
            cases hx : a.x with
            | none =>
              simp [headMergeDecide, hh, ho, hw, ht, hcl, hx, need, named, bind, Except.bind] at h
            | some x =>
            cases hm : mergeHear P.lay #[claim] #[x.sV] a.F t with
            | error e =>
              simp [headMergeDecide, hh, ho, hw, ht, hcl, hx, hm, need, named, bind,
                Except.bind] at h
            | ok r =>
              obtain ⟨wo, F, t'⟩ := r
              by_cases he : t'.isEmpty = true
              · by_cases hc : (F.next == P.nMsg) = true
                · simp [headMergeDecide, hh, ho, hw, ht, hcl, hx, hm, he, hc, need, named, bind,
                    Except.bind, pure, Except.pure] at h
                  have ht' : t' = [] := List.isEmpty_iff.1 he
                  subst ht'
                  exact ⟨a, t, claim, x, wo, F, rfl, ho, hw, rfl, hcl, hx, hm, by simpa using hc, by
                    rw [hx, hcl, ho]
                    exact h.symm⟩
                · simp [headMergeDecide, hh, ho, hw, ht, hcl, hx, hm, he, hc, need, named, bind,
                    Except.bind] at h
              · simp [headMergeDecide, hh, ho, hw, ht, hcl, hx, hm, he, need, named, bind,
                  Except.bind] at h
        · simp [headMergeDecide, hh, ho, hw, need, bind, Except.bind] at h
      · simp [headMergeDecide, hh, ho, need, bind, Except.bind] at h
    | _ => simp [headMergeDecide, hh] at h
  · rintro ⟨a, tp, claim, x, wo, F, hh, ho, hw, ht, hcl, hx, hm, hn, rfl⟩
    simp [headMergeDecide, hh, ho, hw, ht, hcl, hx, hm, hn, need, named, bind, Except.bind, pure,
      Except.pure]

/-- **WHAT A YES ASKS**, in one statement. -/
theorem yes_asks {P : HeadMergeP} {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') :
    ∃ a claim x r rs', s.here = .head a ∧ a.opened = true ∧ s.noneWaits = true ∧
      a.claim = some claim ∧ a.x = some x ∧ claim.ui < P.lay.U.size ∧
      claimFits P.lay claim = true ∧ rs = r :: rs' ∧
      batchEntryB { name := RoundName.batSigma.name, work := P.work, drawE := 1, rows := 1 } = true
          ∧
      batchRoundB { name := RoundName.batSigma.name, work := P.work, drawE := 1, rows := 1 } r =
        true := by
  obtain ⟨a, tp, claim, x, wo, F, hh, ho, hw, ht, hcl, hx, hm, _, _⟩ := (decide_iff P s s' rs).1 h
  obtain ⟨r, rs', e, es', _, e1, e2, b1, b2, _, _⟩ := (tape_iff _ _ _).1 ht
  obtain ⟨_, t2, t3⟩ := hear_tests hm
  have ee : e = { name := RoundName.batSigma.name, work := P.work, drawE := 1, rows := 1 } := by
    unfold mergeEntries at e2
    exact (List.cons.inj e2).1.symm
  subst ee
  exact ⟨a, claim, x, r, rs', hh, ho, hw, hcl, hx, by simpa using t2, by simpa using t3, e1, b1, b2⟩

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.tape_iff
#print axioms VerifiableInference.Desc.First.MergeLaw.decide_iff
#print axioms VerifiableInference.Desc.First.MergeLaw.yes_asks
