-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/RunsStill.lean: FOR THE BATCHING KIND's PREMISE ON A RUN OF CLAIMS: THE
OUTPUT HEAD's OWN THREE RUNS ("norm", "policy", "logits"), AT THE SEAT AT THE CARRIED RECORD, LEAVE
THE RECORD AS IT IS, AND THEIR FORMS ARE A FUNCTION OF WHAT THE HEAD's READERS SEE BESIDE THE LEDGER
AND OF A SNAPSHOT OF THE LEDGER IN FRONT. Definitions, statements and proofs. It names none of the
batching kind's letters: a short file over them calls still_core and still_filled.

WHY A SNAPSHOT. Two of the five readers of lettersAt look at the live ledger at this seat
(Stored/HeadSeatAt.lean): heard reads what was shown under the slots of the head's own hearing;
reads divides by the number of columns of the reads' array. So the forms are no function of what was
heard alone. They are the same at every ledger that is later than the snapshot and has the same
numbers of columns (Law/RunsFixed.lean: letters_alike).

  Seen, seenOf     what the readers see beside the ledger: the head's x, squaresP, t, opened,
                   lookHeard; the reply; the request's words.
  Sees s z F       the record s stands in the head's link, shows z, and its ledger is F.
  alike_of_sees    two records that show the same, the second's ledger later, with the same numbers
                   of columns: Law/RunsFixed.lean's Alike.
  lettersOf z U    the letters that are read at any record which shows z with the ledger U (by
                   choice of one: letters_at says that it does not matter which).
  formsOf name z U the forms of the run of that name at these letters.
  reads_bare       at this seat an entry of a read names no slot.
  K6Ready z U      A PROMISE ON WHAT IS FIXED IN FRONT: at a record that shows (z, U) the letters in
                   front are read (given) and the seat reads back as heard what the head's own
                   hearing returned from some well laid ledger; U is later than the ledger that this
                   hearing left. NOTHING IS ASKED OF THE READS: that their reader
                   answers at the snapshot follows BACKWARD from the run's own yes (letters_back).
  lettersAt_ok, lettersOf_of, letters_back, ready_at_letters   tools.
  still_core       MAIN: under K6Ready z U, at a record that shows z, whose ledger is later than U
                   with the same numbers of columns: where one of the three runs returns, the record
                   behind is the record, and the claims are the plain claims of formsOf name z U.
  still_filled     under K6Ready z U every slot that a form of formsOf name z U names is filled in
                   U.
  seen_of_run      where a run returns the record shows something.

WHAT IT IS NOT. K6Ready IS A PREMISE: that it holds in front of the batching's draw is owed: by the
head's own block at its border (what it leaves) and by every block between, which must keep it.
Nothing on the entries that the forms name (the virtual rows' weights). Nothing on the run "join".
lettersOf is made by choice: no code. Nothing on soundness.
LETTERS. K6Ready: under "there are": s0: any record that shows (z, U) (it does not matter which:
Alike); g, H: pinned by the two readers' equations at s0; F0, rs, G: tied to H by the hearing's
equation and to U by "later": no equation to a record: they say "there was such a hearing".
still_core: fs: pinned by formsOf name z U = some fs.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RunsFixed
import Johnson.Desc.Kinds.Law.SlotsFilled

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S)

/-- What the head's readers see of a record beside the ledger. -/
structure Seen where
  x : Option OnBytes.Model.Head.Heard
  squaresP : Option OnBytes.Model.Psc
  t : Option OnBytes.Model.Head.Tables
  opened : Bool
  lookHeard : Option OnBytes.Model.Forest.Heard
  reply : Option E
  req : Array UInt32

/-- Off a record in the head's link. -/
def seenOf (s : S) : Option Seen :=
  match s.here with
  | .head o => some ⟨o.x, o.squaresP, o.t, o.opened, o.lookHeard, s.out.reply, s.req⟩
  | _ => none

/-- The record stands in the head's link, shows z, and its ledger is F. -/
def Sees (s : S) (z : Seen) (F : Fork) : Prop :=
  ∃ o, s.here = .head o ∧ o.F = F ∧
    z = ⟨o.x, o.squaresP, o.t, o.opened, o.lookHeard, s.out.reply, s.req⟩

theorem alike_of_sees {s0 e : S} {z : Seen} {U F : Fork} (h0 : Sees s0 z U) (h1 : Sees e z F)
    (hL : Later U F) (hK : F.trees.map (·.K) = U.trees.map (·.K)) : Alike s0 e := by
  obtain ⟨o, ho, rfl, hz⟩ := h0
  obtain ⟨o', ho', rfl, hz'⟩ := h1
  have e := hz.symm.trans hz'
  simp only [Seen.mk.injEq] at e
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := e
  exact ⟨o, o', ho, ho', e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, e6.symm, e7.symm, hL, hK⟩

theorem sees_of_seen {e : S} {z : Seen} {F : Fork} (hz : seenOf e = some z)
    (hF : e.fork? = some F) : Sees e z F := by
  unfold seenOf at hz
  unfold S.fork? at hF
  cases hh : e.here with
  | head o =>
    rw [hh] at hz hF
    simp only [Option.some.injEq] at hz
    by_cases ho : o.opened = true
    · simp only [ho, if_true, Option.some.injEq] at hF
      exact ⟨o, hh, hF, hz.symm⟩
    · simp [ho] at hF
  | between => rw [hh] at hz; cases hz
  | lay a => rw [hh] at hz; cases hz
  | att a => rw [hh] at hz; cases hz
  | fin a => rw [hh] at hz; cases hz
  | mem a => rw [hh] at hz; cases hz

section At

variable (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Par)

open Classical in
/-- The letters that are read at a record which shows z with the ledger U. -/
noncomputable def lettersOf (z : Seen) (U : Fork) : Option (Given × Behind × Places) :=
  if hs : ∃ s, Sees s z U then (lettersAt p (seatAt h iU3) (Classical.choose hs)).toOption else none

/-- The forms of a run at these letters. -/
noncomputable def formsOf (name : String) (z : Seen) (U : Fork) : Option (List Form) :=
  (lettersOf h iU3 p z U).bind fun v =>
    ((fun (_ : Given) (_ : Behind) (_ : Places) => claims) v.1 v.2.1 v.2.2).lookup name

/-- There is a record that shows z with the ledger U at which these letters are read. -/
theorem lettersOf_some {z : Seen} {U : Fork} {v : Given × Behind × Places}
    (e : lettersOf h iU3 p z U = some v) :
    ∃ s0, Sees s0 z U ∧ lettersAt p (seatAt h iU3) s0 = .ok v := by
  unfold lettersOf at e
  split at e
  · rename_i hs
    refine ⟨Classical.choose hs, Classical.choose_spec hs, ?_⟩
    cases hl : lettersAt p (seatAt h iU3) (Classical.choose hs) with
    | error m => rw [hl] at e; cases e
    | ok w =>
      rw [hl] at e
      exact congrArg Except.ok (Option.some.inj e)
  · cases e

/-- **The same letters are read at every record that shows z and goes on from U.** -/
theorem letters_at {z : Seen} {U F : Fork} {v : Given × Behind × Places} {e : S}
    (hv : lettersOf h iU3 p z U = some v) (he : Sees e z F) (hL : Later U F)
    (hK : F.trees.map (·.K) = U.trees.map (·.K)) : lettersAt p (seatAt h iU3) e = .ok v := by
  obtain ⟨s0, h0, e0⟩ := lettersOf_some h iU3 p hv
  exact letters_alike h iU3 p (alike_of_sees h0 he hL hK) v e0

/-- At this seat an entry of a read names no slot. -/
theorem reads_bare {s : S} {x : FinalNorm.Reads × Reads} (e : (seatAt h iU3).reads s = some x) :
    (∀ r i, (x.1.entry r i).slots = #[]) ∧ ∀ r i, (x.2.entry r i).slots = #[] := by
  unfold seatAt at e
  dsimp only at e
  split at e
  · obtain ⟨tt, _, e1⟩ := Option.bind_eq_some_iff.mp e
    obtain ⟨tr, _, e2⟩ := Option.bind_eq_some_iff.mp e1
    split at e2
    · cases e2
    · have e3 := Option.some.inj e2
      subst e3
      exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  · cases e

/-- **A PROMISE ON WHAT IS FIXED IN FRONT**: at a record that shows z with the ledger U: the head's
letters in front are read; what the seat reads back as heard is what the head's own hearing returned
from some well laid ledger; U is later than the ledger which that hearing left. NOTHING IS ASKED OF
THE READS. -/
def K6Ready (z : Seen) (U : Fork) : Prop :=
  ∃ (s0 : S) (g : Given) (H : HeardAll) (F0 G : Fork) (rs : List Fmt.RoundView),
    Sees s0 z U ∧ given p (seatAt h iU3) s0 = .ok g ∧ (seatAt h iU3).heard s0 = some H ∧
    WellLaid F0 ∧ hear F0 rs = some (H, G, []) ∧ Later G U

/-- Where the letters are read: the three readers' answers. -/
theorem lettersAt_ok {s : S} {v : Given × Behind × Places}
    (e : lettersAt p (seatAt h iU3) s = .ok v) :
    ∃ (H : HeardAll) (x : FinalNorm.Reads × Reads), given p (seatAt h iU3) s = .ok v.1 ∧
      (seatAt h iU3).heard s = some H ∧ (seatAt h iU3).reads s = some x ∧
      v = (v.1, ⟨H.1, H.2.1, H.2.2⟩, ⟨x.1, x.2⟩) := by
  unfold lettersAt at e
  cases hg : given p (seatAt h iU3) s with
  | error m => rw [hg] at e; cases e
  | ok g =>
    rw [hg] at e
    cases hH : (seatAt h iU3).heard s with
    | none => rw [hH] at e; cases e
    | some H =>
      rw [hH] at e
      cases hx : (seatAt h iU3).reads s with
      | none => rw [hx] at e; cases e
      | some x =>
        rw [hx] at e
        have e1 := Except.ok.inj e
        subst e1
        exact ⟨H, x, rfl, rfl, rfl, rfl⟩

/-- The letters that are read at a record are lettersOf of what it shows. -/
theorem lettersOf_of {s : S} {z : Seen} {U : Fork} {v : Given × Behind × Places}
    (hs : Sees s z U) (e : lettersAt p (seatAt h iU3) s = .ok v) :
    lettersOf h iU3 p z U = some v := by
  unfold lettersOf
  have hx : ∃ s, Sees s z U := ⟨s, hs⟩
  rw [dif_pos hx]
  rw [letters_alike h iU3 p (alike_of_sees hs (Classical.choose_spec hx) (Later.refl _) rfl) v e]
  rfl

/-- **BACKWARD**: under the promise, the letters that are read at a record which goes on from
(z, U) are read at (z, U) too: two of the three readers answer the same along Alike (equations); the
third answers at (z, U) by the promise, and then the same further on. -/
theorem letters_back {z : Seen} {U F : Fork} {v : Given × Behind × Places} {e : S}
    (hR : K6Ready h iU3 p z U) (he : Sees e z F) (hL : Later U F)
    (hK : F.trees.map (·.K) = U.trees.map (·.K)) (hv : lettersAt p (seatAt h iU3) e = .ok v) :
    lettersOf h iU3 p z U = some v := by
  obtain ⟨s0, g, H, _, _, _, hs0, hg, hH, _⟩ := hR
  have a := alike_of_sees hs0 he hL hK
  obtain ⟨H', x, e1, e2, e3, e4⟩ := lettersAt_ok h iU3 p hv
  have hHe := heard_alike h iU3 a H hH
  rw [e2] at hHe
  obtain rfl := Option.some.inj hHe
  refine lettersOf_of h iU3 p hs0 ?_
  unfold lettersAt
  rw [← given_alike h iU3 p a, e1, hH, ← reads_alike h iU3 a, e3, e4]
  rfl

/-- Under the promise, at the letters that are read at (z, U): what they hold as heard is what the
head's own hearing returned. -/
theorem ready_at_letters {z : Seen} {U : Fork} {v : Given × Behind × Places}
    (hR : K6Ready h iU3 p z U) (hv : lettersOf h iU3 p z U = some v) :
    ∃ (F0 G : Fork) (rs : List Fmt.RoundView), WellLaid F0 ∧
      (letI := v.1
       hear F0 rs = some ((v.2.1.norm, v.2.1.final, v.2.1.head), G, [])) ∧ Later G U := by
  obtain ⟨s0, g, H, F0, G, rs, hs0, hg, hH, hW, hh, hL⟩ := hR
  obtain ⟨s1, hs1, e1⟩ := lettersOf_some h iU3 p hv
  have a := alike_of_sees hs0 hs1 (Later.refl _) rfl
  obtain ⟨H', x, k1, k2, _, k4⟩ := lettersAt_ok h iU3 p e1
  have hH1 := heard_alike h iU3 a H hH
  rw [k2] at hH1
  obtain rfl := Option.some.inj hH1
  have hg1 : (Except.ok v.1 : Except String Given) = .ok g := by
    rw [← k1, given_alike h iU3 p a, hg]
  obtain rfl := Except.ok.inj hg1
  refine ⟨F0, G, rs, hW, ?_, hL⟩
  rw [k4]
  exact hh

/-- Where a run returns, the record shows something. -/
theorem seen_of_run (l piece : Nat) (name : String)
    (run : Nat → S → Except String (List Claim × S))
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run) (n : Nat)
    (e e₁ : S) (c : List Claim) (hr : run n e = .ok (c, e₁)) : ∃ z, seenOf e = some z := by
  obtain ⟨g, b, x, fs, h1, _, _⟩ := k6_run_spec asClaim (seatAt h iU3) l piece p name run n e e₁ c
    hrun hr
  unfold seenOf
  cases hh : e.here with
  | head o => exact ⟨_, rfl⟩
  | _ =>
    exfalso
    unfold lettersAt at h1
    have hH : (seatAt h iU3).heard e = none := by
      show (match e.here with
        | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
          allOf o.F x (some (keptOf q x.wpl.sL))
        | _ => none) = none
      rw [hh]
    cases hg : given p (seatAt h iU3) e with
    | error m => rw [hg] at h1; cases h1
    | ok g' =>
      rw [hg, hH] at h1
      cases h1

/-- **THE RUN's SHAPE.** -/
theorem still_core (l piece : Nat) (name : String)
    (run : Nat → S → Except String (List Claim × S))
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run)
    {z : Seen} {U F : Fork} {e : S} (hz : seenOf e = some z) (hF : e.fork? = some F)
    (hL : Later U F) (hK : F.trees.map (·.K) = U.trees.map (·.K)) (hR : K6Ready h iU3 p z U)
    (n : Nat) (c : List Claim) (e₁ : S) (hr : run n e = .ok (c, e₁)) :
    e₁ = e ∧ ∃ fs, formsOf h iU3 p name z U = some fs ∧ c = fs.map asClaim := by
  obtain ⟨g, b, x, fs, h1, h2, h3⟩ := k6_run_spec asClaim (seatAt h iU3) l piece p name run n e e₁ c
    hrun hr
  have hv := letters_back h iU3 p hR (sees_of_seen hz hF) hL hK h1
  refine ⟨k6_same h iU3 l piece p (name, run) (lookup_mem _ _ _ hrun) n e (c, e₁) hr, fs, ?_, h3⟩
  unfold formsOf
  rw [hv]
  exact h2

/-- **EVERY SLOT THAT A FORM NAMES IS FILLED IN THE SNAPSHOT.** -/
theorem still_filled (name : String) {z : Seen} {U : Fork} (hR : K6Ready h iU3 p z U)
    (fs : List Form) (hf : formsOf h iU3 p name z U = some fs) :
    ∀ f ∈ fs, ∀ x ∈ f.slots.toList, OnBytes.PscRun.Filled U x.1 := by
  unfold formsOf at hf
  obtain ⟨v, hv, hf⟩ := Option.bind_eq_some_iff.mp hf
  obtain ⟨F0, G, rs, hW, hh, hL⟩ := ready_at_letters h iU3 p hR hv
  obtain ⟨s0, _, e0⟩ := lettersOf_some h iU3 p hv
  -- the reads' entries name no slot
  have hb : (∀ r i, (v.2.2.final.entry r i).slots = #[]) ∧
      ∀ r i, (v.2.2.head.entry r i).slots = #[] := by
    unfold lettersAt at e0
    cases hg : given p (seatAt h iU3) s0 with
    | error m => rw [hg] at e0; cases e0
    | ok g =>
      rw [hg] at e0
      cases hH : (seatAt h iU3).heard s0 with
      | none => rw [hH] at e0; cases e0
      | some H =>
        rw [hH] at e0
        cases hx : (seatAt h iU3).reads s0 with
        | none => rw [hx] at e0; cases e0
        | some x =>
          rw [hx] at e0
          have e1 := Except.ok.inj e0
          subst e1
          exact reads_bare h iU3 hx
  intro f hfm x hx
  letI := v.1
  letI := v.2.2
  exact (forms_filled hW hh hb.1 hb.2 hL name fs hf f hfm x hx).2.1

end At

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.letters_at
#print axioms VerifiableInference.Desc.Kinds.Head.Law.reads_bare
#print axioms VerifiableInference.Desc.Kinds.Head.Law.still_core
#print axioms VerifiableInference.Desc.Kinds.Head.Law.still_filled
