-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6YesAtMember.lean.
WHAT IT IS NOT. Every statement is CONDITIONAL. THAT THE HEAD's HEARING RETURNS ON ANY ROUNDS (hh)
IS A PREMISE, as are the facts on the state in front and the member's form. No prover's text is
read: that rounds which an honest side plays meet the premises is shown nowhere here. Nothing on
soundness, on completeness or on hiding.
WHAT IT IS. Law/K6Returns.lean's laws on the output head's bare sub-protocol (K6), carried by
Law/K6WayUp.lean to THE MEMBER AS THE IOP AS WRITTEN IN LEAN SEATS IT (K6MemberIs), at Block.step.
  member_yes         (i) CONDITIONAL: the member's form; the step's own tests on rounds and columns
                     (Block.Fits, Top/H0/StepLaws/StepLaws.lean); no mark; the opened head's link;
                     the state's own test on the request; the letters are read; the hearing returns
                     on the rounds without the sealed digest: THE MEMBER's STEP ACCEPTS AND TAKES NO
                     COLUMN; so does its decision at what the step shows it; the ledger behind is
                     the hearing's own return. The rounds' shape is no premise: the step's test on
                     the rounds pays it (shapedNZ_of_blockFit, Law/K06FitsShape.lean).
  member_ledger      CONDITIONAL: behind ANY accept of the member's step the ledger is the hearing's
                     own return, and no column was taken.
  member_reads_back  (iii) CONDITIONAL: a well laid ledger and "every word is below the prime"
                     besides: behind any accept of the member's step the seat reads back what was
                     heard, the same letters, the same points of the lookup.
  member_yes', member_ledger', member_reads_back'   THE SAME THREE WITH THE PREMISES ON THE ADDRESS
                     AND THE GUARD THAT THEY DO NOT NEED STRUCK: the first without hk (the address
                     is not K7's); the two others without hk and without hsm (the guard accepts
                     where the reply is as it was). All else as in the elder three.
  ((ii), what the hearing takes of the ledger, names no sub-protocol: Law/K6Returns.lean's
  k6_takes.)
WHY "WITHOUT THE SEALED DIGEST". Block.step shows the decision its rounds so (Desc/Block.lean).
WHO IS MEANT TO PAY. The member's form: Law/K6WayUpAtSeat.lean. hF: whoever shows what is played.
The test on the request: the same file's startOk_reached. No mark, the opened link, the letters:
what is known of the state in front of the member. hh: a law on the hearing, which is not here.
CALLED: K6MemberIs.rounds, .decide_iff, .decide_iff', .decide_down, .want (Law/K6WayUp.lean);
k6_decides, k6_ledger, k6_reads_back (Law/K6Returns.lean); shapedNZ_of_blockFit
(Law/K06FitsShape.lean); of the library: step_iff (Top/H0/StepLaws/StepLaws.lean).

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K6WayUp
import Johnson.Desc.Kinds.Law.K6Returns
import Johnson.Desc.Kinds.Law.K06FitsShape

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (Block OpenedColumn Place KindName Claim noDigest)
open VerifiableInference.Desc.First (S)
open OnBytes.Model (Fork)


variable {W : OnBytes.Model.Verify.Public} {l : Nat} {same : S → S → Bool} {a : Place}
  {b : Block S Claim}

/-- (i) **THE MEMBER's OWN STEP ACCEPTS.** CONDITIONAL. No premise TESTS a value that is sent; of
what is sampled, hF alone does (the step's own test on the rounds); hh speaks of the rounds whole:
it is a routine's return. The second clause of the end says the same of the decision alone, at what
the step shows it: the rounds without the sealed digest and the groups of columns (Block.shown): for
a reader whose law speaks of Block.decide. -/
theorem member_yes (M : K6MemberIs W l same a b) (hk : a.kind ≠ KindName.K7)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true) (ft : Nat) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (H : HeardAll) (G : Fork) (hF : b.Fits ft rs cols)
    (hfail : s.failed = none) (hopen : HeadOpen s) (hstart : startOk W s = true) (g : Given)
    (hg : given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g)
    (hh : hear ((seatAt W.hS (readsOf W)).ledger s) (rs.map noDigest) = some (H, G, [])) :
    ∃ s' : S, b.step ft s rs cols = .ok (s', 0) ∧
      b.decide s (rs.map noDigest) (b.shown ft rs cols) = .ok s' ∧
      (seatAt W.hS (readsOf W)).ledger s' = G := by
  have hsh : ShapedNZ (rs.map noDigest) (@rounds (parOf W.hS (workOf W)).sizes) :=
    shapedNZ_of_blockFit W.hS (readsOf W) (workOf W) l rs (by rw [← M.rounds]; exact hF.1)
  obtain ⟨s', hd, hL⟩ := k6_decides W.hS (readsOf W) (workOf W) l s (rs.map noDigest)
    (b.shown ft rs cols) H G hfail hopen g hg hsh hh
  have hb := (M.decide_iff hk hsm s s' _ _).2 ⟨hd, hstart⟩
  exact ⟨s', (VerifiableInference.Desc.step_iff ft b s s' rs cols 0).2
    ⟨hF, hb, by rw [M.want]; rfl⟩, hb, hL⟩

/-- `member_yes` without hk: at every address. CONDITIONAL, as that. -/
theorem member_yes' (M : K6MemberIs W l same a b)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true) (ft : Nat) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (H : HeardAll) (G : Fork) (hF : b.Fits ft rs cols)
    (hfail : s.failed = none) (hopen : HeadOpen s) (hstart : startOk W s = true) (g : Given)
    (hg : given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g)
    (hh : hear ((seatAt W.hS (readsOf W)).ledger s) (rs.map noDigest) = some (H, G, [])) :
    ∃ s' : S, b.step ft s rs cols = .ok (s', 0) ∧
      b.decide s (rs.map noDigest) (b.shown ft rs cols) = .ok s' ∧
      (seatAt W.hS (readsOf W)).ledger s' = G := by
  have hsh : ShapedNZ (rs.map noDigest) (@rounds (parOf W.hS (workOf W)).sizes) :=
    shapedNZ_of_blockFit W.hS (readsOf W) (workOf W) l rs (by rw [← M.rounds]; exact hF.1)
  obtain ⟨s', hd, hL⟩ := k6_decides W.hS (readsOf W) (workOf W) l s (rs.map noDigest)
    (b.shown ft rs cols) H G hfail hopen g hg hsh hh
  have hb := (M.decide_iff' hsm s s' _ _).2 ⟨hd, hstart⟩
  exact ⟨s', (VerifiableInference.Desc.step_iff ft b s s' rs cols 0).2
    ⟨hF, hb, by rw [M.want]; rfl⟩, hb, hL⟩

/-- Behind ANY accept of the member's step the ledger is the hearing's own return; and the count of
columns. CONDITIONAL. -/
theorem member_ledger (M : K6MemberIs W l same a b) (hk : a.kind ≠ KindName.K7)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true) {ft : Nat} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat} {H : HeardAll} {G : Fork}
    (hs : b.step ft s rs cols = .ok (s', n)) (g : Given)
    (hg : given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g)
    (hh : hear ((seatAt W.hS (readsOf W)).ledger s) (rs.map noDigest) = some (H, G, [])) :
    (seatAt W.hS (readsOf W)).ledger s' = G ∧ n = 0 := by
  obtain ⟨_, hd, hn⟩ := (VerifiableInference.Desc.step_iff ft b s s' rs cols n).1 hs
  have hd' := ((M.decide_iff hk hsm s s' _ _).1 hd).1
  exact ⟨k6_ledger W.hS (readsOf W) (workOf W) l g hg hh hd', by rw [hn, M.want]; rfl⟩

/-- `member_ledger` without hk and hsm: from the member's form alone. CONDITIONAL, as that. -/
theorem member_ledger' (M : K6MemberIs W l same a b) {ft : Nat} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat} {H : HeardAll} {G : Fork}
    (hs : b.step ft s rs cols = .ok (s', n)) (g : Given)
    (hg : given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g)
    (hh : hear ((seatAt W.hS (readsOf W)).ledger s) (rs.map noDigest) = some (H, G, [])) :
    (seatAt W.hS (readsOf W)).ledger s' = G ∧ n = 0 := by
  obtain ⟨_, hd, hn⟩ := (VerifiableInference.Desc.step_iff ft b s s' rs cols n).1 hs
  have hd' := (M.decide_down hd).1
  exact ⟨k6_ledger W.hS (readsOf W) (workOf W) l g hg hh hd', by rw [hn, M.want]; rfl⟩

/-- (iii) What the seat reads back behind ANY accept of the member's step. CONDITIONAL. -/
theorem member_reads_back (M : K6MemberIs W l same a b) (hk : a.kind ≠ KindName.K7)
    (hsm : ∀ s t : S, t.out.reply = s.out.reply → same s t = true) {ft : Nat} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat} {H : HeardAll} {G : Fork}
    (hs : b.step ft s rs cols = .ok (s', n))
    (hWL : WellLaid ((seatAt W.hS (readsOf W)).ledger s)) (hcan : Canonical (rs.map noDigest))
    (g : Given) (hg : given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g)
    (hh : hear ((seatAt W.hS (readsOf W)).ledger s) (rs.map noDigest) = some (H, G, [])) :
    (seatAt W.hS (readsOf W)).heard s' = some H ∧
      given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s' =
        given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s ∧
      (seatAt W.hS (readsOf W)).lookup s' = (seatAt W.hS (readsOf W)).lookup s := by
  obtain ⟨_, hd, _⟩ := (VerifiableInference.Desc.step_iff ft b s s' rs cols n).1 hs
  have hd' := ((M.decide_iff hk hsm s s' _ _).1 hd).1
  exact k6_reads_back W.hS (readsOf W) (workOf W) l hWL hcan g hg hh hd'

/-- `member_reads_back` without hk and hsm: from the member's form alone. CONDITIONAL, as that. -/
theorem member_reads_back' (M : K6MemberIs W l same a b) {ft : Nat} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat} {H : HeardAll} {G : Fork}
    (hs : b.step ft s rs cols = .ok (s', n))
    (hWL : WellLaid ((seatAt W.hS (readsOf W)).ledger s)) (hcan : Canonical (rs.map noDigest))
    (g : Given) (hg : given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g)
    (hh : hear ((seatAt W.hS (readsOf W)).ledger s) (rs.map noDigest) = some (H, G, [])) :
    (seatAt W.hS (readsOf W)).heard s' = some H ∧
      given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s' =
        given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s ∧
      (seatAt W.hS (readsOf W)).lookup s' = (seatAt W.hS (readsOf W)).lookup s := by
  obtain ⟨_, hd, _⟩ := (VerifiableInference.Desc.step_iff ft b s s' rs cols n).1 hs
  have hd' := (M.decide_down hd).1
  exact k6_reads_back W.hS (readsOf W) (workOf W) l hWL hcan g hg hh hd'

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.member_yes
#print axioms VerifiableInference.Desc.Kinds.Head.Law.member_ledger
#print axioms VerifiableInference.Desc.Kinds.Head.Law.member_reads_back
#print axioms VerifiableInference.Desc.Kinds.Head.Law.member_yes'
#print axioms VerifiableInference.Desc.Kinds.Head.Law.member_ledger'
#print axioms VerifiableInference.Desc.Kinds.Head.Law.member_reads_back'
