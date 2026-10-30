-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortLetters.lean: THE FREE LETTERS OF WHAT IS LEFT OF A LINK's LAW
(LinkRestAtSort3.lean: β, ψ, rd, kap, Kx), CHOSEN ONCE FOR ALL THREE SORTS OF LINK, so that every
payer ends at one set of letters. Definitions, and theorems: what the sorts' lists ask of these
letters (hψ, hrd, hkap), and what the lookups' payers ask of φ.

The choice. φ := phiAll u psiAll (u stays a letter). phiAll's one free field carries THREE things
that were heard before the batching's draw:
  `psiAll s` := (psiAtt s, seenOf s, s.lookHeard?): what attention's runs read beside the ledger ·
    what the output head's runs see · what the lookup on the calls returned.
  `rdAll`, `kapAll`, `hdCalls`: the three read back off φ's free field. `hdDigits`: what the
    digits' lookup returned, read off φ's own field tl (the smallness test's record, its fourteen
    written fields blanked: "heard" is none of the fourteen).
  `kxAll lmC jC lmD jD` := K3's promise on the fixed part (K3Ok, Johnson/Top/H/Keep/RunsPlain.lean)
    AT THE LINK's TWO LOOKUP SEATS, EACH WITH ITS OWN READER AND ITS OWN TWO PUBLIC NUMBERS: the
    calls' (hdCalls, lmC, jC) and the digits' (hdDigits, lmD, jD).

What is said.
  `rests_look`: what the lookup on the calls returned rests under the writings behind the draw.
    `rests_all`: **hψ.**
  `hrd_all`: **hrd.** `hkap_all`: **hkap.** Both by definition.
  `hdCalls_all`, `hdDigits_all`: φ holds what was heard at the two seats (the lookups' payers'
    premise on φ). `phiAll_putFork_all`: φ is blind to the putting of a ledger (their other
    premise).
  `heard5_of_rdAll`: what rdAll reads as attention's own hearing is the state's: the premise hrd of
    okAtt_k5_at (OkK5Paid.lean).
  `kxAll_calls`, `kxAll_digits`: the two clauses read back.

THE FOUR NUMBERS ARE NOT CHOSEN HERE. By a reading of the lookup argument's files (no theorem): jC,
jD must be the ledger's next slot in front of that lookup (the place's own "first") and lmC, lmD the
place's own lm (5 at the digits): AT ANY OTHER NUMBERS THE PROMISE's THIRD CLAUSE IS, AS FAR AS
THAT READING SEES, FALSE AT AN HONEST STATE. OF lmD THAT READING IS OVERTAKEN: `kxDigits_front`,
`kxDigits_head` (KxAtFront.lean) have the digits' clause at EVERY lm, at every state reached in
front of a batching whose ledger is open and has its sizes (in scope, at an opening, under hp).

Limits. DEFINITIONS AND LIGHT FACTS. NOTHING IS SHOWN OF ANY REACHED STATE. WHETHER kxAll ASKS TOO
MUCH OF AN HONEST STATE HAS NOT BEEN EVALUATED. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.PayAttention
import Johnson.Desc.First.Link.Law.PayHead
import Johnson.Top.H.Keep.RunsPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.PhiAll
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Wrote)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L (Pub9)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.Kinds.Head.Law (Seen seenOf rests_seen)
open VerifiableInference.OnPublicFiles (K3Ok)

/-- What the lookup on the calls returned. -/
def psiLook (s : S) : Option Forest.Heard := s.lookHeard?

/-- **It rests under the writings behind the draw.** -/
theorem rests_look (u : HTailF2) : Rests u psiLook where
  fork := fun s F => by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here with
    | head x => by_cases ho : x.opened = true <;> simp [psiLook, S.lookHeard?, S.putFork, ho]
    | _ => rfl
  set := fun s a => by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here with
    | head x =>
      by_cases ho : x.opened = true <;>
        simp [psiLook, S.lookHeard?, atS, S.putLink, S.putFork, ho]
    | _ => rfl
  tl := fun s _ tl' _ _ => by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here with
    | head x => by_cases ho : x.opened = true <;> simp [psiLook, S.lookHeard?, S.putTl, ho]
    | _ => rfl
  wrote := fun s a G s' h => by
    obtain ⟨h1, rfl⟩ := h
    simp [psiLook, S.lookHeard?, h1]
  head := fun s a G h => by
    simp [psiLook, S.lookHeard?, h]

/-- The type of φ's free field. -/
abbrev BetaAll : Type :=
  Option (Forest.Heard × First.Att.P.Heard) × Option Seen × Option Forest.Heard

/-- **THE FREE FIELD, FOR ALL THREE SORTS.** -/
def psiAll (s : S) : BetaAll := (psiAtt s, seenOf s, psiLook s)

/-- **hψ.** -/
theorem rests_all (u : HTailF2) : Rests u psiAll :=
  rests_pair u (rests_att u) (rests_pair u (rests_seen u) (rests_look u))

/-- Attention's reader. -/
def rdAll (x : Phi BetaAll) : Option (Forest.Heard × First.Att.P.Heard) := x.more.1

/-- The output head's reader. -/
def kapAll (x : Phi BetaAll) : Option Seen := x.more.2.1

/-- The reader of what the lookup on the calls returned. -/
def hdCalls (x : Phi BetaAll) : Option Forest.Heard := x.more.2.2

/-- The reader of what the digits' lookup returned. -/
def hdDigits (x : Phi BetaAll) : Option Forest.Heard := x.tl.bind (·.heard)

/-- **hrd.** -/
theorem hrd_all (u : HTailF2) : ∀ e, rdAll (phiAll u psiAll e) = psiAtt e := fun _ => rfl

/-- **hkap.** -/
theorem hkap_all (u : HTailF2) : ∀ e, kapAll (phiAll u psiAll e) = seenOf e := fun _ => rfl

/-- φ holds what was heard at the calls' seat. -/
theorem hdCalls_all (u : HTailF2) : ∀ e, hdCalls (phiAll u psiAll e) = e.lookHeard? :=
  fun _ => rfl

/-- φ holds what was heard at the digits' seat. -/
theorem hdDigits_all (u : HTailF2) :
    ∀ e, hdDigits (phiAll u psiAll e) = e.tl?.bind (·.heard) := fun e => by
  show (e.tl?.map (blank u)).bind (·.heard) = e.tl?.bind (·.heard)
  cases e.tl? <;> rfl

/-- φ is blind to the putting of a ledger. -/
theorem phiAll_putFork_all (u : HTailF2) (s : S) (G : Fork) :
    phiAll u psiAll (s.putFork G) = phiAll u psiAll s := phi_putFork u psiAll (rests_all u) s G

/-- What rdAll reads as attention's own hearing is the state's. -/
theorem heard5_of_rdAll (u : HTailF2) (s : S) :
    ∀ g h, rdAll (phiAll u psiAll s) = some (g, h) → s.heard5? = some h := by
  intro g h e
  rw [hrd_all] at e
  unfold psiAtt at e
  unfold S.heard5?
  cases hh : s.here with
  | att a =>
    rw [hh] at e
    obtain ⟨g', -, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨h', e1, e2⟩ := Option.map_eq_some_iff.1 e
    show a.heard5 = some h
    rw [e1, (Prod.mk.inj e2).2]
  | _ => rw [hh] at e; cases e

/-- **Kx**: K3's promise on the fixed part at the link's two lookup seats. -/
def kxAll (lmC jC lmD jD : ℕ) (q : Phi BetaAll × Option Pub9) : Prop :=
  K3Ok hdCalls lmC jC q ∧ K3Ok hdDigits lmD jD q

theorem kxAll_calls {lmC jC lmD jD : ℕ} {q : Phi BetaAll × Option Pub9}
    (h : kxAll lmC jC lmD jD q) : K3Ok hdCalls lmC jC q := h.1

theorem kxAll_digits {lmC jC lmD jD : ℕ} {q : Phi BetaAll × Option Pub9}
    (h : kxAll lmC jC lmD jD q) : K3Ok hdDigits lmD jD q := h.2

end VerifiableInference.Desc.PhiAll

#print axioms VerifiableInference.Desc.PhiAll.rests_look
#print axioms VerifiableInference.Desc.PhiAll.rests_all
#print axioms VerifiableInference.Desc.PhiAll.hrd_all
#print axioms VerifiableInference.Desc.PhiAll.hkap_all
#print axioms VerifiableInference.Desc.PhiAll.hdCalls_all
#print axioms VerifiableInference.Desc.PhiAll.hdDigits_all
#print axioms VerifiableInference.Desc.PhiAll.phiAll_putFork_all
#print axioms VerifiableInference.Desc.PhiAll.heard5_of_rdAll
#print axioms VerifiableInference.Desc.PhiAll.kxAll_calls
#print axioms VerifiableInference.Desc.PhiAll.kxAll_digits
