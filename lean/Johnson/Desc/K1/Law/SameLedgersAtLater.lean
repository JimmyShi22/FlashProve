-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SameLedgersAtLater.lean: AT KIND K1's LATER SENDINGS EVERY MESSAGE THAT IS THERE
KEEPS ITS LEDGER WHOLE, "closed" too.

LedStay (Johnson/Desc/K13/Law/LedgersStay.lean) says that a ledger's four numbers stay; it does not
read whether the ledger is shut. A test that reads "is not closed" beside "so many are left" wants
more: SameLedgers (Johnson/Desc/K1/Law/LedgerMade.lean: the code table stays; every message that is
there stays with its shape and its ledger), which that file has at a new group and at the joinings.
Here it is carried over the sendings.

  sameLedgers_kept   where every older message is left whole (Kept, Johnson/Desc/K1/Law/Sound.lean).
  sendAtS_sameLedgers, commitAtS_sameLedgers   W's sending; a segment's later moment.
  later_sameLedgers   both sub-protocols of a segment's later places (Later,
                   Johnson/Desc/K1/Law/InOrderAtLater.lean), on any rounds.
  later_ledgerAtMasks   SO: the index masks' number stays, and the ledger of the message under that
                   number is the same, whole.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.LedgerMade
import Johnson.Desc.K1.Law.RowsFactAtLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (By)
open VerifiableInference.Desc.Keeps (Decides)
open OnBytes.Model.Stages (LinkH)
open IM (k1Reads k1Quiet)

variable {L Cl : Type}

theorem sameLedgers_kept {d d' : DState L} (h : Kept d d') : SameLedgers d.st d'.st := by
  refine ⟨h.1, fun i x hx => ⟨x, ?_, rfl, rfl⟩⟩
  rw [h.2.2 i (Array.getElem?_eq_some_iff.1 hx).1]
  exact hx

/-- **W's sending.** -/
theorem sendAtS_sameLedgers (P : Par) :
    Decides (By SameLedgers fun s : S => s.st) (sendAtS (Cl := Cl) P) := by
  intro s rs gs s' h
  obtain ⟨a, -, c⟩ := sendAtS_kept P s s' rs gs h
  refine ⟨a, fun i x hx => ⟨x, ?_, rfl, rfl⟩⟩
  rw [c i (Array.getElem?_eq_some_iff.1 hx).1]
  exact hx

/-- **A segment's later moment.** -/
theorem commitAtS_sameLedgers (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    Decides (By SameLedgers fun s : S => s.st) (commitAtS (Cl := Cl) P link moment arrays) := by
  intro s rs gs s' h
  unfold commitAtS at h
  dsimp only at h
  split at h
  · obtain ⟨y, hy, rfl⟩ := Keeps.emap_ok h
    obtain ⟨ids, d₁, f', h2, h3⟩ := commitOwn_ok P link moment arrays _ y _ gs hy
    show SameLedgers s.st (((laid s y.held.w).putLink y.held.L).putFork y.held.F).st
    rw [Rel.putFork_st, Rel.putLink_st]
    exact (sameLedgers_kept (decideSend_kept P _ _ d₁ rs ids h2)).trans
      (sameLedgers_joinOwn _ _ _ _ _ _ h3)
  · cases h

/-- **At both sub-protocols of a segment's later places**, on any rounds. -/
theorem later_sameLedgers {B own : Block S Unit} (hB : Later B own) :
    Decides (By SameLedgers fun s : S => s.st) B := by
  intro s rs gs s' h
  cases hB with
  | digits q gp l piece digits => exact commitAtS_sameLedgers _ l 2 digits s rs gs s' h
  | reads Z G l X pr reads =>
    have h' : ((laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).decide s
        (rs.take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length)
        (gs.take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).openings)).bind (fun s₁ =>
        (k1Quiet G l X).decide s₁
          (rs.drop (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length)
          (gs.drop (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).openings)) = .ok s' := h
    obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 h'
    show SameLedgers s.st s'.st
    rw [k1Quiet_st G l X _ _ _ _ h2]
    exact commitAtS_sameLedgers _ l 1 reads s _ _ s₁ h1

/-- **So the index masks' message's ledger is the same, whole, under the same number.** -/
theorem later_ledgerAtMasks {B own : Block S Unit} (hB : Later B own) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (h : B.decide s rs gs = .ok s')
    {l : Ledger} (hl : (s.st.oracles[s.out.indexMasks]?).bind (·.ledger) = some l) :
    s'.out.indexMasks = s.out.indexMasks ∧
      (s'.st.oracles[s'.out.indexMasks]?).bind (·.ledger) = some l := by
  have hi := (later_same hB s rs gs s' h).2.1
  obtain ⟨x, hx, hxl⟩ := Option.bind_eq_some_iff.1 hl
  obtain ⟨x', hx', -, e⟩ := (later_sameLedgers hB s rs gs s' h).msg _ x hx
  refine ⟨hi, ?_⟩
  rw [hi, hx']
  show x'.ledger = some l
  rw [e]
  exact hxl

end VerifiableInference.Desc.K1
