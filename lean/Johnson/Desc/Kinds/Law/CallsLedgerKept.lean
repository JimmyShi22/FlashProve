-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/CallsLedgerKept.lean.
WHAT IT DOES NOT SHOW. No soundness. It speaks of the value B of K3.theStated at the address of a
link's lookup on the calls; that the IOP as written in Lean holds it at a place is not shown here.
stated_via AND stated_via3 CONCLUDE AN ACCEPTANCE, UNDER NO PREMISE ON THE PLAN. IN stated_free,
hOk, THAT B PASSES ITS TEST ON THE PLAN, IS A PREMISE: without it the lookup's law on the
exchanged hearing says nothing.
WORDS. "The verifier's state": the value of type S that the sub-protocols hand on. "The ledger": the
open link's Fork, as S.fork? reads it. FreeAt (Desc/First/Look/K3KeepsFree.lean): a ledger is there,
its three lists have one entry for each of its numbers, and no number from its next free one on is
filled.
LETTERS. No "there is" but FreeAt's own. a: the address; i: its link's number.
OBJECT. Desc/First/Look/K3Stated.lean: theStated, at its decision.
USER. The walk back from the output head's own place along the chain's fold
(P4R/Back341N.lean), and the fact "in the open output head's link the ledger is well laid": kept at
the head's third place.
WHAT IT IS. WHERE THE LOT's OWN TERM FOR A LINK's LOOKUP ON THE CALLS ACCEPTS, THE LOOKUP's
OWN SUB-PROTOCOL ACCEPTS BETWEEN THE SAME TWO STATES; SO FreeAt IS HANDED ON.
  stated_via        where B accepts, blockVia at the calls' seat accepts between the
                    same two states, and passes its plan test where B does: by the
                    equations of texts (K3OwnIs.lean: theStated_is, theWhole_is, theOwn_is) and
                    quiet_calls_same (the step joined behind hands the state back).
  stated_via3       the same from "the address's piece is 3".
  stated_free       so FreeAt is handed on: via_freeAt (K3KeepsFree.lean).
NEAREST RELATIVES: k3_calls_stated_yes (K3CallsStatedYes.lean): the like join AT A
PIECE, not at the decision; k3_head_free_at (K3KeepsFree.lean): FreeAt inside a law at a piece.

-/
import Johnson.Desc.First.Look.K3CallsStated
import Johnson.Desc.First.Look.K3KeepsFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

/-- **Where the lot's term for a link's lookup on the calls accepts, the lookup's own
sub-protocol with the hearing exchanged accepts between the same two states**, at the address's own
arguments; and it passes its test on the plan where the lot's term does. -/
theorem stated_via {Cl : Type} {X : Verify.Public} (claim : Aff → Cl)
    (readers : Nat → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B)
    {i : Nat} (hl : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i false)
    (s t : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : B.decide s rs gs = .ok t) :
    ∃ (P : Desc.First.Look.P) (sent : List (Nat × Nat)) (laid : Array Nat) (rs' : List Fmt.RoundView)
      (gs' : List (List (Nat × List UInt64))),
      (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent P []).decide s rs' gs' =
        .ok t ∧
      (B.planOk = true →
        (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent P []).planOk = true) := by
  obtain ⟨B₁, hB₁, -, e2, -, e4⟩ := Desc.K3.theStated_is claim readers X codes shape a B h
  obtain ⟨b, hb, hW⟩ := Desc.K3.theWhole_is claim true X codes shape a B₁ hB₁
  obtain ⟨j, digits, P, sent, laid, hj, hpj, -, -, -, -, r2, -, r4⟩ :=
    Desc.K3.theOwn_is claim true X codes shape a b hb
  obtain rfl : i = j := Option.some.inj (hl.symm.trans hj)
  cases digits with
  | true => exact absurd (hpj.symm.trans hpc) (pieceAt_ne X i)
  | false =>
    rw [e2] at hd
    rcases hW with ⟨-, rfl⟩ | ⟨f, hf, rfl⟩
    · rw [r2] at hd
      exact ⟨P, sent, laid, rs, gs, hd, fun hOk => r4 (e4.symm.trans hOk)⟩
    · have hd' : ((b.decide s (rs.take b.rounds.length) (gs.take b.openings)).bind fun m =>
          f m) = .ok t := hd
      cases hm : b.decide s (rs.take b.rounds.length) (gs.take b.openings) with
      | error e => rw [hm] at hd'; cases hd'
      | ok m =>
        rw [hm] at hd'
        obtain rfl := quiet_calls_same X a i hl hpc f hf m t hd'
        rw [r2] at hm
        refine ⟨P, sent, laid, _, _, hm, fun hOk => r4 ?_⟩
        have hpl : (b.planOk && true) = true := e4.symm.trans hOk
        simpa using hpl

/-- The same at an address whose piece is 3: the third place of a head's link: that it is the
lookup on the calls', and the link a head's, follows from the address. -/
theorem stated_via3 {Cl : Type} {X : Verify.Public} (claim : Aff → Cl)
    (readers : Nat → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B)
    {i : Nat} (hl : a.link = some i) (h3 : a.piece = 3)
    (s t : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : B.decide s rs gs = .ok t) :
    ∃ (P : Desc.First.Look.P) (sent : List (Nat × Nat)) (laid : Array Nat) (rs' : List Fmt.RoundView)
      (gs' : List (List (Nat × List UInt64))),
      (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent P []).decide s rs' gs' =
        .ok t ∧
      (B.planOk = true →
        (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent P []).planOk = true) := by
  have hpc : a.piece = Desc.K3.pieceAt X i false := by
    obtain ⟨B₁, hB₁, -⟩ := Desc.K3.theStated_is claim readers X codes shape a B h
    obtain ⟨b, hb, -⟩ := Desc.K3.theWhole_is claim true X codes shape a B₁ hB₁
    obtain ⟨j, digits, _, _, _, hj, hpj, -⟩ := Desc.K3.theOwn_is claim true X codes shape a b hb
    obtain rfl : i = j := Option.some.inj (hl.symm.trans hj)
    rw [h3] at hpj ⊢
    unfold Desc.K3.pieceAt at hpj ⊢
    cases hH : Desc.K3.isHead X i <;> cases digits <;> simp [hH] at hpj ⊢
  exact stated_via claim readers codes shape a B h hl hpc s t rs gs hd

/-- **FreeAt is handed on where the lot's term for the lookup on the calls accepts.** -/
theorem stated_free {Cl : Type} {X : Verify.Public} (claim : Aff → Cl)
    (readers : Nat → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    {i : Nat} (hl : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i false)
    (s t : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : B.decide s rs gs = .ok t) (hI : FreeAt (Desc.K3.seatCalls claim).fork s) :
    FreeAt (Desc.K3.seatCalls claim).fork t := by
  obtain ⟨P, sent, laid, rs', gs', hv, hp⟩ :=
    stated_via claim readers codes shape a B h hl hpc s t rs gs hd
  exact via_freeAt claim a.piece laid sent P [] (hp hOk) s rs' gs' t hv hI

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.stated_via
#print axioms VerifiableInference.OnPublicFiles.stated_via3
#print axioms VerifiableInference.OnPublicFiles.stated_free
