-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/FirstFresh.lean: kind K1: BEHIND THE FIRST SEGMENT's OPENING THE MESSAGE THAT
THE FRAME's TEST ON THE INDEX MASKS FINDS BEARS THE FRESH LEDGER OF MASK ENTRIES. Statements and
proofs.
  `firstOwn_codes`, `firstAtS_codes`: an accepting decision of the opening leaves the statement with
    the sub-protocol's own codes: the sending tests them.
  `firstAtS_fresh`: the decision accepts from s to m; the shape in front has a message "at the
    start"; `IndexMasksAt room m.check m.st.oracles im`; the sending's last message's shape sh has a
    mask row and an answer: THEN im is the sending's last message, and its ledger is there, is not
    closed, and has just `Send.freeMaskEntries sh.maskRows (q.codes.mask.getD sh.maskCode
    default).ell sh.answers` entries left. General in the state in front.
Called: `firstAtS_im` (FirstIndexMasks.lean); `laysFresh_firstAtS`, `sameLedgers_newGroup`,
`sameLedgers_joinOwn` (LedgerMade.lean); `decideSend_iff` (Writes3.lean).
Nothing on soundness.

-/
import Johnson.Desc.K1.Law.FirstIndexMasks
import Johnson.Desc.K1.Law.LedgerMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Props (IndexMasksAt)

variable {Cl : Type}

/-- The codes behind the opening's decision are the sub-protocol's own. -/
theorem firstOwn_codes (P : Par) (owed : Option Nat) (c c' : ChainCheck) (d d' : DState Unit)
    (r₁ r₂ : Fmt.RoundView) (h : firstOwn P owed c d [r₁, r₂] = .ok (c', d')) :
    d'.st.codes = P.codes := by
  unfold firstOwn at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨g, d₁⟩, h1, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨ids, d₂⟩, h2, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨mask, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨f₂, d₃⟩, h3, hfin⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, rfl⟩ := Prod.mk.inj (Except.ok.inj hfin)
  obtain ⟨⟨_, hc, _, _, _⟩, _, rfl⟩ := (decideSend_iff P owed d₁ d₂ r₁ r₂ ids).1 h2
  have hcodes : (behind P d₁ (seedsOf P r₁) (answersIn r₂)).st.codes = P.codes := hc
  rw [(sameLedgers_joinOwn _ _ _ _ _ _ ((named_ok _ _ _).1 h3)).codes]
  exact hcodes

theorem firstAtS_codes (q : Params.First) (gp : GPar) (s m : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s [r₁, r₂] gs = .ok m) : m.st.codes = q.codes := by
  obtain ⟨c, d', h1, e, _⟩ := firstAtS_ok q gp s m _ gs h
  rw [e]
  exact firstOwn_codes _ _ _ _ _ d' r₁ r₂ h1

/-- **The found message bears the fresh ledger.** -/
theorem firstAtS_fresh (q : Params.First) (gp : GPar) (s m : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s [r₁, r₂] gs = .ok m)
    (hne : s.check.frame.shape.atStart ≠ []) (room im : Nat)
    (hi : IndexMasksAt room m.check m.st.oracles im)
    (hm : 0 < ((firstPar q gp).sent.getD ((firstPar q gp).sent.size - 1) default).shape.maskRows)
    (ha : 1 ≤ ((firstPar q gp).sent.getD ((firstPar q gp).sent.size - 1) default).shape.answers) :
    im = s.st.oracles.size + ((firstPar q gp).sent.size - 1) ∧
    ∃ l, (m.st.oracles[im]?).bind (·.ledger) = some l ∧ l.closed = false ∧
      l.left = Send.freeMaskEntries
        ((firstPar q gp).sent.getD ((firstPar q gp).sent.size - 1) default).shape.maskRows
        (q.codes.mask.getD
          ((firstPar q gp).sent.getD ((firstPar q gp).sent.size - 1) default).shape.maskCode
          default).ell
        ((firstPar q gp).sent.getD ((firstPar q gp).sent.size - 1) default).shape.answers := by
  obtain ⟨hpos, him⟩ := firstAtS_im q gp s m r₁ r₂ gs h hne room im hi
  obtain ⟨x, hx, _, hl⟩ := laysFresh_firstAtS q gp s m r₁ r₂ gs h
    ((firstPar q gp).sent.size - 1) (by omega) hm ha
  have hb : (m.st.oracles[im]?).bind (·.ledger) = x.ledger := by
    rw [him, hx]
    rfl
  rw [hl] at hb
  refine ⟨him, _, hb, rfl, ?_⟩
  show Send.freeMaskEntries _ (m.st.codes.mask.getD _ default).ell _ = _
  rw [firstAtS_codes q gp s m r₁ r₂ gs h]

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.firstAtS_codes
#print axioms VerifiableInference.Desc.K1.firstAtS_fresh
