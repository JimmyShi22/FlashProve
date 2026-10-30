-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/ReplyLeft.lean: KIND K1's SUB-PROTOCOLS LEAVE THE REPLY
THAT THE VERIFIER's STATE HAS HEARD (`out.reply`): the one fact on a step that the letter
`headPart` of the composed filling's constraints' sentence wants (`head_atAll`).
Statements with their proofs. `commitAtS_out`: a later sending
  leaves the whole field "out" (it lays the statement, the book and the roots back and puts the
  link's copy and the ledger). `out_blkL`, `reply_later`: so at each of the fifty later places, at
  the lot's own sub-protocol (at the reads: the sending, then a quiet step, whose own law leaves
  "out"). `reply_G`: the first segment's opening turns of "out" the index masks' number alone.
Nothing on soundness.

-/
import Johnson.Desc.K1.Law.LaterOne
import Johnson.Desc.K1.Law.KeepAtLater
import Johnson.Desc.K1.Law.PubAtLaterKeeper
import Johnson.Desc.K1.Law.PubAtLaterIndex
import Johnson.Desc.K13.Law.AtTableFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Maker
open Johnson.Desc.First.Walk (LayPar)
open VerifiableInference.Desc.First (S Numbers)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix k1Reads)
open VerifiableInference.Desc.K13.Law (StepG)

/-- **A later sending leaves "out".** -/
theorem commitAtS_out {Cl : Type} (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    s'.out = s.out := by
  obtain ⟨L, L', F', w, _, _, rfl⟩ := commitAtS_rec P link moment arrays s s' rs gs h
  cases hs : s.here with
  | head a => cases ho : a.opened <;> simp [S.putFork, S.putLink, laid, hs, ho]
  | _ => simp [S.putFork, S.putLink, laid, hs]

theorem out_blkL (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h2 : rs.length = 2)
    (h : (blkL Z G l d X arrs).decide s rs gs = .ok s') : s'.out = s.out := by
  cases d with
  | true => exact commitAtS_out _ _ _ _ s s' rs gs h
  | false =>
    obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
    obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ := joined_yes _ _ _ _ _ _ s s' r₁ r₂ gs h
    exact ((quietP_orLoud _ _ _ G l X _) _ _ _ _ h3).2.2.1.trans
      (commitAtS_out _ _ _ _ s s₁ _ gs₁ h1)

/-- **The fifty later places leave the heard reply.** -/
theorem reply_later {Pp : Type} (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) (x x' : Pp × S) (hy : YesOf (blkL Z G l d X arrs) x x') :
    x'.2.out.reply = x.2.out.reply := by
  obtain ⟨_, rs, gs, hfit, hd⟩ := hy
  have h2 : (rs.map noDigest).length = 2 := by
    rw [List.length_map, K13.Law.roundsFit_length _ _ hfit]
    cases d with
    | true => rfl
    | false => exact rounds_k1Reads _ _ _ _ _ _
  rw [out_blkL Z G l d X arrs _ _ _ _ h2 hd]

/-- **The first segment's opening leaves the heard reply.** -/
theorem reply_G {Pp Cl : Type} {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
    {fvs : List Bool} {kCol : ℕ} (x x' : Pp × S) (h : StepG Cl q gp nm X fvs kCol x x') :
    x'.2.out.reply = x.2.out.reply := by
  obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
  rw [(openingZero_rec hd).2.2.2.2.2.1]

end VerifiableInference.Desc.K1
