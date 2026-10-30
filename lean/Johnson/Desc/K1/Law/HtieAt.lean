-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/HtieAt.lean: THE BINDER htie OF new_of_onQ
(Johnson/Desc/K1/Law/NewAtSending.lean) (the proof of k01_fifty calls it so: Johnson/Desc/K1/Law/K01Law.lean), AT THE NAMED READER OF
OUT-OF-DOMAIN (OOD) SAMPLES (our files call an OOD sample the record) smp := smpNamed cs seats
(Johnson/Desc/Sound/SmpNamed.lean): behind a yes of a sending's piece, inside the promise in front,
the reader is tied (SmpTie, Johnson/Desc/K1/Law/SealedNoColl.lean) to the statement's sample rows at
every member that sits at one of the place's new seats. GENERAL IN THE SENDING: the place P, the
radii, the base, the two rounds' data, the price, the block.

  onQ_msgs   the promise in front of block k, unmarked: the statement has the plan's number of
             messages.
  htie_at    **the binder.**
HOW. smpTie_named_at (Johnson/Desc/K1/Law/SmpTieNamed.lean). Its number: the yes books the place's
messages behind those in front (Booked.msgs, off piece_step and step_ok); in front there are
N.msgsAt ps[k]? (onQ_msgs); the member's seat stands in seats at that number and j, and seats has no
seat twice, so the seat's place in the list is that number. Its tie: the member has the message's
shape (MemsAt.entry); cond_tie (Johnson/Desc/K1/Law/Port6.lean).
PREMISES THAT STAY, BY NAME.
  hmems   MemsAt cs ms P rad base (a field of PlanAt).
  hsam    a member sits at the seat of a message of the place only if that message has an OOD sample
          (where every message of the place has one: nothing is asked).
  hC      K1's condition at the place, at any radii.
  hnd     ON THE PLAN: seats has no seat twice.
  hpl     ON THE PLAN: the place's seats stand in seats from N.msgsAt ps[k]? on.
  hB2 · hBk · hu   on the block's text, as in new_of_onQ.
What is not claimed. hnd, hpl at a plan. That a piece says yes. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.NewAtSending
import Johnson.Desc.K1.Law.SmpTieNamed
import Johnson.Desc.K1.Law.Port6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.Sound (Frame Mem SitsAt MsgT smpNamed numAt)

variable {Pp Cl Cells Tok : Type} {F : Frame}

/-- The promise in front of block k, unmarked: the statement has the plan's number of messages. -/
theorem onQ_msgs {W : Type} (N : First.Numbers) (Mg : Meaning Pp W) (links : List First.ModelPart)
    (ps : List Place) (k : ℕ) (z : Pp) (a : S × F.E.Str)
    (ha : Sound.onQ N Mg links ps (fun s : S => (z, s)) k a) (hm : a.1.failed = none) :
    a.1.st.oracles.size = N.msgsAt ps[k]? := by
  unfold Sound.onQ First.onAt at ha
  obtain ⟨_, hr⟩ := ha
  rcases hr with hx | ⟨h1, _, _, _⟩
  · exact absurd hm hx
  · simp only [Bool.and_eq_true] at h1
    obtain ⟨_, c6⟩ := h1
    unfold First.bookAt at c6
    simp only [Bool.and_eq_true, beq_iff_eq] at c6
    exact c6.2

/-- **htie at the named reader.** -/
theorem htie_at (cs : Codes) (seats : List (ℕ × ℕ)) (ms : List Mem) (N : First.Numbers)
    (Mg : Meaning Pp (Wit Cells Tok MsgT)) (links : List First.ModelPart) (ps : List Place) (k : ℕ)
    (P : Par) (rad rad₀ : ℕ → ℕ) (base : ℕ) (d₁ d₂ : RDT) (hmems : MemsAt cs ms P rad base)
    (hsam : ∀ j : Fin (shapesOf P).length, ∀ m' ∈ ms,
      SitsAt m' (seatOfMsg P base j.val).1 (seatOfMsg P base j.val).2 → sampledAt P j)
    (hC : condPort P rad₀ = true) (hnd : seats.Nodup)
    (hpl : ∀ j : Fin (shapesOf P).length,
      seats[N.msgsAt ps[k]? + j.val]? = some (seatOfMsg P base j.val))
    (B : Block S Unit) (hB2 : B.rounds.length = 2)
    (hBk : ∀ s s' r₁ r₂ gs, B.decide s [r₁, r₂] gs = .ok s' →
      Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size)
    (c : Block S Cl) (hu : c.UnderR (B.retype : Block S Cl)) (e : ℕ) (z : Pp) :
    ∀ a τ x, Sound.onQ N Mg links ps (fun s : S => (z, s)) k a → a.1.failed = none →
      (sendPiece (W := Wit Cells Tok MsgT) (F := F) c base d₁ d₂ P.coordinates e).ior.red.out a τ =
        some x →
      ∀ j : Fin (shapesOf P).length, ∀ m' ∈ ms,
        SitsAt m' (seatOfMsg P base j.val).1 (seatOfMsg P base j.val).2 →
        SmpTie cs (smpNamed cs seats) (z, x.1) m' x.1.st
          (x.1.st.oracles.size - (shapesOf P).length + j.val) := by
  intro a τ x ha hm hx j m' hm' hs
  obtain ⟨rs, cols, n, hst⟩ := K13.Law.piece_step _ hx
  obtain ⟨hfit, gs, hd⟩ := step_ok F.ft c _ _ rs cols n hst
  have hlen : (rs.map noDigest).length = 2 := by
    rw [List.length_map, Keeps.fit_length _ _ hfit, hu.1]
    exact hB2
  obtain ⟨r₁, r₂, er⟩ := List.length_eq_two.1 hlen
  rw [er] at hd
  have hB := (hBk _ _ _ _ _ (hu.2 _ _ _ _ hd)).msgs
  have hmsg := onQ_msgs N Mg links ps k z a ha hm
  have hL : (shapesOf P).length = P.sent.size := by simp [shapesOf]
  have hj := hsam j m' hm' hs
  have hent := hmems.entry j hj m' hm' hs
  have hT : Tie cs (m'.1.l.get m'.2).1 := by
    rw [hent, hmems.codes]
    exact cond_tie P rad₀ hC j hj
  have hseat : m'.1.seat m'.2 = seatOfMsg P base j.val := hs
  obtain ⟨hi, eg⟩ := List.getElem?_eq_some_iff.1 (hpl j)
  refine smpTie_named_at cs seats (z, x.1) m' x.1.st _ ?_ hT rfl ?_
  · rw [hseat, ← eg]
    exact List.getElem_mem hi
  · show seats.idxOf (m'.1.seat m'.2) = _
    rw [hseat, ← eg, hnd.idxOf_getElem _ hi]
    omega

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.onQ_msgs
#print axioms VerifiableInference.Desc.K1.htie_at
