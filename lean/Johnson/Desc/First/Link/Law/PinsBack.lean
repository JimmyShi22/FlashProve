-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/PinsBack.lean: THE LINK LAW's CONTEXT, CHOSEN AS THE TABLE's OWN (what
the table's rows of the batching and of the frame's sub-protocol behind it read: the pins of the
segment's three moments, `pinsOf m`), AT A MEANING WHOSE PIN IS THE LIBRARY's OWN NOTION (`pinJT`,
Johnson/Desc/Sound/MeaningSig.lean: the composed meaning's is, by definition); AND ITS THREE RIDES
BACKWARD: the law's premises hcb, hcq and hce (LinkOwes.lean: `OwesLetters`): a witness that is
pinned behind a piece's accepting transcript is pinned in front. Definitions and theorems.

Why. A pin reads the oracles through its tenant's commitment tree alone
(Johnson/Desc/Sound/ReadsTreeAt.lean: `pinJT_col`), the verifier's state through the reader of the
OOD samples alone, and the witness. A tree that was sent in front of a sub-protocol passes it
unturned (Johnson/Desc/Sound/StringsStay.lean): an equation: so it serves backward too.

What is said.
  `ctxPins Nm Mg z m`: every tenant of the segment's three moments is pinned. `ctxPins_iff`: it is
    just «every item of `pinsOf m` holds». `pin_back`: one pin, backward. `PinAsks`: what the ride
    takes: the segment's tenants sit in trees below the piece's first tree; the samples' reader
    answers alike at the two states. `ctx_back`: **`ctxPins` behind gives `ctxPins` in front.**
    `hc_at`: **the form of hcb, hcq and hce, at a piece.**

Limits. `PinAsks` is a premise: its first half is a test on the plan's numbers (`fence_of_fit` pays
it where the three pins are open); its second is `OracleAsks`' third. hpin («two witnesses with the
context name one table») is not here. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.OracleRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers pinsOf)
open _root_.Run.PQ (CK)

variable {C : CK} {F : Frame}
variable {P Cells Tok Xi : Type}

/-- **The context**: every tenant of the segment's three moments is pinned. -/
def ctxPins (Nm : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT)) (z : P) (m : ℕ) :
    S × F.E.Str → Wit Cells Tok MsgT → Prop :=
  fun a w => ∀ t < 3, ∀ x ∈ Nm.sent m t, Mg.pin x.1 x.2 (z, a.1) (strsOf F a.2) w

/-- It is just «every item of pinsOf m holds». -/
theorem ctxPins_iff (Nm : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT)) (z : P) (m : ℕ)
    (a : S × F.E.Str) (w : Wit Cells Tok MsgT) :
    ctxPins Nm Mg z m a w ↔ ∀ i ∈ pinsOf m, i.holds Nm Mg (z, a.1) (strsOf F a.2) w := by
  constructor
  · intro h i hi
    simp only [pinsOf, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact h 0 (by omega)
    · exact h 1 (by omega)
    · exact h 2 (by omega)
  · intro h t ht
    have ht' : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases ht' with rfl | rfl | rfl
    · exact h (.pin m 0) (by simp [pinsOf])
    · exact h (.pin m 1) (by simp [pinsOf])
    · exact h (.pin m 2) (by simp [pinsOf])

variable (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem)

/-- One pin, backward. -/
theorem pin_back (z : P) (s s' : S) (j t base : ℕ) (hj : j < base) (ds : List RDT)
    (y : F.E.Str) (τ : Iop.Tr (uLT C ds)) (hs : smp (z, s') = smp (z, s))
    (w : Wit Cells Tok MsgT)
    (h : pinJT cs G arr smp ms j t (z, s') (strsOf F (behind C F base ds y τ)) w) :
    pinJT cs G arr smp ms j t (z, s) (strsOf F y) w := by
  have h1 : pinJT cs G arr smp ms j t (z, s') (strsOf F y) w :=
    pinJT_col cs G arr smp ms j t (z, s') (strsOf F (behind C F base ds y τ)) (strsOf F y) w
      (fun x => (colStays C F base ds y τ j x hj).symm) h
  refine ⟨h1.1, fun x hx hsit => ?_⟩
  obtain ⟨v, hv, h2, h3⟩ := h1.2 x hx hsit
  exact ⟨v, by show smp (z, s) x.1 x.2 = some v; rw [← hs]; exact hv, h2, h3⟩

/-- **What the ride takes.** -/
structure PinAsks (Nm : Numbers) (z : P) (m base : ℕ) (s s' : S) : Prop where
  /-- the segment's tenants sit in trees below the piece's first tree -/
  fence : ∀ t < 3, ∀ x ∈ Nm.sent m t, x.1 < base
  /-- the reader of the OOD samples answers alike at the two states -/
  smp : smp (z, s') = smp (z, s)

/-- **The context behind gives the context in front.** -/
theorem ctx_back (Nm : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT))
    (hP : Mg.pin = pinJT cs G arr smp ms) (z : P) (m base : ℕ) (ds : List RDT)
    (a b : S × F.E.Str) (τ : Iop.Tr (uLT C ds)) (hb : b.2 = behind C F base ds a.2 τ)
    (A : PinAsks cs smp Nm z m base a.1 b.1) (w : Wit Cells Tok MsgT)
    (h : ctxPins Nm Mg z m b w) : ctxPins Nm Mg z m a w := by
  intro t ht x hx
  have h1 := h t ht x hx
  rw [hP] at h1 ⊢
  rw [hb] at h1
  exact pin_back cs G arr smp ms z a.1 b.1 x.1 x.2 base (A.fence t ht x hx) ds a.2 τ A.smp w h1

/-- **THE FORM OF hcb, hcq AND hce, AT A PIECE.** -/
theorem hc_at {Cl : Type} (Nm : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT))
    (hP : Mg.pin = pinJT cs G arr smp ms) (z : P) (m : ℕ)
    (q : Piece C F S Cl (Wit Cells Tok MsgT)) (on : S × F.E.Str → Prop)
    (A : ∀ a τ b, on a → q.ior.red.out a τ = some b → PinAsks cs smp Nm z m q.base a.1 b.1) :
    ∀ a τ b' w, on a → q.ior.red.out a τ = some b' → ctxPins Nm Mg z m b' w →
      ctxPins Nm Mg z m a w :=
  fun a τ b' w ha hout h =>
    ctx_back cs G arr smp ms Nm Mg hP z m q.base q.ds a b' τ (out_strs hout) (A a τ b' ha hout) w h

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.ctxPins_iff
#print axioms VerifiableInference.Desc.LinkJoin.pin_back
#print axioms VerifiableInference.Desc.LinkJoin.ctx_back
#print axioms VerifiableInference.Desc.LinkJoin.hc_at
