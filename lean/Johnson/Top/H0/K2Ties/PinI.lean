-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/PinI.lean: A PIN OF AN EARLIER TENANT ACROSS A PIECE THAT SENDS, at the
sentence
that the composed meaning gives (`pinJT`, Johnson/Desc/Sound/MeaningSig.lean). Three theorems. A law
file: no sub-protocol imports it. Typed for the index masks' pin at the code switch; nothing in it
names the kind or the tenant.

What is said.
  `pin_back`: THE STATEMENT's SIDE: at an accept of a piece over the state alone, the public part z
    beside it: where the tenant's tree was sent in front of the piece (j < p.base) and the reader of
    OOD samples gives behind what it gives in front at the members that sit at the tenant: the pin
    behind gives the pin in front. It is `pinJT_rides` (Johnson/Desc/Sound/SigRides.lean), called at
    the reader with z laid in.
  `msgsOf_turn`: a member's message, as the pin reads it off the witness, bears a turn of pads off
    the member's tenant.
  `pin_bears`: THE WITNESS's SIDE: so the pin bears a turn of pads (PadsTurn.lean) off the tenant.

Limits. j < p.base and the samples' staying are premises. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.SigRides
import Johnson.Desc.K13.Law.ReaderByBook
import Johnson.Top.H0.K2Ties.PadsTurn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Wit FileDescription Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Comp)
open VerifiableInference.Desc.K13.Law (tab_same)

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {P S Cells Tok : Type}
  (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  {C : CK} {Fr : Frame} {Cl W : Type}

/-- **The statement's side.** -/
theorem pin_back (p : Piece C Fr S Cl W) (ms : List Mem) (j t : ℕ) (hj : j < p.base) (z : P)
    (a b : S × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds)) (hb : p.ior.red.out a τ = some b)
    (hS : ∀ x ∈ ms, SitsAt x j t → smp (z, b.1) x.1 x.2 = smp (z, a.1) x.1 x.2)
    (w : Wit Cells Tok MsgT) (h : pinJT cs G arr smp ms j t (z, b.1) (strsOf Fr b.2) w) :
    pinJT cs G arr smp ms j t (z, a.1) (strsOf Fr a.2) w :=
  (pinJT_rides cs G arr (fun s => smp (z, s)) p ms j t hj a b τ hb hS w).1 h

/-- A member's message, as the pin reads it, bears a turn of pads off the member's tenant. -/
theorem msgsOf_turn (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)
    (T : List (ℕ × ℕ)) (w w' : Wit Cells Tok MsgT) (hw : PadsTurn T w w') (i : Fin l.length)
    (hi : seat i ∉ T) : msgsOf cs l seat arr w' i = msgsOf cs l seat arr w i := by
  have hm : w.msg (arr (seat i).1 (seat i).2) = w'.msg (arr (seat i).1 (seat i).2) :=
    hw (.msg _) fun _ _ c => nomatch c
  have hp : w.pad (seat i).1 (seat i).2 = w'.pad (seat i).1 (seat i).2 :=
    hw (.pad (seat i).1 (seat i).2) fun x hx c => hi (by
      have e1 : (seat i).1 = x.1 := by injection c
      have e2 : (seat i).2 = x.2 := by injection c
      rw [show seat i = x from Prod.ext e1 e2]
      exact hx)
  funext q
  unfold msgsOf
  rw [tab_same w w' cs (l.get i).1 _ _ _ hm hp]

/-- **The witness's side.** -/
theorem pin_bears (ms : List Mem) (j t : ℕ) (T : List (ℕ × ℕ)) (hT : (j, t) ∉ T) (a : P × S)
    (y : Strs) (w w' : Wit Cells Tok MsgT) (hw : PadsTurn T w w')
    (h : pinJT cs G arr smp ms j t a y w) : pinJT cs G arr smp ms j t a y w' := by
  refine ⟨h.1, fun x hx hs => ?_⟩
  obtain ⟨zz, h1, h2, h3⟩ := h.2 x hx hs
  refine ⟨zz, h1, h2, ?_⟩
  have e : x.1.seat x.2 = (j, t) := hs
  rw [msgsOf_turn cs arr x.1.l x.1.seat T w w' hw x.2 (by rw [e]; exact hT)]
  exact h3

end

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.pin_back
#print axioms VerifiableInference.Desc.First.K2Ties.msgsOf_turn
#print axioms VerifiableInference.Desc.First.K2Ties.pin_bears
