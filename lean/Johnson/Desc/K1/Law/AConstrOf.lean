-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/AConstrOf.lean: THE CALL aConstr_of: the
arm aConstr of hgo_of_arms (K1/Law/GoAtLater.lean) at one later place of kind K1: the riding
item constr m p goes back over the block's own yes. A statement with its proof.

OBJECT. Any block B over the chain's state. USER. aConstr at links := linksFull,
ps := flatPlacesOf linksFull true, k := noL l d, B := blkL Z G l d X arrs, base := (L l d).1.
LETTERS. decT, hd, put, H, headPart, digitsPart, N, Mg.
IT FIXES THE TOP's LETTER Cells := Sound.CellsQ rows cols: the top must take that value.
HOW. By the text of P5J.constrQAt (Johnson/P5J/MeansQ.lean), arm by arm, as constr_back_one
goes; IT IS NOT A CALL OF THAT THEOREM: here each premise on a letter
is asked ONLY IN ITS OWN ARM AND AT AN ITEM THAT IS OPEN: so this statement is the stronger one.
PREMISES THAT STAY, BY NAME: ALL ON LETTERS: A ROUTING, NO PAYMENT.
  hconstr  Mg.constr is the composed meaning's term (mgAll_constr: rfl).
  hdec     the decoder decT answers behind the yes as in front (the row's DecLeft, to the letter).
  hreq     so does H.req.
  hhead    headPart goes back, at an open item of the head's segment hd.
  hdig     digitsPart goes back, at an open item constr m lookDigits.
What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.GoAtLaterForms
import Johnson.Desc.K1.Law.KeepAtLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers)
open VerifiableInference.Desc.K13.Law (openAt)

variable {Pp Tok : Type}

/-- **THE CALL aConstr_of**: the top's binder aConstr at one later place. ALL FOUR PREMISES ARE ON
LETTERS. -/
theorem aConstr_of {X : Model.Verify.Public} {rows cols : ℕ}
    (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option (Sound.CellsQ rows cols)) (hd : ℕ)
    (put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq)
    (H : P5J.HidAt X Pp (Wit (Sound.CellsQ rows cols) Tok Sound.MsgT) rows cols)
    (headPart : P5J.TPart → Sound.IdxQ → Pp × S → Strs →
      Wit (Sound.CellsQ rows cols) Tok Sound.MsgT → Prop)
    (digitsPart : ℕ → Pp × S → Strs → Wit (Sound.CellsQ rows cols) Tok Sound.MsgT → Prop)
    (N : Numbers) (Mg : Meaning Pp (Wit (Sound.CellsQ rows cols) Tok Sound.MsgT))
    (hconstr : Mg.constr = P5J.constrQAt hd put (Sound.oneDec decT H) headPart digitsPart)
    (links : List ModelPart) (ps : List Place) (k : ℕ) (B : Block S Unit) (base : ℕ)
    (hdec : ∀ x x' c, YesOf B x x' → decT c x' = decT c x)
    (hreq : ∀ x x', YesOf B x x' → H.req x' = H.req x)
    (hhead : ∀ x x' y y' w p i, YesOf B x x' → InAt N Mg links ps k x y → KeptBelow base y y' →
      Item.constr hd p ∈ openAt links ps k → headPart p i x' y' w → headPart p i x y w)
    (hdig : ∀ x x' y y' w m, YesOf B x x' → InAt N Mg links ps k x y → KeptBelow base y y' →
      Item.constr m .lookDigits ∈ openAt links ps k → digitsPart m x' y' w →
      digitsPart m x y w) :
    ∀ (x x' : Pp × S) y y' w m p, YesOf B x x' → InAt N Mg links ps k x y → KeptBelow base y y' →
      Item.constr m p ∈ openAt links ps k → Mg.constr m p x' y' w → Mg.constr m p x y w := by
  intro x x' y y' w m p hy hIn hk ho h0
  rw [hconstr] at h0 ⊢
  unfold P5J.constrQAt at h0 ⊢
  by_cases hp : p = .lookDigits
  · rw [if_pos hp] at h0 ⊢
    subst hp
    exact hdig x x' y y' w m hy hIn hk ho h0
  · rw [if_neg hp] at h0 ⊢
    refine ⟨h0.1, fun M i hM hi => ?_⟩
    have hM' : (Sound.oneDec decT H).dec x' y' = some M := by
      show decT y'.cell x' = some M
      rw [hk.1, hdec x x' _ hy]
      exact hM
    have h1 := h0.2 M i hM' hi
    by_cases hm : m = hd
    · rw [if_pos hm] at h1 ⊢
      subst hm
      exact hhead x x' y y' w p i hy hIn hk ho h1
    · rw [if_neg hm] at h1 ⊢
      have e : (Sound.oneDec decT H).req x' = (Sound.oneDec decT H).req x := hreq x x' hy
      rw [e] at h1
      exact h1

end VerifiableInference.Desc.K1
