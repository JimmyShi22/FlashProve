-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05IdnClause.lean: kind K5: THE CLAUSE "idn" OF K5FillIns (Att/K05Closes.lean: with the context's constr m .small in front): the kind's own identities at the cells off the messages give the meaning's part .idn at
segment m.

How. By the make of the meaning that is meant (THE SHAPE: the premise hC, as in Att/K05ConstrBack.lean) the part .small at m holds bs m w: "segment m's committed symbols, as the witness holds them, are the packing of small integers". Under that the cells off
the messages are the casts of the model's integers Zof w (hCells: the named reading CellsAre). Then own12_of_cells (Att/K05IdnAt.lean) carries the two families of identities to the base field at these integers, which is what the body says at (m, .idn) (hBody).
Main names: k5FillIns_idn (the clause's text) · idn_fits (Lean's own check that the conclusion is the field's type: it calls the theorem itself; it proves nothing new).
PREMISES: hC (the shape) · hCells : bs m w → CellsAre x S tl D rad (part w) (Zof w) [its road: attCells_cast, Johnson/Desc/First/Look/K3CallerAttMeans.lean, with "the model's integers at m are those that the symbols pack, at the caller's own seats": the
  filling's: NOT PAID] · hBody : the two families over the base field at Zof w give body m .idn [at the meaning that is meant: the integer model's AttOwn1 ∧ AttOwn2, by their definitions].
THE LETTERS UNDER "FOR ALL": hC, hCells, hBody: laws on letters of the filling: w free on purpose; i, a, y free on purpose (the body at (m, .idn) reads none of them).
IS IT EMPTY HERE? Implications.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Closes
import Johnson.Desc.First.Att.K05IdnAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Road.L5 (dimOf callsOf Zs cellsA)
open VerifiableInference.Desc.First.Look (Sent attSg JAtt attCells CellsAre)
open VerifiableInference.Desc.Sound (Frame strsOf)
open VerifiableInference.Desc (Place Strs)
open VerifiableInference.Desc.First (Item Pub Meaning Numbers ModelPart Part)

section
variable {Pp W Cells Ix : Type} {Fr : Frame} (Mg : Meaning Pp W) (π : Pp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × First.S → Option Cells) (Hd : Cells → Ix → Prop) (bs : ℕ → W → Prop)
  (dP : ℕ → Pp × First.S → Strs → W → Prop) (body : ℕ → Part → Ix → Pp × First.S → Strs → W → Prop)
  (hC : ∀ n p a y w, Mg.constr n p a y w ↔
    if p = .lookDigits then dP n a y w
    else (p = .small → bs n w) ∧ ∀ M i, decT y.cell a = some M → Hd M i → body n p i a y w)
  (N : Numbers) (links : List ModelPart) (m : ℕ) (pl : Place) (O : List Item) (Q : List Pub)
  (x : VerifiableInference.Desc.First.Look.Place) (S : Attention.Shape) (tl : HTailF2) (D : Sent) (rad : OracleShape → Nat)
  (part : W → (attSg x D rad).Msg) (Zof : W → Zs)
  (hCells : ∀ w, bs m w → CellsAre x S tl D rad (part w) (Zof w))
  (hBody : ∀ i a y w,
    ((∀ k b g' n, (Idn.at1 k b g' n).Valid (dimOf S) →
        idnVal (dimOf S) (castT (cellsA S (Zof w)) : Raw → Cb.Gl.F) (.at1 k b g' n) = 0) ∧
      ∀ b g' n, (Idn.at2 b g' n).Valid (dimOf S) →
        idnVal (dimOf S) (castT (cellsA S (Zof w)) : Raw → Cb.Gl.F) (.at2 b g' n) = 0) → body m .idn i a y w)
include hC hCells hBody

/-- **The clause "idn" of K5FillIns (with the context's constr m .small in front).** -/
theorem k5FillIns_idn : ∀ a' w, onT N Mg links π Fr pl O Q a' →
    (∀ j b g i, (Idn.at1 j b g i).Valid (dimOf S) →
      idnVal (dimOf S) (attCells x S tl D rad (part w)) (.at1 j b g i) = 0) →
    (∀ b g i, (Idn.at2 b g i).Valid (dimOf S) →
      idnVal (dimOf S) (attCells x S tl D rad (part w)) (.at2 b g i) = 0) →
    Mg.constr m .small (π, a'.1) (strsOf Fr a'.2) w →
    Mg.constr m .idn (π, a'.1) (strsOf Fr a'.2) w := by
  intro a' w _ h1 h2 hs
  rw [hC] at hs ⊢
  rw [if_neg (by decide)] at hs ⊢
  exact ⟨fun h => absurd h (by decide), fun M i _ _ => hBody i _ _ w (own12_of_cells (hCells w (hs.1 rfl)) h1 h2)⟩

theorem idn_fits (base : ℕ) (own : Params.AttentionRounds) (Ex : Iop.ExtSpec) (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E) (ns : ℕ) (Nn : Nums)
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)))
    (I : K5FillIns Mg N links π Fr base m pl O Q own x S tl D rad Ex Wp α ns Nn x0 part) :
    K5FillIns Mg N links π Fr base m pl O Q own x S tl D rad Ex Wp α ns Nn x0 part :=
  { I with idn := (k5FillIns_idn Mg π decT Hd bs dP body hC N links m pl O Q x S tl D rad part Zof hCells hBody) }

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.k5FillIns_idn
#print axioms VerifiableInference.Desc.First.Att.P.idn_fits
