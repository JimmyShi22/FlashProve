-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldWfWith.lean: lemmas which say that conditions proved of one record of data still hold
after another definition has overwritten some of its fields: the clauses on weights-formedness do
not read what the builder of the object overwrites.

Definitions, statements and proofs. Generic; nothing assumed beyond the hypotheses of the
statements and whatever the arguments hold as proofs.

Why: the builder of the object (Cb/Ld/LdBldObj.lean) takes all data of weights-formedness Z :
`LdWfE` as an input and puts in the families of the offline linear test (`Z.withBld L`: the fields
e', t and the three families of `Z.W`). The records on the object ask their clauses of
`Z.withBld L`; Cb/Ld/LdBldWfSpec.lean's statements are about Z.

Main names:
  `Spec.ldWfWith_rest2`: `Z.Rest2 p` ⇒ `(Z.withBld L).Rest2 p`.
  `Spec.ldWfWith_std`: the six clauses on the standard sender's data V (`LdWfE.StdW.Six`: wfStd,
    wfBody, wfBd, wfAtL, wfAtB, wfNoPad, in the words of `Gl.FinalPP`) pass likewise, with the same
    term for "finitely many vectors of masks".
  `Spec.bldWf_with`: the builder's value in the object: `X.Room p` ⇒ for every hpl and L, the six
    clauses and `Rest2 p` after `withBld L` (see its doc comment).

Limits: this file does not say that the clause on the messages' codes (wfM) passes. Of Z and V that
clause reads `Z.W.P.S`, `V.Y`, `Z.L`, `Z.t` alone, the same terms on both sides (`Z.t` is a field of
Z; `withBld` overwrites the field t of `Z.W`): nothing to pass.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBldWfProofs
import Cb.Ld.LdBldObj

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp Cb.Lkp

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

/-- the data of the standard sender, beside Z.withBld L -/
@[reducible] def LdWfE.StdW.withBld {Z : LdWfE F E} {Fp : Type} [Field Fp] [Fintype Fp]
    [Algebra Fp E] (V : Z.StdW Fp)
    (L : BldLn E ((Fin Z.W.Cf.X.v ⊕ Fin Z.W.klo) → Bool) (Fin Z.W.Cf.C₀.k) Z.W.P.Rw) :
    (Z.withBld L).StdW Fp :=
  ⟨V.Y, V.dat, V.w0, V.bd, V.nAt, V.RdW, V.atL, V.pl, V.hpl⟩

/-- the six clauses on the standard sender's data, as one proposition -/
def LdWfE.StdW.Six {Z : LdWfE F E} {Fp : Type} [Field Fp] [Fintype Fp] [Algebra Fp E]
    (V : Z.StdW Fp) (fin : ∀ b, Fintype (Z.K.wfI Z.Rl b → E)) : Prop :=
  ((⟨Z.D, Z.X⟩ : Σ D, Z.K.MaskPl D Z.Rl) =
    ⟨Z.W.P.stdD V.Y V.dat V.w0,
      @LdWfP.Lks.stdX E _ _ _ _ Z.K Fp _ _ _ Z.Rl fin V.Y V.dat V.w0 V.nAt
        V.RdW V.atL V.pl V.hpl⟩) ∧
  (∀ m, Z.W.P.body m = V.bd (V.Y.dataOf m)) ∧
  (∀ b, V.bd (V.dat b) = b) ∧
  (∀ l i, V.nAt (V.atL l i) = V.Y.entF (V.pl (some l) i)) ∧
  (∀ i, V.nAt (Z.W.P.wAt i) = V.Y.entF (V.pl none i)) ∧
  ∀ n, V.RdW n → V.Y.NoPad n

end

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

def ldWfWith_rest2 : Prop :=
  ∀ (Z : LdWfE F E)
      (L : BldLn E ((Fin Z.W.Cf.X.v ⊕ Fin Z.W.klo) → Bool) (Fin Z.W.Cf.C₀.k) Z.W.P.Rw) (p : ℕ),
    Z.Rest2 p → (Z.withBld L).Rest2 p

def ldWfWith_std : Prop :=
  ∀ (Fp : Type) [Field Fp] [Fintype Fp] [Algebra Fp E] (Z : LdWfE F E)
      (L : BldLn E ((Fin Z.W.Cf.X.v ⊕ Fin Z.W.klo) → Bool) (Fin Z.W.Cf.C₀.k) Z.W.P.Rw)
      (V : Z.StdW Fp) (fin : ∀ b, Fintype (Z.K.wfI Z.Rl b → E)),
    V.Six fin → (V.withBld L).Six fin

/-- States: if `X.Room p`, then for every hpl and L the six clauses and `Rest2 p` hold at
`(X.Zw hpl).withBld L`, `(X.V hpl).withBld L`. -/
def bldWf_with : Prop :=
  ∀ (Fp : Type) [Field Fp] [Fintype Fp] [Algebra Fp E] (X : BldWf F E Fp) (p : ℕ), X.Room p →
    ∀ (hpl : X.Hpl) (L : BldLn E ((Fin X.Cf.X.v ⊕ Fin X.klo) → Bool) (Fin X.Cf.C₀.k) X.Rw),
      ((X.V hpl).withBld L).Six X.finWfI ∧ ((X.Zw hpl).withBld L).Rest2 p

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

theorem ldWfWith_rest2 : Spec.ldWfWith_rest2 F E := fun _ _ _ h =>
  { val := h.val, describes := h.describes, lin := h.lin, lks := h.lks, deg := h.deg, zOK := h.zOK,
    fair := h.fair, multOf := h.multOf
    tie := h.tie, lkPl := h.lkPl, rdL := h.rdL, own := h.own, ent := h.ent, inRd := h.inRd,
      rdJ := h.rdJ, atEq := h.atEq, ownL := h.ownL
    apart := fun b j hj n hS => by
      cases b with
      | some l => exact h.apart (some l) j hj n hS
      | none => exact h.apart none j hj n hS }

theorem ldWfWith_std : Spec.ldWfWith_std F E := fun _ _ _ _ _ _ _ _ h => h

theorem bldWf_with : Spec.bldWf_with F E := fun Fp _ _ _ X p h hpl L =>
  ⟨ldWfWith_std F E Fp (X.Zw hpl) L (X.V hpl) X.finWfI (bldWf_std F E Fp X p h hpl),
    ldWfWith_rest2 F E (X.Zw hpl) L p (bldWf_rest2 F E Fp X p h hpl)⟩

end
end Cb
