-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectWf.lean: assembly of the holographic IOP from its sub-protocols: the preamble of
weights-formedness and the test for linear constraints over one "what is left".

Definitions, statements and proofs.
Weights-formedness (`ConfigurationWithOutOfDomainSample.Rwf`, Hiop/RecConf.lean) is the relation that an encoded index is the
encoding of a message that holds an index, and that the record (`ConfigurationWithOutOfDomainSample.Rec`) is the prover's and has
the answers of that message (`ConfigurationWithOutOfDomainSample.Enc`); its relaxation `ConfigurationWithOutOfDomainSample.RwfR`: the index decoder answers.
Its preamble reduces it to linear claims (Cb/Ld/LdWf.lean). A tensor row is the claim ∑ g(y) · eq(ψ,
c) · M(y, c) + rest = τ, summed over the rows y and columns c of the index matrix M (`Claim`,
Cb/Ld/LdLinWords.lean).

Why: `SubsR` (Hiop/RecSubs.lean) has one datum "what the preamble leaves" for the preamble of
weights-formedness and for the test that follows it. Cb/Ld/LdWf.lean ends with `P.left`: claims "one
tensor row with masks and a public target, as the batching of tensor rows leaves it, and the rows
filed". Cb/Obj/LdObjectLin.lean starts from `O.left`: claims "the tensor row in the test's
parameters, and a further predicate".
The first writes the tensor part as the multilinear extension, at the point of the batching's
sumcheck, of a vector on the columns of "the matrix of the index" (an abstract map `P.mat`, columns
on a cube of k variables); the second as a double sum with equality weights over the index matrix in
the layout of the encoded index (columns: the variables that name a code row, then klo variables
inside a row).

Main names:
  `LdOWf F E`: the data of both, over one configuration `Cf`: the preamble's data
    `P : LdWfP E Cf.conf`; how its k column variables are the two groups (e); the layout (lay, py,
    klo, l); what else the test needs (radius e', locations t, its three families NW, NU, NO).
  `W.O`: the test's data, read off the preamble's last claims: oracle messages and claims are the
    preamble's; row vector: ε times the batched row vector; point: the point of the sumcheck, split
    along e; target: the last value; "rest": the two mask terms (the hiding polynomial's form; ε
    times the product of the coordinates times the batched incoming mask forms); further predicate:
    the rows filed hold.
  `W.Tie`: the one condition: `P.mat U` is the index matrix of U in that layout, read over E.
  `Spec.ldOWf_holds`: under `W.Tie` the two predicates (`W.P.holds`, `W.O.holds`) are equivalent,
    claim by claim.
  `Spec.ldOWf_left`: so, under `W.Tie`, the two data are equal: `W.P.left = W.O.left`.
  `Spec.ldOWf_items`: under `W.Tie`, `W.P.Laws` and `B.Hyp`, the preamble's two items at the test's
    datum (`PreListR`, `PreKnowR` at `W.O.left`, `B.wf`): the theorem of Cb/Ld/LdWf.lean, moved. The
    term `B.wf` is the same; no cast occurs (the types of "what is left" do not read the claims'
    predicate).
  `Spec.ldOWf_fit`: under the hypotheses of its statement, the line "the preamble's budget bears
    what the test reads of the oracles left", for any test Q over `W.O.left` that needs, at no
    further reads, sets within the demand that the preamble bears.

Limits: this file does not say that a `P.mat` with `W.Tie` fits the key maps of an instance
(`P.Laws.keyLin` is a hypothesis of the preamble). No test is given.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectWfKit
import Cb.Obj.LdObjectLinProofs
import Cb.Ld.LdWfProofs
import Cb.Ld.LdWfSide
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp

/-- the two mask terms of the row that the batching of tensor rows leaves -/
def BattPar.maskPart {E : Type} [Field E] [Fintype E] (B : BattPar E)
    (z : B.par.Mid) (m : B.J → E) : E :=
  ∑ i, hSl (B.par.vars z.st) (B.par.hp z.st z.pt) i * m (B.wAt (pIx B.fmt (pdPlains E B.n B.k) i)) +
    z.eps * (∏ i, B.outPt z i) * ∑ q, B.chi z q * ∑ j, B.slM q z.st.1 j * m j

/-- the batched row vector -/
def BattPar.rowVec {E : Type} [Field E] [Fintype E] (B : BattPar E) (z : B.par.Mid) : B.Rw → E :=
  fun r => ∑ q, B.chi z q * Alg.eqPt (B.pt z.st.1 q) (B.outPt z) * B.g z.st.1 q r

/-- The data of the preamble and of the test, over one configuration. -/
structure LdOWf (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Type 1 where
  Cf : LdCf F E
  P  : LdWfP E Cf.conf
  /-- the column variables of the matrix of the index: those that name a code row, and klo inside a
  row -/
  klo : ℕ
  e   : Fin P.k ≃ Fin Cf.X.v ⊕ Fin klo
  /-- the layout -/
  l   : ℕ
  lay : P.Rw × (Fin klo → Bool) → Cf.J₀
  py  : P.Rw → Fin l → Bool
  /-- what else the test needs -/
  e' : ℕ
  t  : ℕ
  NW  : Sig E
  SdW : NW.Seeds
  iW  : NW.O
  lW  : ((Fin Cf.X.v ⊕ Fin klo) → Bool) → (NW.om iW).C.J
  NU  : Sig E
  SdU : NU.Seeds
  iU  : NU.O
  lU  : Fin Cf.C₀.k → (NU.om iU).C.J
  NO  : Sig E
  SdO : NO.Seeds
  iO  : NO.O
  lO  : P.Rw → (NO.om iO).C.J

namespace LdOWf
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (W : LdOWf F E)

/-- The test's data, read off the preamble's last claims. -/
@[reducible] def O : LdOL F E where
  Cf := W.Cf
  S := W.P.S
  Cl := W.P.Cl
  Y := W.P.Rw
  klo := W.klo
  l := W.l
  lay := W.lay
  py := W.py
  g := fun cl y => cl.eps * W.P.bt.rowVec cl y
  ψ := fun cl =>
    (fun i => W.P.bt.outPt cl (W.e.symm (Sum.inl i)),
      fun i => W.P.bt.outPt cl (W.e.symm (Sum.inr i)))
  τ := fun cl => cl.fin
  restM := fun cl m => W.P.bt.maskPart cl (Sum.elim (fun _ => 0) (W.P.ent m))
  more := fun cl m => W.P.RowsV (W.P.stOf cl) m
  e' := W.e'
  t := W.t
  NW := W.NW
  SdW := W.SdW
  iW := W.iW
  lW := W.lW
  NU := W.NU
  SdU := W.SdU
  iU := W.iU
  lU := W.lU
  NO := W.NO
  SdO := W.SdO
  iO := W.iO
  lO := W.lO

/-- The matrix of the index is the index matrix in the layout of the encoded index. -/
def Tie : Prop :=
  ∀ (U : W.Cf.conf.Msg) (r : W.P.Rw) (c : Fin W.Cf.X.v ⊕ Fin W.klo → Bool),
    W.P.mat U (r, fun i => c (W.e i)) = W.O.D.mat (W.Cf.upM U) r c

end LdOWf

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- States: under `W.Tie` the two predicates are equivalent. -/
def ldOWf_holds : Prop :=
  ∀ (W : LdOWf F E), W.Tie →
    ∀ (cl : W.P.Cl) (rec : W.Cf.conf.Rec) (U : W.Cf.conf.Msg) (m : W.P.S.Msg),
      W.P.holds cl rec U m ↔ W.O.holds cl rec U m

/-- The condition says what `P.mat` is: it can always be met by the choice of `P.mat`. (No theorem
states that it can always be met; see "Limits" in the head.) -/
def ldOWf_tie : Prop :=
  ∀ (W : LdOWf F E),
    W.Tie ↔ ∀ (U : W.Cf.conf.Msg) (r : W.P.Rw) (c : Fin W.P.k → Bool),
      W.P.mat U (r, c) = W.O.D.mat (W.Cf.upM U) r fun i => c (W.e.symm i)

def ldOWf_left : Prop := ∀ (W : LdOWf F E), W.Tie → W.P.left = W.O.left

/-- The preamble's two items at the test's datum. -/
def ldOWf_items : Prop :=
  ∀ (W : LdOWf F E) (B : W.P.Blk), W.Tie → W.P.Laws → B.Hyp →
    PreListR W.O.left B.wf B.hWf id id W.Cf.conf.Rwf B.nums ∧
    PreKnowR W.O.left B.wf W.Cf.conf.free W.Cf.conf.RwfR (fun _ _ _ => ()) B.nums.err

open Classical in
/-- Under the hypotheses below, the preamble's budget bears what the test reads of the oracles
left. -/
def ldOWf_fit : Prop :=
  ∀ (W : LdOWf F E) (B : W.P.Blk) (Q : IOR (W.O.left.Xl × W.Cf.conf.Rec) W.O.left.El Unit extNone)
      (q : Finset W.Cf.conf.E0.Pos → Prop),
    B.Hyp → (∀ l, l ≤ W.P.n → ∀ ρ, (B.sub l).P.bud ρ ∅) →
    (∀ l, l ≤ W.P.n → ∀ ρ U, (B.sub l).R.need ρ U = U) →
    (∀ U V, V ⊆ U → W.P.S.qFam q B.t U → W.P.S.qFam q B.t V) →
    (∀ ρ, W.P.S.qFam q B.t (Q.given ρ ∅) ∧ Q.extReads ρ ⊆ Q.given ρ ∅) →
    ∀ ρ₁ ρ₂, B.nums.bud ρ₁ ((Q.extReads ρ₂).biUnion (B.wf.srcO ρ₁))

end
end Spec

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- the mask terms do not read the entries of the matrix -/
theorem LdOWf.maskPart_msg (W : LdOWf F E) (cl : W.P.Cl) (U : W.Cf.conf.Msg) (m : W.P.S.Msg) :
    W.P.bt.maskPart cl (W.P.msg (U, m)) =
      W.P.bt.maskPart cl (Sum.elim (fun _ => 0) (W.P.ent m)) := by
  unfold BattPar.maskPart
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  cases j with
  | inl j =>
      show (0 : E) * _ = (0 : E) * _
      rw [zero_mul, zero_mul]
  | inr j => rfl

theorem ldOWf_holds : Spec.ldOWf_holds F E := by
  intro W hT cl rec U m
  have hten : W.P.bt.ten (W.P.bt.rowVec cl) (W.P.bt.outPt cl) (W.P.msg (U, m)) =
      ∑ y, ∑ c, W.P.bt.rowVec cl y * Alg.eqk (W.O.D.pt (W.O.ψ cl)) c * W.O.D.mat (W.Cf.upM U) y c :=
    ldOWk_ten W.P.Rw (Fin W.P.k) (Fin W.Cf.X.v) (Fin W.klo) W.e (W.P.bt.rowVec cl) (W.P.mat U)
      (W.O.D.mat (W.Cf.upM U)) (W.P.bt.outPt cl) (hT U)
  have hA : cl.eps * W.P.bt.ten (W.P.bt.rowVec cl) (W.P.bt.outPt cl) (W.P.msg (U, m)) =
      ∑ y, ∑ c, W.O.g cl y * Alg.eqk (W.O.D.pt (W.O.ψ cl)) c * W.O.D.mat (W.Cf.upM U) y c := by
    rw [hten, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    show _ = cl.eps * W.P.bt.rowVec cl y * _ * _
    ring
  have hrow : W.P.bt.RowHolds cl (W.P.msg (U, m)) ↔
      W.O.D.Claim (W.Cf.upM U) (W.O.g cl) (W.O.ψ cl) (W.O.restM cl m) (W.O.τ cl) := by
    show cl.eps * W.P.bt.ten (W.P.bt.rowVec cl) (W.P.bt.outPt cl) (W.P.msg (U, m)) + _ + _ =
        cl.fin ↔
      _ + W.P.bt.maskPart cl (Sum.elim (fun _ => 0) (W.P.ent m)) = cl.fin
    rw [hA, ← W.maskPart_msg cl U m, add_assoc]
    rfl
  exact and_congr hrow Iff.rfl

theorem ldOWf_tie : Spec.ldOWf_tie F E := by
  intro W
  constructor
  · intro h U r c
    have e := h U r fun i => c (W.e.symm i)
    simp only [Equiv.symm_apply_apply] at e
    exact e
  · intro h U r c
    rw [h U r]
    simp only [Equiv.apply_symm_apply]

theorem ldOWf_left : Spec.ldOWf_left F E := fun W hT =>
  ldOWk_left W.Cf.conf W.P.S W.P.Cl W.P.holds W.O.holds (ldOWf_holds W hT)

theorem ldOWf_items : Spec.ldOWf_items F E := fun W B hT hL hB =>
  have h := ldWf E W.Cf.conf W.P B hL hB
  have k := ldOWk_pre W.Cf.conf W.P.S W.P.Cl W.P.holds W.O.holds _ _ Unit B.wf B.hWf
    id id W.Cf.conf.Rwf B.nums W.Cf.conf.free W.Cf.conf.RwfR (fun _ _ _ => ())
    B.nums.err (ldOWf_holds W hT)
  ⟨k.1 h.1, k.2 h.2⟩

open Classical in
theorem ldOWf_fit : Spec.ldOWf_fit F E := fun W B Q q hB h1 h2 hm hQ =>
  ldObj_fit _ _ _ _ B.wf Q B.nums.bud q (W.P.S.qFam q B.t)
    (ldWf_side E W.Cf.conf W.P B q hB h1 h2).bears hm hQ

end
end Cb
