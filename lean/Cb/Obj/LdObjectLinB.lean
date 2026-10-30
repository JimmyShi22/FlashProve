-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectLinB.lean: the test for linear constraints at N instances, over the configuration of
Cb/Obj/LdObjectConf.lean: the item on knowledge soundness.

The test for linear constraints is the interactive oracle proof of proximity (IOPP) for the
constraint relation. In a session it runs on a batch of at most N instances that share the encoded
index. This file derives the item on knowledge soundness that the proof system requires of the test
for a batch from round-by-round knowledge soundness of any batch protocol at the test's first
joint, under the hypotheses told under "Main names".

Definitions, statements (Cb.Spec.ldOB_*) and proofs.
`KnowB` (Ior/BatchSeq.lean) is round-by-round knowledge soundness for the instances of a batch:
each statement has sets of bad verifier messages; if a statement has the condition (`on`), a
transcript avoids these sets, the verifier outputs a next statement and w is a witness of it (in
`RB`), then the extractor's witness from w is in `RA` (here the relaxed relation); over an
admissible vector of statements (`adm`) the sets are jointly within the errors ε.
Hiop/RecSubs.lean requires (`LinBKnowR`): for each record, with that record in all slots, on the
collision-free statements whose encoded index decodes with the record, knowledge soundness for the
instances of a batch, the extractor decoding the statement.
Cb/Obj/LdObjectBatch.lean (`Spec.ldObj_linB_know`) leads there from one `KnowB` of a whole chain,
for vectors of statements with one (index, record), and two bridging facts (b), (c). Here these two
are shown for the test over `O.Cf.conf` (`O : LdOL`, Cb/Obj/LdObjectLin.lean), at the first joint
`O.P.j0 on0`.
Generic in the condition on0 on the index: any on0 with `O.Fits on0`.

Main names:
  `Spec.ldOB_fits`: the second regime's `O.onDec` fits; so does the first regime's `O.on0` (no
    collision).
  `Spec.ldOB_on` (b), `Spec.ldOB_relR` (c).
  `Spec.ldOB_know`: if `HasDist O.Cf.C₀.G O.Cf.C₀.d`, `O.Cf.eM < O.Cf.C₀.d` and `O.Fits on0`, then
    `KnowB` of any batch protocol Q from `O.P.j0 on0`, for vectors with one (index, record), gives
    `Hiop.LinBKnowR O.left Q N d0 ε`, same errors.
  `Spec.ldOB_foldErr`: in the second regime, if `HasDist O.Cf.C₀.G O.Cf.C₀.d` and e' + eM is below
    `O.Cf.C₀.d`: no point is bad for the fold (what the chain asks of the condition:
    `O.P.FoldErr O.onDec 0`).

Limits: no chain is given, no `KnowB` is proved here. This file says nothing on the honest side of a
batch (`LinBListR`).

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectLinProofs
import Cb.Obj.LdObjectBatch
import Cb.Obj.LdObjectConfMore

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace LdOL
variable {F E : Type} [Field F] [Field E] [Algebra F E] (O : LdOL F E)

/-- The second regime: the index decodes with its record. -/
def onDec : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop := fun f rec =>
  O.Cf.X.dec f rec ≠ none

/-- a condition on the index that holds wherever the list's item (`LinBKnowR`, Hiop/RecSubs.lean)
speaks -/
def Fits (on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop) : Prop :=
  ∀ f rec, O.Cf.X.dec f rec ≠ none → ¬ O.Cf.X.Coll f rec.1 → on0 f rec

end LdOL

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldOB_fits : Prop := ∀ (O : LdOL F E), O.Fits O.onDec ∧ O.Fits O.on0

/-- (b) States: if `O.Fits on0`, a collision-free statement of the list (`O.left.cond`) whose index
decodes has the chain's condition. -/
def ldOB_on : Prop :=
  ∀ (O : LdOL F E) (on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop), O.Fits on0 →
    ∀ a : O.left.St, (O.Cf.conf.dcd a.2.1 a.1.2).isSome → O.left.cond a → (O.P.j0 on0).on a

/-- (c) States: if `HasDist O.Cf.C₀.G O.Cf.C₀.d` and `O.Cf.eM < O.Cf.C₀.d`, the chain's relaxed
relation gives the list's (`O.left.RlinR`), at the messages of the witness. -/
def ldOB_relR : Prop :=
  ∀ (O : LdOL F E) (on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop),
    HasDist O.Cf.C₀.G O.Cf.C₀.d → O.Cf.eM < O.Cf.C₀.d →
    ∀ (a : O.left.St) (w : O.P.W0), (O.P.j0 on0).relR a w → O.left.RlinR a (O.S.msgs w.2)

/-- The item of the list (`LinBKnowR`), from `KnowB` of any batch protocol that starts at the test's
first joint.
(not all hypotheses are named here: see the statement below) -/
def ldOB_know : Prop :=
  ∀ (O : LdOL F E) (on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop)
      (Q : BIOP (O.left.Xl × O.Cf.conf.Rec) O.left.El) (N : ℕ)
      (ext : (O.left.Xl × O.Cf.conf.Rec) × O.left.El.Str → Tr Q.ior.shape → Unit → O.P.W0)
      (ε : Err Q.ior.shape) (d0 : O.left.AMsg),
    HasDist O.Cf.C₀.G O.Cf.C₀.d → O.Cf.eM < O.Cf.C₀.d → O.Fits on0 →
    Q.ior.KnowB Q.ann N (SameKey fun a => (a.2.1, a.1.2)) (O.P.j0 on0).on (O.P.j0 on0).relR
      (fun _ (_ : Unit) => True) ext ε →
    LinBKnowR O.left Q N d0 ε

/-- States: if `HasDist O.Cf.C₀.G O.Cf.C₀.d` and `O.e' + O.Cf.eM < O.Cf.C₀.d`, in the second regime
no point is bad for the fold. -/
def ldOB_foldErr : Prop :=
  ∀ (O : LdOL F E), HasDist O.Cf.C₀.G O.Cf.C₀.d → O.e' + O.Cf.eM < O.Cf.C₀.d → O.P.FoldErr O.onDec 0

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

omit [Fintype F] [Fintype E] in
theorem ldOB_fits : Spec.ldOB_fits F E := fun _ => ⟨fun _ _ h _ => h, fun _ _ _ h => h⟩

omit [Fintype E] in
theorem ldOB_on : Spec.ldOB_on F E := by
  intro O on0 hF a hd hc
  refine ⟨hF _ _ (fun h0 => ?_) hc.1, hc.2⟩
  have h1 : ((O.Cf.X.dec (O.Cf.tab a.2.1) a.1.2).map O.Cf.dnM).isSome := hd
  rw [show O.Cf.X.dec (O.Cf.tab a.2.1) a.1.2 = none from h0] at h1
  exact Bool.false_ne_true h1

omit [Fintype E] in
theorem ldOB_relR : Spec.ldOB_relR F E := fun O _ hd he a w h => ldOL_relR F E O hd he a w h

omit [Fintype E] in
theorem ldOB_know : Spec.ldOB_know F E := fun O on0 Q N ext ε d0 hd he hF hK =>
  ldObj_linB_know O.Cf.conf O.left O.P.W0 Q N (O.P.j0 on0).on (O.P.j0 on0).relR ext ε
    (fun w => O.S.msgs w.2) d0 hK (ldOB_on F E O on0 hF)
    (fun a w _ _ h => ldOB_relR F E O on0 hd he a w h)

omit [Fintype F] in
theorem ldOB_foldErr : Spec.ldOB_foldErr F E := fun O hd he =>
  ldLin_foldErr_far O.P O.Cf.C₀.d (ldCm_dist F E O.Cf hd) he

end
end Cb
