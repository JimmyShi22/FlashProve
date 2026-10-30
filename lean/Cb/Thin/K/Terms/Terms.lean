-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Thin/K/Terms/Terms.lean: for each kind of term of the object, the part of the library's
conditions on that term which the road to index binding reads, as a record; and the half on
knowledge soundness of the library's four theorems on the object, from these records alone.

Definitions, statements and proofs. The object (`LdObj`, Cb/Obj/LdObject.lean) has terms of four
kinds, typed over `LdOL` (Cb/Obj/LdObjectLin.lean): for weights-formedness, for the test at one
instance, for a request, for the test at N instances. The library's own record of conditions on a
term also holds what the honest side needs. The records here hold the item on knowledge soundness,
two facts on relations, locality and the shape's point structure; for a request also that the record
is handed on and that the index is copied.
Main names:
  `LdOL.WfT.KnowOK`, `LdOL.LinT.KnowOK`, `LdOL.ReqT.KnowOK`: the records for three kinds. For the
    test at N instances the record is `LdOL.LinBT.LinBK` (Cb/Thin/K4/BatchK.lean), which also holds
    coherence: one record, not two.
  `ldOW_know`, `ldOT_know`, `ldOR_know`, `ldOBT_know`: the half on knowledge soundness of
    `ldOW_object`, `ldOT_object`, `ldOR_object`, `ldOBT_object`.
  `ldOW_local`, `ldOR_local`, `ldOR_passes`, `ldOR_copy`: the closed preambles are local; a
    request's hands the record on and copies the encoded index.
  `ldOlA_local`, `ldOlA_point`: the link is local, and its shape has a point structure, if the
    tail's has.
Limits: that a term meets its record is not shown here. No statement of this file names a bundle or
an honest prover.

-/
import Cb.Obj.LdObject
import Cb.Thin.K.Obj
import Cb.Thin.K4.BatchK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- What the road reads of a term for the preamble of weights-formedness. -/
structure LdOL.WfT.KnowOK {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] {O : LdOL F E}
    {Kc : Type} (T : O.WfT Kc) : Prop where
  /-- round-by-round knowledge soundness of the term, from "no collision" and the relaxed relation
  of weights-formedness into the last joint -/
  know    : T.F.red.KnowInto O.Cf.conf.free (O.S.over T.B).on (fun a _ => O.Cf.conf.RwfR a ())
    (O.S.over T.B).relR T.ext T.P.err
  /-- what holds of the decoded index gives the last base joint's relaxed relation, at the fixed
  further witness -/
  relRB   : ∀ a m U,
    O.Cf.conf.dcd a.2 a.1.2 = some U → O.holds a.1.1 a.1.2 U m → T.B.relR a (m, T.z0)
  /-- the last base joint's condition excludes a collision -/
  onB     : ∀ a, T.B.on a → ¬ O.Cf.conf.coll a.2 a.1.2.1
  /-- the verifier is local -/
  isLocal : T.F.IsLocal
  /-- the shape has a point structure -/
  point   : Nonempty T.F.shape.IsPoint

/-- What the road reads of a tail for the test at one instance. -/
structure LdOL.LinT.KnowOK {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] {O : LdOL F E}
    (T : O.LinT) : Prop where
  /-- round-by-round knowledge soundness of the tail, from the test's first joint to the trivial
  statement -/
  know    : T.Q.red.Know (O.P.j0 O.on0).on (O.P.j0 O.on0).relR (fun _ _ => True) T.ext T.N.err
  /-- the verifier is local -/
  isLocal : T.Q.IsLocal
  /-- the shape has a point structure -/
  point   : Nonempty T.Q.shape.IsPoint

/-- What the road reads of a term for the preamble of a request; z0: the fixed further witness. -/
structure LdOL.ReqT.KnowOK {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] {O : LdOL F E}
    {Kc : Type} (T : O.ReqT Kc) (z0 : T.Wp) : Prop where
  /-- round-by-round knowledge soundness of the term, from "the index decoder answers" and the
  relaxed request relation of the cells into the last joint -/
  know    : T.F.red.KnowInto (fun a => (O.Cf.conf.D a.2 a.1.2).isSome) (O.S.over T.B).on
    (fun a w => O.Cf.conf.RreqR a w.2) (O.S.over T.B).relR T.ext T.P.err
  /-- what holds of the decoded index gives the last base joint's relaxed relation, at z0 -/
  relRB   : ∀ a m U,
    O.Cf.conf.dcd a.2 a.1.2 = some U → O.holds a.1.1 a.1.2 U m → T.B.relR a (m, z0)
  /-- the last base joint's condition excludes a collision -/
  onB     : ∀ a, T.B.on a → ¬ O.Cf.conf.coll a.2 a.1.2.1
  /-- the verifier is local -/
  isLocal : T.F.IsLocal
  /-- the shape has a point structure -/
  point   : Nonempty T.F.shape.IsPoint
  /-- the record is handed on -/
  passes  : T.F.Passes Prod.snd fun b => b.1.2
  /-- the encoded index is copied -/
  copy    : ∀ y τ, (T.F.imp y τ).1 = y

/-- The half on knowledge soundness of `ldOW_object` (Cb/Obj/LdObjectOff.lean). -/
theorem ldOW_know (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (O : LdOL F E)
    (Kc : Type) (T : O.WfT Kc) (h : T.KnowOK) :
    PreKnowR O.left T.wf O.Cf.conf.free O.Cf.conf.RwfR (fun _ _ _ => ()) T.nums.err :=
  ldClose_know E O.Cf.conf O.S Kc _ _ Unit O.Cl T.Wp O.holds T.F O.Cf.conf.free
    (fun a _ => O.Cf.conf.RwfR a ()) T.B T.ext T.P.err O.Cf.conf.RwfR (fun _ => ()) T.z0
    (fun _ _ => 0) h.know h.relRB h.onB (fun _ _ _ hR => hR)

/-- The closed preamble of weights-formedness is local. -/
theorem ldOW_local (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (O : LdOL F E)
    (Kc : Type) (T : O.WfT Kc) (h : T.KnowOK) : T.wf.IsLocal :=
  h.isLocal.post _ _ (extMap_isLocal.1 _)

/-- The half on knowledge soundness of `ldOT_object` (Cb/Obj/LdObjectOff.lean), over
`ldObj_lin_know` (Cb/Thin/K/Obj.lean). -/
theorem ldOT_know (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (O : LdOL F E)
    (T : O.LinT) (d0 : O.left.AMsg) (hd : HasDist O.Cf.C₀.G O.Cf.C₀.d) (he : O.Cf.eM < O.Cf.C₀.d)
    (h : T.KnowOK) : LinKnowR O.left T.Q d0 T.nums.err :=
  ldObj_lin_know O.Cf.conf O.left O.P.W0 T.Q (O.P.j0 O.on0).on (O.P.j0 O.on0).relR T.ext T.N.err
    (fun w => O.S.msgs w.2) d0 h.know (fun a => (ldOL_on F E O a).1)
    (fun a w _ => ldOL_relR F E O hd he a w)

/-- The half on knowledge soundness of `ldOR_object` (Cb/Obj/LdObjectReq.lean). -/
theorem ldOR_know (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (O : LdOL F E)
    (Kc : Type) (T : O.ReqT Kc) (z0 : T.Wp) (r0 : O.S.Rnd) (h : T.KnowOK z0) :
    PreKnowR O.left T.req (fun a => (O.Cf.conf.D a.2 a.1.2).isSome) O.Cf.conf.RreqR
      (T.cellsOf z0 r0) T.nums.err :=
  ldClose_know E O.Cf.conf O.S Kc _ _ O.Cf.conf.Cells O.Cl T.Wp O.holds T.F
    (fun a => (O.Cf.conf.D a.2 a.1.2).isSome) (fun a w => O.Cf.conf.RreqR a w.2) T.B T.ext T.P.err
    O.Cf.conf.RreqR Prod.snd z0 r0 h.know h.relRB h.onB (fun _ _ _ hR => hR)

/-- The closed preamble of a request is local. -/
theorem ldOR_local (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (O : LdOL F E)
    (Kc : Type) (T : O.ReqT Kc) (z0 : T.Wp) (h : T.KnowOK z0) : T.req.IsLocal :=
  h.isLocal.post _ _ (extMap_isLocal.1 _)

/-- The closed preamble of a request hands the record on. -/
theorem ldOR_passes (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (O : LdOL F E)
    (Kc : Type) (T : O.ReqT Kc) (z0 : T.Wp) (h : T.KnowOK z0) :
    ∀ x y τ b, T.req.out x y τ = some b → b.2 = x.2 :=
  h.passes.post (r₃ := fun b : O.left.Xl × O.Cf.conf.Rec => b.2) _ _
    fun _ _ hx => by rw [← Option.some.inj hx]; rfl

/-- The closed preamble of a request copies the encoded index. -/
theorem ldOR_copy (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (O : LdOL F E)
    (Kc : Type) (T : O.ReqT Kc) (z0 : T.Wp) (h : T.KnowOK z0) :
    ∀ y τ, (T.req.imp y τ).1 = y :=
  fun y τ => h.copy y τ

/-- The half on knowledge soundness of `ldOBT_object` (Cb/Obj/LdObjectOnB.lean). -/
theorem ldOBT_know (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (O : LdOL F E)
    (N : ℕ) (T : O.LinBT N) (d0 : O.left.AMsg) (hd : HasDist O.Cf.C₀.G O.Cf.C₀.d)
    (he : O.Cf.eM < O.Cf.C₀.d) (h : T.LinBK) : LinBKnowR O.left T.Q N d0 T.P.err :=
  ldOB_know F E O T.on0 T.Q N T.ext T.P.err d0 hd he h.fits h.know

/-- The link (the entering step, then the tail) is local if the tail is. -/
theorem ldOlA_local (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E)
    (K : Cf.LinkPar) (T : K.Tail) (h : T.Q.IsLocal) : (K.link T).IsLocal :=
  (ldOlA_enter F E Cf K K.free K.free).good.isLocal.seq h

/-- The link's shape has a point structure if the tail's has. -/
theorem ldOlA_point (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E)
    (K : Cf.LinkPar) (T : K.Tail) (h : Nonempty T.Q.shape.IsPoint) :
    Nonempty (K.link T).shape.IsPoint :=
  (ldOlA_enter F E Cf K K.free K.free).good.point.elim fun p => h.elim fun q =>
    ⟨Blocks.pointApp p q⟩

end Cb

