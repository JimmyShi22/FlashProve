-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectCtb.lean: bookkeeping for the compiler to a random-oracle argument, for which it is
asked that the types of positions, symbols and plain messages of every round are countable: here for
the test that two encodings hold the same index, for the test for linear constraints, and for a
smallest example of the object.

Definitions, theorems. Bookkeeping for the passage to one random oracle: a coding of all query
points into bit strings exists as soon as these types, the instances and the alphabet of an encoded
index are countable (`Spec.countable_pts`, `CtbSh`, `CtbS`: CompileK/ImplCountable.lean;
CompileK/ImplExists.lean).
`CtbSh s`: the positions, symbols and plain parts of every round of the shape s are countable.
`CtbS`: the same for a shape with an annotation, the plain parts being those of the two components.
A code `C : LdCode E P` (Cb/Ld/LdRel.lean) has native positions `C.NP`; `C.NS p` names the
coordinates of the native symbol at the position p.

Main names:
  `ctbSh_append`; `l.Ctb`, `c.Ctb` (a step `IOR.Link` of a chain, every step of an `IOR.Chain`);
    `chainCtb_link`, `chainCtb_append`: the shape of a chain as one link is countable if every
    link's is.
  `ctb_plain`: a prover message without oracles, before a countable shape. Asked: its plain part is
    countable (`Countable Pl`).
  `ctb_peek`: a round without a prover message. `ctb_sendFam`: the sending of a family; asked:
    `Sig.CtbSy` (its symbols as sent are countable). `ctb_base`: the base case; asked of its code:
    `LdCode.FinNS` (a native symbol has finitely many coordinates). `ctb_run`: a whole test on a
    group; asked: its whole test's shape is countable. `ctb_cons`, `ctb_nil`: plans of tests;
    asked of `ctb_cons`: the same, and `Chain.Ctb` of the plan that follows. Asked of all but
    `ctb_peek` and `ctb_nil`: the field is finite.
  `ldOCtb_link`, `ldOCtb_lin`. Asked: the code has a position (`Nonempty (Fin Cf.C₀.n)`);
    `Sig.CtbSy` of the families sent; for the link a countable shape of the closing's whole test,
    for the test `Chain.Ctb` of its closing's plan.
  `stdObj_ctb` (`StdObj`, Cb/Obj/LdObjectStd.lean). Asked: the code has a position, and each of the
    two sets of long positions a member (`Nonempty`); countably many instances, and `FinNS` of
    four of its codes (those of `T.Lo` and of `T.Lk`).

Limits: on a protocol this file has two kinds of conclusion: countability (as in `ctb_peek`,
`ctb_nil`) and, of the codes of a group and of a test, `LdCode.FinNS` (`finNS_grp`, `stdLn_fin`:
each from `FinNS` of the members' codes); beyond these no statement of the file concludes anything
of a protocol.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectStd
import Cb.Obj.LdObjectLinkPairFull
import CompileK.ImplCountable
import Cond.ObjBits

set_option autoImplicit false

namespace Iop

theorem ctbSh_append : ∀ {s t : Shape}, CtbSh s → CtbSh t → CtbSh (s ++ t)
  | [], _, _, h => h
  | _ :: _, _, h, h' => ⟨h.1, ctbSh_append h.2 h'⟩

namespace IOR
variable {K : Type}

def Link.Ctb {A B : Joint K} (l : Link K A B) : Prop := CtbSh l.R.shape

def Chain.Ctb : {A B : Joint K} → Chain K A B → Prop
  | _, _, .one l => l.Ctb
  | _, _, .snoc c l => c.Ctb ∧ l.Ctb

theorem Chain.ctb_one {A B : Joint K} (l : Link K A B) : (Chain.one l).Ctb ↔ l.Ctb := by
  rw [Chain.Ctb]
theorem Chain.ctb_snoc {A B C : Joint K} (c : Chain K A B) (l : Link K B C) :
    (c.snoc l).Ctb ↔ c.Ctb ∧ l.Ctb := by rw [Chain.Ctb]

end IOR

open IOR

theorem chainCtb_link {K : Type} {A B : Joint K} (c : Chain K A B) (d : A.W) (h : c.Ctb) :
    (c.link d).Ctb := by
  induction c with
  | one l =>
    rw [Chain.link]
    exact (Chain.ctb_one l).1 h
  | snoc c l ih =>
    rw [Chain.link]
    exact ctbSh_append (ih ((Chain.ctb_snoc c l).1 h).1) ((Chain.ctb_snoc c l).1 h).2

theorem chainCtb_append {K : Type} {A B C : Joint K} (c : Chain K A B) (c' : Chain K B C)
    (h : c.Ctb) (h' : c'.Ctb) : (c.append c').Ctb := by
  induction c' with
  | one l =>
    rw [Chain.append]
    exact (Chain.ctb_snoc c l).2 ⟨h, (Chain.ctb_one l).1 h'⟩
  | snoc c' l ih =>
    rw [Chain.append]
    exact (Chain.ctb_snoc _ l).2 ⟨ih ((Chain.ctb_snoc c' l).1 h').1, ((Chain.ctb_snoc c' l).1 h').2⟩

end Iop

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- a prover message without oracles -/
theorem ctb_plain (Pl Ch : Type) [Fintype Ch] [Nonempty Ch] (d : Pl) [Countable Pl]
    {s : Shape} (h : CtbSh s) :
    CtbSh (plainRound Pl Ch d :: s) :=
  ⟨⟨inferInstanceAs (Countable Empty), fun p => p.elim, inferInstanceAs (Countable Pl)⟩, h⟩

theorem ctb_peek {Xi Xo : Type} {Ei Eo : ExtSpec} (V : PeekV Xi Ei Xo Eo) :
    CtbSh (IOR.peek V).shape :=
  ctb_plain Unit V.D () trivial

section
variable {E : Type} [Field E] [Fintype E]

/-- the symbols as sent of every member are countable -/
def Sig.CtbSy (N : Sig E) : Prop := ∀ a p, Countable ((N.om a).Sy p)

theorem ctb_sendFam (N : Sig E) (Sd : N.Seeds) (X : Type) (E₀ : ExtSpec) (h : N.CtbSy) :
    CtbSh (ldSendFam N Sd X E₀).shape :=
  ⟨⟨inferInstanceAs (Countable (Σ a, (N.om a).C.NP)),
      fun p => h p.1 p.2,
      inferInstanceAs (Countable Unit)⟩,
    ctb_plain N.Answ Unit _ trivial⟩

/-- a native symbol of the code has finitely many coordinates -/
def LdCode.FinNS {P : Type} (C : LdCode E P) : Prop := ∀ p, Finite (C.NS p)

theorem ctb_base (a : LdJoint E) (t : ℕ) (cov : a.C.NP → a.P) (d bad L2 : ℕ) (h : a.C.FinNS) :
    CtbSh (ldBaseEnd a t cov d bad L2).R.shape :=
  ⟨⟨inferInstanceAs (Countable a.C.NP), fun p => by
      haveI := h p
      exact inferInstanceAs (Countable (a.C.NS p → E)), inferInstanceAs (Countable E)⟩, ctb_plain a.C.MR (Fin t → a.P) 0 trivial⟩

theorem ctb_run {S : Sig E} (D : LdRunD S) {St₀ Wp : Type} {E₀ : ExtSpec}
    (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp)
    (d' : LdBrW D.G D.kp Wp) (h : CtbSh D.T.R.shape) : (D.link A₀ d d').Ctb := by
  show CtbSh ((ldBridge D.G D.kp D.Sb D.Z St₀ E₀).shape ++ (D.T.R.shape ++ []))
  exact ctbSh_append (ctb_plain Unit D.Z.D () trivial) (ctbSh_append h trivial)

theorem ctb_cons {S : Sig E} {E₀ : ExtSpec} {Wp : Type} (D : LdRunD S) (Q : LdTc (S.sub D.kp) E₀ Wp)
    (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) (h : CtbSh D.T.R.shape) (hQ : Q.c.Ctb) :
    (LdTc.cons D Q d d').c.Ctb :=
  chainCtb_append _ _ ((Chain.ctb_one _).2 (ctb_run D Q.base d d' h)) hQ

omit [Fintype E] in
theorem ctb_nil (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (w₀ : S.Wit × Wp) :
    (LdTc.nil S E₀ Wp w₀).c.Ctb :=
  (Chain.ctb_one _).2 trivial

omit [Field E] [Fintype E] in
/-- a complex of codes whose native symbols have finitely many coordinates -/
theorem finNS_grp {S : Sig E} (G : Grp S) (h : ∀ a, (S.om a).C.FinNS) : G.C.FinNS := fun p =>
  h p.1.1 p.2

end

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The link with its closing. -/
theorem ldOCtb_link {Cf : LdCf F E} [Nonempty (Fin Cf.C₀.n)] (K : Cf.LinkPar)
    (on0 on1 : (K.P.D.X.Row → Fin Cf.C₀.n → E) → K.P.D.X.Rec → Prop) (S : K.P.Snd) (ε₀ ε₁ : ℕ)
    (Kc : K.P.Cl) (d₂ : K.P.W2) (d : K.P.W0) (hN : K.N.CtbSy) (hT : CtbSh Kc.T.R.shape) :
    CtbSh (K.link (K.fullAt on0 on1 S ε₀ ε₁ Kc d₂ d)).shape := by
  show (K.P.linkC on0 on1 S ε₀ ε₁ (Kc.cZ d₂) d).Ctb
  unfold LdLkP.linkC LdLkP.coreC LdLkP.Cl.cZ
  refine chainCtb_link _ _
    (chainCtb_append _ _ ?_
      (chainCtb_append _ _ ((Chain.ctb_one _).2 trivial)
        (ctb_cons Kc.run _ _ _ hT (ctb_nil _ _ _ _))))
  rw [Chain.ctb_snoc, Chain.ctb_snoc, Chain.ctb_snoc, Chain.ctb_one]
  exact ⟨⟨⟨ctb_peek _, ctb_sendFam _ _ _ _ hN⟩, ctb_peek _⟩, ctb_peek _⟩

/-- The test at one instance with its closing. -/
theorem ldOCtb_lin (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (εf : ℕ) (Sn : O.toC.P.Snd)
    (Qt : LdTc O.toC.S O.toC.E₀ O.toC.Wpa) (fq : O.toC.St6 → Qt.St) (d : O.toC.P.W0)
    (hW : O.NW.CtbSy) (hU : O.NU.CtbSy) (hO : O.NO.CtbSy) (hQ : Qt.c.Ctb) :
    CtbSh (O.full Sn εf Qt fq d).shape := by
  show (O.toC.P.linC O.on0 Sn εf (O.toC.cZ Qt fq) d).Ctb
  unfold LdLinP.linC LdLinP.chain LdLinC.cZ LdLinC.chain
  refine chainCtb_link _ _
    (chainCtb_append _ _ ?_ (chainCtb_append _ _ ((Chain.ctb_one _).2 trivial) hQ))
  rw [Chain.ctb_snoc, Chain.ctb_snoc, Chain.ctb_snoc, Chain.ctb_snoc, Chain.ctb_snoc,
    Chain.ctb_snoc, Chain.ctb_one]
  exact ⟨⟨⟨⟨⟨⟨trivial, ctb_sendFam _ _ _ _ hW⟩, ctb_peek _⟩, ctb_sendFam _ _ _ _ hU⟩, ctb_peek _⟩,
      ctb_sendFam _ _ _ _ hO⟩,
    ctb_peek _⟩

/-- a standard oracle message alone, as a family -/
theorem ctbSy_one {P : Type} [Fintype P] (M : StdM E P) (h : M.Cm.FinNS) :
    (Sig.one M.om).CtbSy := fun _ p => by
  haveI := h p
  exact inferInstanceAs (Countable (M.Cm.NS p → E))

section
variable {Cf : LdCf F E} {P : Type} [Fintype P] (D : StdLn Cf P)

omit [Fintype F] in
/-- all oracle messages at the end of the standard test -/
theorem stdLn_fin (hW : D.MW.Cm.FinNS) (hU : D.MU.Cm.FinNS) (hO : D.MO.Cm.FinNS) :
    ∀ o : D.C.S.O, (D.C.S.om o).C.FinNS
  | .inl (.inl (.inl e)) => e.elim
  | .inl (.inl (.inr _)) => hW
  | .inl (.inr _) => hU
  | .inr _ => hO

omit [Fintype F] in
/-- the standard test's plan -/
theorem stdLn_ctbQ [Nonempty P] (hW : D.MW.Cm.FinNS) (hU : D.MU.Cm.FinNS) (hO : D.MO.Cm.FinNS) :
    D.T.Q.c.Ctb := by
  unfold LdLinPlT.Q
  exact ctb_cons D.T.D₁ _ D.T.d₁ D.T.d₁' (ctb_base _ _ _ _ _ _ (finNS_grp _ (stdLn_fin D hW hU hO)))
    (ctb_cons D.T.D₂ D.T.Q' D.T.d₂ D.T.d₂'
      (ctb_base _ _ _ _ _ _ (finNS_grp _ fun a => stdLn_fin D hW hU hO a.1)) (ctb_nil _ _ _ _))

end

/-- The three shapes of the smallest object, its instances and symbols. -/
theorem stdObj_ctb {Cf : LdCf F E} [Nonempty (Fin Cf.C₀.n)] {Pl Pk : Type} [Fintype Pl] [Fintype Pk]
    [Nonempty Pl] [Nonempty Pk] (T : StdObj Cf Pl Pk) (r : Cf.conf.Rec) (hX : Countable Cf.Xm)
    (hW : T.Lo.MW.Cm.FinNS) (hU : T.Lo.MU.Cm.FinNS) (hO : T.Lo.MO.Cm.FinNS) (hK : T.Lk.M.Cm.FinNS) :
    Countable Cf.conf.X ∧
    Countable (T.obj.subs.obj r).Symbol ∧
    CtbSh (T.obj.subs.obj r).offline.shape ∧
    CtbSh (T.obj.subs.obj r).link.shape ∧
    CtbS (T.obj.subs.obj r).onlineBatch.loc.shape (T.obj.subs.obj r).onlineBatch.ann := by
  refine ⟨hX, inferInstanceAs (Countable (Cf.Row → F)), ?_, ?_, trivial⟩
  · exact ldOCtb_lin T.Lo.O T.εf (T.Lo.Sn T.L T.tW T.tU T.tO) T.Lo.T.Q T.Lo.T.fq T.Lo.w0
      (ctbSy_one _ hW) (ctbSy_one _ hU) (ctbSy_one _ hO) (stdLn_ctbQ T.Lo hW hU hO)
  · exact ldOCtb_link T.Lk.K T.Lk.K.free T.Lk.K.free (T.Lk.S T.Ll T.tl) T.ε₀ T.ε₁ T.Lk.Kc T.wK2 T.wK0 (fun _ p => by
      haveI := hK p
      exact inferInstanceAs (Countable (T.Lk.M.Cm.NS p → E))) (ctb_base _ _ _ _ _ _ (finNS_grp _ fun _ => hK))

end
end Cb
