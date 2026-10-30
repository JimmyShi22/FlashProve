-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectErr.lean: the round-by-round errors of three sub-protocols of the holographic IOP
(the test that two encodings hold the same index; the test for linear constraints at one instance;
the preamble of a request), read as plain lists of numbers.

Statements (in `Cb.Spec`) and proofs: unfolding, by Ior/KnowCollRulesChainErr.lean. Generic: any
configuration, any closing.

The lists of the object (`SubsR.Nums`, Hiop/RecBuild.lean) hold lists of errors whose types depend
on the terms' shapes. An error is a count of values of one verifier message. Here the lists are read
as plain lists of numbers (`Err.toList`), and the numbers of values of the verifier messages beside
them (`Shape.chalList`). These errors are numbers that a link or a term lists (the data fields
`Link.P.err`, read by `Link.errs` and `Chain.errs`, and `err` of `K.nums ..`, `O.numsF ..` and
`(O.termOf ..).nums`): that a link or a sub-protocol is sound at the numbers that are listed for it
is no statement of this file; that tie is `Spec.ldChain_link`, `Spec.ldChain_cons`
(Cb/Ld/LdLinCloseChain.lean), `Spec.ldOl_chainC` (Cb/Obj/LdObjectLinkChain.lean), `Spec.ldOl_full`
(Cb/Obj/LdObjectLinkFull.lean), `Spec.ldOLF_items` (Cb/Obj/LdObjectLinFull.lean) and
`Spec.ldOS_object` (Cb/Obj/LdObjectReqSeg.lean), each under the hypotheses of its statement (that
condition itself asks soundness of some of the parts one level down: for these the tie carries
soundness, it does not found it).

Main names:
  `Spec.ldOErr_run`: one whole test on a group, as an `IOR.Link`, carries the bridge's error L ·
    (the evader's number), then the errors of the whole test T.
  `Spec.ldOErr_linkC`: the link (the test that two encodings hold the same index) with any closing
    chain cZ carries the errors:
      γ: `errGam ε₀ ε₁`;
      the joint seed: the sending's;
      the answers: 0;
      the locations: `errLoc`;
      φ: `errPhi`;
      then cZ's errors.
  `Spec.ldOErr_link`: with the closing of Cb/Ld/LdLinkClose.lean it carries the same five, then the
    bridge's `Kc.L * Kc.Z.err`, then the errors of the whole test `Kc.T`.
  `Spec.ldOErr_lin`: the test at one instance with its closing (Cb/Obj/LdObjectLinFull.lean), any
    plan Qt:
      seed of W: the sending's;
      its answers: 0;
      the shared point: `errPt εf`;
      seed of G_u;
      0;
      the locations: `errLoc`;
      seed of Ω;
      0;
      ζ: `errZeta`;
      then the plan's errors, `Qt.c.errs`.
    (For W, G_u, Ω and ζ see the head of Cb/Ld/LdLin.lean.)
  `Spec.ldOErr_cons`: a plan that begins with a test D: D's bridge, D's whole test, then the rest of
    the plan.
  `Spec.ldOErr_req`: the preamble of a request built of segments (Cb/Obj/LdObjectReqSeg.lean:
    `O.termOf`, the case without a ghost; not the general form `O.termAt`): the errors of all links
    (`IOR.Link`) of `r.chain`, in a row (`Chain.errs`). Not unfolded further: how the list of
    `r.chain` is put together from the first sending, the segments' moves and the last part is not
    written out here.
  `ldOErr_run`, `ldOErr_cons`, `ldOErr_linkC`, `ldOErr_req` also give the numbers of values of the
  verifier messages, in the same order; `ldOErr_link` and `ldOErr_lin` give the errors alone.
  `ldOErr_linkC`, `ldOErr_link` and `ldOErr_lin` ask that the code has a position
  (`Nonempty (Fin Cf.C₀.n)`).

Notation: `ε₀`, `ε₁`: natural numbers, the arguments of `errGam` (see `FoldErr`: Cb/Ld/LdLink.lean);
`εf`: a natural number, the argument of `errPt` (see `FoldErr`: Cb/Ld/LdLin.lean).

Limits: this file does not say what the numbers mean: the blocks' own files do. Nothing on the
preamble of weights-formedness nor on the test at N instances. `Spec.ldWf_err` (Cb/Ld/LdWf.lean) has
the errors of the first.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectLinkFull
import Cb.Obj.LdObjectLinFullProofs
import Cb.Obj.LdObjectReqSeg
import Ior.KnowCollRulesChainErr

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Spec

/-- One whole test on a group. -/
def ldOErr_run : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (St₀ Wp : Type) (E₀ : ExtSpec)
      (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp),
    (D.link A₀ d d').errs = (D.L * D.Z.err) :: D.T.N.err.toList ∧
    (D.link A₀ d d').chs = @Fintype.card D.Z.D D.Z.fin :: D.T.R.shape.chalList

/-- a plan that begins with the test D -/
def ldOErr_cons : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (D : LdRunD S)
      (Q : LdTc (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp),
    (LdTc.cons D Q d d').c.errs = (D.L * D.Z.err) :: D.T.N.err.toList ++ Q.c.errs ∧
    (LdTc.cons D Q d d').c.chs = @Fintype.card D.Z.D D.Z.fin :: D.T.R.shape.chalList ++ Q.c.chs

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The link, any closing chain. -/
def ldOErr_linkC : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (K : Cf.LinkPar) (S : K.P.Snd) (ε₀ ε₁ : ℕ)
      (cZ : Chain Unit K.P.J4 ldJT) (d : K.P.W0),
    (K.nums (K.ofChainC S ε₀ ε₁ cZ d)).err.toList =
      [K.P.errGam ε₀ ε₁, ldSendFamErr K.P.N S.Sd S.L, 0, K.P.errLoc, K.P.errPhi] ++ cZ.errs ∧
    (K.link (K.ofChainC S ε₀ ε₁ cZ d)).shape.chalList =
      [Fintype.card K.P.Gam, Fintype.card S.Sd.D, Fintype.card Unit,
          Fintype.card ((Fin K.t₀ → Fin Cf.C₀.n) × (Fin K.t₁ → Fin Cf.C₀.n)),
          Fintype.card (Fin K.l → E)] ++ cZ.chs

/-- The link with its closing. -/
def ldOErr_link : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (K : Cf.LinkPar) (S : K.P.Snd) (ε₀ ε₁ : ℕ)
      (Kc : K.P.Cl) (d₂ : K.P.W2) (d : K.P.W0),
    (K.nums (K.full S ε₀ ε₁ Kc d₂ d)).err.toList =
      [K.P.errGam ε₀ ε₁, ldSendFamErr K.P.N S.Sd S.L, 0, K.P.errLoc, K.P.errPhi, Kc.L * Kc.Z.err] ++
        Kc.T.N.err.toList

/-- The test at one instance with its closing. -/
def ldOErr_lin : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (εf : ℕ) (Sn : O.toC.P.Snd)
      (Qt : LdTc O.toC.S O.toC.E₀ O.toC.Wpa) (fq : O.toC.St6 → Qt.St) (d : O.toC.P.W0),
    (O.numsF Sn εf Qt fq d).err.toList =
      [ldSendFamErr O.toC.P.NW O.toC.P.SdW Sn.LW, 0, O.toC.P.errPt εf,
          ldSendFamErr O.toC.P.NU O.toC.P.SdU Sn.LU, 0, O.toC.P.errLoc,
          ldSendFamErr O.toC.P.NO O.toC.P.SdO Sn.LO, 0, O.toC.P.errZeta] ++ Qt.c.errs

/-- The preamble of a request built of segments (`O.termOf`: the case without a ghost): the errors
of all links of its chain, in a row. -/
def ldOErr_req : Prop :=
  ∀ (O : LdOL F E) (Kc : Type) (core : O.Cf.conf.PIdx × O.Cf.conf.Cells → Kc)
      (core' : O.S.Msg × O.Cf.conf.PIdx → Kc) (r : O.Req core core')
      (w₀ : O.Cf.conf.PIdx × O.Cf.conf.Cells),
    (O.termOf r w₀).nums.err.toList = r.chain.errs ∧
    (O.termOf r w₀).req.shape.chalList = r.chain.chs

end
end Spec

theorem ldOErr_run : Spec.ldOErr_run := by
  intro E _ _ S D St₀ Wp E₀ A₀ d d'
  constructor
  · show Err.toList
        (Err.app (ldBridgeN D.G D.kp D.Sb D.Z St₀ E₀ Unit (D.L * D.Z.err)).err
          (Err.app (s := D.T.R.shape) (t := []) D.T.N.err ())) = _
    rw [Err.toList_app, Err.toList_app]
    show [D.L * D.Z.err] ++ (D.T.N.err.toList ++ []) = _
    rw [List.append_nil]
    rfl
  · show Shape.chalList ((ldBridge D.G D.kp D.Sb D.Z St₀ E₀).shape ++ (D.T.R.shape ++ [])) = _
    rw [Shape.chalList_append, List.append_nil]
    rfl

theorem ldOErr_cons : Spec.ldOErr_cons := by
  intro E _ _ S E₀ Wp D Q d d'
  constructor
  · show ((Chain.one (D.link Q.base d d')).append Q.c).errs = _
    rw [(chainErr_append _ _ _ _ _ _).1, Chain.errs_one, (ldOErr_run E S D _ _ _ Q.base d d').1]
  · show ((Chain.one (D.link Q.base d d')).append Q.c).chs = _
    rw [(chainErr_append _ _ _ _ _ _).2, Chain.chs_one, (ldOErr_run E S D _ _ _ Q.base d d').2]

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldOErr_linkC : Spec.ldOErr_linkC F E := by
  intro Cf _ K S ε₀ ε₁ cZ d
  constructor
  · show (K.P.linkC K.free K.free S ε₀ ε₁ cZ d).errs = _
    unfold LdLkP.linkC LdLkP.coreC
    rw [(chainErr_link _ _ _ _ _).1, (chainErr_append _ _ _ _ _ _).1,
      Chain.errs_snoc, Chain.errs_snoc, Chain.errs_snoc, Chain.errs_one]
    rfl
  · show (K.P.linkC K.free K.free S ε₀ ε₁ cZ d).chs = _
    unfold LdLkP.linkC LdLkP.coreC
    rw [(chainErr_link _ _ _ _ _).2, (chainErr_append _ _ _ _ _ _).2,
      Chain.chs_snoc, Chain.chs_snoc, Chain.chs_snoc, Chain.chs_one]
    rfl

theorem ldOErr_link : Spec.ldOErr_link F E := by
  intro Cf _ K S ε₀ ε₁ Kc d₂ d
  have h := (ldOErr_linkC F E Cf K S ε₀ ε₁ (Kc.cZ d₂) d).1
  have hc : (Kc.cZ d₂).errs = (Kc.L * Kc.Z.err) :: Kc.T.N.err.toList := by
    unfold LdLkP.Cl.cZ
    rw [(chainErr_append _ _ _ _ _ _).1, Chain.errs_one]
    show [] ++ (LdTc.cons Kc.run _ _ _).c.errs = _
    rw [(ldOErr_cons E _ _ _ Kc.run _ _ _).1]
    show [] ++ ((Kc.L * Kc.Z.err) :: Kc.T.N.err.toList ++ (Chain.one _).errs) = _
    rw [Chain.errs_one]
    show (Kc.L * Kc.Z.err) :: (Kc.T.N.err.toList ++ []) = _
    rw [List.append_nil]
  rw [hc] at h
  exact h

theorem ldOErr_lin : Spec.ldOErr_lin F E := by
  intro O _ εf Sn Qt fq d
  show (O.toC.P.linC O.on0 Sn εf (O.toC.cZ Qt fq) d).errs = _
  unfold LdLinP.linC LdLinP.chain LdLinC.cZ LdLinC.chain
  rw [(chainErr_link _ _ _ _ _).1, (chainErr_append _ _ _ _ _ _).1,
    Chain.errs_snoc, Chain.errs_snoc, Chain.errs_snoc, Chain.errs_snoc,
    Chain.errs_snoc, Chain.errs_snoc, Chain.errs_one]
  have h2 : ((Chain.one (O.toC.link fq Qt.base)).append Qt.c).errs = Qt.c.errs := by
    rw [(chainErr_append _ _ _ _ _ _).1, Chain.errs_one]
    rfl
  erw [h2]
  rfl

theorem ldOErr_req : Spec.ldOErr_req F E := fun _ _ _ _ r _ => chainErr_link _ _ _ r.chain _

end
end Cb
