-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseChain.lean: sequential composition of interactive oracle reductions: several
proximity tests on groups of oracles (whole tests), one after the other, given as a list of
sub-reductions (a chain of links).

In standard terms (Ior/KnowCollRulesChain.lean): a joint (`IOR.Joint`) fixes the types of statement,
oracles and witness at one point of a protocol, with an exact relation, a relaxed relation and a
condition on statements. A link (`IOR.Link`) is an interactive oracle reduction from one joint to
the next, with its honest prover, its extractor and its numbers. A chain is a sequence of links,
composed one after the other.
`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge.

Definitions, statements and proofs (an assembly).

Why: Cb/Ld/LdLinCloseRuns.lean puts the tests of a closing in a row as one reduction (`LdTl`;
`LdTl.OK`: it is a tail). A closing that also holds a splitting whose masks were sent earlier is no
tail by itself (the head of Cb/Ld/LdTowerKitChain.lean): a sub-protocol then takes its closing as a
chain of links (Ior/KnowCollRulesChain.lean) that stands behind its core. Here the tests are given
in that form; nothing new is proved about them.

Main names:
  `S.jointCf A`: the joint over the signature S with the base joint A, with its types, the condition
    ("collision-free", and the base joint's own condition) moved into the relaxed relation
    (`Rels.cf`): the form in which chains are made after a sending.
  `Spec.ldChain_link`: if `D.OK` (`LdRunD.OK`, Cb/Ld/LdLinCloseRuns.lean: what is asked of one
    test), the link `D.link` (of `ldRunE`, Cb/Ld/LdLinCloseRun.lean) has the whole bundle (`GoodT`)
    and the budgets' half of a piece that may tie (`SideC`, Cb/Ld/LdTowerKitChain.lean: the clauses
    `noHid`, `tied`, `free`, `bears` of `ClosedTr`, Cb/Ld/LdLinCloseKit.lean, without its bundle);
    the half stands between two demands on positions: at the output: qF, what follows needs of the
    kept and further oracles; at the input: any demand qi that covers, beside qF, one position of
    each member for each of at most `D.t` common long positions. The arguments d, d' of `D.link` and
    `LdTc.cons` are the extractor's values where nothing was output (`ldRunEX`,
    Cb/Ld/LdLinCloseRun.lean).
  `LdTc S E₀ Wp`: a closing of a statement over S as a chain: the explicit part beside the samples,
    the base joint, the chain down to the trivial statement, what is needed of the oracles.
  `Q.OK`: every link has the whole bundle (`Q.c.AllT`); the halves fit along the chain, the last
    link's being that of a last piece (`Q.c.SidesCT Q.q`).
  `Spec.ldChain_nil`: if S has no oracle message, `LdTc.nil` is OK.
  `Spec.ldChain_behind`: a closing that is OK comes after every chain (`OkFrom`), and has `SidesCT`:
    the two hypotheses of `Spec.chain_tail_append` on its closing chain.
  `Spec.ldChain_after`: if `c₀.Ok` and `Q.OK`, links in front of it (steps without rounds,
    batchings, splittings: a chain c₁ with `OkFrom` c₀ and `SidesC`) may be put before it:
    `c₁.append Q.c` has `OkFrom` c₀ and `SidesCT`.

Limits: this file says nothing on a splitting, nothing on rows of a protocol. What the heads of
Cb/Ld/LdLinCloseRun.lean and Cb/Ld/LdLinCloseRuns.lean list as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinCloseRunsProofs
import Cb.Ld.LdTowerKitChain
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood

/-- the trivial statement, as a joint with its types -/
abbrev ldTrivJ : Joint Unit := ⟨Unit, extNone, Unit, trivRels⟩

/-- The joint over S with the base joint A, with its types; the condition may fail. -/
abbrev Sig.jointCf {E : Type} [Field E] (S : Sig E) {St Wp : Type} {E₀ : ExtSpec}
    (A : IOR.Rels Unit St E₀ (S.Msg × Wp)) : Joint Unit :=
  ⟨St × S.Smp, E₀.prod S.ext, S.Wit × Wp, (S.over A).cf⟩

section
variable {E : Type} [Field E] [Fintype E] {S : Sig E}

/-- the base joint in front of the test D: D's rows on its group's message, and A₀ of the kept
messages -/
abbrev LdRunD.pre (D : LdRunD S) {St₀ Wp : Type} {E₀ : ExtSpec}
    (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) :
    IOR.Rels Unit (((D.B → E) × (∀ b, D.Sb b)) × St₀) E₀ (S.Msg × Wp) :=
  claimRels (fun x m => Slf.All D.sl x (D.G.msg m)) (onMsgRels (S.res (T := OMsg.Msg) D.kp) A₀)

/-- One whole test on a group, beside what is carried, as a link. -/
def LdRunD.link (D : LdRunD S) {St₀ Wp : Type} {E₀ : ExtSpec}
    (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) :
    Link Unit (S.jointCf (D.pre A₀)) ((S.sub D.kp).jointCf A₀) :=
  ⟨ldRunE D.G D.kp D.Sb D.sl D.Z St₀ E₀ D.T,
    ldRunEH D.G D.kp D.Sb D.sl D.Z St₀ Wp E₀ D.T,
    ldRunEX D.G D.kp D.Sb D.sl D.Z St₀ Wp E₀ D.T D.hc d d',
    ldRunEN D.G D.kp D.Sb D.sl D.Z St₀ E₀ D.T Unit (D.L * D.Z.err)⟩

end

/-- A closing of a statement over S, as a chain: the data. -/
structure LdTc {E : Type} [Field E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) where
  St   : Type
  base : IOR.Rels Unit St E₀ (S.Msg × Wp)
  c    : Chain Unit (S.jointCf base) ldTrivJ
  q    : Finset (E₀.prod S.ext).Pos → Prop

namespace LdTc
variable {E : Type} [Field E] {S : Sig E} {E₀ : ExtSpec} {Wp : Type}

/-- every link has the whole bundle; the budgets' halves fit along the chain -/
def OK (Q : LdTc S E₀ Wp) : Prop := Q.c.AllT ∧ Q.c.SidesCT Q.q

/-- For a signature without oracle messages (`[IsEmpty S.O]`: `Spec.ldChain_nil`): no oracle message
is left, nothing is claimed. -/
def nil (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (w₀ : S.Wit × Wp) : LdTc S E₀ Wp where
  St := Unit
  base := (LdTl.nil S E₀ Wp w₀).base
  c := .one ⟨(LdTl.nil S E₀ Wp w₀).R, (LdTl.nil S E₀ Wp w₀).H,
      (LdTl.nil S E₀ Wp w₀).ext, (LdTl.nil S E₀ Wp w₀).N⟩
  q := (LdTl.nil S E₀ Wp w₀).q

variable [Fintype E]

open Classical in
/-- The test D, then the closing Q of what is kept. -/
def cons (D : LdRunD S) (Q : LdTc (S.sub D.kp) E₀ Wp)
    (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) : LdTc S E₀ Wp where
  St := ((D.B → E) × (∀ b, D.Sb b)) × Q.St
  base := D.pre Q.base
  c := (Chain.one (D.link Q.base d d')).append Q.c
  q := fun V =>
    ∃ U,
      besideQ ((D.G.joint D.Sb D.sl D.Z).atMost D.t) Q.q U ∧ V = U.biUnion (ldBrG D.G D.kp E₀).src

end LdTc

namespace Spec

open Classical in
/-- One whole test as a link: the whole bundle, and the budgets' half of a piece that may tie. -/
def ldChain_link : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (St₀ Wp : Type) (E₀ : ExtSpec)
      (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp)
      (qi : Finset (E₀.prod S.ext).Pos → Prop) (qF : Finset (LdCarE D.kp E₀).Pos → Prop),
    D.OK → (∀ U, besideQ ((D.G.joint D.Sb D.sl D.Z).atMost D.t) qF U →
      qi (U.biUnion (ldBrG D.G D.kp E₀).src)) →
    (D.link A₀ d d').GoodT ∧ (D.link A₀ d d').SideC qi qF

def ldChain_nil : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) [IsEmpty S.O] (E₀ : ExtSpec) (Wp : Type) (w₀ : S.Wit × Wp),
    (LdTc.nil S E₀ Wp w₀).OK

/-- States: if `D.OK` and `Q.OK`, a test, then a closing of what is kept, is a closing that is
OK. -/
def ldChain_cons : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (D : LdRunD S)
      (Q : LdTc (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp),
    D.OK → Q.OK → (LdTc.cons D Q d d').OK

/-- States: a closing that is OK comes after every chain. -/
def ldChain_behind : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (Q : LdTc S E₀ Wp)
      (Z : Joint Unit) (c₀ : Chain Unit Z (S.jointCf Q.base)),
    Q.OK → Q.c.OkFrom c₀ ∧ Q.c.SidesCT Q.q

/-- Links in front of a closing. -/
def ldChain_after : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (Q : LdTc S E₀ Wp)
      (Z A : Joint Unit) (c₀ : Chain Unit Z A)
      (c₁ : Chain Unit A (S.jointCf Q.base)) (qa : Finset A.E.Pos → Prop),
    c₀.Ok → Q.OK → c₁.OkFrom c₀ → c₁.SidesC qa Q.q →
    (c₁.append Q.c).OkFrom c₀ ∧ (c₁.append Q.c).SidesCT qa

end Spec

theorem ldChain_link : Spec.ldChain_link := by
  intro E _ _ S D St₀ Wp E₀ A₀ d d' qi qF hD hq
  have h := closedTr_cf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (ldClose_run E D.B Unit St₀ Wp S D.G D.kp D.Sb D.sl D.Z D.L E₀ A₀ D.hc d d' D.T D.t qi qF hD.ev
      hD.list hD.fits hD.tail hq)
  exact ⟨h.good, h.noHid, h.tied, h.free, h.bears⟩

theorem ldChain_nil : Spec.ldChain_nil := by
  intro E _ S _ E₀ Wp w₀
  have h := ldRuns_cf E S E₀ Wp (LdTl.nil S E₀ Wp w₀) (ldRuns_nil E S E₀ Wp w₀)
  exact ⟨(Chain.allT_one _).2 h.good, (Chain.sidesCT_one _ _).2 ⟨h.noHid, h.tied, h.bears⟩⟩

theorem ldChain_cons : Spec.ldChain_cons := by
  intro E _ _ S E₀ Wp D Q d d' hD hQ
  obtain ⟨h1, h2⟩ :=
    ldChain_link E S D Q.St Wp E₀ Q.base d d' (LdTc.cons D Q d d').q Q.q hD fun U hU => ⟨U, hU, rfl⟩
  exact ⟨((all_append Unit _ _ _ (Chain.one (D.link Q.base d d')) Q.c).2).2
      ⟨(Chain.allT_one _).2 h1, hQ.1⟩,
    sidesCT_append Unit _ _ _ (Chain.one (D.link Q.base d d')) Q.c _ Q.q
      ((Chain.sidesC_one _ _ _).2 h2) hQ.2⟩

theorem ldChain_behind : Spec.ldChain_behind := fun _ _ _ _ _ Q Z c₀ hQ =>
  ⟨okFrom_of_ok Unit Z _ _ c₀ Q.c ((ok_of_allT Unit _ _ Q.c).1 hQ.1), hQ.2⟩

/-- putting chains in a row is associative -/
theorem ldChain_assoc {K : Type} {A B C D : Joint K} (c₀ : Chain K A B)
    (c₁ : Chain K B C) (c₂ : Chain K C D) :
    (c₀.append c₁).append c₂ = c₀.append (c₁.append c₂) := by
  induction c₂ with
  | one l => rw [Chain.append_one, Chain.append_one, Chain.append_snoc]
  | snoc c l ih => rw [Chain.append_snoc, Chain.append_snoc, Chain.append_snoc, ih]

theorem ldChain_after : Spec.ldChain_after := by
  intro E _ S E₀ Wp Q Z A c₀ c₁ qa h₀ hQ h₁ s₁
  refine ⟨?_, sidesCT_append Unit _ _ _ c₁ Q.c qa Q.q s₁ hQ.2⟩
  have e1 : (c₀.append c₁).Ok := (ok_append Unit Z A _ c₀ c₁).2 ⟨h₀, h₁⟩
  have e2 : ((c₀.append c₁).append Q.c).Ok :=
    (ok_append Unit Z _ _ (c₀.append c₁) Q.c).2
      ⟨e1, (ldChain_behind E S E₀ Wp Q Z (c₀.append c₁) hQ).1⟩
  rw [ldChain_assoc] at e2
  exact ((ok_append Unit Z A _ c₀ (c₁.append Q.c)).1 e2).2

end Cb
