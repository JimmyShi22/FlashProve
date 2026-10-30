-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinChainVMask.lean: the honest prover of a batch (several instances proved in one run) along
a sequence of interactive oracle reductions, a chain some of whose links use masks that were sent
earlier in the chain. Continued from Cb/Ld/LdLinChainV.lean: two kinds of steps, and lemmas on their
composition.

Definitions, statements (`Iop.Spec.pv_iff` to `Iop.Spec.chainV_ok_end`) and proofs. Generic: no
protocol, no code occurs here. The analogue for batches of the second half of
Ior/KnowCollRulesChain.lean (`FreshFor`, `Ok`).
What a piece (`LinkV.PV`), a demand and the argument d are is told in the head of
Cb/Ld/LdLinChainV.lean.
The slots: j : `Fin N` (`BTr`, Iop/Batch.lean). In this head the shared part and a slot are the
parts of the honest prover (`SStratR`, `LStratR`, Ior/BatchSeqZk.lean; `HonestV.strat0`,
`HonestV.strat`, Ior/LinkV.lean); what the shared part of the prover holds: `JV.W0`,
Cb/Ld/LdLinChainV.lean.

Why: a link that hides what it sends in the clear by mask entries sent earlier (by the shared part,
or by a slot) is not zero knowledge by itself, so it is no piece (`LinkV.PV`). The rules for two in
a row (Ior/LinkVMasked.lean: `exactV_seq_masked`; Ior/LinkVMaskedRules.lean: `freshV_snd`,
`freshV_seq`) are iterated here, once and for all.

Main names:
  `v.PB`: all of a piece but zero knowledge: local (`isLocal`), complete for each slot (`acc`:
    `HonestV.AccV`, Ior/LinkV.lean: outside `v.hv.withheld`), bears what follows (`bears`: `BearsV`,
    Ior/LinkVBears.lean), and the demand at its end is kept by subsets of the set of slots (`her`).
  `v.PM D`: a masked link: `PB` (`base`); the item "masked messages" for sets of slots (`mm`:
    `MMV D`); the joint's relation gives the claim (`claim`); its budget asks nothing (`free`; it
    has no oracle).
  `c.FreshForV ..`: by recursion on the chain: the last link is `FreshV` on all its inputs (it sends
    the masks); or the last link does not look at them (`BlindV`, from some readings to these) and
    the chain before it is `FreshForV` those readings.
  `c.OkV`: the first link is a piece; every later link is a piece, or it is a masked link and the
    chain before it is `FreshForV` its readings and masks.
  `Spec.linkV_seq_masked`: a piece that is `FreshV`, then a masked link, is a piece.
  `Spec.chainV_fresh`: under `c.AllB` (M0, Mj nonempty): `FreshForV` of the chain gives `FreshV` of
    the chain as one link, on the chain's input relation, at its budget.
  `Spec.chainV_ok`: the flat statement: a chain each of whose links is of one of the two kinds, with
    these conditions (`c.OkV`), is a piece: complete, and exactly honest-verifier zero knowledge for
    sets of slots (`PieceV.exact`: `HonestV.ExactV`, Ior/LinkV.lean).
  `Spec.chainV_ok_end`: under `c.OkV`: so at its end, if the last demand holds of the empty family:
    exactly honest-verifier zero knowledge for sets of slots at no further reads, and what the
    simulator is given is within the first joint's demand.

Limits: the first link cannot be a masked link. This file says nothing on soundness. No chain is
given here. This file says nothing on running times: a simulator is any term of `SimV`
(Ior/LinkV.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinChainV
import Ior.LinkVMaskedProofs
import Ior.LinkVMaskedRulesSeq

set_option autoImplicit false

namespace Iop
open Prob

namespace IOR
variable {K : Type} {N : ℕ}

/-- All of a piece but zero knowledge. -/
structure LinkV.PB {A B : Joint K} {VA : JV N A} {VB : JV N B} (v : LinkV K N VA VB) : Prop where
  isLocal : v.a.l.R.IsLocal
  acc     : v.hv.AccV VA.rel VB.rel
  bears   : v.a.l.R.BearsV v.a.ann v.bud VA.q VB.q
  her     : VB.q.Her

/-- A masked link. -/
structure LinkV.PM {A B : Joint K} {VA : JV N A} {VB : JV N B}
    (v : LinkV K N VA VB) (D : MaskDataV v.a.l.R VA.W0 A.W N) : Prop where
  base  : v.PB
  mm    : v.hv.MMV D
  claim : ∀ x y w, VA.rel x y w → D.Cl (D.pub x) (D.k0 w.1) (D.kj w.2)
  free  : v.bud = fun _ _ _ => True

namespace ChainV

def AllB : {A B : Joint K} → {VA : JV N A} → {VB : JV N B} → ChainV K N VA VB → Prop
  | _, _, _, _, .one v => v.PB
  | _, _, _, _, .snoc c v => c.AllB ∧ v.PB

/-- After the chain the masks are fresh: the last link sends them, or it does not look at them and
they were fresh before it. -/
def FreshForV :
    {A B : Joint K} → {VA : JV N A} → {VB : JV N B} → ChainV K N VA VB → {K0 Kj : Type} →
    (VB.W0 → K0) → (B.W → Kj) → (M0 : Type) → [Fintype M0] → [Nonempty M0] → (M0 → K0 → K0) →
    (Mj : Type) → [Fintype Mj] → [Nonempty Mj] → (Mj → Kj → Kj) → Prop
  | _, _, VA, _, .one v, _, _, k0, kj, M0, _, _, put0, Mj, _, _, putj =>
    v.hv.FreshV N VA.rel v.bud k0 kj M0 put0 Mj putj
  | _, _, _, _, .snoc (B := B) (VB := VB) c v, _, _, k0, kj, M0, _, _, put0, Mj, _, _, putj =>
      v.hv.FreshV N VB.rel v.bud k0 kj M0 put0 Mj putj ∨
      ∃ (K0' Kj' : Type) (k0' : VB.W0 → K0') (kj' : B.W → Kj')
          (put0' : M0 → K0' → K0') (putj' : Mj → Kj' → Kj'),
        c.FreshForV k0' kj' M0 put0' Mj putj' ∧
        v.hv.BlindV k0' kj' k0 kj M0 Mj put0' putj' put0 putj

/-- Every link is of one of the two kinds, and a masked link's masks are fresh after the chain
before it. -/
def OkV : {A B : Joint K} → {VA : JV N A} → {VB : JV N B} → ChainV K N VA VB → Prop
  | _, _, _, _, .one v => v.PV
  | _, _, _, _, .snoc c v =>
    c.OkV ∧ (v.PV ∨
      ∃ D : MaskDataV v.a.l.R _ _ N, v.PM D ∧ c.FreshForV D.k0 D.kj D.M0 D.put0 D.Mj D.putj)

variable {A B C : Joint K} {VA : JV N A} {VB : JV N B} {VC : JV N C}
theorem allB_one (v : LinkV K N VA VB) : (ChainV.one v).AllB ↔ v.PB := by rw [AllB]
theorem allB_snoc (c : ChainV K N VA VB) (v : LinkV K N VB VC) :
    (c.snoc v).AllB ↔ c.AllB ∧ v.PB := by rw [AllB]
theorem okV_one (v : LinkV K N VA VB) : (ChainV.one v).OkV ↔ v.PV := by rw [OkV]
theorem okV_snoc (c : ChainV K N VA VB) (v : LinkV K N VB VC) :
    (c.snoc v).OkV ↔
    c.OkV ∧ (v.PV ∨
      ∃ D : MaskDataV v.a.l.R _ _ N, v.PM D ∧ c.FreshForV D.k0 D.kj D.M0 D.put0 D.Mj D.putj) := by
  rw [OkV]
theorem freshForV_one (v : LinkV K N VA VB) {K0 Kj : Type} (k0 : VB.W0 → K0) (kj : B.W → Kj)
    (M0 : Type) [Fintype M0] [Nonempty M0] (put0 : M0 → K0 → K0) (Mj : Type) [Fintype Mj]
    [Nonempty Mj] (putj : Mj → Kj → Kj) :
    (ChainV.one v).FreshForV k0 kj M0 put0 Mj putj ↔
    v.hv.FreshV N VA.rel v.bud k0 kj M0 put0 Mj putj := by rw [FreshForV]
theorem freshForV_snoc (c : ChainV K N VA VB) (v : LinkV K N VB VC) {K0 Kj : Type} (k0 : VC.W0 → K0)
    (kj : C.W → Kj) (M0 : Type) [Fintype M0] [Nonempty M0] (put0 : M0 → K0 → K0) (Mj : Type)
    [Fintype Mj] [Nonempty Mj] (putj : Mj → Kj → Kj) :
    (c.snoc v).FreshForV k0 kj M0 put0 Mj putj ↔
    (v.hv.FreshV N VB.rel v.bud k0 kj M0 put0 Mj putj ∨
      ∃ (K0' Kj' : Type) (k0' : VB.W0 → K0') (kj' : B.W → Kj')
          (put0' : M0 → K0' → K0') (putj' : Mj → Kj' → Kj'),
        c.FreshForV k0' kj' M0 put0' Mj putj' ∧
        v.hv.BlindV k0' kj' k0 kj M0 Mj put0' putj' put0 putj) := by rw [FreshForV]

end ChainV
end IOR

namespace Spec
open IOR

/-- A piece is all of a piece but zero knowledge, and honest-verifier zero knowledge. -/
def pv_iff : Prop :=
  ∀ (K : Type) (N : ℕ) (A B : Joint K) (VA : JV N A) (VB : JV N B) (v : LinkV K N VA VB),
    v.PV ↔ v.PB ∧ v.hv.ExactV N VA.rel v.bud

/-- Two in a row, all of it but the clause on zero knowledge. -/
def linkV_seq_b : Prop :=
  ∀ (K : Type) (N : ℕ) (A B C : Joint K) (VA : JV N A) (VB : JV N B) (VC : JV N C)
      (v : LinkV K N VA VB) (v' : LinkV K N VB VC) (d : A.W),
    v.PB → v'.PB → (v.seq v' d).PB

/-- A piece that is fresh for the masks, then a masked link, is a piece. -/
def linkV_seq_masked : Prop :=
  ∀ (K : Type) (N : ℕ) (A B C : Joint K) (VA : JV N A) (VB : JV N B) (VC : JV N C)
      (v : LinkV K N VA VB) (v' : LinkV K N VB VC) (d : A.W) (D : MaskDataV v'.a.l.R VB.W0 B.W N),
    v.PV → v.hv.FreshV N VA.rel v.bud D.k0 D.kj D.M0 D.put0 D.Mj D.putj → v'.PM D → (v.seq v' d).PV

def chainV_allB : Prop :=
  ∀ (K : Type) (N : ℕ) (A B : Joint K) (VA : JV N A) (VB : JV N B) (c : ChainV K N VA VB),
    c.OkV → c.AllB

def chainV_accB : Prop :=
  ∀ (K : Type) (N : ℕ) (A B : Joint K) (VA : JV N A) (VB : JV N B) (c : ChainV K N VA VB) (d : A.W),
    c.AllB → (c.linkV d).PB

def okV_of_allPV : Prop :=
  ∀ (K : Type) (N : ℕ) (A B : Joint K) (VA : JV N A) (VB : JV N B) (c : ChainV K N VA VB),
    c.AllPV → c.OkV

def chainV_fresh : Prop :=
  ∀ (K : Type) (N : ℕ) (A B : Joint K) (VA : JV N A) (VB : JV N B) (c : ChainV K N VA VB) (d : A.W)
      (K0 Kj : Type) (k0 : VB.W0 → K0) (kj : B.W → Kj) (M0 : Type) [Fintype M0] [Nonempty M0]
      (put0 : M0 → K0 → K0) (Mj : Type) [Fintype Mj] [Nonempty Mj] (putj : Mj → Kj → Kj),
    c.AllB → c.FreshForV k0 kj M0 put0 Mj putj →
    (c.linkV d).hv.FreshV N VA.rel (c.linkV d).bud k0 kj M0 put0 Mj putj

/-- The flat statement: a chain with `c.OkV` is, as one link, a piece. -/
def chainV_ok : Prop :=
  ∀ (K : Type) (N : ℕ) (A B : Joint K) (VA : JV N A) (VB : JV N B) (c : ChainV K N VA VB) (d : A.W),
    c.OkV → (c.linkV d).PV

/-- States what a chain with `c.OkV` has at the end, if the last demand holds of the empty
family. -/
def chainV_ok_end : Prop :=
  ∀ (K : Type) (N : ℕ) (A B : Joint K) (VA : JV N A) (VB : JV N B) (c : ChainV K N VA VB) (d : A.W),
    c.OkV → (∀ J, VB.q J fun _ => ∅) →
    (c.linkV d).a.l.R.IsLocal ∧
    (c.linkV d).hv.AccV VA.rel VB.rel ∧
    (c.linkV d).hv.ExactV N VA.rel (fun _ _ Ts => ∀ j, Ts j = ∅) ∧
    ∀ (J : Finset (Fin N)) (ρ : BRho N (c.linkV d).a.l.R.shape (c.linkV d).a.ann),
      VA.q J fun j => (c.linkV d).a.l.R.given (ρ.slot j.1) ∅

end Spec

open IOR IOR.ChainV

theorem pv_iff : Spec.pv_iff := fun _ _ _ _ _ _ _ =>
  ⟨fun h => ⟨⟨h.1.isLocal, h.1.acc, h.1.bears, h.2⟩, h.1.exact⟩,
    fun h => ⟨⟨h.1.isLocal, h.1.acc, h.2, h.1.bears⟩, h.1.her⟩⟩

theorem linkV_seq_b : Spec.linkV_seq_b := fun _ N _ _ _ VA VB VC v v' _ h h' =>
  { isLocal := isLocal_seq _ _ _ _ _ _ _ _ h.isLocal h'.isLocal
    acc := acc_seqV _ _ _ _ _ _ v.a.l.R v'.a.l.R v.a.ann v'.a.ann _ _ _ _ _ _ v.hv v'.hv VA.rel
      VB.rel VC.rel h.acc h'.acc
    bears := bearsV_seq _ _ _ _ _ _ v.a.l.R v'.a.l.R v.a.ann v'.a.ann N v.bud v'.bud VA.q VB.q
      VC.q h.bears h'.bears h'.her
    her := h'.her }

theorem linkV_seq_masked : Spec.linkV_seq_masked := by
  intro K N A B C VA VB VC v v' d D h hF hM
  have hB := ((pv_iff K N A B VA VB v).1 h).1
  refine (pv_iff K N A C VA VC (v.seq v' d)).2
    ⟨linkV_seq_b K N A B C VA VB VC v v' d hB hM.base, ?_⟩
  obtain ⟨S₁, hS₁⟩ := h.1.exact
  have h1 := exactV_seq_masked _ _ _ _ _ _ v.a.l.R v'.a.l.R v.a.ann v'.a.ann _ _ _ _ _ _ v.hv v'.hv
    VA.rel VB.rel N v.bud S₁ D hM.mm h.1.isLocal h.1.acc hS₁ hF hM.claim
  refine ⟨LinkVSeq.sim v.a.l.R v'.a.l.R v.hv.withheld S₁ (D.simOwnV hM.mm.noOrc), ?_⟩
  show (v.hv.seqV v'.hv).ExactVWith N VA.rel (budSeqV v.a.l.R v'.a.l.R v.bud v'.bud) _
  rw [hM.free]
  exact h1

theorem chainV_allB : Spec.chainV_allB := by
  intro K N A B VA VB c
  induction c with
  | one v =>
      rw [okV_one, allB_one]
      exact fun h => ((pv_iff _ _ _ _ _ _ v).1 h).1
  | snoc c v ih =>
      rw [okV_snoc, allB_snoc]
      refine fun h => ⟨ih h.1, ?_⟩
      rcases h.2 with h2 | ⟨D, h2, -⟩
      · exact ((pv_iff _ _ _ _ _ _ v).1 h2).1
      · exact h2.base

theorem chainV_accB : Spec.chainV_accB := by
  intro K N A B VA VB c d h
  induction c with
  | one v =>
      rw [linkV_one]
      exact (allB_one v).1 h
  | snoc c v ih =>
      rw [linkV_snoc]
      obtain ⟨h1, h2⟩ := (allB_snoc c v).1 h
      exact linkV_seq_b _ _ _ _ _ _ _ _ _ _ d (ih h1) h2

theorem okV_of_allPV : Spec.okV_of_allPV := by
  intro K N A B VA VB c
  induction c with
  | one v => rw [allPV_one, okV_one]; exact fun h => h
  | snoc c v ih =>
      rw [allPV_snoc, okV_snoc]
      exact fun h => ⟨ih h.1, Or.inl h.2⟩

theorem chainV_fresh : Spec.chainV_fresh := by
  intro K N A B VA VB c d
  induction c with
  | one v =>
      intro K0 Kj k0 kj M0 _ _ put0 Mj _ _ putj _ h
      rw [linkV_one]
      exact (freshForV_one v k0 kj M0 put0 Mj putj).1 h
  | snoc c v ih =>
      intro K0 Kj k0 kj M0 _ _ put0 Mj _ _ putj hB hF
      have gB := chainV_accB K N _ _ _ _ c d ((allB_snoc c v).1 hB).1
      rw [linkV_snoc]
      rcases (freshForV_snoc c v k0 kj M0 put0 Mj putj).1
        hF with hF | ⟨K0', Kj', k0', kj', put0', putj', hF, hBl⟩
      · exact freshV_snd _ _ _ _ _ _ (c.linkV d).a.l.R v.a.l.R (c.linkV d).a.ann v.a.ann _ _ _ _ _ _
          (c.linkV d).hv v.hv _ _ N (c.linkV d).bud v.bud K0 Kj k0 kj M0 put0 Mj putj gB.acc hF
      · exact freshV_seq _ _ _ _ _ _ (c.linkV d).a.l.R v.a.l.R (c.linkV d).a.ann v.a.ann _ _ _ _ _ _
          (c.linkV d).hv v.hv _ N (c.linkV d).bud v.bud K0' Kj' K0 Kj k0' kj' k0 kj M0 Mj put0'
          putj' put0 putj (ih K0' Kj' k0' kj' M0 put0' Mj putj' ((allB_snoc c v).1 hB).1 hF) hBl

theorem chainV_ok : Spec.chainV_ok := by
  intro K N A B VA VB c d
  induction c with
  | one v =>
      intro h
      rw [linkV_one]
      exact (okV_one v).1 h
  | snoc c v ih =>
      intro h
      obtain ⟨h1, h2⟩ := (okV_snoc c v).1 h
      rw [linkV_snoc]
      rcases h2 with h2 | ⟨D, h2, hF⟩
      · exact linkV_seq _ _ _ _ _ _ _ _ _ _ d (ih h1) h2
      · exact linkV_seq_masked _ _ _ _ _ _ _ _ _ _ d D (ih h1)
          (chainV_fresh K N _ _ _ _ c d _ _ D.k0 D.kj D.M0 D.put0 D.Mj D.putj
            (chainV_allB K N _ _ _ _ c h1) hF) h2

theorem chainV_ok_end : Spec.chainV_ok_end := fun K N A B VA VB c d h h0 =>
  pieceV_end _ _ _ _ _ _ _ _ _ _ (c.linkV d).hv N VA.rel VB.rel (c.linkV d).bud VA.q VB.q
    (chainV_ok K N A B VA VB c d h).1 h0

end Iop
