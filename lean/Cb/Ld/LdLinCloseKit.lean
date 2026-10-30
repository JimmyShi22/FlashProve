-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseKit.lean: rules for the sequential composition of interactive oracle reductions, for
a sub-reduction that is itself a whole proximity test and is followed by further sub-reductions (a
piece that may tie).

Definitions, statements and proofs. No protocol, no code occurs here.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Why: Cb/Ld/LdTowerKit.lean makes chains of pieces (`PieceTr`) that end in a tail (`TailTr`). A piece
ties nothing (`IOR.tie`, Ior/Ior.lean): no position of its oracles gives away a symbol of its input
(data: see `given`, Ior/Honest.lean). A whole proximity test is a tail: its last block does tie
positions of a mask oracle to positions of its input, and its verifier reads what is tied to the
positions that it reads (`IOR.Tied`).
`R.tie ρ p` is a finite set of positions of the implicit instance, for each ρ and each position p of
the prover's oracles; it enters `R.given`. `R.given ρ T` is the set of positions of the implicit
instance that the verifier reads at ρ, together with `R.tie ρ p` for every p that the verifier reads
in the prover's oracles or that is in T. `R.Tied`: for every ρ and every position p that the
verifier reads in the prover's oracles, `R.tie ρ p` lies within the positions that the verifier
reads in the implicit instance.
A protocol may run several whole tests in a row, each beside what the statement carries on, and go
on sending oracles after a test. Such a test is no piece, and the rules of Cb/Ld/LdTowerKit.lean do
not take it.
The rule "the verifier of the composition reads all that is tied to its positions"
(`Spec.tied_seq_free`) needs less of the first of two blocks than "it ties nothing". Of that block
it needs two things: (1) it is `Tied` itself; (2) it is free: those of its own oracle positions that
survive, as sources of a position of its new implicit instance, are tied to nothing. So whatever a
later verifier reads of them, and whatever is later tied to them, gives away nothing of the input.

Main names:
  `R.Free`, `R.Shut`: free; "shut": no position of the output has a source in R's oracles at all
    (then R is free: `Spec.free_of_shut`).
  `ClosedTr R H A B ext P qi qo`, a piece that may tie: the bundle `IOR.GoodT` (`good`); nothing
    hidden is withheld (`noHid`); R is `Tied` (`tied`); R is free (`free`); R bears what follows,
    from sets of positions within qo to sets within qi (`bears`).
    `IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with
    its honest side, between two joints, at given numbers; among its clauses: completeness between
    the honest relations, outside sets of verifier randomness whose probabilities further clauses
    bound by the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations,
    on the input joint's set of statements, with a given extractor, at the numbers' list of errors;
    and one on honest-verifier zero knowledge.
    `R.Bears bud qi qo`: for every ρ and every set U of positions of the new implicit instance for
    which qo holds, `bud ρ` holds of the positions `R.srcO ρ q` for q in U, and qi holds of
    `R.need ρ U`. (`need`: Ior/Bears.lean; `srcO`: a field of `IOR`, Ior/Ior.lean.)
  `Spec.tied_seq_free`: R₁ `Tied` and free, R₂ `Tied` ⇒ `R₁.seq R₂` is `Tied`.
  `Spec.tieFree_seq`: free, then free, is free.
  `Spec.closedTr_of_piece`: every piece of Cb/Ld/LdTowerKit.lean is one (it ties nothing).
  `Spec.closedTr_seq`: one, then another, is one: errors in a row, probabilities added, budgets
    composed, extractors composed. So sendings, steps without rounds, draws and whole tests may
    follow each other in any order.
  `Spec.tailTr_consC`: one, then a tail, is a tail.
  `Spec.closedTr_beside`, a tail beside a carried part is one: if Q is a tail from A to B (a
    statement without oracles; both with core type `Unit`), then `Q.keep Z F`, whose honest prover
    hands the carried witness on, leads from `A.beside S` to `B.beside S`, for every joint S and
    every demand qF on the carried oracles; it is shut.
  `Spec.closedTr_mono`: weaker demands on positions: a piece that may tie at qi, qo is one at every
    qi' that qi implies and every qo' that implies qo.
  `Spec.closedTr_cf`, `Spec.tailTr_cf`: the same blocks between the joints whose condition is moved
    into the relaxed relation (`Rels.cf`, Ior/KnowCollGood.lean): the form in which a chain is made
    after a block that is proved into a condition. For a tail: from `A.cf` to B itself, if B has no
    condition (∀ b, `B.on b`).

Limits: the rules are conditional; they give no protocol. Further reads of a test's own oracles by a
distinguisher are not in these notions (the head of Cb/Ld/LdTowerKit.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupKit

set_option autoImplicit false

namespace Iop
open Prob

namespace IOR
variable {K Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type}

/-- Those of R's own oracle positions that survive in its output are tied to nothing. -/
def Free (R : IOR Xi Ei Xo Eo) : Prop := ∀ ρ q, ∀ p ∈ R.srcO ρ q, R.tie ρ p = ∅

/-- None of R's own oracles survives in its output. -/
def Shut (R : IOR Xi Ei Xo Eo) : Prop := ∀ ρ q, R.srcO ρ q = ∅

/-- A piece of a chain that may tie. -/
structure ClosedTr (R : IOR Xi Ei Xo Eo) (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi)
    (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R)
    (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop) : Prop where
  good  : GoodT R H A B ext P
  noHid : ∀ w x, H.Hid w x = ∅
  tied  : R.Tied
  free  : R.Free
  bears : R.Bears P.bud qi qo

end IOR

namespace Spec
open IOR

def free_of_shut : Prop := ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo), R.Shut → R.Free

def tied_seq_free : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃),
    R₁.Tied → R₁.Free → R₂.Tied → (R₁.seq R₂).Tied

def tieFree_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃),
    R₁.Free → R₂.Free → (R₁.seq R₂).Free

/-- Every piece is a piece that may tie. -/
def closedTr_of_piece : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
      (P : Nums K R) (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop),
    PieceTr R H A B ext P qi qo → ClosedTr R H A B ext P qi qo

/-- A piece that may tie, then another, is a piece that may tie. -/
def closedTr_seq : Prop :=
  ∀ (K X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (A : Rels K X₁ E₁ W₁)
      (B : Rels K X₂ E₂ W₂) (C : Rels K X₃ E₃ W₃) (e₁ : X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁)
      (e₂ : X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂) (d : W₁) (P₁ : Nums K R₁) (P₂ : Nums K R₂)
      (qa : Finset E₁.Pos → Prop) (qb : Finset E₂.Pos → Prop) (qc : Finset E₃.Pos → Prop),
    ClosedTr R₁ H₁ A B e₁ P₁ qa qb → ClosedTr R₂ H₂ B C e₂ P₂ qb qc →
    ClosedTr (R₁.seq R₂) (H₁.seq H₂) A C (IOR.extSeq R₁ R₂ e₁ e₂ d) (P₁.seq P₂) qa qc

/-- A piece that may tie, then a tail, is a tail. -/
def tailTr_consC : Prop :=
  ∀ (K X₁ X₂ X₃ : Type) (E₁ E₂ : ExtSpec) (R : IOR X₁ E₁ X₂ E₂) (Q : IOR X₂ E₂ X₃ extNone)
      (W₁ W₂ W₃ : Type) (H₁ : R.Honest W₁ W₂) (H₂ : Q.Honest W₂ W₃) (A : Rels K X₁ E₁ W₁)
      (B : Rels K X₂ E₂ W₂) (C : Rels K X₃ extNone W₃) (e₁ : X₁ × E₁.Str → Tr R.shape → W₂ → W₁)
      (e₂ : X₂ × E₂.Str → Tr Q.shape → W₃ → W₂) (d : W₁) (P₁ : Nums K R) (P₂ : Nums K Q)
      (qa : Finset E₁.Pos → Prop) (qb : Finset E₂.Pos → Prop),
    ClosedTr R H₁ A B e₁ P₁ qa qb → TailTr Q H₂ B C e₂ P₂ qb →
    TailTr (R.seq Q) (H₁.seq H₂) A C (IOR.extSeq R Q e₁ e₂ d) (P₁.seq P₂) qa

/-- A tail beside a carried part is a piece that may tie; none of its oracles survives. -/
def closedTr_beside : Prop :=
  ∀ (K Xi Xo Z : Type) (Ei F : ExtSpec) (Q : IOR Xi Ei Xo extNone) (Wi Wo Wz : Type)
      (H : Q.Honest Wi Wo) (A : Rels Unit Xi Ei Wi) (B : Rels Unit Xo extNone Wo)
      (ext : Xi × Ei.Str → Tr Q.shape → Wo → Wi) (P : Nums Unit Q) (S : Rels K Z F Wz)
      (qi : Finset Ei.Pos → Prop) (qF : Finset F.Pos → Prop),
    TailTr Q H A B ext P qi →
    ClosedTr (Q.keep Z F) ((H.keep Z F).carry Wz) (A.beside S) (B.beside S)
      (fun a τ w => (ext (a.1.1, a.2.1) τ w.1, w.2)) (P.beside K Z F)
      (besideQ qi qF) (besideQ (fun _ => True) qF) ∧
    (Q.keep Z F).Shut

def closedTr_mono : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
      (P : Nums K R) (qi qi' : Finset Ei.Pos → Prop) (qo qo' : Finset Eo.Pos → Prop),
    ClosedTr R H A B ext P qi qo → (∀ S, qi S → qi' S) →
    (∀ U, qo' U → qo U) → ClosedTr R H A B ext P qi' qo'

/-- A piece that may tie carries the conditions of its joints. -/
def closedTr_cf : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
      (P : Nums K R) (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop),
    ClosedTr R H A B ext P qi qo → ClosedTr R H A.cf B.cf ext P qi qo

/-- A tail to a joint without a condition, from the joint whose condition may fail. -/
def tailTr_cf : Prop :=
  ∀ (K Xi Xo : Type) (Ei : ExtSpec) (Q : IOR Xi Ei Xo extNone) (Wi Wo : Type) (H : Q.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo extNone Wo) (ext : Xi × Ei.Str → Tr Q.shape → Wo → Wi)
      (P : Nums K Q) (qi : Finset Ei.Pos → Prop),
    (∀ b, B.on b) → TailTr Q H A B ext P qi → TailTr Q H A.cf B ext P qi

end Spec

open IOR

theorem free_of_shut : Spec.free_of_shut := fun _ _ _ _ _ h ρ q p hp => by
  rw [h ρ q] at hp
  exact absurd hp (Finset.notMem_empty _)

theorem tied_seq_free : Spec.tied_seq_free := by
  classical
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ h₁ hf h₂ ρ p hp q hq
  rcases left_or_right (s := R₁.shape) (t := R₂.shape) p with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · rw [seq_tie_left] at hq
    rcases (left_mem_seq_reads R₁ R₂ _ _).1 hp with hr | ⟨u, _, hu⟩
    · exact (mem_seq_extReads R₁ R₂ _ _).2 (Or.inl (h₁ _ r hr hq))
    · rw [hf _ u r hu] at hq
      exact absurd hq (Finset.notMem_empty _)
  · obtain ⟨e, he, hq⟩ := (mem_seq_tie_right R₁ R₂ _ _ _).1 hq
    rcases hq with hq | ⟨p₁, hp₁, hq⟩
    · exact (mem_seq_extReads R₁ R₂ _ _).2
        (Or.inr ⟨e, h₂ _ r ((right_mem_seq_reads R₁ R₂ _ _).1 hp) he, hq⟩)
    · rw [hf _ e p₁ hp₁] at hq
      exact absurd hq (Finset.notMem_empty _)

theorem tieFree_seq : Spec.tieFree_seq := by
  classical
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ h₁ h₂ ρ q p hp
  have hp' : p ∈
      ((R₂.srcE (Rho.snd (s := R₁.shape) ρ) q).biUnion (R₁.srcO (Rho.fst ρ))).image OPos.left ∪
        (R₂.srcO (Rho.snd (s := R₁.shape) ρ) q).image (OPos.right (s := R₁.shape)) := hp
  rcases Finset.mem_union.1 hp' with h | h
  · obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.1 hp₁
    rw [seq_tie_left]
    exact h₁ _ u p₁ hu
  · obtain ⟨p₂, hp₂, rfl⟩ := Finset.mem_image.1 h
    ext u
    constructor
    · intro hu
      obtain ⟨e, he, _⟩ := (mem_seq_tie_right R₁ R₂ _ _ _).1 hu
      rw [h₂ _ q p₂ hp₂] at he
      exact absurd he (Finset.notMem_empty _)
    · intro hu
      exact absurd hu (Finset.notMem_empty _)

theorem closedTr_of_piece : Spec.closedTr_of_piece := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h =>
  ⟨h.good, h.noHid, fun ρ p _ => by rw [h.noTie ρ p]; exact Finset.empty_subset _,
    fun ρ _ p _ => h.noTie ρ p, h.bears⟩

theorem closedTr_seq : Spec.closedTr_seq := by
  intro K X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ A B C e₁ e₂ d P₁ P₂ qa qb qc h₁ h₂
  exact ⟨goodT_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂ d _ _ h₁.good h₂.good,
    noHid_seq _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.noHid h₂.noHid,
    tied_seq_free _ _ _ _ _ _ _ _ h₁.tied h₁.free h₂.tied,
    tieFree_seq _ _ _ _ _ _ _ _ h₁.free h₂.free,
    bears_seq _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.bears h₂.bears⟩

theorem tailTr_consC : Spec.tailTr_consC := by
  intro K X₁ X₂ X₃ E₁ E₂ R Q W₁ W₂ W₃ H₁ H₂ A B C e₁ e₂ d P₁ P₂ qa qb h₁ h₂
  exact ⟨goodT_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂ d _ _ h₁.good h₂.good,
    noHid_seq _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.noHid h₂.noHid,
    tied_seq_free _ _ _ _ _ _ _ _ h₁.tied h₁.free h₂.tied,
    bears_seq _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.bears h₂.bears⟩

theorem closedTr_beside : Spec.closedTr_beside := by
  classical
  intro K Xi Xo Z Ei F Q Wi Wo Wz H A B ext P S qi qF h
  have hs : (Q.keep Z F).Shut := fun ρ q => by
    rcases q with q | q
    · exact q.elim
    · rfl
  refine ⟨⟨goodT_beside K Xi Xo Z Ei extNone F Q Wi Wo Wz H A B ext P S h.good,
      fun w x => h.noHid w.1 x.1,
      fun ρ p hp => ?_,
      free_of_shut _ _ _ _ _ hs,
      fun ρ U hU => ⟨?_, ?_, ?_⟩⟩,
    hs⟩
  · show (Q.tie ρ p).map _ ⊆ (Q.extReads ρ).map _
    exact Finset.map_subset_map.2 (h.tied ρ p hp)
  · rw [keep_srcO]
    exact (h.bears ρ U.toLeft trivial).1
  · show qi ((Q.keep Z F).need ρ U).toLeft
    rw [keep_need_left]
    exact (h.bears ρ U.toLeft trivial).2
  · show qF ((Q.keep Z F).need ρ U).toRight
    rw [keep_need_right]
    exact hU.2

theorem closedTr_mono : Spec.closedTr_mono := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h hi ho =>
  ⟨h.good, h.noHid, h.tied, h.free,
    bears_mono _ _ _ _ _ _ _ _ _ _ _ h.bears (fun _ _ hb => hb) hi ho⟩

theorem closedTr_cf : Spec.closedTr_cf := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h =>
  ⟨goodT_cf _ _ _ _ _ _ _ _ _ _ _ _ _ h.good, h.noHid, h.tied, h.free, h.bears⟩

theorem tailTr_cf : Spec.tailTr_cf := fun K Xi Xo Ei Q Wi Wo H A B ext P _ hB h =>
  ⟨goodT_conseq K Xi Xo Ei extNone Q Wi Wo H A.cf A.cf B.cf B ext P P
      (goodT_cf _ _ _ _ _ _ _ _ _ _ _ _ _ h.good) (fun _ _ _ h => h) (fun _ _ _ h => h)
      (fun _ h => h) (fun b _ => hB b) (fun _ _ _ h => h) (fun _ _ h => Or.inl h) (fun _ => rfl)
      (fun _ => rfl) ⟨Err.le_refl _, le_refl _, le_refl _, fun _ _ h => h, fun _ => rfl⟩,
    h.noHid, h.tied, h.bears⟩

end Iop
