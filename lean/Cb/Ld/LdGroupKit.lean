-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupKit.lean: a rule for composing interactive oracle reductions.

In standard terms: a protocol is built as a chain of interactive oracle reductions. Often one of
them works on a part of the statement, while a further part of statement, oracles and witness is
passed on unchanged. This file shows that a reduction with the properties that the chain's
composition rules ask of each step still has them when it is read on the whole statement; the rule
is stated for a reduction between joints of core type `Unit`.

Definitions, statements (in `Iop.Spec`) and proofs. No protocol, no code occurs here.
Ior/KnowCollRulesFrame.lean has the rule "any reduction beside a carried part" for the bundle
`IOR.GoodT`. A chain is made of pieces (`PieceTr`, Cb/Ld/LdTowerKit.lean, is: `GoodT`; nothing
hidden is withheld; nothing is tied; the budgets bear what follows). Here is the same rule for
pieces. `PieceTr`, a piece of a chain, asks of a reduction between two joints the bundle `IOR.GoodT`
and three further clauses, `noHid`, `noTie` and `bears`, which Cb/Ld/LdTowerKit.lean states (`bears`
through `IOR.Bears`, Ior/Bears.lean); `IOR.Piece` (Ior/Tail.lean) asks the same over `IOR.Good`.

Main names:
  `Spec.pieceTr_beside`: the rule.

Why: what follows needs the carried oracles exactly where it reads them; R adds nothing there.

Limits: the rule is conditional; it gives no protocol.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdTowerKit
import Ior.KnowCollRulesFrameProofs
import Ior.BearsProofs

set_option autoImplicit false

namespace Iop
open Prob

/-- For two kinds of oracles side by side: the demand q on the set of positions on the left and the
demand qF on that on the right. -/
def besideQ {E F : ExtSpec} (q : Finset E.Pos → Prop) (qF : Finset F.Pos → Prop) :
    Finset (E.prod F).Pos → Prop :=
  fun U => q U.toLeft ∧ qF U.toRight

namespace Spec
open IOR

/-- States: if R is a piece from A to B (A, B and the numbers of R have the core type `Unit`), from
sets within qo to sets within qi, then `R.keep Z F`, whose honest prover passes the carried witness
on, is a piece from `A.beside S` to `B.beside S`, from sets within `besideQ qo qF` to sets within
`besideQ qi qF`, for every joint S (`S : Rels K Z F Wz`) and every demand qF on the carried
oracles. -/
def pieceTr_beside : Prop :=
  ∀ (K Xi Xo Z : Type) (Ei Eo F : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wz : Type)
      (H : R.Honest Wi Wo) (A : Rels Unit Xi Ei Wi) (B : Rels Unit Xo Eo Wo)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums Unit R) (S : Rels K Z F Wz)
      (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop) (qF : Finset F.Pos → Prop),
    PieceTr R H A B ext P qi qo →
    PieceTr (R.keep Z F) ((H.keep Z F).carry Wz) (A.beside S) (B.beside S)
      (fun a τ w => (ext (a.1.1, a.2.1) τ w.1, w.2)) (P.beside K Z F)
      (besideQ qi qF) (besideQ qo qF)

end Spec

open IOR

section
variable {Xi Xo Z : Type} {Ei Eo F : ExtSpec} (R : IOR Xi Ei Xo Eo)

open Classical in
/-- the sources, in the prover's oracles, of a set of positions of the two kinds: those of its left
part -/
theorem keep_srcO (ρ : Rho R.shape) (U : Finset (Eo.prod F).Pos) :
    U.biUnion ((R.keep Z F).srcO ρ) = U.toLeft.biUnion (R.srcO ρ) := by
  ext p
  refine Finset.mem_biUnion.trans (Iff.trans ?_ Finset.mem_biUnion.symm)
  constructor
  · rintro ⟨u, hu, hp⟩
    rcases u with u | u
    · exact ⟨u, Finset.mem_toLeft.2 hu, hp⟩
    · exact absurd hp (Finset.notMem_empty _)
  · rintro ⟨u, hu, hp⟩
    exact ⟨.inl u, Finset.mem_toLeft.1 hu, hp⟩

theorem keep_mem_given_inl (ρ : Rho R.shape) (T : Finset (OPos R.shape)) (q : Ei.Pos) :
    (Sum.inl q : (Ei.prod F).Pos) ∈ (R.keep Z F).given ρ T ↔ q ∈ R.given ρ T := by
  rw [mem_given, mem_given]
  constructor
  · rintro (h | ⟨p, hp, h⟩)
    · obtain ⟨q', hq', he⟩ := Finset.mem_map.1 h
      exact Or.inl ((Sum.inl.inj he) ▸ hq')
    · obtain ⟨q', hq', he⟩ := Finset.mem_map.1 h
      exact Or.inr ⟨p, hp, (Sum.inl.inj he) ▸ hq'⟩
  · rintro (h | ⟨p, hp, h⟩)
    · exact Or.inl (Finset.mem_map.2 ⟨q, h, rfl⟩)
    · exact Or.inr ⟨p, hp, Finset.mem_map.2 ⟨q, h, rfl⟩⟩

theorem keep_not_mem_given_inr (ρ : Rho R.shape) (T : Finset (OPos R.shape)) (q : F.Pos) :
    (Sum.inr q : (Ei.prod F).Pos) ∉ (R.keep Z F).given ρ T := by
  rw [mem_given]
  rintro (h | ⟨p, _, h⟩)
  · obtain ⟨q', _, he⟩ := Finset.mem_map.1 h
    cases he
  · obtain ⟨q', _, he⟩ := Finset.mem_map.1 h
    cases he

/-- what is needed on the left is what R needs; what is needed on the right is what follows reads
there (`keep_need_right`) -/
theorem keep_need_left (ρ : Rho R.shape) (U : Finset (Eo.prod F).Pos) :
    ((R.keep Z F).need ρ U).toLeft = R.need ρ U.toLeft := by
  ext q
  rw [Finset.mem_toLeft, mem_need, mem_need, keep_srcO, keep_mem_given_inl]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨u, hu, hq⟩
    rcases u with u | u
    · obtain ⟨q', hq', he⟩ := Finset.mem_map.1 hq
      exact ⟨u, Finset.mem_toLeft.2 hu, (Sum.inl.inj he) ▸ hq'⟩
    · exact absurd (Finset.mem_singleton.1 hq) (by simp)
  · rintro ⟨u, hu, hq⟩
    exact ⟨.inl u, Finset.mem_toLeft.1 hu, Finset.mem_map.2 ⟨q, hq, rfl⟩⟩

theorem keep_need_right (ρ : Rho R.shape) (U : Finset (Eo.prod F).Pos) :
    ((R.keep Z F).need ρ U).toRight = U.toRight := by
  ext q
  rw [Finset.mem_toRight, Finset.mem_toRight, mem_need]
  constructor
  · rintro (h | ⟨u, hu, hq⟩)
    · exact absurd h (keep_not_mem_given_inr R ρ _ q)
    · rcases u with u | u
      · obtain ⟨q', _, he⟩ := Finset.mem_map.1 hq
        cases he
      · rw [Sum.inr.inj (Finset.mem_singleton.1 hq)]
        exact hu
  · exact fun h => Or.inr ⟨.inr q, h, Finset.mem_singleton_self _⟩

end

theorem pieceTr_beside : Spec.pieceTr_beside := by
  intro K Xi Xo Z Ei Eo F R Wi Wo Wz H A B ext P S qi qo qF h
  refine ⟨goodT_beside K Xi Xo Z Ei Eo F R Wi Wo Wz H A B ext P S h.good,
    fun w x => h.noHid w.1 x.1,
    fun ρ p => ?_,
    fun ρ U hU => ⟨?_, ?_, ?_⟩⟩
  · show (R.tie ρ p).map _ = ∅
    rw [h.noTie ρ p, Finset.map_empty]
  · rw [keep_srcO]
    exact (h.bears ρ U.toLeft hU.1).1
  · show qi ((R.keep Z F).need ρ U).toLeft
    rw [keep_need_left]
    exact (h.bears ρ U.toLeft hU.1).2
  · show qF ((R.keep Z F).need ρ U).toRight
    rw [keep_need_right]
    exact hU.2

end Iop
