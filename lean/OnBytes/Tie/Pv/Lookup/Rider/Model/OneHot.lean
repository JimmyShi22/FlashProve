-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lookup/Rider/Model/OneHot.lean: identity j10 of a feed-forward segment, tested on the
challenges of the lookup of a sub-proof.

Statements and proofs. No protocol of its own. The term forB and its counts are those of
OnBytes/Tie/Pv/Lookup/Forest/FoHole.lean; the rule is `forB_ride`
(OnBytes/Tie/Pv/Lookup/Rider/ForB.lean); the arrays are those of Cb/G6/Rider/Model/OneHot.lean;
`outZt` is that of OnBytes/Tie/Pv/Lookup/Rider/Model/Zt.lean.
Main names:
  `hot_target_zt`: `AtCoords` of the family `hotFam` at the last D.lT places of `outZx`, in the
    names of the field relation.
  `hot_forB`: from `KnowAt` of forB between any two joints JA and JB, `KnowAt` of the same
    reduction, with the same extractor and the same counts, from JA and "`idnVal` is 0 at every
    valid `Idn.j10 l i`, for every embedding, prompt and flag" to JB and "for every l < D.ne the
    multilinear extension of i ↦ `idnVal` .. (.j10 l i) is 0 at the last D.lT places of `outZx`".
    Asked: D.lT ≤ h.dT. `cells`, how the cells are read off the caller's state and the tuple of
    messages, is a free letter.
  `hot_forB_in`: the same at forB's own joints, the first clause laid inside the relation R0 that
    rides along, at the input alone.
Limits: JA, JB, R0 and `cells` are free letters. If JA's relaxed relation without the first clause,
or JB's, already gives the first clause, the statement follows from its premise alone and says
nothing (`knowAt_hollow_own`, `knowAt_hollow_out`, Cb/G6/Rider/KnowAt.lean; `forB_hollow`). So a
caller whose R0 is a record of the segment's relation has to leave j10 out of it. No value of the
letters is given here at which the first clause fails while JA's relaxed relation holds. Nothing on
whether the programs test this target, on whether a later block takes it up, or on an honest prover.
-/
import OnBytes.Tie.Pv.Lookup.Rider.Model.Zt
import Cb.G6.Rider.Model.OneHot

set_option autoImplicit false

namespace Cb.Rider
open Iop Prob Cb Blocks Cb.LdLkp Cb.LdLkp.Kn TWhole Cb.Fo Inst.Model Inst.Model.FFSeg

/-- The target at the last D.lT places of the first part of the key point, in the names of the field
relation. -/
theorem hot_target_zt {E St St' J M : Type} [Field E] [scl : Scl] (h : Sh) (D : Dim)
    (hlt : D.lT ≤ h.dT) (cells : St → M → Cell → E) (st : St) (b : TX St' E J) (m : M) :
    AtCoords (fun _ : Fin D.ne => D.lT) (fun _ t => h.dT - D.lT + t) (hotFam D cells) st b.2.1.pt
        m ↔
      ∀ l, l < D.ne →
        ext D.lT (fun i => idnVal D (cells st m) (fun _ _ => 0) (fun _ => 0) (.j10 l i))
          (ofList (outZt h D.lT b)) = 0 := by
  rw [hot_target D cells (fun t => h.dT - D.lT + t) st b.2.1.pt m]
  refine forall_congr' fun l => imp_congr_right fun _ => Eq.congr_left ?_
  exact ext_congr_point (fun t ht => outZt_pt h hlt b ht) _

section Rule
variable {E : Type} [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]
  {h : Sh} {L : Lay E St₀ J₀} {Ex : ExtSpec} {Kc M Wp : Type} [scl : Scl]

/-- The identity j10 on the challenges of forB, between any two joints between which forB has
KnowAt. Warning: JA and JB are free (knowAt_hollow_own, knowAt_hollow_out). -/
theorem hot_forB {JA : IOR.Rels Kc St₀ Ex (M × Wp)}
    {JB : IOR.Rels Kc (TX (St₀ × E) E (Option J₀)) Ex (M × Wp)}
    {xt : M → St₀ × Ex.Str → Tr (forB E h L V₀ V₀C (Ex := Ex)).R.shape → Wp → Wp}
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R JA JB xt (forB E h L V₀ V₀C (Ex := Ex)).e)
    (D : Dim) (hlt : D.lT ≤ h.dT) (cells : St₀ → M → Cell → E) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (withRider JA fun m a =>
        ∀ (emb : ℕ → ℕ → E) (tok : ℕ → ℕ) (first : Bool) (l i : ℕ), (Idn.j10 l i).Valid D first →
          idnVal D (cells a.1 m) emb tok (.j10 l i) = 0)
      (withRider JB fun m b =>
        ∀ l, l < D.ne →
          ext D.lT (fun i => idnVal D (cells b.1.1.1 m) (fun _ _ => 0) (fun _ => 0) (.j10 l i))
            (ofList (outZt h D.lT b.1)) = 0)
      xt (forB E h L V₀ V₀C (Ex := Ex)).e :=
  knowAt_congr_rider (fun m a => hot_source D cells a.1 m)
    (fun m b => hot_target_zt h D hlt cells b.1.1.1 b.1 m)
    (forB_ride hK _ _ (selIn_last h hlt) (hotFam D cells))

variable {R0 : IOR.Rels Kc St₀ Ex (M × Wp)} {msg₀ : M → J₀ → E}

/-- The identity j10 on the challenges of forB, at forB's own joints: the first clause comes in
inside R0 and does not come out. Warning: R0 is free (forB_hollow): it has to be without j10. -/
theorem hot_forB_in
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e)
    (D : Dim) (hlt : D.lT ≤ h.dT) (cells : St₀ → M → Cell → E) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (forIn E h L (withRider R0 fun m a =>
        ∀ (emb : ℕ → ℕ → E) (tok : ℕ → ℕ) (first : Bool) (l i : ℕ), (Idn.j10 l i).Valid D first →
          idnVal D (cells a.1 m) emb tok (.j10 l i) = 0) msg₀)
      (withRider (forOut E h L R0 msg₀) fun m b =>
        ∀ l, l < D.ne →
          ext D.lT (fun i => idnVal D (cells b.1.1.1 m) (fun _ _ => 0) (fun _ => 0) (.j10 l i))
            (ofList (outZt h D.lT b.1)) = 0)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e :=
  forIn_in (hot_forB hK D hlt cells)

end Rule

end Cb.Rider

#print axioms Cb.Rider.hot_target_zt
#print axioms Cb.Rider.hot_forB
#print axioms Cb.Rider.hot_forB_in
