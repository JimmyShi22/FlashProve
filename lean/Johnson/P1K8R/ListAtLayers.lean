-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ListAtLayers.lean: the proof of the statement of
Johnson/P1K8R/ListAtLayersStatement.lean, to the letter, with one definition of a relation and two
helpers. Lemmas; none of the library's goals.

A FURTHER TEXT. `reads_lay_list` OPENS THE BLOCK OF THE READS' SENDING AT A LAYERS' SEGMENT BY THE
STEPS OF THE LIBRARY's `back_reads_layers` (Johnson/Desc/First/Link/Law/StretchBack.lean), SOME
FIFTEEN LINES WRITTEN A FURTHER TIME: that lemma asks of its relation that every kind's text keeps
it, which a sentence on the state behind alone does not meet.

How. `Both s s'`: s' has s's reading `wide` (Johnson/Desc/First/K8/LawWide.lean: among others the
list, its mark "closed", the matrices and their number) and holds the same return of the own rounds.
`both_stretch`: the library's `StretchKeeps` at that relation: each field from two laws on the
kind's text: for `wide`: `hear_leaves_wide` (LawWide.lean), `laterAt_tl`
(Johnson/Desc/K1/Law/TlAtRecord.lean), `theStated_leaves_wide` (LawWideK3.lean), `decide_leaves_tl`
(Johnson/Top/H0/MergeLaw/LeavesTl.lean); for the return: the fields of `sameOwn_stretch`
(OwnStay.lean). So ONE walk back from 28 g + 9 to 28 g + 6 keeps both (`stretch_back`).
`reads_lay_list`: behind the reads' sending the quiet step has closed the plan's structure with the
list held (`quiet_arms`, Johnson/Desc/First/K8/LawCondK1.lean; `quiet_layers_yes`,
Johnson/Meaning/QuietFront.lean). The line that takes the instance Inst.Model.Scl.ref off stands as
in StretchBack.lean, whose lemmas are called.

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.P1K8R.ListAtLayersStatement
import Johnson.IMR.PureJoin
import Johnson.IMR.K1Scope
import Johnson.Desc.First.Link.Law.StretchBack
import Johnson.Desc.First.Link.Law.OwnStay
import Johnson.Desc.First.K8.LawWideK3
import Johnson.Desc.First.K8.LawCondK1
import Johnson.Desc.K1.Law.TlAtRecord
import Johnson.Top.H0.MergeLaw.LeavesTl
import Johnson.Meaning.QuietFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (wide wideOf)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.LinkJoin (StretchKeeps stretch_back back_of sameOwn_stretch)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- The reading `wide` and the return of the own rounds are as they were. -/
def Both (s s' : S) : Prop := wide s' = wide s ∧ s'.own? = s.own?

/-- The members between the reads' sending and the batching keep both. -/
theorem both_stretch : StretchKeeps Both where
  trans := fun _ _ _ h k => ⟨k.1.trans h.1, k.2.trans h.2⟩
  k8 := fun p s rs gs s' h =>
    ⟨VerifiableInference.Desc.First.K8.hear_leaves_wide
      (Cl := VerifiableInference.Desc.Claim) p.toPar s rs gs s' h,
      sameOwn_stretch.k8 p s rs gs s' h⟩
  k1 := fun q gp link piece moment arrays s rs gs s' h =>
    ⟨congrArg (Option.map wideOf)
      (VerifiableInference.Desc.K1.laterAt_tl q gp link piece moment arrays s s' rs gs h).1,
      sameOwn_stretch.k1 q gp link piece moment arrays s rs gs s' h⟩
  k3 := fun claim readers X codes shape a _ hb s rs gs s' h =>
    ⟨VerifiableInference.Desc.First.K8.theStated_leaves_wide hb s rs gs s' h,
      sameOwn_stretch.k3 claim readers X codes shape a hb s rs gs s' h⟩
  k11 := fun Pm s rs gs s' h =>
    ⟨congrArg (Option.map wideOf)
      (VerifiableInference.Desc.First.MergeLaw.decide_leaves_tl Pm h),
      sameOwn_stretch.k11 Pm s rs gs s' h⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- Behind the reads' sending at a layers' segment. -/
theorem reads_lay_list (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Q : Type} {start : Q → S}
    {g : Nat} (hg : g < 12) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (14 * (2 * g) + 6) (z, s')) :
    ∃ hp tl o, Bs.G₀.W.G[g]? = some hp ∧ s'.tl? = some tl ∧ s'.own? = some o ∧
      tl.funs = o.funs ∧ tl.mats = hp.tl.mats ∧ tl.NM = hp.tl.NM := by
  obtain ⟨m0, -, fm, km, gm, -⟩ := (IM.ground_named hS hR O.pub O.blank).1 g hg
  have n24 : ¬ 2 * g = 24 := by omega
  have i1 : IM.k1Ix (2 * g) false = 3 := by
    show (if false = true then 5 else 3) + (if 2 * g = 24 then 1 else 0) = 3
    rw [if_neg (fun e => nomatch e), if_neg n24]
  obtain ⟨Lk, b, Xl, pd, reads, digits, e1, e2, hX, -, e4⟩ :=
    IM.k1_reads_of hS hR O (2 * g) (by omega)
  rw [i1] at e2
  obtain ⟨-, -, k⟩ := back_of (R := fun _ t => ∃ hp tl o, Bs.G₀.W.G[g]? = some hp ∧
      t.tl? = some tl ∧ t.own? = some o ∧ tl.funs = o.funs ∧ tl.mats = hp.tl.mats ∧
      tl.NM = hp.tl.NM) hS hR O (l := 2 * g) (i := 3) (by omega) e1 e2 e4 (fun e => nomatch e)
    (by
      intro s rs gs t hd
      have hd' : (IM.k1Reads Z Bs.G₀ (2 * g) Xl (IM.k1Ix (2 * g) false + 1) reads).decide s rs gs =
          .ok t := hd
      unfold IM.k1Reads at hd'
      obtain ⟨m, -, h2⟩ := VerifiableInference.Desc.Keeps.ebind_ok hd'
      unfold IM.k1Quiet at h2
      rcases VerifiableInference.Desc.First.K8.Ready.quiet_arms Bs.G₀ (2 * g) Xl _ _ _ _ h2 with
        ⟨k1, -⟩ | ⟨-, Y, hY, hc⟩
      · obtain rfl : m0 = Xl := Option.some.inj (fm.symm.trans hX)
        rw [km] at k1
        exact absurd k1 (fun e => nomatch e)
      · obtain rfl : m0 = Y := Option.some.inj (fm.symm.trans hY)
        rcases hc with ⟨-, hp, hG, hq⟩ | ⟨k2, -⟩
        · obtain ⟨a, own, -, ho, rfl⟩ := _root_.Meaning.Reads.quiet_layers_yes hq
          rw [gm] at hG
          exact ⟨hp, _, own, hG, rfl, ho, rfl, rfl, rfl⟩
        · rw [km] at k2
          exact absurd k2 (fun e => nomatch e)) h
  exact k

end

/-- **In front of the batching the list is the one held.** -/
theorem list_at_layers : ListAtLayers := by
  intro P pp lay F Z Bs base c A B hS hR O Q start g hg z s' h
  have h' : Reach 0 c.blocksInOrder start (14 * (2 * g) + 9) (z, s') := by
    rw [show 14 * (2 * g) + 9 = 28 * g + 9 by omega]
    exact h
  obtain ⟨s, r, qw, qo⟩ := stretch_back both_stretch hS hR O (l := 2 * g) (by omega) h'
  obtain ⟨hp, tl, o, hG, etl, eo, c1, c2, c3⟩ := reads_lay_list hS hR O hg r
  have ew : wide s' = some (wideOf tl) := by
    rw [qw]
    show s.tl?.map wideOf = some (wideOf tl)
    rw [etl]
    rfl
  obtain ⟨tl', etl', ee⟩ := Option.map_eq_some_iff.1 ew
  have q1 : tl'.funs = tl.funs := congrArg (fun y => y.2.2.2) ee
  have q3 : tl'.mats = tl.mats := congrArg (fun y => y.1.2.2.2.2.2.2) ee
  have q4 : tl'.NM = tl.NM := congrArg (fun y => y.1.2.2.2.2.1) ee
  exact ⟨hp, tl', o, hG, etl', qo.trans eo, q1.trans c1, q3.trans c2, q4.trans c3⟩

end P1K8

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms P1K8.both_stretch
#print axioms P1K8.reads_lay_list
#print axioms P1K8.list_at_layers
#print axioms P1K8.Both
