-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lookup/Rider/Model/TwoLines.lean: the two clauses of the acceptance policy on a
position's cost, tested on the challenges of the lookup of a sub-proof, for any number lt of bits of
a position.

Statements and proofs. No protocol of its own. The term forB and its counts are those of
OnBytes/Tie/Pv/Lookup/Forest/FoHole.lean; the rule is `forB_ride`
(OnBytes/Tie/Pv/Lookup/Rider/ForB.lean); the arrays are those of Cb/G6/Rider/Model/TwoLines.lean;
`LinesAll` and `LinesAtPt` are those of Cb/Pv/Head/TwoLines.lean; `outZt` is that of
OnBytes/Tie/Pv/Lookup/Rider/Model/Zt.lean.
Main names:
  `two_target_zt`: `AtCoords` of the family `twoFam` at the last lt places of `outZx` is `LinesAtPt`
    at `outZt` read by `Blocks.ofList`.
  `twoLines_forB`: from `KnowAt` of forB between any two joints JA and JB, `KnowAt` of the same
    reduction, with the same extractor and the same counts, from JA and `LinesAll t y lt` to JB and
    `LinesAtPt t y lt u`, u the last lt places of `outZx`. Asked: lt ≤ h.dT. `cells` (t, off the
    caller's state and the tuple of messages) and `req` (y, off the caller's state) are free
    letters.
  `twoLines_forB_in`: the same at forB's own joints, `LinesAll` laid inside the relation R0 that
    rides along, at the input alone.
Limits: JA, JB, R0 and `cells`, `req` are free letters. If JA's relaxed relation without the first
clause, or JB's, already gives the first clause, the statement follows from its premise alone and
says nothing (`knowAt_hollow_own`, `knowAt_hollow_out`, Cb/G6/Rider/KnowAt.lean; `forB_hollow`). So
a caller whose R0 is a record of the head's relation has to leave the two clauses (at lt = 10: the
clause jc, `linesAll_jc`) out of it. At a request without a counted position both clauses hold of
all cells (`linesAll_none`). The two vectors are at the reference sizes of Inst/Model/Head whatever
lt is. No value of the letters is given here at which the first clause fails while JA's relaxed
relation holds. Nothing on whether the programs test this target, on whether a later block takes it
up, or on an honest prover.
-/
import OnBytes.Tie.Pv.Lookup.Rider.Model.Zt
import Cb.G6.Rider.Model.TwoLines

set_option autoImplicit false

namespace Cb.Rider
open Iop Prob Cb Blocks Cb.LdLkp Cb.LdLkp.Kn TWhole Cb.Fo Inst.Model Inst.Model.Head Cb.Pv.Head

/-- The target at the last lt places of the first part of the key point. -/
theorem two_target_zt {E St St' J M : Type} [Field E] (h : Sh) {lt : ℕ} (hlt : lt ≤ h.dT)
    (cells : St → M → Cells E) (req : St → Req) (st : St) (b : TX St' E J) (m : M) :
    AtCoords (fun _ : Fin 2 => lt) (fun _ t => h.dT - lt + t) (twoFam cells req) st b.2.1.pt m ↔
      LinesAtPt (cells st m) (req st) lt (ofList (outZt h lt b)) :=
  forall_congr' fun _ => Eq.congr_left (ext_congr_point (fun _ ht => outZt_pt h hlt b ht) _)

section Rule
variable {E : Type} [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]
  {h : Sh} {L : Lay E St₀ J₀} {Ex : ExtSpec} {Kc M Wp : Type}

/-- The two clauses on the challenges of forB, between any two joints between which forB has KnowAt.
Warning: JA and JB are free (knowAt_hollow_own, knowAt_hollow_out). -/
theorem twoLines_forB {JA : IOR.Rels Kc St₀ Ex (M × Wp)}
    {JB : IOR.Rels Kc (TX (St₀ × E) E (Option J₀)) Ex (M × Wp)}
    {xt : M → St₀ × Ex.Str → Tr (forB E h L V₀ V₀C (Ex := Ex)).R.shape → Wp → Wp}
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R JA JB xt (forB E h L V₀ V₀C (Ex := Ex)).e)
    {lt : ℕ} (hlt : lt ≤ h.dT) (cells : St₀ → M → Cells E) (req : St₀ → Req) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (withRider JA fun m a => LinesAll (cells a.1 m) (req a.1) lt)
      (withRider JB fun m b =>
        LinesAtPt (cells b.1.1.1 m) (req b.1.1.1) lt (ofList (outZt h lt b.1)))
      xt (forB E h L V₀ V₀C (Ex := Ex)).e :=
  knowAt_congr_rider (fun m a => two_source cells req lt a.1 m)
    (fun m b => two_target_zt h hlt cells req b.1.1.1 b.1 m)
    (forB_ride hK _ _ (selIn_last h hlt) (twoFam cells req))

variable {R0 : IOR.Rels Kc St₀ Ex (M × Wp)} {msg₀ : M → J₀ → E}

/-- The two clauses on the challenges of forB, at forB's own joints: LinesAll comes in inside R0 and
does not come out. Warning: R0 is free (forB_hollow): it has to be without the two clauses. -/
theorem twoLines_forB_in
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e)
    {lt : ℕ} (hlt : lt ≤ h.dT) (cells : St₀ → M → Cells E) (req : St₀ → Req) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (forIn E h L (withRider R0 fun m a => LinesAll (cells a.1 m) (req a.1) lt) msg₀)
      (withRider (forOut E h L R0 msg₀) fun m b =>
        LinesAtPt (cells b.1.1.1 m) (req b.1.1.1) lt (ofList (outZt h lt b.1)))
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e :=
  forIn_in (twoLines_forB hK hlt cells req)

end Rule

end Cb.Rider

#print axioms Cb.Rider.two_target_zt
#print axioms Cb.Rider.twoLines_forB
#print axioms Cb.Rider.twoLines_forB_in
