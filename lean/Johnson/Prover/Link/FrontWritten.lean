-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FrontWritten.lean: Src (Johnson/Prover/Link/FrontSrc.lean) AT THE TYPED
STATEMENT AFTER THE LINK's FIVE WRITTEN ROUNDS (st4R, OnBytes/Slice/CorePeelRec.lean). Statement and
proof.

  src_st4R   the two stored strings are the tables of M₀'s and M₁'s rows' code words · the pair of
             OOD samples holds each row's answers · the two tables' message parts agree on the
             entries that are compared · μ holds, at the places putAt, the folds at the point that
             round 1 drew, and 0 on the rows that no member has · the answers that round 3 shows are
             the sample's rows, at the seed that round 2 drew, at each member's share of μ
             ⟹ Src t (st4R ...).1 μ M₀ M₁

By: the statement's parts are what st4R's text says (by unfolding); what it holds as read at the
drawn locations: LdLkP.loc_nx (Cb/Ld/LdLinkProofs.lean).

Not shown here. That a written strategy's rounds meet these premises. Nothing on a decision, a
file or a hash function; nothing on soundness; nothing on what any entry of a message discloses or
does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FrontSrc
import OnBytes.Slice.CorePeelRec
import Cb.Ld.LdLinkProofs

set_option autoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice Cb Cb.Ood Iop _root_.Run

/-- **Src at the statement after the five written rounds.** -/
theorem src_st4R (S : Sz) (Z : Sample GE S.En) (r : (S.lkR Z).X0) (d1 d2 d3 d4 d5 : PQ.RD)
    (y : (S.lkR Z).E0.Str) (c1 : (wRound d1).Chal) (m2 : (wRound d2).Msg) (c2 : (wRound d2).Chal)
    (m3 : (wRound d3).Msg) (c4 : (wRound d4).Chal) (c5 : (wRound d5).Chal) (t : ℕ)
    (μ : (S.sg t).cIn.J → GE) (M₀ M₁ : (S.ixR Z).Row → S.Co → GE)
    (free : FreeZero S t μ)
    (at0 : ∀ k, μ (atJ S t false (S.putAt k)) = foldAll (gVec S.P.v _ (valsOf d1 c1)) M₀ k)
    (at1 : ∀ k, μ (atJ S t true (S.putAt k)) = foldAll (gVec S.P.v _ (valsOf d1 c1)) M₁ k)
    (rec0 : ∀ ρ s, r.1.2 (ρ, s) = ∑ j, Z.mat r.1.1 s j * M₀ ρ ((S.ixR Z).pl j))
    (rec1 : ∀ ρ s, r.2.2 (ρ, s) = ∑ j, Z.mat r.2.1 s j * M₁ ρ ((S.ixR Z).pl j))
    (tab0 : (S.lkR Z).tab y.1 = fun ρ => (S.ixR Z).G.mulVec (M₀ ρ))
    (tab1 : (S.lkR Z).tab y.2 = fun ρ => (S.ixR Z).G.mulVec (M₁ ρ))
    (same : (S.lwR Z).SameOn ((S.ixR Z).view M₀) ((S.ixR Z).view M₁))
    (sm : ∀ a : Bool, ∑ j, (S.fam.om a).Z.mat (gSeed (S.P.aR + S.P.aP) _ (valsOf d2 c2)) () j *
      μ (atJ S t a j) = answOf S d3 m3 a ()) :
    Src t (st4R S Z r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1 μ M₀ M₁ where
  free := free
  sm := sm
  at0 := at0
  at1 := at1
  rec0 := rec0
  rec1 := rec1
  col0 := fun i => by
    have h := congrArg (fun z => z.2.1.2 i) ((S.lkR Z).loc_nx
      (st2R S Z d2 d3 ((S.lkR Z).vGam.nx r y (gVec S.P.v _ (valsOf d1 c1)),
        (S.lkR Z).vGam.g.map y) m2 c2 m3).1
      (st2R S Z d2 d3 ((S.lkR Z).vGam.nx r y (gVec S.P.v _ (valsOf d1 c1)),
        (S.lkR Z).vGam.g.map y) m2 c2 m3).2
      (gLoc S.P.T.a S.P.nu0 S.P.nuj _ (valsOf d4 c4)))
    refine h.trans ?_
    show foldAll _ ((S.lkR Z).tab y.1) _ = _
    rw [tab0]
    rfl
  col1 := fun i => by
    have h := congrArg (fun z => z.2.2.2 i) ((S.lkR Z).loc_nx
      (st2R S Z d2 d3 ((S.lkR Z).vGam.nx r y (gVec S.P.v _ (valsOf d1 c1)),
        (S.lkR Z).vGam.g.map y) m2 c2 m3).1
      (st2R S Z d2 d3 ((S.lkR Z).vGam.nx r y (gVec S.P.v _ (valsOf d1 c1)),
        (S.lkR Z).vGam.g.map y) m2 c2 m3).2
      (gLoc S.P.T.a S.P.nu0 S.P.nuj _ (valsOf d4 c4)))
    refine h.trans ?_
    show foldAll _ ((S.lkR Z).tab y.2) _ = _
    rw [tab1]
    rfl
  same := same

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.src_st4R
