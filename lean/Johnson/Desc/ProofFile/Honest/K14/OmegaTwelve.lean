-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/OmegaTwelve.lean: kind K14: THE TESTS OF Honest/K14/OmegaEnd.lean
AT THE SHARED CHAIN's BORDERS 10, 11 AND 12, OFF THE RUN: that is: read off the return of the fold
over the chain's first members, which Thr (Honest/Thread/Thr.lean) holds as one of its parts.
Wherever Thr holds at one of these borders of a Thread of the shared chain (three premises say that
it is one: Plan2, ChainAt and TailAt, below), omegaEndB, omegaPadB and notedB are true at the state;
at border 12, the last, Desc.K14.ended returns there, and what the last chain takes of its value is
the library's oOf of the state. NO FIELD keeps AND NO CLAUSE OF THE FIELD rides IS ASKED: the laws
of Honest/K14/OmegaDoor.lean on the members 9, 10 and 11 are called on that run. Two definitions,
and statements with their proofs.

  TailLike xs p₉ p₁₀ front the members 9, 10 and 11 of the list xs are like
                  (Johnson/Desc/K14/Honest/FlatForm.lean: Like: the same rounds, oracles, place and
                  decide function) the library's test on G_u at p₉, its test on G_omega at p₁₀
                  (onGu, onGomega: Johnson/Desc/K12/Seat.lean) and the shared chain's closing
                  sub-protocol at front (last: Johnson/Desc/K12/Seat/Fill.lean)
  TailAt xs p₉ p₁₀ front **THE ONE PREMISE ON THE LIST BESIDE ChainAt**: TailLike, and the two
                  tests' own tests on the plan accept (plan₉, plan₁₀)
  fold_rung       where the fold over the first k + 1 members returns, the fold over the first k
                  returns, and the member k's decide function has returned the later state from the
                  earlier, at some rounds and columns: general in the two types. By the library's
                  foldBlocks_append_ok and foldBlocks_cons_ok (Johnson/Desc/RunLaws.lean) and
                  step_decides (Johnson/Desc/K14/Law/Step.lean). The library says this thought at
                  other types or in other forms: Meaning.K2.fold_next and fold_back
                  (Johnson/IMR/FoldTools.lean)
                  and VerifiableInference.OnPublicFiles.foldCut (Johnson/Desc/First/Look/K03RowsBare.lean)
                  at the first chain's state alone; nearest of all, IM.fold_last
                  (Johnson/IMR/SendsFold.lean: from the same one premise the earlier fold's return
                  and the member's step) and P1L20.fold_last (Johnson/P1L20R/FrameFold.lean: the
                  step alone), both at the first chain's state alone too; IM.fold_step
                  (Johnson/IMR/MemberFold.lean), general, takes both folds and ends in another form:
                  none can be called here for less
  omega_of_fold10, omega_of_fold11, omega_of_fold12 ONE LADDER: ten from nine (omega_of_fold) and
                  the member 9; eleven from ten and the member 10; twelve from eleven and the
                  closing sub-protocol
  omega_at_ten, omega_at_eleven, omega_at_twelve **AT THESE BORDERS, WHEREVER Thr HOLDS**: general
                  in the Thread
  closing_ours    **at border 11, in front of the closing sub-protocol, where a test has begun on
                  every group, each of o_u, o_omega and o_sp is in a tested group**: noted_pays at
                  the border in front of the closing sub-protocol
  door_at_twelve  **so omegaEndL is all true at what the last chain takes of the shared chain's
                  end**: the premise hO of door_of_omega, at x.shared := sharedOfEnd e

PREMISES of the theorems on a Thread: Plan2 (Honest/K14/Debts2.lean: so the row (Fold) is split over
two codes, and the masks are sent ahead), ChainAt (Honest/K14/AcceptedAt.lean: the first nine
members and the first state) and TailAt. All three borders take the whole of TailAt, though border
10 spends its first member and plan₉ alone: it is one thing to show.

WHERE THE PLAN HAS NO SECOND PROXIMITY TEST the shared chain has eleven members, TailLike is false,
and no theorem of this file that names it says anything: by reading; no theorem says so.

What is not claimed. TailAt or ChainAt at any Thread (at the Thread that is laid for the shared
chain of the IOP as written in Lean: Honest/K14/OmegaAtShared.lean). That Thr holds at one of these
borders at any run: at border 12 it holds only where all twelve members have accepted; no fold over
twelve members that returns has been evaluated in this library. That the state which the last
chain's start is handed is that last state. Nothing on any property of the protocol: nothing on
completeness, on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.OmegaDoor
import Johnson.Desc.RunLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (OracleNotice TreeLay TableKey)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks foldBlocks_append_ok foldBlocks_cons_ok)
open VerifiableInference.Desc.Ground (ok)
open VerifiableInference.Desc.Third.Law (oOf)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (P14 St first)
open Desc.K14.Honest (Like FlatAt Eight Public8)

/-- The members 9, 10 and 11 of a list of the shared chain's sub-protocols are like the library's
two proximity tests and its closing sub-protocol. -/
structure TailLike {Cl : Type} (xs : List (Block St Cl)) (p₉ p₁₀ : P12)
    (front : List (Block St Unit)) : Prop where
  nine : ∃ x, xs[9]? = some x ∧
    Like x (VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p₉ : Block T12 Unit))
  ten : ∃ x, xs[10]? = some x ∧
    Like x (VerifiableInference.Desc.K12.Seat.onGomega (proximityTestKind guardedProximityTestParts p₁₀ : Block T12 Unit))
  eleven : ∃ x, xs[11]? = some x ∧ Like x (VerifiableInference.Desc.K12.Seat.last front)

/-- **TailLike, and the two proximity tests' own tests on the plan accept.** -/
structure TailAt {Cl : Type} (xs : List (Block St Cl)) (p₉ p₁₀ : P12)
    (front : List (Block St Unit)) : Prop extends TailLike xs p₉ p₁₀ front where
  plan₉ : (proximityTestKind guardedProximityTestParts p₉ : Block T12 Unit).planOk = true
  plan₁₀ : (proximityTestKind guardedProximityTestParts p₁₀ : Block T12 Unit).planOk = true

/-- Where the fold over the first k + 1 members returns, the fold over the first k returns, and the
member k's decide function has returned the later state from the earlier, at some rounds and
columns. -/
theorem fold_rung {S Cl : Type} {ft k : Nat} {bs : List (Block S Cl)} {b : Block S Cl}
    (hb : bs[k]? = some b) {s t' : S} {rs r' : List Fmt.RoundView} {cols c' : List OpenedColumn}
    (h : foldBlocks ft (bs.take (k + 1)) s rs cols = .ok (t', r', c')) :
    ∃ t r c, foldBlocks ft (bs.take k) s rs cols = .ok (t, r, c) ∧
      ∃ rs' gs, b.decide t rs' gs = .ok t' := by
  rw [List.take_add_one, hb] at h
  obtain ⟨t, r, c, g0, g1⟩ := (foldBlocks_append_ok [b] _ _ _ _ _).1 h
  obtain ⟨-, u, n, hs, g2⟩ := foldBlocks_cons_ok.1 g1
  obtain rfl : u = t' := congrArg Prod.fst (Except.ok.inj g2)
  obtain ⟨gs, hd⟩ := Desc.K14.Law.step_decides ft b t u _ c n hs
  exact ⟨t, r, c, g0, _, gs, hd⟩

/-! ## The ladder -/

section run
variable {P : P14} {sentU : Array OracleNotice} {layO : TreeLay} {d0 : St} {B : Eight P} {ft : Nat}
  {Cl : Type} {xs : List (Block St Cl)} {c : OnBytes.Model.Verify.Chains} {p₉ p₁₀ : P12}
  {front : List (Block St Unit)}

/-- From the fold over the first ten members: nine, and the test on G_u. -/
theorem omega_of_fold10 (F : FlatAt xs c B) (Tl : TailAt xs p₉ p₁₀ front)
    (S : Public8 P sentU layO d0) (s : St) (rs rs' : List Fmt.RoundView) (cl cl' : List OpenedColumn)
    (h : foldBlocks ft (xs.take 10) d0 rs cl = .ok (s, rs', cl')) :
    omegaEndB P.S s = true ∧ omegaPadB P.S s = true ∧ notedB s = true := by
  obtain ⟨x9, h9, l9⟩ := Tl.nine
  obtain ⟨s9, _, _, hf, _, _, k9⟩ := fold_rung h9 h
  have F9 := omega_of_fold F S s9 _ _ _ _ hf
  have a9 := omegaEnd_of_facts F9
  rw [l9.decide] at k9
  have hm := mask_of_omegaEnd a9
  exact ⟨omega_stays P.S (omegaKept_onGu p₉ Tl.plan₉ _ _ _ _ k9 hm) a9,
    pad_stays P.S (padKept_onGu p₉ Tl.plan₉ _ _ _ _ k9 hm) (omegaPad_of_facts F9),
    noted_stays (notedKept_onGu p₉ Tl.plan₉ _ _ _ _ k9) F9.noted⟩

/-- From the fold over the first eleven members: ten, and the test on G_omega. -/
theorem omega_of_fold11 (F : FlatAt xs c B) (Tl : TailAt xs p₉ p₁₀ front)
    (S : Public8 P sentU layO d0) (s : St) (rs rs' : List Fmt.RoundView) (cl cl' : List OpenedColumn)
    (h : foldBlocks ft (xs.take 11) d0 rs cl = .ok (s, rs', cl')) :
    omegaEndB P.S s = true ∧ omegaPadB P.S s = true ∧ notedB s = true := by
  obtain ⟨x10, h10, l10⟩ := Tl.ten
  obtain ⟨s10, _, _, hf, _, _, k10⟩ := fold_rung h10 h
  obtain ⟨a, b, n⟩ := omega_of_fold10 F Tl S s10 _ _ _ _ hf
  rw [l10.decide] at k10
  exact ⟨omega_stays P.S (omegaKept_onGomega p₁₀ Tl.plan₁₀ _ _ _ _ k10) a,
    pad_stays P.S (padKept_onGomega p₁₀ Tl.plan₁₀ _ _ _ _ k10) b,
    noted_stays (notedKept_onGomega p₁₀ Tl.plan₁₀ _ _ _ _ k10) n⟩

/-- From the fold over the first twelve members: eleven, and the closing sub-protocol. -/
theorem omega_of_fold12 (F : FlatAt xs c B) (Tl : TailAt xs p₉ p₁₀ front)
    (S : Public8 P sentU layO d0) (s : St) (rs rs' : List Fmt.RoundView) (cl cl' : List OpenedColumn)
    (h : foldBlocks ft (xs.take 12) d0 rs cl = .ok (s, rs', cl')) :
    omegaEndB P.S s = true ∧ omegaPadB P.S s = true ∧ notedB s = true ∧
      ∃ e, Desc.K14.ended s = some e ∧ VerifiableInference.Desc.Third.sharedOfEnd e = oOf s := by
  obtain ⟨x11, h11, l11⟩ := Tl.eleven
  obtain ⟨s11, _, _, hf, _, _, k11⟩ := fold_rung h11 h
  obtain ⟨a, b, n⟩ := omega_of_fold11 F Tl S s11 _ _ _ _ hf
  rw [l11.decide] at k11
  obtain ⟨K1, K2, K3⟩ := kept_closing front _ _ _ _ k11
  exact ⟨omega_stays P.S K1 a, pad_stays P.S K2 b, noted_stays K3 n,
    ended_of_closing front _ _ _ _ k11⟩

end run

/-! ## At a Thread -/

-- Every variable of this section is implicit. Their order is the order of the statements' implicit
-- arguments, which only a call with @ reads.
section thread
variable {Bk : ProverCoinCounts} {Cl V Wt X Pb : Type} {Q : P14} {sentU : Array OracleNotice} {layO : TreeLay}
  {T : Thread Bk St Cl V Wt X Pb} {c : OnBytes.Model.Verify.Chains} {key : Wt → TableKey}
  {p₉ p₁₀ : P12} {front : List (Block St Unit)}

/-- **At border 10, wherever Thr holds, under Plan2, ChainAt and TailAt.** -/
theorem omega_at_ten (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key)
    (hL : TailAt T.bs p₉ p₁₀ front) {k : Coins Bk} {s : St} {m : Mid Wt X} {E : Env}
    (hA : Thr T 10 k s m E) :
    omegaEndB Q.S s = true ∧ omegaPadB Q.S s = true ∧ notedB s = true := by
  obtain ⟨B⟩ := hQ.eight
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes (key m.st.input) := hT.begun _ _ _ _ hbeg
  exact omega_of_fold10 (hT.bs B) hL (hQ.pub (key m.st.input)) s _ _ _ _ hfold

/-- **At border 11, in front of the closing sub-protocol, wherever Thr holds, under Plan2, ChainAt
and TailAt.** -/
theorem omega_at_eleven (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key)
    (hL : TailAt T.bs p₉ p₁₀ front) {k : Coins Bk} {s : St} {m : Mid Wt X} {E : Env}
    (hA : Thr T 11 k s m E) :
    omegaEndB Q.S s = true ∧ omegaPadB Q.S s = true ∧ notedB s = true := by
  obtain ⟨B⟩ := hQ.eight
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes (key m.st.input) := hT.begun _ _ _ _ hbeg
  exact omega_of_fold11 (hT.bs B) hL (hQ.pub (key m.st.input)) s _ _ _ _ hfold

/-- **So at border 11, where a test has begun on every group, each of o_u, o_omega and o_sp is in a
tested group**: the closing sub-protocol's second clause at this kind's three messages. Wherever Thr
holds there, under Plan2, ChainAt and TailAt. -/
theorem closing_ours (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key)
    (hL : TailAt T.bs p₉ p₁₀ front) {k : Coins Bk} {s : St} {m : Mid Wt X} {E : Env}
    (hA : Thr T 11 k s m E) (hall : s.st.groups.all (·.inRun) = true) :
    ∀ o ∈ [s.loc.oU.oracle, s.loc.oOmega, s.loc.oSp], ∃ x, s.st.oracles[o]? = some x ∧
      (x.groups.any fun g => (s.st.groups[g]?).any (·.inRun)) = true :=
  noted_pays (omega_at_eleven hQ hT hL hA).2.2 hall

end thread

-- The same variables in another order, all implicit: so the implicit arguments of these two
-- statements stand in another order than those above. Only a call with @ reads that order; joining
-- the two sections would turn it.
section last
variable {sentU : Array OracleNotice} {layO : TreeLay} {Bk : ProverCoinCounts} {Cl V Wt X Pb : Type} {Q : P14}
  {T : Thread Bk St Cl V Wt X Pb} {c : OnBytes.Model.Verify.Chains} {key : Wt → TableKey}
  {p₉ p₁₀ : P12} {front : List (Block St Unit)}

/-- **At border 12, wherever Thr holds, under Plan2, ChainAt and TailAt.** -/
theorem omega_at_twelve (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key)
    (hL : TailAt T.bs p₉ p₁₀ front) {k : Coins Bk} {s : St} {m : Mid Wt X} {E : Env}
    (hA : Thr T 12 k s m E) :
    omegaEndB Q.S s = true ∧ omegaPadB Q.S s = true ∧ notedB s = true ∧
      ∃ e, Desc.K14.ended s = some e ∧ VerifiableInference.Desc.Third.sharedOfEnd e = oOf s := by
  obtain ⟨B⟩ := hQ.eight
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes (key m.st.input) := hT.begun _ _ _ _ hbeg
  exact omega_of_fold12 (hT.bs B) hL (hQ.pub (key m.st.input)) s _ _ _ _ hfold

/-- **So omegaEndL is all true at what the last chain takes of the shared chain's end**: wherever
Thr holds at border 12, under Plan2, ChainAt and TailAt. -/
theorem door_at_twelve (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key)
    (hL : TailAt T.bs p₉ p₁₀ front) {k : Coins Bk} {s : St} {m : Mid Wt X} {E : Env}
    (hA : Thr T 12 k s m E) :
    ∃ e, Desc.K14.ended s = some e ∧
      ok (omegaEndL Q.S (VerifiableInference.Desc.Third.sharedOfEnd e)) = true := by
  obtain ⟨a, -, -, e, he, hs⟩ := omega_at_twelve hQ hT hL hA
  refine ⟨e, he, ?_⟩
  rw [hs]
  unfold omegaEndB at a
  rw [Bool.and_eq_true] at a
  exact a.1

end last

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.fold_rung
#print axioms ProofFile.Honest.K14.omega_of_fold10
#print axioms ProofFile.Honest.K14.omega_of_fold11
#print axioms ProofFile.Honest.K14.omega_of_fold12
#print axioms ProofFile.Honest.K14.omega_at_ten
#print axioms ProofFile.Honest.K14.omega_at_eleven
#print axioms ProofFile.Honest.K14.closing_ours
#print axioms ProofFile.Honest.K14.omega_at_twelve
#print axioms ProofFile.Honest.K14.door_at_twelve
