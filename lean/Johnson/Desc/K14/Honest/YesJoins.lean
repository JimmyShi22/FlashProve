--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/YesJoins.lean: the function of the joinings of the linear claim's shared
rounds returns a state, which is written out.

The place asks that o_omega has a tree to itself; then o_omega joins its group, and the mask message
o_sp joins both groups.

The function is the own text of the IOP as written in Lean (Johnson/Desc/K14/Text.lean). The
sub-protocol's decide function is that function under the names of its tests. A decision is the
format's step (Johnson/Desc/Block.lean: Block.step), which tests the rounds' form and the columns in
front of the decide function. That the eight decide functions return .ok: Returned.decides
(Johnson/Desc/K14/Honest/YesChain.lean). That the eight steps do: eight_steps_hold
(Johnson/Desc/K14/Honest/ChainSteps.lean).

Main names: Front6 (the facts in front; the joinings are the sixth of the eight sub-protocols),
joins_returns.

What is not claimed. That a decision accepts. That the facts in front hold at any state. Shapes with
one code are not served. Nothing on soundness, on completeness or on hiding.

-/
import Johnson.Desc.K14.Honest.YesFacts
import Johnson.Desc.Key.Laid.Joined

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Slice (withMessageInGroup joined_same joined_other)
open VerifiableInference.Desc.Ground (ok)
open VerifiableInference.Desc.Key (entered joined_groupAt joined_groupOff)
open VerifiableInference.Desc.Own (linFits aloneIn)

/-- In front of the joinings, the sixth of the eight sub-protocols. -/
structure Front6 (p : Par) (d : St) : Prop where
  lin : linFits d.st.codes p.S = true
  two : d.loc.gU ≠ d.loc.gOmega
  gU : GroupIs d.st d.loc.gU p.S.fold.u.code p.S.sharedMaskCode [d.loc.oU.oracle]
  gO : GroupIs d.st d.loc.gOmega p.S.omega.code p.S.sharedMaskCode []
  omega : MsgIs d.st d.loc.oOmega p.S.omega
  sp : MsgIs d.st d.loc.oSp p.S.sharedSplit
  apart : d.loc.oOmega ≠ d.loc.oSp
  apartU : d.loc.oSp ≠ d.loc.oU.oracle
  alone : aloneIn d.book d.loc.oOmega = true

/-- **The function of the joinings returns**: o_omega and then o_sp have joined the group GO, and
o_sp the group GU. -/
theorem joins_returns (p : Par) (d : St) (rs : List Fmt.RoundView) (hS : p.S.sharedSplitNeeded = true)
    (h : Front6 p d) :
    ∃ GU GO, d.st.groups[d.loc.gU]? = some GU ∧ d.st.groups[d.loc.gOmega]? = some GO ∧
      joins p d rs = some { d with
        st := (withMessageInGroup (withMessageInGroup (withMessageInGroup d.st d.loc.gOmega d.loc.oOmega false GO) d.loc.gOmega
                      d.loc.oSp false (entered GO d.loc.oOmega false)) d.loc.gU d.loc.oSp false GU) } := by
  obtain ⟨GU, hGU, _, hmaskU, hrunU, hmemU⟩ := h.gU
  obtain ⟨GO, hGO, hcodeO, hmaskO, hrunO, hmemO⟩ := h.gO
  obtain ⟨xO, hxO, hsO, hsamO, _⟩ := h.omega
  obtain ⟨xS, hxS, hsS, hsamS, _⟩ := h.sp
  obtain ⟨hsh, _⟩ := (VerifiableInference.Desc.Own.linFits_iff d.st.codes p.S).1 h.lin
  have hOm : p.S.omega.maskRows = 0 := hsh.2.2.2.2.2.2.2.2.2.2.1
  have hSp : VerifiableInference.Desc.Own.SplitMessageFits p.S.sharedSplit p.S.sharedMaskCode := by
    rcases hsh.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with e | e
    · rw [hS] at e
      cases e
    · exact e
  have hok : ok (joinsL d) = true := by
    simp only [ok, joinsL, List.all_cons, List.all_nil, Bool.and_true]
    exact h.alone
  have j1 := joinP_of d d.loc.gOmega d.loc.oOmega GO xO hGO hxO hsamO hrunO
    (Or.inr (by rw [hsO, hcodeO])) (Or.inl (by rw [hsO]; exact hOm))
    (not_contains_of hmemO _ (by simp))
  have g1 : (withMessageInGroup d.st d.loc.gOmega d.loc.oOmega false GO).groups[d.loc.gOmega]? =
      some (entered GO d.loc.oOmega false) := joined_groupAt _ _ _ _ _ hGO
  have m1 : (withMessageInGroup d.st d.loc.gOmega d.loc.oOmega false GO).oracles[d.loc.oSp]? = some xS := by
    rw [joined_other _ _ _ _ _ _ h.apart]
    exact hxS
  have j2 := joinP_of ({ d with st := withMessageInGroup d.st d.loc.gOmega d.loc.oOmega false GO } : St)
    d.loc.gOmega d.loc.oSp (entered GO d.loc.oOmega false) xS g1 m1 hsamS hrunO
    (Or.inl (by rw [hsS]; exact hSp.1)) (Or.inr (by rw [hsS, hSp.2.2.2]; exact hmaskO.symm))
    (by
      cases hc : (entered GO d.loc.oOmega false).members.contains d.loc.oSp with
      | false => rfl
      | true =>
        rcases (mem_entered _ _ _ _).1 (Array.contains_iff_mem.1 hc) with e | e
        · exact absurd e.symm h.apart
        · exact absurd ((hmemO _).1 e) (by simp))
  have g2 : (withMessageInGroup (withMessageInGroup d.st d.loc.gOmega d.loc.oOmega false GO) d.loc.gOmega d.loc.oSp false
      (entered GO d.loc.oOmega false)).groups[d.loc.gU]? = some GU := by
    rw [joined_groupOff _ _ _ _ _ _ (Ne.symm h.two), joined_groupOff _ _ _ _ _ _ (Ne.symm h.two)]
    exact hGU
  have m2 := joined_same (withMessageInGroup d.st d.loc.gOmega d.loc.oOmega false GO) d.loc.gOmega d.loc.oSp
    false (entered GO d.loc.oOmega false) xS m1
  have j3 := joinP_of ({ d with
      st := (withMessageInGroup (withMessageInGroup d.st d.loc.gOmega d.loc.oOmega false GO) d.loc.gOmega d.loc.oSp false
        (entered GO d.loc.oOmega false)) } : St)
    d.loc.gU d.loc.oSp GU _ g2 m2 hsamS hrunU
    (Or.inl (by show xS.shape.mainRows = 0; rw [hsS]; exact hSp.1))
    (Or.inr (by show xS.shape.maskCode = GU.maskCode; rw [hsS, hSp.2.2.2]; exact hmaskU.symm))
    (not_contains_of hmemU _ (by simpa using h.apartU))
  refine ⟨GU, GO, hGU, hGO, ?_⟩
  unfold joins
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
  refine ⟨(), by simp [guard, hok], _, j1, ?_⟩
  rw [if_pos hS]
  simp only [Option.bind_eq_some_iff]
  exact ⟨_, j2, j3⟩

end Desc.K14.Honest

#print axioms Desc.K14.Honest.joins_returns
