--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/YesPoint.lean: the functions of the places "LIN point" and "LIN zeta" of the
linear claim's shared rounds return a state, which is written out.

"LIN point" asks four things of the codes and the public shape and opens the two groups. "LIN zeta"
notes the sampled point and asks nothing.

The function is the own text of the IOP as written in Lean (Johnson/Desc/K14/Text.lean). The
sub-protocol's decide function is that function under the names of its tests. A decision is the
format's step (Johnson/Desc/Block.lean: Block.step), which tests the rounds' form and the columns in
front of the decide function. That the eight decide functions return .ok: Returned.decides
(Johnson/Desc/K14/Honest/YesChain.lean). That the eight steps do: eight_steps_hold
(Johnson/Desc/K14/Honest/ChainSteps.lean).

Main names: linPoint_returns, linZeta_returns.

What is not claimed. That a decision accepts. Shapes with one code (no split) are not served.
Nothing on soundness, on completeness or on hiding.

-/
import Johnson.Desc.K14.Honest.YesFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc.Ground (groupOk withGroup ok)
open VerifiableInference.Desc.Own (lengthsFit linFits)

/-- **The function of "LIN point" returns**: two groups more; the point and the groups' numbers are
noted. -/
theorem linPoint_returns (p : Par) (d : St) (r : Fmt.RoundView) (h1 : lengthsFit d.st.codes = true)
    (h2 : linFits d.st.codes p.S = true)
    (h3 : groupOk d.st.codes p.S.fold.u.code p.S.sharedMaskCode = true)
    (h4 : groupOk d.st.codes p.S.omega.code p.S.sharedMaskCode = true)
    (hS : p.S.sharedSplitNeeded = true) :
    linPoint p d [r] = some { d with
      st := (withGroup (withGroup d.st p.S.fold.u.code p.S.sharedMaskCode) p.S.omega.code
        p.S.sharedMaskCode)
      loc := { d.loc with
        psiSh := drawn r, gU := d.st.groups.size
        gOmega := d.st.groups.size + 1 } } := by
  have hsz : (withGroup d.st p.S.fold.u.code p.S.sharedMaskCode).groups.size =
      d.st.groups.size + 1 := by simp [withGroup]
  rw [← hsz]
  have hok : ok (linPointL p d) = true := by
    simp only [ok, linPointL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨h1, h2⟩
  have e1 := newGroupP_of d _ _ h3
  have e2 := newGroupP_of ({ d with
    st := (withGroup d.st p.S.fold.u.code p.S.sharedMaskCode) } : St)
    p.S.omega.code p.S.sharedMaskCode h4
  unfold linPoint
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
  refine ⟨(), by simp [guard, hok], _, e1, ?_⟩
  rw [if_pos hS]
  simp only [Option.bind_eq_some_iff, Option.some.injEq]
  exact ⟨_, e2, rfl⟩

/-- **The function of "LIN zeta" returns**: the point is noted. -/
theorem linZeta_returns (d : St) (r : Fmt.RoundView) :
    linZeta d [r] = some { d with loc := { d.loc with zFd := drawn r } } := rfl

end Desc.K14.Honest

#print axioms Desc.K14.Honest.linPoint_returns
#print axioms Desc.K14.Honest.linZeta_returns
