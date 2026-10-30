-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/ThreeOfLeftOn.lean: LeftRest's FIELD three
(Johnson/Desc/First/Link/Law/LeftOfRest.lean: what is left of K9's hLeft): WHAT THE DIGITS' LOOKUP
RETURNED FITS THE STRUCTURE AT WHICH THE EQUATIONS ARE MADE: tl.f9 = g.shape · 5 ≤ g.shape.kT +
g.shape.cK · the key points' sizes are the calls' n. A statement and its proof: a reduction.

IT DOES NOT FOLLOW FROM Ok's Kx ALONE. K3Ok (Top/H/Keep/RunsPlain.lean) speaks of g.shape and
never of the state's structure: nothing in it ties g.shape to tl.f9. WHAT TIES THEM: the lookups'
promise on the state itself, K3LeftOn (Top/H/K3LeftStatement.lean), AT THE SHAPE tlD.f9: its
K3Left.shape says g.shape = that shape, its zkLen the sizes; and Ok's clause dig (OkCore.dig:
SameDig tlD tlb) ties the state's structure to tlD.

  three_of_leftOn   at a state s in front of the batching: (hc : ∀ q, Ok q → OkCore nU tlD q) · (L
                    : K3LeftOn S.fork? ‹what the digits' lookup left as heard› tlD.f9 lm first Qf s)
                    · two closed facts on tlD (P2 · P3) ⊢ the field's text at every e that goes on
                    from what is fixed at s

WHAT IS LEFT. L at every state of the condition in front of the batching:
shown in Johnson/P5J/K09LeftD.lean (P5J.leftD_at: for some first, at Qf := fun _ => True), from the
standing hypotheses (P5J.AtMgA) at OnBytes.secondHashFunction, m < 25, digAt (At.X Zp) m = some (xx, tlD), and a
state that meets the table's promise in front of the batching (ho): by
leftOn_digits_front | leftOn_digits_head (Link/Law/KxAtFront.lean) and shape_of_dig
(Johnson/LPFE1R/ShapeOfDig.lean).
P2 · P3: closed facts on tlD: kin of DigOK.tail (PortOK.call · wide) and
FoNums.ok.
Limits. AN IMPLICATION. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.OkOne
import Johnson.Top.H.K3LeftStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.PhiAll

variable {β : Type}

/-- **LeftRest's FIELD three, from the lookups' promise on the state in front.** -/
theorem three_of_leftOn (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ)
    (tlD : HTailF2) (hc : ∀ q, Ok q → OkCore nU tlD q)
    (P2 : 5 ≤ tlD.f9.kT + tlD.f9.cK)
    (P3 : ∀ q < 2, q < tlD.f9.NC ∧
      ((tlD.f9.calls[q]?).map (·.n)).getD 0 = (tlD.zOf q).call.n)
    (s : S) {lm first : ℕ} {Qf : Fork → Prop}
    (L : K3LeftOn S.fork? (fun s : S => s.tl?.bind (·.heard)) tlD.f9 lm first Qf s) :
    ∀ (e : S) (tl : HTailF2) (g : Forest.Heard), e.tl? = some tl → tl.heard = some g →
      Fx9 (phiAll u ψ) Ok (fixed9 (phiAll u ψ) s) e →
      tl.f9 = g.shape ∧ 5 ≤ g.shape.kT + g.shape.cK ∧
        ∀ q < 2, (g.zk.getD q #[]).size = (tl.zOf q).call.n := by
  intro e tl g htl hg fx
  obtain ⟨hok, hφ, v, b, hv, _, _⟩ := fx
  have h1 : e.tl?.map (blank u) = s.tl?.map (blank u) := congrArg (·.tl) hφ
  rw [htl] at h1
  obtain ⟨tls, hs, hbl⟩ := Option.map_eq_some_iff.1 h1.symm
  have hh : tls.heard = tl.heard := congrArg (·.heard) hbl
  obtain ⟨F, F', G, g', rs, -, -, hL, hg', -, -, -⟩ := L
  have hg2 : tls.heard = some g' := by
    have := hg'
    simp only [hs, Option.bind_some] at this
    exact this
  obtain rfl : g' = g := Option.some.inj (hg2.symm.trans (hh.trans hg))
  have hq1 : (pi8 (fixed9 (phiAll u ψ) s).1).1 = some (blank u tls) := by
    show s.tl?.map (blank u) = _
    rw [hs]
    rfl
  have sd := ((hc _ hok).dig (blank u tls) v hq1 hv).same
  have f9s : tls.f9 = tlD.f9 := sd.f9
  have f9e : tl.f9 = tls.f9 := (congrArg (·.f9) hbl).symm
  have z1e : tl.z1 = tlD.z1 := ((congrArg (·.z1) hbl).symm : tl.z1 = tls.z1).trans sd.z1
  have z2e : tl.z2 = tlD.z2 := ((congrArg (·.z2) hbl).symm : tl.z2 = tls.z2).trans sd.z2
  refine ⟨(f9e.trans f9s).trans hL.shape.symm, by rw [hL.shape]; exact P2, fun q hq => ?_⟩
  rw [hL.zkLen q (P3 q hq).1, (P3 q hq).2]
  unfold HTailF2.zOf
  rw [z1e, z2e]

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.three_of_leftOn
