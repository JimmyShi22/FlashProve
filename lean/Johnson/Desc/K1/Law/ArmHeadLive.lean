-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmHeadLive.lean: THE OUTPUT HEAD's CONJUNCT OF THE LETTER J (JHead,
Johnson/Desc/K1/Law/ArmHeadJ.lean): ITS CLAUSE hlay (the open link's own copy of the rows' layout is the
written one) FALLS TO A FACT THAT HAS A PAYER ALONG THE REACHED STATES: "the layout of the copy in use is
the public one" (First.FoldFacts.liveLayout, Johnson/Desc/First/FoldFacts.lean): where a link is open the
copy in use is the link's. So of JHead THREE clauses stay. A definition, and statements with their proofs.

Main names:
  layout_of_live      the step from the copy in use to the open segment's part.
  HeadLeft7 · JHead3  what stays: hT hRun hMats.
  jHead_of_live       **JHead from JHead3 and the fact on the copy in use.**
What is not claimed. JHead3 at any state. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.ArmHeadJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc.First (S Here HeadOwn Numbers)

/-- Where a segment's part is open, the copy in use is the open link's. -/
theorem layout_of_live {s : S} {a : K9.Part} {lay6 : OnBytes.Params.ReqLayout}
    (hA : K9.segAt? s = some a) (h : s.live.rows.layout = lay6) :
    a.L.check.rows.layout = lay6 := by
  have hL : s.link? = some a.L := by
    unfold K9.segAt? at hA
    cases e1 : s.link? with
    | none =>
      rw [e1] at hA
      cases hA
    | some L =>
      cases e2 : s.fork? with
      | none =>
        rw [e1, e2] at hA
        cases hA
      | some F0 =>
        cases e3 : s.tl? with
        | none =>
          rw [e1, e2, e3] at hA
          cases hA
        | some t0 =>
          rw [e1, e2, e3] at hA
          rw [← Option.some.inj hA]
  unfold S.live at h
  rw [hL] at h
  exact h

section
open VerifiableInference.Desc.Kinds.Head.Law VerifiableInference.Desc.Kinds.Head
  VerifiableInference.Desc.Kinds
open OnBytes (E zeroE)
open OnBytes.Model (World Reading HFun HTailF2 Fork)
open OnBytes.Model.Verify (borderOf publicOf layerShape)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.K9 (Readers RunOf)

/-- **What stays of HeadRest: three clauses on the state in front alone.** -/
structure HeadLeft7 (X : OnBytes.Model.Verify.Public) (own : List (Nat × Nat)) (s : S)
    (a : K9.Part) (arr : Nat → Nat → Nat) (N : Numbers) (num : Nat → Nat → Nat)
    (lay6 : OnBytes.Params.ReqLayout) : Prop where
  hT : K6HeardAt X.hS (readsOf X) (parOf X.hS (workOf X)) s
  hRun : ∀ e v, withTables (p8K6 X 24) s = some e →
      lettersAt (parOf X.hS (workOf X)) (seatAt X.hS (readsOf X)) e = .ok v →
      ∃ o cov x t, e.here = .head o ∧ e.covered X.hS.T X.hS.V = .ok cov ∧ o.x = some x ∧
        o.t = some t ∧ K8.ReadsQuiet.tables X.hS X.HLy X.H cov x = .ok t ∧
        (letI := v.1
         letI := v.2.1
         RunIs ⟨X.hS, X.HLy, borderOf X.y, X.H, cov, x, t, readsOf X⟩)
  hMats : MatsSeated (ColFour X.hS X.HLy (borderOf X.y)) arr N X own a num lay6

end

/-- JHead less hlay. -/
def JHead3 (X : OnBytes.Model.Verify.Public) (own : List (ℕ × ℕ)) (arr : ℕ → ℕ → ℕ) (N : Numbers)
    (num : ℕ → ℕ → ℕ) (lay6 : OnBytes.Params.ReqLayout) (s : S) : Prop :=
  ∀ o a, s.here = .head o → K9.segAt? s = some a → HeadLeft7 X own s a arr N num lay6

/-- **JHead from JHead3 and the fact on the copy in use.** -/
theorem jHead_of_live {X : OnBytes.Model.Verify.Public} {own : List (ℕ × ℕ)} {arr : ℕ → ℕ → ℕ}
    {N : Numbers} {num : ℕ → ℕ → ℕ} {lay6 : OnBytes.Params.ReqLayout} {s : S}
    (hl : s.live.rows.layout = lay6) (h : JHead3 X own arr N num lay6 s) :
    JHead X own arr N num lay6 s := fun o a ho ha =>
  have L := h o a ho ha
  ⟨L.hT, L.hRun, layout_of_live ha hl, L.hMats⟩

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.layout_of_live
#print axioms VerifiableInference.Desc.K1.jHead_of_live
