-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/K3X/CountsLaw.lean: the sixteen counts of padding keys of a layer sub-proof's lookup
on the calls, as written numbers.

The verifier counts, when it lays a layer sub-proof out, how many keys of each tree of the lookup
are padding: the field fo.pub of the layout (Lay.pubOfCall and layoutLook in
OnBytes/Model/LayerLayout.lean). It does so column by column, over 131,072 and more columns a call,
with a write into an array at each padding column. In Lean's kernel an array is a list, so that walk
was reckoned too long to evaluate there; it was not tried on its own. This file gets the sixteen
numbers without running that loop: the library's law pub_eq (Johnson/Road/FormsKeysPub.lean) says
that the verifier's count of a tree is the library's closed form padCount
(Inst/Model/FF/Index.lean: a sum over the layers that a tree holds, of which a group has four at
these sizes), and the closed form is evaluated.

  `countsW`: the sixteen written numbers.
  `trees_ref`, `padCount_ref`: at the library's reference sizes there are sixteen trees, and
    padCount is countsW, tree by tree. Proved by evaluation in Lean's kernel.
    `padCount_ref_no`: a negative test: with the first number raised by one the comparison fails.
  `counts_of_layout`: **for every layout that the verifier returns under the switches, at sizes
    that agree with the library's reference sizes and at the library's eight lines of calls,
    fo.pub = countsW.** A law: nothing of the layout is evaluated.
  `counts_in_scope`: the same at all public files in the goals' scope, wherever publicOf returns;
    `counts_in_scope_o`: wherever the same text with the hash as an argument returns, at the
    second hash function.

Limits. The numbers are the verifier's own count: that the key forms treat just these places as
padding is not said here. Nothing on soundness, completeness or hiding.

-/
import Johnson.Goal.Meaning.Pub34Scope
import Johnson.Road.FormsKeysPub
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.K3X
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Shape Env layout)
open Inst.Model.All (DF)
open Inst.Model.FFSeg (fams used NT padCount)

/-- **The sixteen written numbers**, tree by tree. -/
def countsW : Array Nat :=
  #[5040128, 4646912, 5040128, 4646912, 0, 0, 2097152, 2097152, 36306944, 36306944, 31326208,
    31326208, 33553408, 33553408, 0, 0]

/-- The library's number of trees at its reference sizes. -/
theorem trees_ref : NT DF = 16 := by decide +kernel

/-- The library's closed form at its reference sizes, tree by tree. -/
theorem padCount_ref : ∀ θ < 16, padCount DF θ = countsW.getD θ 0 := by decide +kernel

/-- A negative test. -/
theorem padCount_ref_no : decide (padCount DF 0 = countsW.getD 0 0 + 1) = false := by
  decide +kernel

/-- **THE LAW.** -/
theorem counts_of_layout {h : Shape} {pc : List (List String)} {v : Env}
    (hy : layout h pc = .ok v.y) (S : Switches h) (Z : Sized h DF) (hc : DF.cap = h.lidb)
    (hN : LinesAre v.y)
    (hfl : ∀ k : Fin 8, h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used DF k)) :
    v.y.fo.pub = countsW := by
  obtain ⟨h8, hl⟩ := lines_calls hN
  have H : ∀ cc : Fin 8, ∃ cd, v.y.calls[cc.val]? = some cd ∧
      cd.segs.map (·.name) = (fams cc).map segName ∧
      h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used DF cc) := fun cc => by
    obtain ⟨cd, a, b⟩ := hl cc
    exact ⟨cd, a, b, hfl cc⟩
  have hs : v.y.fo.pub.size = 16 := by
    rw [(pub_fold hy).1, NT_of_layout hy S Z hc h8 H, trees_ref]
  have hv : ∀ θ, θ < 16 → v.y.fo.pub.getD θ 0 = countsW.getD θ 0 := fun θ hθ => by
    rw [pub_eq hy S Z hc h8 H Inst.Model.FFSeg.ref_ok θ (by rw [trees_ref]; exact hθ)]
    exact padCount_ref θ hθ
  apply Array.ext
  · rw [hs]
    rfl
  · intro i h1 h2
    have h3 : i < 16 := hs ▸ h1
    have e := hv i h3
    simpa [Array.getD, h1, h2] using e

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Verify.Public}

/-- **At all public files in the goals' scope.** -/
theorem counts_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : Verify.publicOf Z.pol Z.KL lay = .ok X) : X.layers.y.fo.pub = countsW := by
  obtain ⟨hy, S, -, -, Zs, hc, hN, hfl, -⟩ := Meaning.P34.pub34_public hZ hR h
  exact counts_of_layout
    (v := { y := X.y, sc := X.layers.sc, g := 0, iU3 := 0, K3 := 0, tab := [], zk := #[] })
    hy S Zs hc hN hfl

/-- The same where `publicOfO` returns, at the second hash function. -/
theorem counts_in_scope_o (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL lay = .ok X) :
    X.layers.y.fo.pub = countsW :=
  counts_in_scope hZ hR ((VerifiableInference.PlanWritten.publicOfO_older _ _ _).symm.trans h)

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.trees_ref
#print axioms Johnson.AtFull.K3X.padCount_ref
#print axioms Johnson.AtFull.K3X.padCount_ref_no
#print axioms Johnson.AtFull.K3X.counts_of_layout
#print axioms Johnson.AtFull.K3X.counts_in_scope
#print axioms Johnson.AtFull.K3X.counts_in_scope_o
