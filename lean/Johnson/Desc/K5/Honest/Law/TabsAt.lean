-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/TabsAt.lean: the three public premises of `tabs_reads`
(Johnson/Desc/K5/Honest/Law/Tabs.lean) paid at the numbers that the verifier's own text gives the
place of the smallness test's draw at an attention link (`ProofFile.k8Par`,
Johnson/Desc/ProofFile/Lot/K8.lean).

Main names:
  `k8Par_attention`: at a link X of the attention sort whose group has the plan A in the public
    parameters and whose smallness test's numbers are the plan's: the place's families are
    `K8.Asks.attention A.S`, its columns and rows those of the plan's list of matrices.
  `tabs_reads_k8Par`: so, behind a yes of the quiet step at the plan A, the closed list that the
    state bears has the shapes `K8.tabs (ProofFile.k8Par Z G X l)`.
  `tabs_reads_scope`: in the scope of the library's goals, with the public letters made at the
    function `OnBytes.secondHashFunction` (OnBytes/Hash/SecondHashFunction.lean) as the two lemmas that are called have it,
    the three premises on X hold at each of the twelve attention links: by `IM.ground_tails`
    (Johnson/IMR/K8Seat.lean) and `IM.ground_named` (Johnson/IMR/PureJoin.lean).

Limits. As in Tabs.lean: shapes alone; the state just behind the quiet step; nothing where the
step refuses. `tabs_reads_scope` is conditional on the scope, on the reading of the public files
and on the two returns by which the public letters are made.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.Tabs
import Johnson.Desc.ProofFile.Lot.K8
import Johnson.IMR.K8Seat
import Johnson.IMR.PureJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S K8.tabs K8.Asks.attention)
open VerifiableInference.Desc.First.Att

/-- **The place's numbers at an attention link.** Conditional: hk: the link is of the attention
sort; hA: the public parameters have the plan A at the link's group; htl: the link's smallness
test's numbers are the plan's. In the library's scope `tabs_reads_scope` pays the three. -/
theorem k8Par_attention (Z : ProofFile.Pub) (G : ProofFile.Ground) (X : Stages.LinkH) (l : ℕ)
    {A : Attention.Plan} (hk : X.kind = 1) (hA : G.W.A[X.g]? = some A) (htl : X.tl = A.seam.tl) :
    (ProofFile.k8Par Z G X l).asks = K8.Asks.attention A.S ∧
      (ProofFile.k8Par Z G X l).ks = A.mats.toList.map (·.k) ∧
      (ProofFile.k8Par Z G X l).ms = A.mats.toList.map (·.m) := by
  refine ⟨?_, ?_, ?_⟩
  · show ProofFile.k8Asks G X = _
    unfold ProofFile.k8Asks
    rw [hk, hA]
    rfl
  · show X.tl.mats.toList.map (·.k) = _
    rw [htl]
    rfl
  · show X.tl.mats.toList.map (·.m) = _
    rw [htl]
    rfl

/-- **Behind a yes of the quiet step the closed list has the shapes of the verifier's own place.**
Conditional on hk, hA, htl as above and on the step's yes. -/
theorem tabs_reads_k8Par (Z : ProofFile.Pub) (G : ProofFile.Ground) (X : Stages.LinkH) (l : ℕ)
    {A : Attention.Plan} (hk : X.kind = 1) (hA : G.W.A[X.g]? = some A) (htl : X.tl = A.seam.tl)
    {s s' : S} (h : readsAtSO A s = .ok s') :
    ∀ tl, s'.tl? = some tl →
      tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = K8.tabs (ProofFile.k8Par Z G X l) := by
  obtain ⟨a, b, c⟩ := k8Par_attention Z G X l hk hA htl
  exact tabs_reads A _ a b c h

/-- **In the library's scope, at each of the twelve attention links.** Conditional: hS: the public
input is in scope; hR: the public files are read; hZ, hG: the two returns by which the public
letters Z and G₀ are made, the first at the function `OnBytes.secondHashFunction`, of which nothing is asked
here. -/
theorem tabs_reads_scope {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    {G₀ : ProofFile.Ground} (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol lay Pb.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) :
    ∀ g < 12, ∃ (A : Attention.Plan) (X : Stages.LinkH),
      G₀.W.A[g]? = some A ∧ G₀.built[2 * g + 1]? = some X ∧
      ∀ s s', readsAtSO A s = .ok s' → ∀ tl, s'.tl? = some tl →
        tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) =
          K8.tabs (ProofFile.k8Par Z G₀ X (2 * g + 1)) := by
  intro g hg
  obtain ⟨_, A, _, X, _, eA, _, _, _, _, _, _, eX, etl, _⟩ := (IM.ground_tails hS hR hZ hG).1 g hg
  obtain ⟨_, X', _, _, _, _, eX', hk, hgX, _⟩ := (IM.ground_named hS hR hZ hG).1 g hg
  obtain rfl : X' = X := Option.some.inj (eX'.symm.trans eX)
  refine ⟨A, X', eA, eX, fun s s' h => tabs_reads_k8Par Z G₀ X' _ hk ?_ etl h⟩
  rw [hgX]
  exact eA

end H2K5.Honest

#print axioms H2K5.Honest.k8Par_attention
#print axioms H2K5.Honest.tabs_reads_k8Par
#print axioms H2K5.Honest.tabs_reads_scope
