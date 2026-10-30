-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/AtSeats/LayLinesAt.lean: THE FIVE LINES ON THE PUBLIC PARAMETERS THAT jLay2_at_reads LEAVES (`LayLines`,
Johnson/Desc/AtSeats/LayEntsAtRch.lean): FOUR ARE THEOREMS IN THE GOALS' SCOPE, BY CALLS; THE FIFTH IS A TEST WITH CODE.
  hm    the group's list of matrices has the layout's rows and columns: the public parameters' lists ARE the
        layout's (`IM.k4_of`'s clause tails = tailsOf y); `OnBytes.Road.matsR` by its text
  htm · hNM   the plan's parameters' list of matrices likewise, and its number is the list's size:
        `OnBytes.Road.planG_sizes` (Johnson/Road/FormsKeysPlan.lean) at `Fo.Pub.plansG_at`
  hg    the group's number is below the number of groups: `OnBytes.Road.Hd.plansFrom_length`
  hK    `layKB X d`: at each feed-forward plan: the plan's length of the reads + d is at most the number of columns of
        the planned ledger's array of the reads. d = 0: THE TEST. A large d: ITS BENT TWIN
  `layLines_scope`   **LayLines at every plan of the public parameters**, under layKB XV 0 = true
What is not claimed. The test's value at any public file. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.LayEntsAtRch
import Johnson.Road.FormsKeysPlan
import Johnson.Road.HeadDict
import OnBytes.Tie.Pv.Lookup.Ends.FoPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

/-- **The test for hK** (d = 0), and its bent twin (a large d). -/
def layKB (X : Verify.Public) (d : ℕ) : Bool :=
  X.G.toList.all fun hp =>
    decide (hp.nU.getD 2 0 + d ≤ ((hp.Fp.trees[u3Of hp.tl]?).map (·.K)).getD 0)

/-- **LayLines at every plan of the public parameters.** -/
theorem layLines_scope {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {XV : Verify.Public}
    (hWX : Bs.G₀.W = XV) (hKB : layKB XV 0 = true) :
    ∀ g hp, XV.G[g]? = some hp → LayLines XV g hp := by
  subst hWX
  intro g hp hg
  obtain ⟨_, _, x, _, _, _, _, _, _, xP, _, xT, xG⟩ := IM.k4_of hS hR O 0 (by omega)
  rw [xP] at xT xG
  have hpl := Fo.Pub.plansG_at _ _ xG g hp hg
  obtain ⟨s1, s2⟩ := OnBytes.Road.planG_sizes hpl
  have hm : ((Bs.G₀.W.layers.tails.getD g {}).mats.map fun M => (M.m, M.k)) =
      OnBytes.Road.matsR Bs.G₀.W.layers.y g := by
    unfold OnBytes.Road.matsR
    rw [xT]
  refine ⟨?_, hm, ?_, s1.trans hm, s2⟩
  · have hmem : hp ∈ Bs.G₀.W.G.toList := by
      obtain ⟨hlt, e⟩ := Array.getElem?_eq_some_iff.1 hg
      rw [← e]
      exact Array.getElem_mem_toList hlt
    simpa using List.all_eq_true.1 hKB hp hmem
  · obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.1 hg
    unfold Layer.plansG at xG
    cases hq : Layer.plansFrom Bs.G₀.W.layers Bs.G₀.W.layers.y.NGr 0 none with
    | error e =>
      rw [hq] at xG
      cases xG
    | ok l =>
      rw [hq] at xG
      have e : l.toArray = Bs.G₀.W.G := Except.ok.inj xG
      have hlen := OnBytes.Road.Hd.plansFrom_length _ _ _ _ l hq
      rw [← e] at hlt
      simpa [hlen] using hlt

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.layLines_scope
