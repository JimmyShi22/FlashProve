-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/AtSeats/LayKAt.lean: THE TEST `layKB X 0` (Johnson/Desc/AtSeats/LayLinesAt.lean: at each feed-forward plan the plan's length
of the reads is at most the number of columns of the planned ledger's array of the reads) IS A THEOREM AT EVERY RETURN
OF THE PUBLIC PARAMETERS' MAKER: with "=" in "≤"'s place. By calls.
  `planG_third`      a feed-forward plan numbers its third vector as array 0: the library's `Fo.ZPlan.planG_u`'s own walk through
                   planG's text (OnBytes/Tie/Pv/Lookup/Ends/FoHasU.lean), with `made_third`
                   (Johnson/Desc/Kinds/Law/ReadsNamed.lean) in `tlU_made`'s place
  `public_G_third`   so at each plan of the public parameters
  `layKB_public`     **layKB X 0 = true**: `Meaning.Plan.public_G_K3` (Johnson/Goal/Meaning/PlanPort.lean)
  `layKB_scope`      in the goals' scope, at an opening, at the letter XV
  `jLay2_whole`      **JLay2 (Johnson/Desc/K1/Law/ArmLayIn.lean) along "reached", in hJ's own letters, WITH NO TEST LEFT**: jLay2_paid
                   (Johnson/Desc/AtSeats/PadAtRch.lean) at layKB_scope: left: hS hR O hOk · hDlk hlk hWX (on letters)
What is not claimed. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.PadAtRch
import Johnson.Desc.Kinds.Law.ReadsNamed
import Johnson.Goal.Meaning.PlanPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 Fo Fo.Pub Fo.ZPlan
open Fo.BatRows (bindE_ok ite_ok)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open VerifiableInference.Desc.Kinds.Head.Law.ReadsNamed (Third made_third)

/-- **A feed-forward plan numbers its third vector as array 0.** -/
theorem planG_third (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : Third hp.tl := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain rfl := pureE_ok hy
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    exact made_third hS hA (ownerIs_sameP tl1 g)
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy]
      exact made_third hS hA ((ownerIs_sameP tl1 g).trans (borderMeans_sameP hB))
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

theorem public_G_third (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) : Third hp.tl :=
  planG_third X.layers g _ hp (public_G h g hp hg)

/-- **The test says yes at every return of the public parameters' maker.** -/
theorem layKB_public (h : Verify.publicOf pol KL layout = .ok X) : layKB X 0 = true := by
  unfold layKB
  refine List.all_eq_true.2 fun hp hm => ?_
  obtain ⟨g, hg⟩ := List.mem_iff_getElem?.1 hm
  rw [Array.getElem?_toList] at hg
  have h3 := public_G_third h g hp hg
  have hu : u3Of hp.tl = 0 := by
    unfold u3Of
    rw [show hp.tl.ix.U.getD 2 none = some 0 from h3]
    rfl
  rw [hu, Meaning.Plan.public_G_K3 h g hp hg h3]
  simp

end

/-- In the goals' scope, at an opening. -/
theorem layKB_scope {P : VerifierAndGoals.PublicFiles} {lay : ByteArray} {F : VerifiableInference.Desc.FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (VerifiableInference.Desc.Block VerifiableInference.Desc.First.S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {XV : Verify.Public} (hWX : Bs.G₀.W = XV) : layKB XV 0 = true :=
  hWX ▸ layKB_public O.public

open VerifiableInference.Desc.Sound (linksFull onQ Frame) in
open VerifiableInference.Desc.First (S Numbers Meaning flatPlacesOf) in
open Johnson.Desc.First.Walk.Tied (RchAt) in
/-- **JLay2 ALONG "REACHED", WITH NO TEST LEFT.** -/
theorem jLay2_whole {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : VerifiableInference.Desc.FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (VerifiableInference.Desc.Block S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    {Xi Tok : Type} {rows cols nR : ℕ} {XV : Verify.Public}
    (Dm : VerifiableInference.Desc.Sound.MgData Xi ProofFile.InstPub Tok rows cols nR XV)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hOk : ∀ b ∈ c.blocksInOrder, b.planOk = true ∧ b.shaped = true) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hWX : Bs.G₀.W = XV) {W : Type} {Fr : Frame}
    (N : Numbers) (Mg : Meaning ProofFile.InstPub W) :
    ∀ l, l < 25 → ∀ a : (ProofFile.InstPub × S) × Fr.E.Str,
      RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
        (14 * l + IM.k1Ix l false + 2) a →
      onQ N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) (14 * l + IM.k1Ix l false + 2) a →
      a.1.2.failed = none → JLay2 Dm a.1.2 :=
  jLay2_paid Dm hS hR O hOk hDlk hlk hWX (layKB_scope O hWX) N Mg

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.planG_third
#print axioms VerifiableInference.Desc.K1.public_G_third
#print axioms VerifiableInference.Desc.K1.layKB_public
#print axioms VerifiableInference.Desc.K1.layKB_scope
#print axioms VerifiableInference.Desc.K1.jLay2_whole
