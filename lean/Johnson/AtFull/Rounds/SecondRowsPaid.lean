-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/SecondRowsPaid.lean: THE JOIN OF THE FIFTEEN LOTS' SECOND ROWS
(`ProofFile.Sk.Full.second_rows`, Johnson/Desc/ProofFile/Law/Skel/Full/SecondRows.lean) WITH ITS 23
PREMISES BROUGHT DOWN TO ELEVEN: seven on the makers' returns, three statements on the public values
X₀, and one that stays as it is. Calls alone; no closed fact of its own.

What carries them. `Johnson.AtFull.Pub.rows_of_written` and `fields_of_written`
(Johnson/AtFull/Pub/FieldsOfWritten.lean) give, under seven premises on the makers' returns and hZ,
the fields of Z in the rows' letters. With `ProofFile.Law.blankBy_first`, five closed ties that lie in the
tree (`PlanWritten.codes_written`, `IM.samples_written`, `Second.Seam.codes_written`,
`OnBytes.Road.K4.shape_one`, `ProofFile.Sk.Full.spots_tie`), `spots_written`
(Johnson/AtFull/Desc/SpotsWritten.lean), `entries_at` (Johnson/AtFull/Rounds/EntriesW.lean),
`works_of_pub` (Johnson/AtFull/Rounds/K13.lean) and `k6_nameW` (Johnson/AtFull/Rounds/K6Name.lean)
they give SIXTEEN: c1 s1 (K1) · q₁ z2 u1 u2 t3 t4 t5 (K2) · e9 g9 (K9) · w13 r13 c13 l13 (K13) · n6
(K6). Where a called theorem names the written first chain's entries by another constant of the
same text, the two are one by unfolding.
IN THE GOALS' SCOPE, THREE: w5 (K5) by `LPFK9.work_at_blank` (Johnson/LPFK9R/WorkFieldRequest.lean)
and `k5Work_of` (Johnson/AtFull/Rounds/K5Work.lean) · a5 (K5) by `H2K5.Row.k5_hA`
(Johnson/Desc/First/Att/Row/K5OwnAtPlacesW.lean) · k8 (K8) by `LinksScope.kinds_in_scope`
(Johnson/AtFull/Desc/Lots/LinksInScope.lean).
ONTO THREE STATEMENTS ON X₀, through `ProofFile.Law.blankBy_W` (G.W = Z.p.X) and Z.p.X = X₀: R3 (K3) onto
(hB), by `readsLeft_of` and `readsX_of` (Johnson/AtFull/Desc/Lots/K3RowX.lean, K3RowXB.lean) · n4
(K4) onto (hn) · t8 (K8) onto (hs), by `k8TritsB_of_sums` (Johnson/AtFull/Rounds/K8TritsTie.lean),
`LPFK9.colSum_layers` and `colSum_fold` (Johnson/LPFK9R/ColSumLayers.lean, ColSumFold.lean).

  `spots_of_cuts`: where the table of stretches is the written one, its places are `spotsW`.
  **`second_rows_paid`**: for public files in the goals' scope (hS, hR), where the public part Z
    (hZ) and the blank ground G (hG) are returned: from the seven (hX hm hF hz hpl u₃ u₄: u₃ at the
    written declared rounds `declProofFull`); (hB) `readsXB X₀ = true`; (hn) K4's fifteen numbers at
    X₀'s twelve layers' plans; (hs) each of X₀'s attention's plans has 10248 columns in its
    smallness test; (v12) K12's:
  `∀ L ∈ onlineFirstChainBlockTables Z, RowL G L`.
  **`k9_paid`**: the premise k9 of `desc_decl_at_full`, from the seven and hZ.

Limits. A JOINING: THE ELEVEN ARE PREMISES: that they can be met together is not shown here. At the
second hash function `OnBytes.secondHashFunction` alone. The first chain alone. The full size alone. Not an
example of the head. Nothing on soundness. On hiding nothing.

-/
import Johnson.Desc.ProofFile.Law.Skel.Full.SecondRows
import Johnson.AtFull.Pub.FieldsOfWritten
import Johnson.AtFull.Desc.Lots.K3RowXB
import Johnson.AtFull.Rounds.K6Name
import Johnson.AtFull.Rounds.EntriesW
import Johnson.IMR.SendsPinned
import Johnson.Desc.Ok.PlanWritten.SizedTestLaws
import Johnson.Second.Seam.CodesOneInScope
import Johnson.Road.K4.K4PlanTied
import Johnson.Desc.K1.Law.FirstMakeFacts
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.LPFK9R.WorkFieldRequest
import Johnson.AtFull.Rounds.K5Work
import Johnson.Desc.First.Att.Row.K5OwnAtPlacesW
import Johnson.AtFull.Desc.Lots.LinksInScope
import Johnson.AtFull.Rounds.K8TritsTie
import Johnson.LPFK9R.ColSumLayers
import Johnson.LPFK9R.ColSumFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Rounds

open OnBytes OnBytes.Model
open ProofFile (pubPlain blankBy pureRoad spotsOf onlineFirstChainBlockTables k9Ninth toldOf Root)
open ProofFile.Law (blankM)
open ProofFile.Sk (Lst)
open ProofFile.Sk.Full (spotsW spots_tie RowL second_rows k9_at_spots)
open VerifiableInference.PlanWritten (publicOfO proofSizedFull FirstWritten)
open VerifiableInference.PlanWritten.Joined (writtenSized)
open VerifiableInference.Number.ByRuns (proofThree)
open VerifiableInference.Desc.Key (madeAt fixedDigest)
open Johnson.G.OfPlan (Made declPOf)
open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.Desc (spots_written)
open Johnson.AtFull.ProofRows (declProofFull)
open Johnson.AtFull.Pub (rows_of_written fields_of_written)
open Johnson.AtFull.Lots.K3 (readsXB readsX_of readsLeft_of)

/-- Where the table of stretches is the written one, its places are `spotsW`. -/
theorem spots_of_cuts {Z : ProofFile.Pub} (h : Z.cuts = cutWritten) : spotsOf Z.cuts = some spotsW := by
  rw [h, spots_written, spots_tie]

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G : ProofFile.Ground}
  {X₀ : Verify.Public} {m : Made} {told : List Root × List Root × List Root}

/-- **The fifteen second rows, their 23 premises brought down to eleven**: in scope, under the two
returns: the seven premises on the makers' returns; three statements on X₀: hB, hn, hs; and one
that stays: v12. -/
theorem second_rows_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : blankBy pureRoad.links Z = some G)
    (hX : publicOfO OnBytes.secondHashFunction P.pol P.KL (some lay) = .ok X₀)
    (hm : madeAt X₀ lay fixedDigest = .ok m)
    (hF : FirstWritten m.p.chains.proof.first)
    (hz : m.p.chains.made.sized = writtenSized)
    (hpl : m.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan])
    (u₃ : declPOf (blankM m) = .ok declProofFull) (u₄ : toldOf (blankM m) = .ok told)
    (hB : readsXB X₀ = true)
    (hn : ∀ g, g < 12 → ∀ hp, X₀.G[g]? = some hp → numsOf X₀.layers hp = numsW g)
    (hs : ∀ a ∈ X₀.A, a.seam.tl.foldColumns = 10248)
    (v12 : H2U.p12OfMade Z.made = H2K.Member.piLFull) :
    ∀ L ∈ onlineFirstChainBlockTables Z, RowL G L := by
  obtain ⟨⟨f1, f2, f3, f4, -, -⟩, -, -, r4, r5, r6, r7, r8, r9⟩ :=
    rows_of_written hX hm hF hz hpl u₃ u₄ hZ
  obtain ⟨-, eX, -, -, -, -, eD, -, -, -⟩ := fields_of_written hX hm hF hz hpl u₃ u₄ hZ
  have eF := ProofFile.Law.blankBy_first hG
  have e9 := entries_at eD
  have RX : Johnson.AtFull.Lots.K3.ReadsX Z.p.X := by
    rw [eX]
    exact readsX_of hB
  have eW : G.W = X₀ := (ProofFile.Law.blankBy_W hG).trans eX
  have n4 : ∀ g < 12, ∀ hp, G.W.G[g]? = some hp → numsOf G.W.layers hp = numsW g := by
    rw [eW]
    exact hn
  have hpub : Verify.publicOf P.pol P.KL (some lay) = .ok Z.p.X := by
    have h := IM.ground_publicK hZ hG
    rwa [ProofFile.Law.blankBy_W hG] at h
  have sA : ∀ (g : ℕ) (a : Attention.Plan), Z.p.X.A[g]? = some a →
      LPFK9.colSum a.seam.tl = 10248 := by
    intro g a h
    rw [eX] at h
    obtain ⟨hi, e⟩ := Array.getElem?_eq_some_iff.1 h
    rw [LPFK9.colSum_fold]
    exact hs a (by rw [← e]; exact Array.getElem_mem hi)
  exact second_rows hS hR hZ hG
    (by rw [eF, f1]; exact VerifiableInference.PlanWritten.codes_written)
    (by rw [eF]; exact f3)
    (spots_of_cuts r5) r4 f3.symm f1.symm r7 r8 (IM.samples_written.trans r6.symm)
    (readsLeft_of (f1.trans Second.Seam.codes_written)
      (f3.trans OnBytes.Road.K4.shape_one.symm) RX)
    n4 (k5Work_of (LPFK9.work_at_blank hS hZ hG)) (H2K5.Row.k5_hA hS hR hZ hG)
    (Johnson.AtFull.Lots.LinksScope.kinds_in_scope hS hR hZ hG)
    (P1K8L.k8TritsB_of_sums hS hR hZ hG (fun _ _ h => LPFK9.colSum_layers hS hR hpub h) sA)
    e9 (r9.trans (congrArg OnBytes.reqGroups OnBytes.Road.K4.shape_one.symm)) v12
    (K13.works_of_pub
      (show ProofFile.pubBy (ProofFile.PlainG.madeOf OnBytes.secondHashFunction) ProofFile.plainStarts P.pol lay P.KL = .ok Z
        from hZ) r5 e9) f4 f1 f2 k6_nameW

/-- **The premise k9 of `desc_decl_at_full`**, under the seven premises on the makers' returns and
hZ. -/
theorem k9_paid (hZ : pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hX : publicOfO OnBytes.secondHashFunction P.pol P.KL (some lay) = .ok X₀)
    (hm : madeAt X₀ lay fixedDigest = .ok m)
    (hF : FirstWritten m.p.chains.proof.first)
    (hz : m.p.chains.made.sized = writtenSized)
    (hpl : m.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan])
    (u₃ : declPOf (blankM m) = .ok declProofFull) (u₄ : toldOf (blankM m) = .ok told) :
    ∀ p ∈ spotsW, ∀ mk, (k9Ninth Z).batch G p.place = some mk →
      ∀ g, Lst listAt p.name (mk g).rounds := by
  obtain ⟨-, -, -, -, r5, -, -, -, -⟩ := rows_of_written hX hm hF hz hpl u₃ u₄ hZ
  obtain ⟨-, -, -, -, -, -, eD, -, -, -⟩ := fields_of_written hX hm hF hz hpl u₃ u₄ hZ
  exact k9_at_spots (spots_of_cuts r5) (entries_at eD)

end Johnson.AtFull.Rounds

#print axioms Johnson.AtFull.Rounds.spots_of_cuts
#print axioms Johnson.AtFull.Rounds.second_rows_paid
#print axioms Johnson.AtFull.Rounds.k9_paid
