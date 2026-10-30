-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/SecondRows.lean: the fifteen lots' second rows, joined: the
theorems of the lots' own modules on what each lot's sub-protocols declare are called by name and
laid, by `lots_all` (Full/PureLots.lean), into the one premise wl of `desc_decl_at_full`
(Full/DescDeclAt.lean); and the row of the batching of K9's lot into its premise k9. Four theorems:
calls alone.
  `second_rows`   ⊢ `∀ L ∈ onlineFirstChainBlockTables Z, RowL G L`
  `k9_at_spots`   ⊢ the premise k9
  `mem_written`, `spots_at_written`: this folder's written places are
                  `Johnson.AtFull.Desc.spotsWritten`: off `spots_tie` (Full/Ties.lean)
The premises are the union of the called theorems' own, each under a name that says whose it is. hS
hR hZ hG: in scope, the files read, the public part Z at the second hash function, the blank ground
G. K1: c1 s1. K2: q₁ (at this folder's `spotsW`: carried to the constant of K2's module by
`spots_tie`) z2 u1 u2 t3 t4 t5. K3: R3. K4: n4. K5: w5 a5. K8: k8 t8. K9: q₁ e9 g9. K12: v12. K13's
three lots: w13 r13 c13 l13. K6: n6. The frames' lot, K11's and K7's ask nothing beside hS … hG.
Limits. A JOINING: IT PAYS NO PREMISE; that they can be met together is not shown here.
The first
chain alone. At the second hash function alone. The full size alone. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Full.DescDeclAt
import Johnson.AtFull.Desc.Lots.FramesRounds
import Johnson.AtFull.Rounds.K1
import Johnson.AtFull.Desc.Lots.K2RoundsNamed
import Johnson.AtFull.Desc.Lots.K3RoundsRow
import Johnson.AtFull.Rounds.K4ByPlace
import Johnson.AtFull.Rounds.K5Spots
import Johnson.AtFull.Rounds.K8ByPlace
import Johnson.AtFull.Rounds.K9At
import Johnson.AtFull.Desc.Lots.K11RoundsNamed
import Johnson.Loose.H2K12.K12RowRoundsNamed
import Johnson.AtFull.Rounds.K13
import Johnson.AtFull.Rounds.K6
import Johnson.AtFull.Rounds.K7Name

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk
open VerifiableInference.Desc
open VerifiableInference.PlanWritten (proofSizedFull)

theorem mem_written {p : Spot} (hp : p ∈ spotsW) : p ∈ Johnson.AtFull.Desc.spotsWritten :=
  spots_tie ▸ hp

theorem spots_at_written {Z : Pub} (q₁ : spotsOf Z.cuts = some spotsW) :
    spotsOf Z.cuts = some Johnson.AtFull.Desc.spotsWritten := spots_tie ▸ q₁

theorem second_rows {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : Pub} {G : Ground}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : blankBy pureRoad.links Z = some G)
    (c1 : G.first.codes = Johnson.G.codesFull2) (s1 : G.first.shape = proofSizedFull.request)
    (q₁ : spotsOf Z.cuts = some spotsW) (z2 : Z.p.chains.made.sized.proof = proofSizedFull)
    (u1 : proofSizedFull.request = Z.first.shape) (u2 : proofSizedFull.codes = Z.first.codes)
    (t3 : Z.s₀.st.codes = proofSizedFull.codes)
    (t4 : Z.s₀.check.frame.shape = proofSizedFull.request)
    (t5 : proofSizedFull.set.samples = Z.P.samples)
    (R3 : Johnson.AtFull.Lots.K3.ReadsLeft Z)
    (n4 : ∀ g < 12, ∀ hp, G.W.G[g]? = some hp →
      Johnson.AtFull.Rounds.numsOf G.W.layers hp = Johnson.AtFull.Rounds.numsW g)
    (w5 : Johnson.AtFull.Rounds.k5Work G.W = 0)
    (a5 : ∀ x ∈ H2K5.k5Places G, ∀ a, G.W.A[x.2.2]? = some a →
      a.own = Johnson.AtFull.Rounds.k5OwnW a.own.rows)
    (k8 : G.built.toList.map (fun X => (X.kind, X.name)) = P1K8L.k8KindsW)
    (t8 : P1K8L.k8TritsB G = true)
    (e9 : Z.D.1.map (·.entry) = Johnson.AtFull.Desc.Lots.esW)
    (g9 : Z.s₀.check.frame.groups = Johnson.AtFull.Desc.Lots.groupsW)
    (v12 : H2U.p12OfMade Z.made = H2K.Member.piLFull)
    (w13 : Johnson.AtFull.Rounds.K13.worksM3 Z.cuts Z.plans.1 = (0, 0, 0))
    (r13 : Z.first.pendingRows = 13) (c13 : Z.first.codes = proofSizedFull.codes)
    (l13 : Z.first.lin = proofSizedFull.batch.shape)
    (n6 : nameW ⟨1, some 24, 4, .K6⟩ = "H:4") :
    ∀ L ∈ onlineFirstChainBlockTables Z, RowL G L := by
  have hs := spots_at_written q₁
  have k13 := Johnson.AtFull.Rounds.K13.three_lst G w13 r13 c13 l13
  exact lots_all (P := RowL G) (Johnson.AtFull.Lots.p4Pure_two Z)
    (rowL_of_name fun b hb => P1L20.Row.frames_rounds_at (lst_nil _) Z G b hb _)
    (rowL_of_name (Johnson.AtFull.Rounds.K1.k1_lst_in_scope hS hR hZ hG c1 s1))
    (rowL_of_name
      (Johnson.AtFull.Lots.K2.k2_lists_named_at_blank hZ hG hs z2 u1 u2 t3 t4 t5))
    (rowL_of_name (Johnson.AtFull.Lots.K3.k3_lists_scope hS hR hZ hG R3 G))
    (rowL_of_name (Johnson.AtFull.Rounds.k4_rounds_by_place hS hR hZ hG n4))
    (fun b hb p hp e =>
      Or.inr (Johnson.AtFull.Rounds.k5_row_spots Z G w5 a5 b hb p (mem_written hp) e))
    (rowL_of_name fun b hb => Or.inr (P1K8L.k8_lists_by_place k8 t8 b hb))
    (fun b hb p hp e =>
      Johnson.AtFull.Rounds.k9_row_spots Z G hs e9 g9 b hb p (mem_written hp) e)
    (rowL_of_name (Johnson.AtFull.Lots.K11Rounds.k11_row_scope_or hS hR hZ hG))
    (rowL_of_name fun b hb => Or.inr (H2K12.k12_row_named Z G v12 b hb))
    (rowL_of_name (k13 _ (List.mem_cons_self ..)))
    (rowL_of_name (k13 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    (rowL_of_name
      (k13 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
    (rowL_of_name (Johnson.AtFull.Rounds.k6_lists_at hS hR hZ hG nameW n6))
    (rowL_of_name (Johnson.AtFull.Rounds.h1_row_lists hS hR hZ hG))

theorem k9_at_spots {Z : Pub} {G : Ground} (q₁ : spotsOf Z.cuts = some spotsW)
    (e9 : Z.D.1.map (·.entry) = Johnson.AtFull.Desc.Lots.esW) :
    ∀ p ∈ spotsW, ∀ mk, (k9Ninth Z).batch G p.place = some mk →
      ∀ g, Lst Johnson.AtFull.Rounds.listAt p.name (mk g).rounds :=
  fun p hp mk h g =>
    Or.inr (Johnson.AtFull.Rounds.k9_batch_spots Z G (spots_at_written q₁) e9 p (mem_written hp)
      mk h g)

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.mem_written
#print axioms ProofFile.Sk.Full.spots_at_written
#print axioms ProofFile.Sk.Full.second_rows
#print axioms ProofFile.Sk.Full.k9_at_spots
