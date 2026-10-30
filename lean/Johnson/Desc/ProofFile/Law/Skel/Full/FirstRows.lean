-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/FirstRows.lean: THE JOIN OF THE FIFTEEN LOTS' FIRST ROWS: the
theorems on each lot's sub-protocols' skeletons, called by name and laid into the fifteen premises
r0 … r14 of `desc_decl_at_full` (Full/DescDeclAt.lean); then that theorem at both joins. Calls
alone.
  `k1_tie`               K1's written lot is a plain lot's skeleton
  `spots_at_cut`         from `Z.cuts = cutWritten`: the places are the written ones (q₁)
  `shape_at_cut`         from the same and h₄: the shape is the written one (q₂)
  `first_rows`           ⊢ `RowAt G L lotN` at each of the fifteen lots, as one conjunction
  `first_rows_all`       ⊢ `List.Forall₂ (RowAt G) (onlineFirstChainBlockTables Z) wsW`
  `decl_first_at_rows`   ⊢ there is a chain c with: `onlineDescription OnBytes.secondHashFunction P.pol lay P.KL` returns
                         the description F over c; `c.blocksInOrder.map skel = flatW`;
                         `F.roundsDeclaredByBlocks.1 = declProofFull.1`
THE PREMISES ARE THE UNION OF THE ROWS' OWN, EACH UNDER A NAME THAT SAYS WHOSE. hS hR hZ hG: in
scope, the files read, the public part Z at the second hash function, the blank ground G (hZ makes
Z of P.pol, P.KL and a layout file lay, WHICH IS A LETTER OF ITS OWN: nothing here ties it to P, of
which hS and hR speak). cW: the cut is the written one (K4 · K8 · K11 · K13 · K6; and q₁, q₂). e9:
the declared rounds' entries are the written ones (K4 · K8 · K9 · K11 · K13 · K6). The frames: l0 g0
a0 p0 d0 m0. K1: c1 s1 l1 g1. K2: z2 u1 u2 t3 t4 t5 b2. K3: R3. K4: n4. K5: q5 m5. K8: k8 n8. K9: g9
t9. K12: v12. K13's three lots: r13 c13 l13 g11. K6 · K7 ASK NOTHING MORE. `decl_first_at_rows`
takes besides: what `second_rows` (Full/SecondRows.lean) alone asks: w5 a5 t8 w13 n6 (n6 is a closed
statement, left as a premise); h₄: the sorts are the written ones; hA hB rA rB: the two later seats.
The three lots' batchings' steadiness is called by name.
Limits. A JOINING: IT PAYS NO PREMISE; that the premises can be met together is not shown here (a
caller that meets them at the full size: Johnson/AtFull/Top/Spine.lean). ALL PREMISES ARE
HYPOTHESES: where a caller meets some of them (cW e9 t3 t4 g9 are such) by reading fields off a
value of Z that is written out, they count only together with a proof that this written value is
what `pubPlain` returns at the public files. Of the rows' files only the statements that are called
have been read for this file. The first chain alone. At the second hash function alone. The full
size alone. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Full.SecondRows
import Johnson.Desc.ProofFile.Law.Skel.Full.Lot00
import Johnson.Desc.ProofFile.Law.Skel.Full.Lot01
import Johnson.Desc.ProofFile.Law.Skel.Full.Lot03
import Johnson.Desc.ProofFile.Law.Skel.Full.Lot04
import Johnson.Desc.ProofFile.Law.Skel.Full.Lot05
import Johnson.Desc.ProofFile.Law.Skel.Full.Lot08
import Johnson.Desc.ProofFile.Law.Skel.Full.Lot09
import Johnson.Desc.ProofFile.Law.Skel.Full.Lot10
import Johnson.Desc.ProofFile.Law.Skel.Full.Lot11
import Johnson.Desc.ProofFile.Law.Skel.Full.Lot12
import Johnson.Desc.ProofFile.Law.Skel.Full.Lot13
import Johnson.Desc.ProofFile.Law.Skel.Full.Lot14
import Johnson.AtFull.Desc.Lots.K1.View
import Johnson.AtFull.Desc.Lots.K2RowScope
import Johnson.AtFull.Desc.Lots.K3RowScope
import Johnson.Desc.First.Att.Row.K5RowSix
import Johnson.AtFull.Desc.Lots.K8RowFull
import Johnson.AtFull.Desc.Lots.K9RowFull
import Johnson.AtFull.Desc.Lots.K11RowScope
import Johnson.Loose.H2K12.K12RowSkel
import Johnson.AtFull.Desc.Lots.K6RowOwner
import Johnson.AtFull.Desc.Lots.H1RowScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk
open VerifiableInference.Desc
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Number.ByRuns (proofThree)
open Johnson.AtFull.ProofRows (declProofFull)

theorem k1_tie : Johnson.AtFull.Desc.K1Lot.k1LotW =
    plainK "the commitments (K1)" Johnson.AtFull.Desc.K1Lot.k1LotW.blocks := rfl

theorem spots_at_cut {Z : Pub} (cW : Z.cuts = Johnson.AtFull.Cut.cutWritten) :
    spotsOf Z.cuts = some spotsW := by
  rw [cW, spots_tie]
  exact Johnson.AtFull.Desc.spots_written

theorem shape_at_cut {Z : Pub} (cW : Z.cuts = Johnson.AtFull.Cut.cutWritten)
    (h₄ : subsOf Z = subsW) : shapeOf Z = .ok shapeW := by
  rw [shape_tie]
  exact Johnson.AtFull.Desc.shapeOf_written cW (h₄.trans subs_tie)

theorem first_rows {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : Pub} {G : Ground}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z) (hG : blankBy pureRoad.links Z = some G)
    (cW : Z.cuts = Johnson.AtFull.Cut.cutWritten)
    (e9 : Z.D.1.map (·.entry) = Johnson.AtFull.Desc.Lots.esW)
    (l0 : Z.p.built.links.toList.map P1L20.Row.viewL = P1L20.Row.viewW) (g0 : Z.p.X.G.size = 12)
    (a0 : Z.p.X.A.size = 12) (p0 : Z.p.X.layers.y.h.p4 = true)
    (d0 : (Z.first.shape.link.map (·.plain)).take 24 = P1L20.Row.plainW)
    (m0 : ∀ l < 25, P1L20.Row.sameB Z.p.built.links Z.p.X l = true)
    (c1 : G.first.codes = Johnson.G.codesFull2) (s1 : G.first.shape = proofSizedFull.request)
    (l1 : G.first.layout = Johnson.G.layoutFull) (g1 : Z.P.samples = 1)
    (z2 : Z.p.chains.made.sized.proof = proofSizedFull)
    (u1 : proofSizedFull.request = Z.first.shape) (u2 : proofSizedFull.codes = Z.first.codes)
    (t3 : Z.s₀.st.codes = proofSizedFull.codes)
    (t4 : Z.s₀.check.frame.shape = proofSizedFull.request)
    (t5 : proofSizedFull.set.samples = Z.P.samples)
    (b2 : Z.p.X.owner.tl.kTX.back? = some (OnBytes.Model.Verify.borderOf Z.p.X.y).kxb)
    (R3 : Johnson.AtFull.Lots.K3.ReadsLeft Z)
    (n4 : ∀ g < 12, ∀ hp, G.W.G[g]? = some hp →
      Johnson.AtFull.Rounds.numsOf G.W.layers hp = Johnson.AtFull.Rounds.numsW g)
    (q5 : ∀ g, g < 12 → ∀ a, Z.p.X.A[g]? = some a →
      VerifiableInference.Desc.First.Att.P.claimsOkAtQ a = true)
    (m5 : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan])
    (k8 : G.built.toList.map (fun X => (X.kind, X.name)) = P1K8L.k8KindsW)
    (n8 : P1K8L.k8GroundB G = true)
    (g9 : Z.s₀.check.frame.groups = Johnson.AtFull.Desc.Lots.groupsW)
    (t9 : ∀ l ∈ lsW, (VerifiableInference.Desc.K9.testsWhere Z.p.X l 0).isSome =
      Johnson.AtFull.Desc.Lots.twW l)
    (v12 : H2U.p12OfMade Z.made = H2K.Member.piLFull) (r13 : Z.first.pendingRows = 13)
    (c13 : Z.first.codes = proofSizedFull.codes) (l13 : Z.first.lin = proofSizedFull.batch.shape)
    (g11 : VerifiableInference.Desc.K1.ownGroup Z.first = 31) :
    RowAt G (framesLot Z) lot0 ∧ RowAt G (k1Pure Z) lot1 ∧ RowAt G (k2Pure Z) lot2 ∧
      RowAt G (K3Lot.lot Z) lot3 ∧ RowAt G (k4Lot Z) lot4 ∧ RowAt G (H2K5.lotN Z) lot5 ∧
      RowAt G (P1K8.lot Z) lot6 ∧ RowAt G (k9Ninth Z) lot7 ∧ RowAt G (K11.lot Z) lot8 ∧
      RowAt G (VerifiableInference.Desc.K12.lot Z) lot9 ∧
      RowAt G (VerifiableInference.Desc.K13.lot Z) lot10 ∧
      RowAt G (VerifiableInference.Desc.K13.lot4 Z) lot11 ∧
      RowAt G (VerifiableInference.Desc.K13.lotEnd Z) lot12 ∧
      RowAt G (P4.k6Lot Z) lot13 ∧ RowAt G Johnson.AtFull.Lots.h1Lot lot14 := by
  have q₁ := spots_at_cut cW
  have eW : Z.D.1.map (·.entry) = Johnson.AtFull.K4Sent.esWritten := e9
  have k10 : Z.first.lin.kCol = 18 := by
    rw [l13]
    exact VerifiableInference.Desc.K13.LotRows.m3_written.2.2.1
  exact ⟨row0 (P1L20.Row.frames_lotSk l0 g0 a0 p0 d0 m0 G),
    row1 ((Johnson.AtFull.Desc.K1Lot.k1_row_in_scope hS hR hZ hG c1 s1 l1 g1).trans k1_tie),
    Johnson.AtFull.Lots.K2.k2_lotW_scope hS hR hZ hG (spots_at_written q₁) z2 u1 u2 t3 t4 t5 b2
      asW lsW,
    row3 (Johnson.AtFull.Lots.K3.k3_row_scope hS hR hZ hG R3 G),
    row4 (Johnson.AtFull.K4Sent.k4_lot_skel hS hR hZ hG cW eW fun g hg hp h =>
      Johnson.AtFull.K4Sent.len_of_nums (n4 g hg hp h)),
    row5 (H2K5.Row.k5_lot_skel_six hS hR hZ hG q5 m5),
    P1K8L.k8_lotW_at cW eW k8 n8 asW lsW,
    Johnson.AtFull.Desc.Lots.k9_row_full Z G q₁ e9 g9 t9,
    row8 (Johnson.AtFull.Lots.K11Row.k11_lotSk_scope hS hR hZ hG cW eW),
    row9 (H2K12.k12_lot_skel Z G v12),
    row10 (VerifiableInference.Desc.K13.LotRows.lot_row G cW eW k10 r13),
    row11 (VerifiableInference.Desc.K13.LotRows.lot4_row G c13 l13 g11),
    row12 (VerifiableInference.Desc.K13.LotRows.lotEnd_row G eW),
    row13 (Johnson.AtFull.Lots.k6_row_scope6 hS hR hZ hG cW eW),
    row14 (Johnson.AtFull.Lots.h1_row_scope hS hR hZ hG)⟩

theorem first_rows_all {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : Pub}
    {G : Ground}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z) (hG : blankBy pureRoad.links Z = some G)
    (cW : Z.cuts = Johnson.AtFull.Cut.cutWritten)
    (e9 : Z.D.1.map (·.entry) = Johnson.AtFull.Desc.Lots.esW)
    (l0 : Z.p.built.links.toList.map P1L20.Row.viewL = P1L20.Row.viewW) (g0 : Z.p.X.G.size = 12)
    (a0 : Z.p.X.A.size = 12) (p0 : Z.p.X.layers.y.h.p4 = true)
    (d0 : (Z.first.shape.link.map (·.plain)).take 24 = P1L20.Row.plainW)
    (m0 : ∀ l < 25, P1L20.Row.sameB Z.p.built.links Z.p.X l = true)
    (c1 : G.first.codes = Johnson.G.codesFull2) (s1 : G.first.shape = proofSizedFull.request)
    (l1 : G.first.layout = Johnson.G.layoutFull) (g1 : Z.P.samples = 1)
    (z2 : Z.p.chains.made.sized.proof = proofSizedFull)
    (u1 : proofSizedFull.request = Z.first.shape) (u2 : proofSizedFull.codes = Z.first.codes)
    (t3 : Z.s₀.st.codes = proofSizedFull.codes)
    (t4 : Z.s₀.check.frame.shape = proofSizedFull.request)
    (t5 : proofSizedFull.set.samples = Z.P.samples)
    (b2 : Z.p.X.owner.tl.kTX.back? = some (OnBytes.Model.Verify.borderOf Z.p.X.y).kxb)
    (R3 : Johnson.AtFull.Lots.K3.ReadsLeft Z)
    (n4 : ∀ g < 12, ∀ hp, G.W.G[g]? = some hp →
      Johnson.AtFull.Rounds.numsOf G.W.layers hp = Johnson.AtFull.Rounds.numsW g)
    (q5 : ∀ g, g < 12 → ∀ a, Z.p.X.A[g]? = some a →
      VerifiableInference.Desc.First.Att.P.claimsOkAtQ a = true)
    (m5 : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan])
    (k8 : G.built.toList.map (fun X => (X.kind, X.name)) = P1K8L.k8KindsW)
    (n8 : P1K8L.k8GroundB G = true)
    (g9 : Z.s₀.check.frame.groups = Johnson.AtFull.Desc.Lots.groupsW)
    (t9 : ∀ l ∈ lsW, (VerifiableInference.Desc.K9.testsWhere Z.p.X l 0).isSome =
      Johnson.AtFull.Desc.Lots.twW l)
    (v12 : H2U.p12OfMade Z.made = H2K.Member.piLFull) (r13 : Z.first.pendingRows = 13)
    (c13 : Z.first.codes = proofSizedFull.codes) (l13 : Z.first.lin = proofSizedFull.batch.shape)
    (g11 : VerifiableInference.Desc.K1.ownGroup Z.first = 31) :
    List.Forall₂ (RowAt G) (onlineFirstChainBlockTables Z) wsW := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13', r14⟩ :=
    first_rows hS hR hZ hG cW e9 l0 g0 a0 p0 d0 m0 c1 s1 l1 g1 z2 u1 u2 t3 t4 t5 b2 R3 n4 q5 m5 k8
      n8 g9 t9 v12 r13 c13 l13 g11
  exact rows_fifteen (Johnson.AtFull.Lots.p4Pure_two Z) r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12
    r13' r14

theorem decl_first_at_rows {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : Pub}
    {G : Ground} {A : SharedSeat} {B : SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z) (hG : blankBy pureRoad.links Z = some G)
    (cW : Z.cuts = Johnson.AtFull.Cut.cutWritten)
    (e9 : Z.D.1.map (·.entry) = Johnson.AtFull.Desc.Lots.esW)
    (l0 : Z.p.built.links.toList.map P1L20.Row.viewL = P1L20.Row.viewW) (g0 : Z.p.X.G.size = 12)
    (a0 : Z.p.X.A.size = 12) (p0 : Z.p.X.layers.y.h.p4 = true)
    (d0 : (Z.first.shape.link.map (·.plain)).take 24 = P1L20.Row.plainW)
    (m0 : ∀ l < 25, P1L20.Row.sameB Z.p.built.links Z.p.X l = true)
    (c1 : G.first.codes = Johnson.G.codesFull2) (s1 : G.first.shape = proofSizedFull.request)
    (l1 : G.first.layout = Johnson.G.layoutFull) (g1 : Z.P.samples = 1)
    (z2 : Z.p.chains.made.sized.proof = proofSizedFull)
    (u1 : proofSizedFull.request = Z.first.shape) (u2 : proofSizedFull.codes = Z.first.codes)
    (t3 : Z.s₀.st.codes = proofSizedFull.codes)
    (t4 : Z.s₀.check.frame.shape = proofSizedFull.request)
    (t5 : proofSizedFull.set.samples = Z.P.samples)
    (b2 : Z.p.X.owner.tl.kTX.back? = some (OnBytes.Model.Verify.borderOf Z.p.X.y).kxb)
    (R3 : Johnson.AtFull.Lots.K3.ReadsLeft Z)
    (n4 : ∀ g < 12, ∀ hp, G.W.G[g]? = some hp →
      Johnson.AtFull.Rounds.numsOf G.W.layers hp = Johnson.AtFull.Rounds.numsW g)
    (q5 : ∀ g, g < 12 → ∀ a, Z.p.X.A[g]? = some a →
      VerifiableInference.Desc.First.Att.P.claimsOkAtQ a = true)
    (m5 : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan])
    (k8 : G.built.toList.map (fun X => (X.kind, X.name)) = P1K8L.k8KindsW)
    (n8 : P1K8L.k8GroundB G = true)
    (g9 : Z.s₀.check.frame.groups = Johnson.AtFull.Desc.Lots.groupsW)
    (t9 : ∀ l ∈ lsW, (VerifiableInference.Desc.K9.testsWhere Z.p.X l 0).isSome =
      Johnson.AtFull.Desc.Lots.twW l)
    (v12 : H2U.p12OfMade Z.made = H2K.Member.piLFull) (r13 : Z.first.pendingRows = 13)
    (c13 : Z.first.codes = proofSizedFull.codes) (l13 : Z.first.lin = proofSizedFull.batch.shape)
    (g11 : VerifiableInference.Desc.K1.ownGroup Z.first = 31)
    (w5 : Johnson.AtFull.Rounds.k5Work G.W = 0)
    (a5 : ∀ x ∈ H2K5.k5Places G, ∀ a, G.W.A[x.2.2]? = some a →
      a.own = Johnson.AtFull.Rounds.k5OwnW a.own.rows)
    (t8 : P1K8L.k8TritsB G = true)
    (w13 : Johnson.AtFull.Rounds.K13.worksM3 Z.cuts Z.plans.1 = (0, 0, 0))
    (n6 : nameW ⟨1, some 24, 4, .K6⟩ = "H:4") (h₄ : subsOf Z = subsW)
    (hA : ((onlineSharedChain Z).map fun A => (A.lot, A.standIns)) = sharedW)
    (hB : ((onlineLastChain Z).map fun A => (A.lot, A.standIns)) = secondW)
    (rA : onlineSharedChain Z = some A) (rB : onlineLastChain Z = some B) :
    ∃ c, onlineDescription OnBytes.secondHashFunction P.pol lay P.KL =
        .ok (fileDescBy OnBytes.secondHashFunction pureRoad.links Z A B (fun s => s) (startS Z) c) ∧
      c.blocksInOrder.map skel = flatW ∧
      (fileDescBy OnBytes.secondHashFunction pureRoad.links Z A B (fun s => s) (startS Z) c).roundsDeclaredByBlocks.1 =
        declProofFull.1 := by
  have q₁ := spots_at_cut cW
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13', r14⟩ :=
    first_rows hS hR hZ hG cW e9 l0 g0 a0 p0 d0 m0 c1 s1 l1 g1 z2 u1 u2 t3 t4 t5 b2 R3 n4 q5 m5 k8
      n8 g9 t9 v12 r13 c13 l13 g11
  exact desc_decl_at_full hZ q₁ (shape_at_cut cW h₄) hG h₄ (Johnson.AtFull.Lots.p4Pure_two Z)
    r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13' r14
    (Johnson.AtFull.Desc.Lots.k9_steady Z G) (Johnson.AtFull.Lots.k6_steady Z G)
    (Johnson.AtFull.Lots.h1_steady G) hA hB rA rB
    (second_rows hS hR hZ hG c1 s1 q₁ z2 u1 u2 t3 t4 t5 R3 n4 w5 a5 k8 t8 e9 g9 v12 w13 r13 c13
      l13 n6)
    (k9_at_spots q₁ e9) (Johnson.AtFull.Rounds.k6_no_batch Z G)
    (Johnson.AtFull.Rounds.h1_no_batch G)

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.k1_tie
#print axioms ProofFile.Sk.Full.spots_at_cut
#print axioms ProofFile.Sk.Full.shape_at_cut
#print axioms ProofFile.Sk.Full.first_rows
#print axioms ProofFile.Sk.Full.first_rows_all
#print axioms ProofFile.Sk.Full.decl_first_at_rows
