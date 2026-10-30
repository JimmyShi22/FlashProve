-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K1/View.lean: THE 25 VIEWS THAT THE LOT OF THE COMMITMENTS READS ARE THE
WRITTEN ONES: from the ground's fields; and so in the goals' scope, behind the return of the public
part's maker and of the segments without a request: NO ENTRY TEST IS ASKED. It pays the fifth
hypothesis of `k1_row_at` (Johnson/AtFull/Desc/Lots/K1/Written.lean). Statements with their proofs;
nothing is evaluated.

  `kinds_at`, `seg_layers`, `seg_att`, `seg_head`   one segment's view, sort by sort
  `view_of_fields`   the 25, from: 25 segments; each one's kind and group; the plans are there; the
      third vector is in the layers' and the head's lists of arrays; the quiet step's test passes
  `ShpN`, `borderMeans_shp`, `planG_shp`, `ownerHeld_shp`, `planH2_shp`   one shape a matrix, at a
      layers' plan and at the head's: by the make: the library's `addTreesF_fits`
      (OnBytes/Tie/Pv/Tail/EndSame.lean) has it behind the list of arrays; what follows in the two
      planners keeps it. THE FOUR WALKS ARE ANOTHER FILE's, line by line: `borderMeans_gtU`,
      `planG_gtU`, `ownerHeld_gtU`, `planH2_gtU`
      (Johnson/Desc/Sound/K8Tests/PlanFitsOfPublic.lean), at another invariant
  `planned_of`, `planned_layers`, `planned_head`   **the quiet step's test on the plan
      (`K8.ReadsQuiet.planned`) is true at every return of publicOf**; "the list of tables is open":
      `planG_open`, `planH2_open` (Johnson/Goal/Meaning/HidOpen.lean)
  `third_there`   from that other file's `both_layers`, `both_head`
  `view_in_scope`   **MAIN**; kinds and groups: `IM.ground_named`, `IM.ground_gets`
      (Johnson/IMR/PureJoin.lean)
  `k1_row_in_scope`, `k1_blocks_in_scope`   so the lot's row, with four hypotheses by field left,
      all on the made parameters: TO BE PAID WITHOUT THE ENTRY TESTS' COMPARISONS

What is not claimed. That the maker returns anywhere. The four hypotheses. Nothing on soundness. No
example of the head is shown in this file; two, at storedPublicFiles and at zGap alone, are
AtFullSide.Top.headMember_zFull and headMember_zGap, whose own Limits say what they are worth.

-/
import Johnson.AtFull.Desc.Lots.K1.Written
import Johnson.Desc.Sound.K8Tests.PlanFitsOfPublic
import Johnson.Goal.Meaning.HidOpen
import Johnson.IMR.PureJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Desc.K1Lot

open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc.K1 (linkNumbers)
open VerifiableInference.Desc.K8.ReadsQuiet (planned)
open ProofFile (Ground Pub)
open OnBytes.Tie.Pv.Tail.Port (excBind_ok throw_bind_ne addTreesF_fits)

/-! ## 1 A segment's view, from the ground's fields -/

theorem kinds_at {G : Ground} {l : ℕ} {X : LinkH} (hX : G.built[l]? = some X) :
    (G.built.toList.map fun Y => (Y.kind, Y.g))[l]? = some (X.kind, X.g) := by
  rw [List.getElem?_map, Array.getElem?_toList, hX]
  rfl

theorem seg_layers {G : Ground} {l g : ℕ} {X : LinkH} {hp : Layer.HPlan2}
    (hX : G.built[l]? = some X) (hk : X.kind = 0) (hg : X.g = g) (hG : G.W.G[g]? = some hp)
    (hU : (hp.tl.ix.U.getD 2 none).isSome = true) (hq : planned hp.tl = true) :
    segView G (X, l) = some (4, 6, true, true, true) := by
  have e0 : (X.kind == 0) = true := by rw [hk]; rfl
  have r : ProofFile.readsQuietAt G l X 4 =
      some (VerifiableInference.Desc.K8.ReadsQuiet.layers ⟨⟨1, some l, 4, .K1⟩, hp.tl⟩) := by
    unfold ProofFile.readsQuietAt VerifiableInference.Desc.K8.ReadsQuiet.blockAt
    rw [kinds_at hX]
    simp [hk, hg, hG]
  have q : (quietOf G l X).planOk = true := by
    unfold quietOf
    have ep : (if X.kind == 0 || X.kind == 1 then 4 else 5) = 4 := by simp [hk]
    simp only [ep, r]
    exact hq
  unfold segView linkNumbers
  rw [if_pos e0, hg, hG]
  show some (4, 6, ((hp.tl.ix.U.getD 2 none).map ([·])).isSome, true, (quietOf G l X).planOk) = _
  rw [Option.isSome_map, hU, q]

theorem seg_att {G : Ground} {l g : ℕ} {X : LinkH} {a : Attention.Plan}
    (hk : X.kind = 1) (hg : X.g = g) (hA : G.W.A[g]? = some a) :
    segView G (X, l) = some (4, 6, true, true, true) := by
  have q : (quietOf G l X).planOk = true := by
    unfold quietOf ProofFile.readsQuietAt VerifiableInference.Desc.First.Att.readsAtO
    simp only [hk, hg, hA]
    rfl
  unfold segView linkNumbers
  simp only [hk, hg, hA, q]
  rfl

theorem seg_head {G : Ground} {l : ℕ} {X : LinkH} (hX : G.built[l]? = some X) (hk : X.kind = 2)
    (hU : (G.W.H.tl.ix.U.getD 2 none).isSome = true) (hq : planned G.W.H.tl = true) :
    segView G (X, l) = some (5, 7, true, true, true) := by
  have e0 : ¬ (X.kind == 0) = true := by rw [hk]; decide
  have e1 : ¬ (X.kind == 1) = true := by rw [hk]; decide
  have r : ProofFile.readsQuietAt G l X 5 =
      some (VerifiableInference.Desc.K8.ReadsQuiet.head
        ⟨⟨1, some l, 5, .K1⟩, G.W.hS, G.W.HLy, G.W.H⟩) := by
    unfold ProofFile.readsQuietAt VerifiableInference.Desc.K8.ReadsQuiet.blockAt
    rw [kinds_at hX]
    simp [hk]
  have q : (quietOf G l X).planOk = true := by
    unfold quietOf
    have ep : (if X.kind == 0 || X.kind == 1 then 4 else 5) = 5 := by simp [hk]
    simp only [ep, r]
    exact hq
  unfold segView linkNumbers
  rw [if_neg e0, if_neg e1]
  show some (5, 7, ((G.W.H.tl.ix.U.getD 2 none).map ([·])).isSome, true,
    (quietOf G l X).planOk) = _
  rw [Option.isSome_map, hU, q]

/-- **The 25 views are the written ones, from the ground's fields.** -/
theorem view_of_fields {G : Ground} (hsz : G.built.size = 25)
    (hL : ∀ g < 12, ∃ X hp, G.built[2 * g]? = some X ∧ X.kind = 0 ∧ X.g = g ∧
      G.W.G[g]? = some hp ∧ (hp.tl.ix.U.getD 2 none).isSome = true ∧ planned hp.tl = true)
    (hA : ∀ g < 12, ∃ X a, G.built[2 * g + 1]? = some X ∧ X.kind = 1 ∧ X.g = g ∧
      G.W.A[g]? = some a)
    (hH : ∃ X, G.built[24]? = some X ∧ X.kind = 2 ∧
      (G.W.H.tl.ix.U.getD 2 none).isSome = true ∧ planned G.W.H.tl = true) :
    (G.built.toList.zipIdx.map fun x => (x.2, segView G x)) = viewW := by
  refine List.ext_getElem? fun l => ?_
  unfold viewW
  rw [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_map, Array.getElem?_toList]
  by_cases hl : l < 25
  · rw [List.getElem?_range hl]
    have key : ∃ X, G.built[l]? = some X ∧ segView G (X, l) = some (viewAt l) := by
      by_cases h24 : l = 24
      · subst h24
        obtain ⟨X, h1, h2, h3, h4⟩ := hH
        exact ⟨X, h1, seg_head h1 h2 h3 h4⟩
      · by_cases hev : l % 2 = 0
        · obtain ⟨X, hp, h1, h2, h3, h4, h5, h6⟩ := hL (l / 2) (by omega)
          rw [show 2 * (l / 2) = l by omega] at h1
          refine ⟨X, h1, ?_⟩
          rw [seg_layers h1 h2 h3 h4 h5 h6]
          unfold viewAt
          simp [h24]
        · obtain ⟨X, a, h1, h2, h3, h4⟩ := hA (l / 2) (by omega)
          rw [show 2 * (l / 2) + 1 = l by omega] at h1
          refine ⟨X, h1, ?_⟩
          rw [seg_att h2 h3 h4]
          unfold viewAt
          simp [h24]
    obtain ⟨X, h1, h2⟩ := key
    rw [h1]
    simp only [Option.map_some, Nat.zero_add, h2]
  · rw [Array.getElem?_eq_none (by omega), List.getElem?_eq_none (by simpa using hl)]
    rfl

/-! ## 2 One shape a matrix, at the layers' and the head's plans -/

/-- The plan's structure has one shape a matrix. -/
def ShpN (tl : HTailF2) : Prop := tl.shp.size = tl.NM

theorem ShpN.of_same {a b : HTailF2} (h : ShpN a) (h1 : b.NM = a.NM) (h2 : b.shp = a.shp) :
    ShpN b := by
  unfold ShpN
  rw [h1, h2]
  exact h

theorem borderMeans_shp {tl tl' : HTailF2} {iF ownerNo index : ℕ}
    (h : tl.borderMeans iF ownerNo index = .ok tl') (hg : ShpN tl) : ShpN tl' := by
  unfold HTailF2.borderMeans at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain rfl := Except.ok.inj h
      exact hg.of_same rfl rfl

theorem planG_shp (P : Layer.Pub) (g : ℕ) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : ShpN hp.tl := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨tl0, hS, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨⟨tla, Fa, Ta⟩, hadd, h⟩ := (excBind_ok _ _ _).1 h
  have f0 : ShpN tla := (addTreesF_fits _ _ _ _ _ _ _ _ _ _ hadd).2.1
  obtain ⟨Tp, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  dsimp only at h
  cases O with
  | none =>
    dsimp only at h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨y, hy, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain rfl := Except.ok.inj hy
    obtain rfl := Except.ok.inj h
    exact f0.of_same rfl rfl
  | some O =>
    dsimp only at h
    split at h
    · obtain ⟨y, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨tlB, hbm, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨y2, hy, h⟩ := (excBind_ok _ _ _).1 h
      obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
      obtain rfl := Except.ok.inj hy
      obtain rfl := Except.ok.inj h
      exact borderMeans_shp hbm (f0.of_same rfl rfl)
    · exact absurd h (throw_bind_ne _ _ _)

theorem ownerHeld_shp (O : Head.Owner) (NGr : ℕ) (tl tl' : HTailF2) (Fp : Fork) (Tp : Tail2)
    (h : Head.ownerHeld O NGr tl Fp Tp = .ok tl') (hg : ShpN tl) : ShpN tl' := by
  unfold Head.ownerHeld at h
  dsimp only at h
  split at h
  · obtain ⟨y, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨tlB, hbm, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain rfl := Except.ok.inj h
    exact borderMeans_shp hbm hg
  · exact absurd h (throw_bind_ne _ _ _)

theorem planH2_shp (g : Settings) (hS : Head.Shape) (Lh : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : ℕ) (hp : Head.HPlanH2)
    (h : Head.planH2 g hS Lh b O NGr lkW = .ok hp) : ShpN hp.tl := by
  unfold Head.planH2 at h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨tl0, hsh, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨⟨tla, Fa, Ta⟩, hadd, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨Tp, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨tlF, ho, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain rfl := Except.ok.inj h
    exact ownerHeld_shp _ _ _ _ _ _ ho (addTreesF_fits _ _ _ _ _ _ _ _ _ _ hadd).2.1
  · exact absurd h (throw_bind_ne _ _ _)

theorem planned_of {tl : HTailF2} (h1 : tl.funClosed = false) (h2 : ShpN tl) :
    planned tl = true := by
  unfold planned
  rw [h1, h2]
  simp

section
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}

/-- **The quiet step's test on the plan, at every return of publicOf: a layers' plan.** -/
theorem planned_layers (h : Verify.publicOf pol KL lay = .ok X) {g : ℕ} {hp : Layer.HPlan2}
    (hg : X.G[g]? = some hp) : planned hp.tl = true :=
  planned_of (_root_.Meaning.planG_open (Fo.Pub.public_G h g hp hg))
    (planG_shp _ _ _ _ (Fo.Pub.public_G h g hp hg))

/-- **The head's plan.** -/
theorem planned_head (h : Verify.publicOf pol KL lay = .ok X) : planned X.H.tl = true := by
  obtain ⟨H0, h1, h2⟩ := Fo.Pub.public_H h
  have e : X.H.tl = H0.tl := by rw [h2]
  rw [e]
  exact planned_of (_root_.Meaning.planH2_open h1) (planH2_shp _ _ _ _ _ _ _ _ h1)

theorem third_there {tl : HTailF2} (h : ∃ t, tl.ix.U[2]? = some (some t)) :
    (tl.ix.U.getD 2 none).isSome = true := by
  obtain ⟨t, ht⟩ := h
  rw [Array.getD_eq_getD_getElem?, ht]
  rfl

end

/-! ## 3 In the goals' scope, behind the front's return -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {Z : Pub} {G : Ground}

/-- **The fifth hypothesis of `k1_row_at`, paid**: no entry test is asked. -/
theorem view_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol ly P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) :
    (G.built.toList.zipIdx.map fun x => (x.2, segView G x)) = viewW := by
  have hX := IM.ground_publicK hZ hG
  obtain ⟨_, _, _, hAll⟩ := _root_.Meaning.scope_plans hS hR hX
  have C := OnBytes.Road.Hd.core_of_scope hS hR hX
  obtain ⟨nm, X24, e24, k24, _⟩ := IM.ground_named hS hR hZ hG
  refine view_of_fields (IM.ground_gets hS hR hZ hG).1 (fun g hg => ?_) (fun g hg => ?_) ?_
  · obtain ⟨l, _, e, kd, kg, _⟩ := nm g hg
    obtain ⟨hp, hgp⟩ := _root_.Meaning.planG_there hX C hg
    exact ⟨l, hp, e, kd, kg, hgp,
      third_there (LT28.K8Tests.both_layers hX hgp).2.2,
      planned_layers hX hgp⟩
  · obtain ⟨_, l', _, _, _, _, e', kd', kg', _⟩ := nm g hg
    obtain ⟨a, ha, _⟩ := hAll g hg
    exact ⟨l', a, e', kd', kg', ha⟩
  · exact ⟨X24, e24, k24,
      third_there (LT28.K8Tests.both_head hX).2.2, planned_head hX⟩

/-- **K1's lot's row in the goals' scope, behind the front's return**: four hypotheses by field are
left, all on the made parameters: to be paid WITHOUT the entry tests' comparisons. -/
theorem k1_row_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol ly P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G)
    (hc : G.first.codes = Johnson.G.codesFull2)
    (hs : G.first.shape = VerifiableInference.PlanWritten.proofSizedFull.request)
    (hl : G.first.layout = Johnson.G.layoutFull) (hgs : Z.P.samples = 1) :
    ProofFile.Sk.lotSk G (ProofFile.k1Pure Z) = k1LotW :=
  k1_row_at hc hs hl hgs (view_in_scope hS hR hZ hG)

/-- **The same on the blocks**: the lot's blocks' skeletons are the 51 made of the written
table's own rows. -/
theorem k1_blocks_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol ly P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G)
    (hc : G.first.codes = Johnson.G.codesFull2)
    (hs : G.first.shape = VerifiableInference.PlanWritten.proofSizedFull.request)
    (hl : G.first.layout = Johnson.G.layoutFull) (hgs : Z.P.samples = 1) :
    ((ProofFile.k1Pure Z).blocks G).map ProofFile.Sk.skel = k1SkW :=
  k1_blocks_at hc hs hl hgs (view_in_scope hS hR hZ hG)

end

end Johnson.AtFull.Desc.K1Lot

#print axioms Johnson.AtFull.Desc.K1Lot.kinds_at
#print axioms Johnson.AtFull.Desc.K1Lot.seg_layers
#print axioms Johnson.AtFull.Desc.K1Lot.seg_att
#print axioms Johnson.AtFull.Desc.K1Lot.seg_head
#print axioms Johnson.AtFull.Desc.K1Lot.view_of_fields
#print axioms Johnson.AtFull.Desc.K1Lot.ShpN.of_same
#print axioms Johnson.AtFull.Desc.K1Lot.borderMeans_shp
#print axioms Johnson.AtFull.Desc.K1Lot.planG_shp
#print axioms Johnson.AtFull.Desc.K1Lot.ownerHeld_shp
#print axioms Johnson.AtFull.Desc.K1Lot.planH2_shp
#print axioms Johnson.AtFull.Desc.K1Lot.planned_of
#print axioms Johnson.AtFull.Desc.K1Lot.planned_layers
#print axioms Johnson.AtFull.Desc.K1Lot.planned_head
#print axioms Johnson.AtFull.Desc.K1Lot.third_there
#print axioms Johnson.AtFull.Desc.K1Lot.view_in_scope
#print axioms Johnson.AtFull.Desc.K1Lot.k1_row_in_scope
#print axioms Johnson.AtFull.Desc.K1Lot.k1_blocks_in_scope
