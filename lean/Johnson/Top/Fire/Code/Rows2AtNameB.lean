-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Rows2AtNameB.lean: THE KEY FILE, THE SHARED CHAIN: THE CALLS OF ROWS 2.7 ("LIN zeta") · 2.4 ("LOC") · 2.1 ("LIN point"): The21's fields r2_7 · r2_4 · r2_1 AT The21Off's WRITTEN TERMS, IN THE GOALS' SCOPE, FROM WHAT THE SEAT HANDS. In the form of Rows2AtName.lean (for rows 2.3 · 2.6 · 2.8).
OBJECT. KeepsAt (On₂' …) (Cl₂ …) ‹the maker's row of chain 2› k at capRest ×3 · () () · baseAt X decN recBack · atSix · readAt tabN · collN · off₂N. Row 2.7: any enc rad. Rows 2.4 | 2.1: rad := Params.recordRadius; any enc that is the code's encoder (henc).
HOW. r2_7_plan | r2_4_plan | r2_1_plan (Johnson/RunOne/KeyRowsAtPlan.lean: Keeps at a piece of ONE written round that holds «held» of the description's own sub-protocol, with its error below the cap) CALLED at the maker's own piece (keepsAt_of_law₂) and lifted over the history (KeepsAt.reached). That the maker's piece has one written round and nothing put behind: one_round₂ (rowAt₂ · one_of_len₂ · cutPut_inner), from «the sub-protocol declares one round» (rounds₂_at: rounds_in_scope). The bases: bases_of_all at basesAll_at_six. Row 2.4's premise on the tiling (Matches): matches₂_of_data (fitOfOk · chainFit_cons, down the maker's cut: cut_matches).
Row 2.1's public facts: the plan has a stage (one_full; the kernel) · the first chain's shape is the shared chain's (lin_of_fileOk) · the reader reads no cells (rfl) · the radius against the distance (numbers).
IN FRONT STAND: the three heads · the five in scope · wantedOk · the data · the pin on the data · (2.4 | 2.1) henc · (2.1) TWO TIES ON LETTERS, LEFT: hcoll : CollTie · hdec : DecTie (Johnson/RunOne/KeyGood21.lean; each speaks under the promise in front): that the stored table has no collision at the key's OOD seeds in the library's sense · that where the library's decoder returns a table the reading's decoder returns cells which the reader reads as that table. collTie_at | decTie_at (KeyTies21At.lean) cut them down; NOT CALLED HERE. ONE BINDER MORE THAN Rows2AtName.lean's: hdata: the description's data ARE DK's (as r1_0_at_name | r1_17_at_name take it; the seat hands it): rows 2.7 | 2.4 | 2.1 hear a round, rows 2.3 | 2.6 | 2.8 hear none.
henc IS A CONDITION ON A LETTER THAT The21Off BINDS BY ∃: a member with code is encOf (Johnson/RunOne/KeyRow24.lean; encIs_encOf).
UNTIL A MEMBER OF THE PROMISE AT THESE BORDERS IS SHOWN, each may be true and empty at the real protocol, and counts as closing nothing.
Limits. Calls, and one lemma on the maker's cut: no new law. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.KeyAtOff
import Johnson.Top.Fire.Code.KeyBasesAtSix
import Johnson.Top.Fire.Code.PieceSame
import Johnson.Top.Fire.Code.RowStretchOne
import Johnson.Desc.Sound.ReadsOfData
import Johnson.RunOne.KeyRowsAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace LPFD
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃ seam₁_at_fk seam₂_at_fk ends_at_fk)
open Johnson.RunOne.KeyRows1 (FirstLetters firstOn_of firstClaim_of CollCell ReadsL open₁)
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₂ open₃)
open Johnson.RunOne.KeyRows23 (p14At shared_flat names_blocks fileOk_all bareB)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope shared_lin_in_scope)
open VerifiableInference.Desc.Key.Fill (six OmAt)
open Johnson.RunOne.KeyRows23 (numSix atSix kreadFam baseK)

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD)
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}

/-- **The maker's piece number n of the shared chain has one written round and nothing put behind**, where the n-th sub-protocol declares one round and is not the last. -/
theorem one_round₂ (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (n : ℕ) (hn : n < k₂.length)
    (b : Block (Fk X N P).S₂ (Fk X N P).Cl) (base : ℕ) (ds : List RDT) (back : List _root_.Fmt.RoundView) (hb : (c₂ :: k₂)[n]? = some b) (hl : b.rounds.length = 1)
    (hrow : ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂)[n]? = some (pieceOf (held b) base ds back (capRest n ds))) :
    ∃ d, cutDs (DK.at frS.P.T.a).ds₂ c₂ k₂ n = [d] ∧ ds = [d] ∧ back = [] := by
  obtain ⟨b', -, e⟩ := rowAt₂ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () n _ hrow
  obtain ⟨d, hd⟩ := one_of_len₂ (Fk X N P) "key file" (DK.at frS.P.T.a) hdata c₂ k₂ q₂ n b hb hl
  have e1 : ds = cutDs (DK.at frS.P.T.a).ds₂ (held c₂ : Block (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) (Fk X N P).Cl) (k₂.map held) n := congrArg (·.ds) e
  have e2 : back = cutPut [] (k₂.map (held (P := ((Fk X N P).XiPub × (Fk X N P).S₁)))) n := congrArg (·.back) e
  exact ⟨d, hd, e1.trans ((cutDs_held k₂ n _ c₂).trans hd), e2.trans (cutPut_inner [] _ n (by rw [List.length_map]; exact hn))⟩

/-- In scope: the shared chain's n-th sub-protocol declares as many rounds as the written list says; the chain has twelve. -/
theorem rounds₂_at (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (n : ℕ) (b : Block (Fk X N P).S₂ (Fk X N P).Cl) (hb : (c₂ :: k₂)[n]? = some b) :
    roundsW₂[n]? = some b.rounds.length ∧ k₂.length = 11 := by
  have h2 := (rounds_in_scope hZ hP hm hX hp hwant).2.1
  have h3 := (lengths_in_scope hZ hP hm hX hp hwant).2.1
  rw [q₂] at h2 h3
  refine ⟨?_, by simpa using h3⟩
  rw [← h2, List.getElem?_map, hb]
  rfl

/-- **The tiling's own sentence at a stretch**: a sub-protocol that is not the last has its declared rounds matched by the stretch that the maker cuts for it. -/
theorem cut_matches {S Cl : Type} (Fr : Frame) (dep : ℕ → Option ℕ) : ∀ (l : List (Block S Cl)) (n base : ℕ) (ds : List RDT) (b b' : Block S Cl) (pb : List _root_.Fmt.RoundView),
    ChainFit Fr dep base b l ds pb → n < l.length → (b :: l)[n]? = some b' → Matches Fr.a dep b'.rounds (cutDs ds b l n)
  | [], _, _, _, _, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | c :: l, 0, base, ds, b, b', pb, H, _, hb => by
    have e : b = b' := Option.some.inj (List.getElem?_cons_zero.symm.trans hb)
    subst e
    exact (chainFit_cons dep base b c l ds pb H).1.1
  | c :: l, n + 1, base, ds, b, b', pb, H, h, hb =>
    cut_matches Fr dep l n _ (ds.drop b.rounds.length) c b' pb (chainFit_cons dep base b c l ds pb H).2 (Nat.lt_of_succ_lt_succ h) (List.getElem?_cons_succ.symm.trans hb)

/-- **At a description's data**: the shared chain's n-th sub-protocol against its stretch. -/
theorem matches₂_of_data {XI : Type} (F : FileDescription XI) (file : String) (D : WholeD) (h : F.data file = .ok D) (hs : F.sealLast = true)
    (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl) (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
    (q₁ : F.first.blocksInOrder = c₁ :: k₁) (q₂ : F.shared.blocksInOrder = c₂ :: k₂) (q₃ : F.second.blocksInOrder = c₃ :: k₃)
    (n : ℕ) (hn : n < k₂.length) (b : Block F.S₂ F.Cl) (hb : (c₂ :: k₂)[n]? = some b) :
    Matches (frameAt D (allOf D) D.key₂ 0).a D.depth b.rounds (cutDs D.ds₂ c₂ k₂ n) := by
  have hl := last_of_seal F hs c₁ k₁ q₁
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, hok, rfl⟩ := data_ok F file D h
  obtain ⟨w₁, w₂, w₃⟩ := written_as file F.roundsDeclaredByBlocks _ hR
  obtain ⟨-, f₂, -⟩ := fitOfOk _ R₁ R₂ R₃ _ _ _ _ _ _ w₁ w₂ w₃ hok F.S₁ F.S₂ F.S₃ F.Cl c₁ k₁ c₂ k₂ c₃ k₃ ⟨[], ⟨[], [], [], none⟩⟩
    (dataOf F.tableDepth R₁ R₂ R₃).key₁ (dataOf F.tableDepth R₁ R₂ R₃).key₂ (dataOf F.tableDepth R₁ R₂ R₃).key₃ 0 0 0
    (by rw [← q₁]; rfl) (by rw [← q₂]; rfl) (by rw [← q₃]; rfl) hl
  exact cut_matches _ _ k₂ n _ _ c₂ b [] f₂ hn hb

/-- **The21's FIELD r2_7 AT The21Off's TERMS, IN SCOPE.** -/
theorem r2_7_at_name (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull) :
    KeepsAt (On₂' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 7 := by
  have hB := (bases_of_all X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () atSix (basesAll_at_six hZ hP hm hX hp hwant hDK) q₁ q₂ q₃).2.1
  refine KeepsAt.reached _ _ (rowBlocksF₂ q₂ 7) ?_
  show KeepsAt (On₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 7
  refine keepsAt_of_law₂ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () _ _ 7 ?_
  intro b base ds back hb hrow
  have hb' : (descriptionFromSource X N P).shared.blocksInOrder[7]? = some b := by
    rw [show (descriptionFromSource X N P).shared.blocksInOrder = c₂ :: k₂ from q₂]
    exact hb
  obtain ⟨hr, hk⟩ := rounds₂_at X N P c₂ k₂ q₂ hZ hP hm hX hp hwant 7 b hb
  have hl : b.rounds.length = 1 := (Option.some.inj hr).symm
  obtain ⟨d, hd, rfl, rfl⟩ := one_round₂ X N P DK c₁ k₁ c₂ k₂ c₃ k₃ hdata q₂ 7 (by omega) b base ds back hb hl hrow
  exact Johnson.RunOne.KeyRows23.r2_7_plan (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (baseAt X decN recBack) atSix (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)) (readAt tabN) enc rad (oneAt X).given.plan.samples collN (Johnson.RunOne.KeyRows23.last₁At (oneAt X)) off₂N X N P hp
    "key file" (DK.at frS.P.T.a) hdata c₂ k₂ q₂ hZ hP hm hX b hb' d hd base (hB 7 _ hrow) cellOnly_collN (fun _ _ => Iff.rfl) (capRest 7 [d]) rfl

/-- **The21's FIELD r2_4 AT The21Off's TERMS, IN SCOPE**, at rad := the radius of the OOD sample's decoder that the planner writes (Params.recordRadius), and at every enc that is the code's encoder. -/
theorem r2_4_at_name (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    (henc : Johnson.RunOne.KeyRows23.EncIs OnBytes.Model.Reading.gl (p14At X P).par.S.fold enc) :
    KeepsAt (On₂' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc OnBytes.Params.recordRadius collN off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc OnBytes.Params.recordRadius) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 4 := by
  have hB := (bases_of_all X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () atSix (basesAll_at_six hZ hP hm hX hp hwant hDK) q₁ q₂ q₃).2.1
  refine KeepsAt.reached _ _ (rowBlocksF₂ q₂ 4) ?_
  show KeepsAt (On₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc OnBytes.Params.recordRadius collN off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc OnBytes.Params.recordRadius) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 4
  refine keepsAt_of_law₂ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () _ _ 4 ?_
  intro b base ds back hb hrow
  have hb' : (descriptionFromSource X N P).shared.blocksInOrder[4]? = some b := by
    rw [show (descriptionFromSource X N P).shared.blocksInOrder = c₂ :: k₂ from q₂]
    exact hb
  obtain ⟨hr, hk⟩ := rounds₂_at X N P c₂ k₂ q₂ hZ hP hm hX hp hwant 4 b hb
  have hl : b.rounds.length = 1 := (Option.some.inj hr).symm
  obtain ⟨d, hd, rfl, rfl⟩ := one_round₂ X N P DK c₁ k₁ c₂ k₂ c₃ k₃ hdata q₂ 4 (by omega) b base ds back hb hl hrow
  have hM := matches₂_of_data (Fk X N P) "key file" (DK.at frS.P.T.a) hdata (VerifiableInference.Desc.Sound.sealLast_of_planOk _ hp) c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ 4 (by omega) b hb
  rw [hd] at hM
  exact Johnson.RunOne.KeyRows23.r2_4_plan (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (baseAt X decN recBack) atSix (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)) (readAt tabN) enc (oneAt X).given.plan.samples collN (Johnson.RunOne.KeyRows23.last₁At (oneAt X)) off₂N X N P hp
    "key file" (DK.at frS.P.T.a) hdata c₂ k₂ q₂ hZ hP hm hX OnBytes.Model.Reading.gl b hb' d hd (DK.at frS.P.T.a).depth hM base (hB 4 _ hrow) cellOnly_collN (fun _ _ => Iff.rfl) henc (capRest 4 [d]) rfl

/-- **The21's FIELD r2_1 AT The21Off's TERMS, IN SCOPE**, at rad := Params.recordRadius and every enc that is the code's encoder, FROM TWO TIES ON LETTERS THAT ARE LEFT (CollTie | DecTie, each under the promise in front). -/
theorem r2_1_at_name (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    (henc : Johnson.RunOne.KeyRows23.EncIs OnBytes.Model.Reading.gl (p14At X P).par.S.fold enc)
    (err : ℕ) (rank : ((Fin (p14At X P).par.S.fold.index.v → Bool) → Fin ((p14At X P).par.S.fold.index.code.r + (p14At X P).par.S.fold.index.code.ell) → Cb.Gl.E) → ℕ)
    (hcoll : Johnson.RunOne.KeyRows23.CollTie (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (baseAt X decN recBack).h₂ atSix (p14At X P).par (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)) (readAt tabN) enc 2852142980 (oneAt X).given.plan.samples collN (Johnson.RunOne.KeyRows23.last₁At (oneAt X)) off₂N err 2852142980 rank)
    (hdec : Johnson.RunOne.KeyRows23.DecTie (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (baseAt X decN recBack).h₂ atSix (p14At X P).par (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)) (readAt tabN) enc 2852142980 (oneAt X).given.plan.samples collN (Johnson.RunOne.KeyRows23.last₁At (oneAt X)) off₂N err 2852142980 rank) :
    KeepsAt (On₂' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc OnBytes.Params.recordRadius collN off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc OnBytes.Params.recordRadius) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 1 := by
  have hB := (bases_of_all X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () atSix (basesAll_at_six hZ hP hm hX hp hwant hDK) q₁ q₂ q₃).2.1
  refine KeepsAt.reached _ _ (rowBlocksF₂ q₂ 1) ?_
  show KeepsAt (On₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc OnBytes.Params.recordRadius collN off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc OnBytes.Params.recordRadius) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 1
  refine keepsAt_of_law₂ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () _ _ 1 ?_
  intro b base ds back hb hrow
  have hb' : (descriptionFromSource X N P).shared.blocksInOrder[1]? = some b := by
    rw [show (descriptionFromSource X N P).shared.blocksInOrder = c₂ :: k₂ from q₂]
    exact hb
  obtain ⟨hr, hk⟩ := rounds₂_at X N P c₂ k₂ q₂ hZ hP hm hX hp hwant 1 b hb
  have hl : b.rounds.length = 1 := (Option.some.inj hr).symm
  obtain ⟨d, hd, rfl, rfl⟩ := one_round₂ X N P DK c₁ k₁ c₂ k₂ c₃ k₃ hdata q₂ 1 (by omega) b base ds back hb hl hrow
  have hst : 1 ≤ (oneAt X).ranges.stages.length := by
    rw [(one_full hZ hP hm hX hp).1]
    decide +kernel
  exact Johnson.RunOne.KeyRows23.r2_1_plan (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (baseAt X decN recBack) atSix (readAt tabN) enc (oneAt X).given.plan.samples collN off₂N X N P hp
    "key file" (DK.at frS.P.T.a) hdata c₂ k₂ q₂ hZ hP hm hX (oneAt X) hst (Johnson.RunOne.KeyRows23.lin_of_fileOk X N P (fileOk_of_planOk' _ hp)) err 2852142980 rank b hb' d hd base (hB 1 _ hrow) cellOnly_collN (fun _ _ => Iff.rfl)
    (fun _ _ _ => rfl) henc (Nat.le_refl _) (by norm_num) hcoll hdec (capRest 1 [d]) rfl

/-- **THE FIT**: the theorem's conclusion IS The21's field r2_7 at The21Off's terms: by Lean's own check of types. -/
def fit_27 (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    (H : The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N off₃N) :
    The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N off₃N :=
  { H with r2_7 := r2_7_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ enc rad q₁ q₂ q₃ hZ hP hm hX hp hwant hdata hDK }

/-- **THE FIT**: the theorem's conclusion IS The21's field r2_4 at The21Off's terms: by Lean's own check of types. -/
def fit_24 (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    (henc : Johnson.RunOne.KeyRows23.EncIs OnBytes.Model.Reading.gl (p14At X P).par.S.fold enc)
    (H : The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) enc OnBytes.Params.recordRadius collN off₂N off₃N) :
    The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) enc OnBytes.Params.recordRadius collN off₂N off₃N :=
  { H with r2_4 := r2_4_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ enc q₁ q₂ q₃ hZ hP hm hX hp hwant hdata hDK henc }

/-- **THE FIT**: the theorem's conclusion IS The21's field r2_1 at The21Off's terms: by Lean's own check of types. -/
def fit_21 (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    (henc : Johnson.RunOne.KeyRows23.EncIs OnBytes.Model.Reading.gl (p14At X P).par.S.fold enc)
    (err : ℕ) (rank : ((Fin (p14At X P).par.S.fold.index.v → Bool) → Fin ((p14At X P).par.S.fold.index.code.r + (p14At X P).par.S.fold.index.code.ell) → Cb.Gl.E) → ℕ)
    (hcoll : Johnson.RunOne.KeyRows23.CollTie (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (baseAt X decN recBack).h₂ atSix (p14At X P).par (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)) (readAt tabN) enc 2852142980 (oneAt X).given.plan.samples collN (Johnson.RunOne.KeyRows23.last₁At (oneAt X)) off₂N err 2852142980 rank)
    (hdec : Johnson.RunOne.KeyRows23.DecTie (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (baseAt X decN recBack).h₂ atSix (p14At X P).par (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)) (readAt tabN) enc 2852142980 (oneAt X).given.plan.samples collN (Johnson.RunOne.KeyRows23.last₁At (oneAt X)) off₂N err 2852142980 rank)
    (H : The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) enc OnBytes.Params.recordRadius collN off₂N off₃N) :
    The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) enc OnBytes.Params.recordRadius collN off₂N off₃N :=
  { H with r2_1 := r2_1_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ enc q₁ q₂ q₃ hZ hP hm hX hp hwant hdata hDK henc err rank hcoll hdec }

end

end LPFD

#print axioms LPFD.one_round₂
#print axioms LPFD.rounds₂_at
#print axioms LPFD.cut_matches
#print axioms LPFD.matches₂_of_data
#print axioms LPFD.r2_7_at_name
#print axioms LPFD.r2_4_at_name
#print axioms LPFD.r2_1_at_name
#print axioms LPFD.fit_27
#print axioms LPFD.fit_24
#print axioms LPFD.fit_21
