-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/LawAtTile.lean: the law's public premises and the game of the proximity test
(the kind K12) at the piece that a description's own tiling holds on the shared chain, first arm;
general in the description. Definitions, statements and proofs; each main proof is a row of calls.

Whose is what. Called: `atPlace_cutJ` (Johnson/Desc/K12/Coin/AtCutJ.lean) with its `errJ` and
`bears_errJ` (GameJ.lean) and `like_of_cut` (LikeOfCut.lean); `roundsOfData`, `opensShaped`,
`chainTrees`, `wants_shared` (Johnson/Desc/Sound/DataRounds.lean, WantsAtStretch.lean), laid as
`atPlace_shared` (AtDesc.lean) lays them; `piecesAt` (Johnson/Desc/Sound/PaidAtDesc.lean);
`cutRow_at` (GameTile.lean), `leftBehind_eq` (GameHeld.lean), `Alike.held` (Alike.lean),
`k12_game_alikeV` (GameLabels.lean). From our own: `ChainAt` (LawAtLight.lean), `labelsPub_own`
(GameAt.lean), `below_like` (LawAtO.lean), `batBelow_like` (Johnson/Desc/K12/Law/BatValsPayAt.lean).
What it is not, first.
  (1) THE FORM IS `Leads`: one statement at a time. The rule `proofSound_at_desc`
    (Johnson/Desc/Plain/AtDesc.lean) asks of the shared chain's row `LeadsK`: one game for all the
    statements with one key. That form is not reached here.
  (2) `herr` is a premise on a letter of `piecesAt`: the family of extractors and errors. Which
    errors the file's piece bears is the choice of whoever fills that family: no theorem pays it.
    «Small» is said of the pair that `herr` names.
  (3) The first arm alone, the shared chain alone; the seat is not the row's last block; the seat's
    entry has the seat's own decision (`Alike`).
  (4) The conclusion's numbering is read off the record by the trees' labels (`nuOf`): all that
    stands first at the head of GameAt.lean on that form stands here: no item and no spender is
    struck on it.
  (5) How the flat list parts, `Alike`, the count of roots in front, the block's test on the plan
    and that the description has data are premises: shown here of no description.
  (6) `errJ_small` has the conclusion of `errJ_below` (Johnson/Desc/K12/Coin/ErrJBelow.lean)
    from other premises: `ChainAt`, "BAT"'s own comparison and «like»: none of which
    reads a table of codes. It falls to `errJ_below` when the name `RoundsBelowAt` has one text
    again on every lane.
Main names.
  `errJ_eq`; `εAt_errJ`: where the chain is there, `εAt` of LawAt.lean is `errJ` at `dtAt`: one list
    of numbers, two names.
  `errJ_small`: the whole entry ("BAT"'s count times the sampler's number, then `errJ`) is below b,
    round by round.
  `TileAt Fr π num r b base dB dt`: `AtPlace` at the Johnson letters, the radii r and `errJ`; and
    that.
  `atPlace_tile₂`: at a description with data whose shared chain's flat list is pre ++ B :: post, B
    declaring the test's rounds.
  `tile_piece₂`: the piece number pre.length of the second row of `piecesAt`, its fields in hand.
  `tile_end₂`: where that piece ends.
  `game_at_tile₂V`: the game at that piece.
Limits: those of the files called. No soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Coin.AtCutJ
import Johnson.Desc.K12.Coin.LawAtLight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.Pub (sgOf writtenOf WR chainFrom johOk batV0 batPriceOk)
open H2K.Member (wsAt w0At dtAt wsAt_cons)
open H2K.Pin (NTuple)
open Johnson.G.OfPlan (rootsOf)
open scoped ENNReal

/-! ## The place's own errors -/

theorem errJ_eq {π : P12} {r : Fmt.M1.Stage → ℕ} {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage}
    {w0 : WR} {l : List WR} {c : OnBytes.Slice.Chain (sgOf a)} (hs : π.nums.stages = a :: rest)
    (hw : writtenOf π.nums = some (w0 :: l))
    (hc : chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) rest a l = some c)
    (dt : List RDT) : errJ π r dt = errOfList (uLT (ckP .two) dt) (errList _ c.errL) := by
  unfold errJ
  rw [hs, hw]
  dsimp only
  rw [hc]

/-- Where the chain is there: one list of numbers, two names. -/
theorem εAt_errJ {π : P12} {r : Fmt.M1.Stage → ℕ} {εs : ℝ≥0∞} (hC : ChainAt π r εs)
    (num : Fmt.TreeSource → ℕ) : εAt num π r = errJ π r (dtAt num π) := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, _⟩ := hC
  rw [errJ_eq e1 e2 e3]
  unfold εAt
  rw [cnts_eq π r a rest w0 l c e1 e2 e3]

/-- **The whole entry is below b, round by round.** -/
theorem errJ_small {π : P12} {r : Fmt.M1.Stage → ℕ} {b : ℝ≥0∞} {dB : RDT} {dt : List RDT}
    (hC : ChainAt π r b)
    (hl : ∃ w0 l, writtenOf π.nums = some (w0 :: l) ∧ List.Forall₂ Like (dB :: dt) (w0 :: l))
    (hb : RoundBelow (batV0 π r) (OnBytes.Flat.toRD dB) b) :
    Err.Below (s := uLT (ckP .two) (dB :: dt))
      (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) b := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, e8⟩ := hC
  obtain ⟨w1, l1, hw1, hlike⟩ := hl
  obtain ⟨_, hll⟩ := List.cons.inj (Option.some.inj (hw1.symm.trans e2))
  have hT : List.Forall₂ Like dt l := by
    cases hlike with
    | cons _ t => exact hll ▸ t
  refine ⟨hb, ?_⟩
  rw [errJ_eq e1 e2 e3]
  exact below_like dt l hT c.rds e4 c.errL _ (Chain.errL_below c _ e8)

/-! ## At the file's own tile -/

/-- **What holds at a tile**: `AtPlace` at the Johnson letters, the radii r and the place's own
errors; and the whole entry is below b, round by round. -/
def TileAt (Fr : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (r : Fmt.M1.Stage → ℕ) (b : ℝ≥0∞)
    (base : ℕ) (dB : RDT) (dt : List RDT) : Prop :=
  AtPlace Fr π num Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) base dB dt (errJ π r dt) ∧
    Err.Below (s := uLT (ckP .two) (dB :: dt))
      (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) b

/-- **At the shared chain of a description with data.** -/
theorem atPlace_tile₂ {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (key : ℕ → ℕ) (ft : ℕ) (π : P12) (r : Fmt.M1.Stage → ℕ) (k : ℕ)
    (pre : List (Block F.S₂ F.Cl)) (B : Block F.S₂ F.Cl) (post : List (Block F.S₂ F.Cl))
    (hfl : F.shared.blocksInOrder = pre ++ B :: post)
    (hB : B.rounds = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ k)) (hj : johOk π r = true)
    (hbat : batPriceOk π r k = true) (ho : π.nums.ownMask = false) :
    ∃ dB dt, (D.ds₂.drop (pre.flatMap (·.rounds)).length).take
        (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt ∧
      TileAt (frameAt D (allOf D) key ft) π (numAt F.t₁ F.t₂ 1) r ((2 : ℝ≥0∞)⁻¹ ^ k)
        (D.t₁ + nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length)) dB dt := by
  obtain ⟨hS, k₁, _⟩ := opensShaped F file D h
  have hA := roundsOfData F file D h
  have e : F.roundsDeclaredByBlocks.2.1 = pre.flatMap (·.rounds) ++
      ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ post.flatMap (·.rounds)) := by
    show F.shared.blocksInOrder.flatMap (·.rounds) = _
    rw [hfl, List.flatMap_append, List.flatMap_cons, hB]
  have hAs : List.Forall₂ RoundAsG D.ds₂ (pre.flatMap (·.rounds) ++
      ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ post.flatMap (·.rounds))) := by
    rw [← e]
    exact hA.2.1
  have hL := (forall₂_cut _ _ _ hAs).length_eq
  have hrs : H2U.roundsOfNums π.nums = some (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds :=
    VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts π hp
  have hpos : 0 < (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length := by
    obtain ⟨_, _, _, R, _, _, hR⟩ := H2K.Made.rounds_top π.nums _ hrs
    rw [hR]
    exact Nat.succ_pos _
  obtain ⟨dB, dt, hlist⟩ : ∃ dB dt, (D.ds₂.drop (pre.flatMap (·.rounds)).length).take
      (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt := by
    cases hq : (D.ds₂.drop (pre.flatMap (·.rounds)).length).take
        (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length with
    | nil =>
      rw [hq, List.length_nil] at hL
      omega
    | cons x y => exact ⟨x, y, rfl⟩
  have hw := (wsAt_cons π hp).1
  have hAt : AtPlace (frameAt D (allOf D) key ft) π (numAt F.t₁ F.t₂ 1) Sg.lstJ Sg.flC Sg.flZ
      Sg.flZ (fun s => r s.st) (D.t₁ + nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length)) dB dt
      (errJ π r dt) :=
    atPlace_cutJ _ π _ r D.ds₂ (pre.flatMap (·.rounds)) _ (post.flatMap (·.rounds)) D.t₁ (allT D)
      dB dt hlist.symm hAs rfl (wants_shared h _ _ _ e key ft)
      (fun n x hx => (chainTrees D n x).2.1 hx)
      (fun r' hr o ho' => hS.2.1 r' (by rw [e]; simp [hr]) o ho') (fun m => by simp [numAt, k₁])
      hfree (H2K.JointK.early_of_planOk π hp) (H2K.JointK.answers_of_planOk π hp) hp
      (H2K.Made.spendOk_of_planOk π hp) hj ho _ _ hw
  refine ⟨dB, dt, hlist, hAt, errJ_small hC hAt.like ?_⟩
  obtain ⟨a₀, rest₀, _, _, _, e1, _⟩ := hC
  exact H2K.Pin.batBelow_like π r k a₀ rest₀ e1 dB dt hAt.like hbat

/-! ## The piece that the description's own tiling holds -/

/-- **The shared chain's piece number pre.length of `piecesAt`, its fields in hand**: block, nothing
put back, base, data; its errors are the family's at that number; and `TileAt` there. -/
theorem tile_piece₂ {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber)
        ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (π : P12) (r : Fmt.M1.Stage → ℕ) (k : ℕ)
    (pre : List (Block F.S₂ F.Cl)) (B b' : Block F.S₂ F.Cl) (post : List (Block F.S₂ F.Cl))
    (hfl : F.shared.blocksInOrder = b₂ :: l₂) (hcut : b₂ :: l₂ = pre ++ B :: b' :: post)
    (hB : B.rounds = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ k)) (hj : johOk π r = true)
    (hbat : batPriceOk π r k = true) (ho : π.nums.ownMask = false) :
    ∃ p dB dt,
      ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₂)[pre.length]? =
        some p ∧
      p.b = held B ∧ p.back = [] ∧
      p.base = D.t₁ + nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length) ∧ p.ds = dB :: dt ∧
      (D.ds₂.drop (pre.flatMap (·.rounds)).length).take
        (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt ∧
      (∀ ε : Err (uLT (ckP .two) (dB :: dt)),
        (∀ ds', ds' = dB :: dt → HEq (rest₂ (0 + pre.length) ds').err ε) → HEq p.err ε) ∧
      D.t₁ + nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length) = baseAt F.t₁ F.t₂ 1 π ∧
      D.t₁ = F.t₁ ∧
      TileAt (frameAt D (allOf D) D.key₂ 0) π (numAt F.t₁ F.t₂ 1) r ((2 : ℝ≥0∞)⁻¹ ^ k)
        (D.t₁ + nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length)) dB dt := by
  obtain ⟨dB, dt, hlist, hAt, hsm⟩ := atPlace_tile₂ F file D h D.key₂ 0 π r k pre B (b' :: post)
    (hfl.trans hcut) hB hfree hp hC hj hbat ho
  have hL' : held (P := F.XiPub × F.S₁) b₂ :: l₂.map held =
      pre.map held ++ held B :: held b' :: post.map held := by
    have := congrArg (List.map (held (P := F.XiPub × F.S₁))) hcut
    simpa using this
  have hat := cutRow_at rest₂ [] (held B) (held b') (post.map held) (pre.map held) (held b₂)
    (l₂.map held) 0 D.t₁ D.ds₂ hL'
  rw [List.length_map] at hat
  have hlb' := leftBehind_eq (pre.map (held (P := F.XiPub × F.S₁))) D.t₁ D.ds₂
  have hsum : ((pre.map (held (P := F.XiPub × F.S₁))).map (·.rounds.length)).sum =
      (pre.flatMap (·.rounds)).length := by
    rw [List.length_flatMap, List.map_map]
    rfl
  rw [hsum] at hlb'
  have hds : (leftBehind (pre.map (held (P := F.XiPub × F.S₁))) D.t₁ D.ds₂).2.take
      (held (P := F.XiPub × F.S₁) B).rounds.length = dB :: dt := by
    rw [hlb']
    show (D.ds₂.drop (pre.flatMap (·.rounds)).length).take B.rounds.length = dB :: dt
    rw [hB]
    exact hlist
  have hb0 : baseAt F.t₁ F.t₂ 1 π =
      D.t₁ + nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length) := by
    have h0 := hAt.numOwn 0
    rw [Nat.add_zero, Nat.add_zero] at h0
    exact h0
  refine ⟨_, dB, dt, hat, rfl, rfl, ?_, hds, hlist, fun ε hε => hε _ hds, hb0.symm,
    (opensShaped F file D h).2.1, hAt, hsm⟩
  show (leftBehind (pre.map (held (P := F.XiPub × F.S₁))) D.t₁ D.ds₂).1 = _
  rw [hlb']

/-- **Where that piece ends**: the number of the first tree behind it is the chain's first tree's
plus the trees of the data as far as the block's last round. (The piece is pinned by its number in
the row.) -/
theorem tile_end₂ {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber)
        ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (π : P12) (r : Fmt.M1.Stage → ℕ) (k : ℕ)
    (pre : List (Block F.S₂ F.Cl)) (B b' : Block F.S₂ F.Cl) (post : List (Block F.S₂ F.Cl))
    (hfl : F.shared.blocksInOrder = b₂ :: l₂) (hcut : b₂ :: l₂ = pre ++ B :: b' :: post)
    (hB : B.rounds = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ k)) (hj : johOk π r = true)
    (hbat : batPriceOk π r k = true) (ho : π.nums.ownMask = false) :
    ∀ p,
      ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₂)[pre.length]? =
        some p →
      p.base + p.trees = D.t₁ + nTrees (D.ds₂.take ((pre.flatMap (·.rounds)).length +
        (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length)) := by
  obtain ⟨p', dB, dt, hrow, _, _, hpbase, hpds, hlist, _⟩ :=
    tile_piece₂ F file D h b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd π r k pre B b' post hfl hcut
      hB hfree hp hC hj hbat ho
  intro p hp'
  obtain rfl : p' = p := Option.some.inj (hrow.symm.trans hp')
  have ht : p'.trees = nTrees p'.ds := rfl
  rw [ht, hpbase, hpds, ← hlist, List.take_add, VerifiableInference.Desc.K12.Coin.nTrees_app,
    Nat.add_assoc]

/-! ## The game there, in the form for one statement -/

/-- **The game with nothing promised of the record, first arm, in the form `Leads`.** That the
family's errors at that number are "BAT"'s count times the sampler's number and the place's own
errors is a premise (`herr`). -/
theorem game_at_tile₂V {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber)
        ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (π : P12) (r : Fmt.M1.Stage → ℕ) (k : ℕ)
    (enter : F.S₂ → Except String T12) (leave : F.S₂ → T12 → Except String F.S₂)
    (pre : List (Block F.S₂ F.Cl)) (B b' : Block F.S₂ F.Cl) (post : List (Block F.S₂ F.Cl))
    (hfl : F.shared.blocksInOrder = b₂ :: l₂) (hcut : b₂ :: l₂ = pre ++ B :: b' :: post)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) B)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ k)) (hj : johOk π r = true)
    (hbat : batPriceOk π r k = true) (ho : π.nums.ownMask = false)
    (hlb : ownLabelsFreeB π = true) (rd : ℕ → ℕ)
    (herr : ∀ dB dt, (D.ds₂.drop (pre.flatMap (·.rounds)).length).take
        (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt →
      ∀ ds', ds' = dB :: dt → HEq (rest₂ (0 + pre.length) ds').err
        ((batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) :
          Err (uLT (ckP .two) (dB :: dt)))) :
    ∃ p dB dt,
      ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₂)[pre.length]? =
        some p ∧
      p.b = held B ∧
      p.base = D.t₁ + nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length) ∧ p.ds = dB :: dt ∧
      HEq p.err ((batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) :
        Err (uLT (ckP .two) (dB :: dt))) ∧
      Err.Below (s := uLT (ckP .two) (dB :: dt))
        (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) ((2 : ℝ≥0∞)⁻¹ ^ k) ∧
      p.ior.red.Leads (fun _ => True)
        (fun a b => (∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
          QN π (NTuple (frameAt D (allOf D) D.key₂ 0) π
            (nuOf π (nlAt π (numAt F.t₁ F.t₂ 1 (.own 0))) t) (fun s => r s.st) rd) (t, a.2)) ∧
          b.1 = (a.1.1, b.1.2))
        p.err := by
  obtain ⟨p, dB, dt, hrow, hpb, hp0, hpbase, hpds, hlist, hperr, hb0, _, hAt, hsm⟩ :=
    tile_piece₂ F file D h b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd π r k pre B b' post hfl hcut
      hal.rounds hfree hp hC hj hbat ho
  refine ⟨p, dB, dt, hrow, hpb, hpbase, hpds, hperr _ (herr dB dt hlist), hsm, ?_⟩
  exact k12_game_alikeV (F.XiPub × F.S₁) F.S₂ F.Cl enter leave _ W π (numAt F.t₁ F.t₂ 1) _
    Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) rd
    (D.t₁ + nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length)) dB dt _ (errJ π r dt) r p
    (by rw [hpb]; exact hal.held) hp0 hpbase hpds (hperr _ (herr dB dt hlist)) hAt (fun _ => rfl)
    hj (H2K.Made.batOneOk_of_planOk guardedProximityTestParts π hp) (Nat.le_refl _)
    (by rw [hb0]; exact labelsPub_own π 1 F.t₁ F.t₂ hlb)

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.εAt_errJ
#print axioms VerifiableInference.Desc.K12.Coin.errJ_small
#print axioms VerifiableInference.Desc.K12.Coin.atPlace_tile₂
#print axioms VerifiableInference.Desc.K12.Coin.tile_piece₂
#print axioms VerifiableInference.Desc.K12.Coin.tile_end₂
#print axioms VerifiableInference.Desc.K12.Coin.game_at_tile₂V
