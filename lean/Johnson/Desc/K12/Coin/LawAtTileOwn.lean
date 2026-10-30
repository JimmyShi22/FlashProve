-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/LawAtTileOwn.lean: the law's public premises and the game of the proximity
test (the kind K12) at the piece that a description's own tiling holds on the shared chain, SECOND
ARM (the first fold sends its own mask); general in the description. Definitions, statements and
proofs; each main proof is a row of calls.

The model is LawAtTile.lean (first arm), statement for statement. `atPlaceOwn_tile₂` and
`tile_pieceOwn₂` were made of its texts by a program that turns five names and one value. What is
free of the arm there is called, not typed again: `errJ_small` (LawAtTile.lean), `errJ`,
`bears_errJ`, `own_pays` (GameJ.lean), `like_of_cut` (LikeOfCut.lean), `batBelow_like`
(Johnson/Desc/K12/Law/BatValsPayAt.lean). Of the second arm's own: `atPlaceOwn_of_cut`
(AtDescOwn.lean), `k12_game_alikeO` (GameAlike.lean).
What it is not, first.
  (1) THE FORM IS `Leads`, one statement at a time, AND UNDER A PROMISE ON THE RECORD
    (`FirstOpensOwn`, OwnArm.lean). The rule `proofSound_at_desc` (Johnson/Desc/Plain/AtDesc.lean)
    asks of the shared chain's row `LeadsK`: one game for all the statements with one key. Neither
    that form nor a form with nothing promised is reached here.
  (2) `herr` is a premise on a letter of `piecesAt`, the family of extractors and errors: that the
    errors which the family lays at the piece are AT LEAST the pair named there, round by round.
    Which errors the file's piece bears is the choice of whoever fills that family. «Small» is said
    of the pair, not of the family's errors.
  (3) The second arm alone, the shared chain alone; the seat is not the row's last block; the seat's
    entry has the seat's own decision (`Alike`).
  (4) How the flat list parts, `Alike`, the count of roots in front, the block's test on the plan
    and that the description has data are premises: shown here of no description.
Main names.
  `atPlaceOwn_cutJ`: `AtPlaceOwn` at a cut of a chain's data, at the place's own errors.
  `TileOwnAt Fr π num r b base dB dt`: `AtPlaceOwn` at the Johnson letters, the radii r and `errJ`;
    and the whole entry ("BAT"'s count times the sampler's number, then `errJ`) is below b, round by
    round.
  `atPlaceOwn_tile₂`: at a description with data whose shared chain's flat list is pre ++ B :: post,
    B declaring the test's rounds.
  `tile_pieceOwn₂`: the piece number pre.length of the second row of `piecesAt`, its fields in hand.
  `tile_endOwn₂`: that piece's base and the trees that it sends: where the next piece begins.
  `pays_at_tile`: the three premises that the second arm's game asks on "BAT"'s round, at the tile's
    own data.
  `gameO_piece_le`: the game at any piece whose block is alike to the held seat and whose errors are
    at least a given pair.
  `game_at_tile₂O`: the game at the tile's piece.
Limits: those of the files called. No soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Coin.LawAtTile
import Johnson.Desc.K12.Coin.AtDescOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.Pub (sgOf writtenOf WR chainFrom spendOk PayPub johOk batV0 batPriceOk codes_of_johOk)
open H2K.Member (wsAt w0At dtAt wsAt_cons)
open H2K.Pin (NTuple)
open Johnson.G.OfPlan (rootsOf)
open scoped ENNReal

/-! ## At a cut, at the place's own errors -/

/-- **`AtPlaceOwn` at a cut of a chain's data, at the place's own errors**: `atPlaceOwn_of_cut` with
its two premises `bears` and `codes` paid, as `atPlace_cutJ` (AtCutJ.lean) pays them at the first
arm: neither payer reads the arm. -/
theorem atPlaceOwn_cutJ (Fr : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (r : Fmt.M1.Stage → ℕ)
    (ds : List RDT) (pre mid post : List Fmt.DeclaredRound) (base₀ : ℕ) (allTs : List Fmt.Shape)
    (dB : RDT) (dt : List RDT) (hcons : dB :: dt = (ds.drop pre.length).take mid.length)
    (hAs : List.Forall₂ RoundAsG ds (pre ++ (mid ++ post)))
    (hmid : mid = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds)
    (hwants : ∀ Rs, wantsOf Fr.a (stg Fr (base₀ + nTrees (ds.take pre.length))
        ((ds.drop pre.length).take mid.length)).depth ((ds.drop pre.length).take mid.length) Rs =
      wantsDecl num mid Rs)
    (hchain : ∀ n x, (ds.flatMap (·.trees))[n]? = some x → allTs[base₀ + n]? = some x)
    (hopen : ∀ r ∈ mid, ∀ o ∈ r.opens, allTs[num o.2]? = some o.1)
    (hnum0 : ∀ m, num (.own m) = base₀ + m) (hfree : π.nums.free = rootsOf pre)
    (early : π.early = true) (answers : π.answers = 1)
    (planOk : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (spend : spendOk π = true)
    (hj : johOk π r = true) (ho : π.nums.ownMask = true) (w0 : WR) (l : List WR)
    (hw : writtenOf π.nums = some (w0 :: l)) :
    AtPlaceOwn Fr π num Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st)
      (base₀ + nTrees (ds.take pre.length)) dB dt (errJ π r dt) :=
  atPlaceOwn_of_cut Fr π num _ _ _ _ _ ds pre mid post base₀ allTs dB dt (errJ π r dt) hcons hAs
    hmid hwants hchain hopen hnum0 hfree early answers planOk spend (codes_of_johOk r π hj) ho w0 l
    hw
    (bears_errJ π r dB dt
      (like_of_cut π num ds pre mid post base₀ allTs dB dt hcons hAs hmid hchain hopen hnum0 hfree
        planOk w0 l hw))

/-! ## At the file's own tile -/

/-- **What holds at a tile, second arm**: `AtPlaceOwn` at the Johnson letters, the radii r and the
place's own errors; and the whole entry is below b, round by round. -/
def TileOwnAt (Fr : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (r : Fmt.M1.Stage → ℕ) (b : ℝ≥0∞)
    (base : ℕ) (dB : RDT) (dt : List RDT) : Prop :=
  AtPlaceOwn Fr π num Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) base dB dt (errJ π r dt) ∧
    Err.Below (s := uLT (ckP .two) (dB :: dt))
      (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) b

/-- **The three premises that the second arm's game asks on "BAT"'s round, at the tile's own data**:
off «the stretch is like the written rounds» and two tests on the plan. -/
theorem pays_at_tile {Fr : Frame} {π : P12} {num : Fmt.TreeSource → ℕ} {r : Fmt.M1.Stage → ℕ}
    {b : ℝ≥0∞} {base : ℕ} {dB : RDT} {dt : List RDT} (A : TileOwnAt Fr π num r b base dB dt)
    (hj : johOk π r = true) :
    PayPub π (fun s => r s.st) dB.entry.rows (batV0 π r) ∧
      Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0] ∧ dB.entry.logN ≤ 64 :=
  own_pays π (fun s => r s.st) r (fun _ => rfl) hj
    (H2K.Made.batOneOk_of_planOk guardedProximityTestParts π A.1.planOk) dB dt A.1.like

/-- **At the shared chain of a description with data.** -/
theorem atPlaceOwn_tile₂ {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (key : ℕ → ℕ) (ft : ℕ) (π : P12) (r : Fmt.M1.Stage → ℕ) (k : ℕ)
    (pre : List (Block F.S₂ F.Cl)) (B : Block F.S₂ F.Cl) (post : List (Block F.S₂ F.Cl))
    (hfl : F.shared.blocksInOrder = pre ++ B :: post)
    (hB : B.rounds = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ k)) (hj : johOk π r = true)
    (hbat : batPriceOk π r k = true) (ho : π.nums.ownMask = true) :
    ∃ dB dt, (D.ds₂.drop (pre.flatMap (·.rounds)).length).take
        (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt ∧
      TileOwnAt (frameAt D (allOf D) key ft) π (numAt F.t₁ F.t₂ 1) r ((2 : ℝ≥0∞)⁻¹ ^ k)
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
  have hAt : AtPlaceOwn (frameAt D (allOf D) key ft) π (numAt F.t₁ F.t₂ 1) Sg.lstJ Sg.flC Sg.flZ
      Sg.flZ (fun s => r s.st) (D.t₁ + nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length)) dB dt
      (errJ π r dt) :=
    atPlaceOwn_cutJ _ π _ r D.ds₂ (pre.flatMap (·.rounds)) _ (post.flatMap (·.rounds)) D.t₁ (allT D)
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
put back, base, data; its errors are the family's at that number; and `TileOwnAt` there. -/
theorem tile_pieceOwn₂ {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
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
    (hbat : batPriceOk π r k = true) (ho : π.nums.ownMask = true) :
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
      TileOwnAt (frameAt D (allOf D) D.key₂ 0) π (numAt F.t₁ F.t₂ 1) r ((2 : ℝ≥0∞)⁻¹ ^ k)
        (D.t₁ + nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length)) dB dt := by
  obtain ⟨dB, dt, hlist, hAt, hsm⟩ := atPlaceOwn_tile₂ F file D h D.key₂ 0 π r k pre B (b' :: post)
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

/-- **Where the tile's piece ends**: whatever stands at number pre.length of the second row of
`piecesAt`: its base and the trees that it sends are the first chain's trees and those of the shared
chain's data up to the end of the test's rounds. So the next piece's base is this number. -/
theorem tile_endOwn₂ {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
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
    (hbat : batPriceOk π r k = true) (ho : π.nums.ownMask = true) :
    ∀ p,
      ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₂)[pre.length]? =
        some p →
      p.base + p.trees = D.t₁ + nTrees (D.ds₂.take ((pre.flatMap (·.rounds)).length +
        (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length)) := by
  intro p hpr
  obtain ⟨p', dB, dt, hrow, _, _, hpbase, hpds, hlist, _⟩ :=
    tile_pieceOwn₂ F file D h b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd π r k pre B b' post hfl
      hcut hB hfree hp hC hj hbat ho
  obtain rfl : p' = p := Option.some.inj (hrow.symm.trans hpr)
  have ht : p'.trees = VerifiableInference.Desc.Sound.nTrees (dB :: dt) := by
    show VerifiableInference.Desc.Sound.nTrees p'.ds = _
    rw [hpds]
  have e : VerifiableInference.Desc.Sound.nTrees (D.ds₂.take ((pre.flatMap (·.rounds)).length +
        (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length)) =
      VerifiableInference.Desc.Sound.nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length) +
        VerifiableInference.Desc.Sound.nTrees ((D.ds₂.drop (pre.flatMap (·.rounds)).length).take
          (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length) := by
    rw [List.take_add]
    unfold VerifiableInference.Desc.Sound.nTrees
    rw [List.map_append, List.sum_append]
  rw [hpbase, ht, e, hlist, Nat.add_assoc]

/-! ## The game there, in the form for one statement, under the promise -/

/-- **The game at any piece whose block is alike to the held seat, second arm, WHATEVER errors the
piece bears**, if only they are at least (e, εt), round by round. The three premises that
`k12_game_alikeO` asks on "BAT"'s round are paid by `own_pays`. -/
theorem gameO_piece_le (P S Cl' : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ)
    (no rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT) (e : ℕ) (εt : Err (uLT (ckP .two) dt))
    (r : Fmt.M1.Stage → ℕ) (p : Piece (ckP .two) F (P × S) Cl' W)
    (hb : Alike (held (P := P) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave)) p.b)
    (h0 : p.back = []) (hbase : p.base = base) (hds : p.ds = dB :: dt)
    (hε : ∀ ε₀ : Err (uLT (ckP .two) p.ds),
      HEq ε₀ ((e, εt) : Err (uLT (ckP .two) (dB :: dt))) → Err.le ε₀ p.err)
    (hA : AtPlaceOwn F π num Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) base dB dt εt)
    (hj : johOk π r = true) (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e) :
    p.ior.red.Leads (fun a => ∀ t, enter a.1.2 = .ok t → FirstOpensOwn π num no base t)
      (fun a b => (∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
        QN π (NTuple F π no (fun s => r s.st) rd) (t, a.2)) ∧ b.1 = (a.1.1, b.1.2))
      p.err := by
  obtain ⟨hP, h1, hlog⟩ := own_pays π (fun s => r s.st) r (fun _ => rfl) hj
    (H2K.Made.batOneOk_of_planOk guardedProximityTestParts π hA.planOk) dB dt hA.like
  obtain ⟨pb, pbase, pds, pback, pext, perr⟩ := p
  dsimp only at hb h0 hbase hds hε
  subst hds
  have h := k12_game_alikeO P S Cl' enter leave F W π num no Sg.lstJ Sg.flC Sg.flZ Sg.flZ
    (fun s => r s.st) rd base dB dt e (batV0 π r) εt
    (⟨pb, pbase, dB :: dt, pback, pext, (e, εt)⟩ : Piece (ckP .two) F (P × S) Cl' W) hb h0 hbase
    rfl HEq.rfl hA hP h1 hlog hle
  exact h.mono_err (hε _ HEq.rfl)

/-- **The game under the promise `FirstOpensOwn`, second arm, in the form `Leads`, at the shared
chain's piece number pre.length of `piecesAt`, WHATEVER the family of extractors and errors lays
there**, if only its errors are at least "BAT"'s count times the sampler's number and the place's
own errors, round by round (`herr`); and that pair is below 2⁻¹ ^ k. The numbering no of the book's
places is a free letter: the promise ties it. -/
theorem game_at_tile₂O {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
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
    (hbat : batPriceOk π r k = true) (ho : π.nums.ownMask = true)
    (no rd : ℕ → ℕ)
    (herr : ∀ dB dt, (D.ds₂.drop (pre.flatMap (·.rounds)).length).take
        (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt →
      Err.le (s := uLT (ckP .two) (dB :: dt))
        (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt)
        (rest₂ (0 + pre.length) (dB :: dt)).err) :
    ∃ p dB dt,
      ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₂)[pre.length]? =
        some p ∧
      p.b = held B ∧
      p.base = D.t₁ + nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length) ∧ p.ds = dB :: dt ∧
      HEq p.err (rest₂ (0 + pre.length) (dB :: dt)).err ∧
      Err.Below (s := uLT (ckP .two) (dB :: dt))
        (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) ((2 : ℝ≥0∞)⁻¹ ^ k) ∧
      p.ior.red.Leads
        (fun a => ∀ t, enter a.1.2 = .ok t → FirstOpensOwn π (numAt F.t₁ F.t₂ 1) no
          (D.t₁ + nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length)) t)
        (fun a b => (∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
          QN π (NTuple (frameAt D (allOf D) D.key₂ 0) π no (fun s => r s.st) rd) (t, a.2)) ∧
          b.1 = (a.1.1, b.1.2))
        p.err := by
  obtain ⟨p, dB, dt, hrow, hpb, hp0, hpbase, hpds, hlist, hperr, _, _, hAt, hsm⟩ :=
    tile_pieceOwn₂ F file D h b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd π r k pre B b' post hfl
      hcut hal.rounds hfree hp hC hj hbat ho
  have hpe : HEq p.err (rest₂ (0 + pre.length) (dB :: dt)).err :=
    hperr _ fun ds' e => by
      subst e
      exact HEq.rfl
  have along : ∀ (ds : List RDT), ds = dB :: dt → ∀ pe ε₀ : Err (uLT (ckP .two) ds),
      HEq pe (rest₂ (0 + pre.length) (dB :: dt)).err →
      HEq ε₀ ((batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) :
        Err (uLT (ckP .two) (dB :: dt))) → Err.le ε₀ pe := by
    intro ds hd
    subst hd
    intro pe ε₀ e1 e0
    rw [eq_of_heq e1, eq_of_heq e0]
    exact herr dB dt hlist
  refine ⟨p, dB, dt, hrow, hpb, hpbase, hpds, hpe, hsm, ?_⟩
  exact gameO_piece_le (F.XiPub × F.S₁) F.S₂ F.Cl enter leave _ W π (numAt F.t₁ F.t₂ 1) no rd
    (D.t₁ + nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length)) dB dt _ (errJ π r dt) r p
    (by rw [hpb]; exact hal.held) hp0 hpbase hpds (fun ε₀ e0 => along _ hpds p.err ε₀ hpe e0) hAt
    hj (Nat.le_refl _)

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.atPlaceOwn_cutJ
#print axioms VerifiableInference.Desc.K12.Coin.pays_at_tile
#print axioms VerifiableInference.Desc.K12.Coin.atPlaceOwn_tile₂
#print axioms VerifiableInference.Desc.K12.Coin.tile_pieceOwn₂
#print axioms VerifiableInference.Desc.K12.Coin.tile_endOwn₂
#print axioms VerifiableInference.Desc.K12.Coin.gameO_piece_le
#print axioms VerifiableInference.Desc.K12.Coin.game_at_tile₂O
