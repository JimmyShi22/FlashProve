-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/LawAtTileFirst.lean: the law's public premises and the game of the proximity
test (the kind K12) at the piece that a description's own tiling holds ON THE FIRST CHAIN, first
arm; general in the description. Statements and proofs; each main proof is a row of calls. It is
LawAtTile.lean (the shared chain), carried to the first row of `piecesAt`, with `Sits` in `Alike`'s
place.

Why. The rule `proofSound_at_desc` (Johnson/Desc/Plain/AtDesc.lean) asks of the first chain's row
`EachLeads`: at each piece a plain law, in the form `Leads`. That is the form which the game has
here. At the first chain's finish the entry of the flat list stands behind guards, and a block
without a round may be joined behind it: it has not the seat's decision, so it is no `Alike` of the
seat; it sits on the kind's block (`Sits`, Johnson/Desc/K12/Law/Sits.lean), and a plain law goes
over to whatever sits there (`k12_game_sitsV`, LeadsSits.lean).
What is called: `atPlace_firstJ` (AtDescJ.lean) and `k12_game_sitsV` (LeadsSits.lean);
`TileAt`, `errJ_small` (LawAtTile.lean), `ChainAt` (LawAtLight.lean),
`labelsPub_own` (GameAt.lean), `batBelow_like` (Johnson/Desc/K12/Law/BatValsPayAt.lean);
`cutRow_at` (GameTile.lean), `leftBehind_eq` (GameHeld.lean), `roundsOfData`
(Johnson/Desc/Sound/DataRounds.lean), `piecesAt` (Johnson/Desc/Sound/PaidAtDesc.lean).
What it is not, first.
  (1) In `game_at_tile₁V`, `herr` is a premise on a letter of `piecesAt`: the family of extractors
  and errors. Which
    errors the file's piece bears is the choice of whoever fills that family: no theorem pays it.
    "Small" is said of the pair that `herr` names.
  (2) The first arm alone (no own mask), the first chain alone; the seat is not the row's last
    block, and the chain's declared rounds end in a round behind the seat (`hend`): the data of the
    first chain hold no entry for that last round.
  (3) The conclusion's numbering is read off the record by the trees' labels (`nuOf`): all that
    stands first at the head of GameAt.lean on that form stands here.
  (4) One clause of `EachLeads` at one piece: the promise in front is "nothing" (`fun _ => True`);
    that what is concluded gives the next piece's promise is not said here.
  (5) How the flat list parts, `Sits`, the count of roots in front, the block's test on the plan and
    that the description has data are premises: shown here of no description.
Main names.
  `atPlace_tile₁`: at a description with data whose first chain's flat list is pre ++ B :: post, B
    declaring the test's rounds: `TileAt` at the stretch of the first chain's data.
  `tile_piece₁`: the piece number pre.length of the first row of `piecesAt`, its fields in hand.
  `tile_end₁`: where that piece ends.
  `game_at_tile₁V`: the game at that piece, in the form `Leads`.
  `game_piece_sitsVY_le`, `game_at_tile₁VY_le`: the game with the step's own yes in the conclusion
    (`StepYes`, `k12_game_sitsVY`, SitsYes.lean), at WHATEVER errors the family
    lays
    there, if they are at least the pair, round by round.
  `game_at_tile₁VY_cap`: where every piece's errors are the cap (`AtCap`): NO PREMISE ON THE ERRORS.
    `game_at_tile₁V`'s `herr` asks that the family bears JUST the pair: at a family that lays the
    cap
    it is false, and that top is idle there: the cap's form is the one to call.
Limits: those of the files called. No soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Coin.LawAtTile
import Johnson.Desc.K12.Coin.AtDescJ
import Johnson.Desc.K12.Coin.SitsYes
import Johnson.Desc.K12.Coin.ReadsKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.Pub (sgOf writtenOf WR chainFrom johOk batV0 batPriceOk)
open H2K.Member (wsAt w0At dtAt wsAt_cons)
open H2K.Pin (NTuple)
open H2K.JointK (Sits)
open Johnson.G.OfPlan (rootsOf)
open scoped ENNReal

/-- **At the first chain of a description with data.** -/
theorem atPlace_tile₁ {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (key : ℕ → ℕ) (ft : ℕ) (π : P12) (r : Fmt.M1.Stage → ℕ) (k : ℕ)
    (pre : List (Block F.S₁ F.Cl)) (B : Block F.S₁ F.Cl) (post : List (Block F.S₁ F.Cl))
    (postR : List Fmt.DeclaredRound) (r₀ : Fmt.DeclaredRound)
    (hfl : F.first.blocksInOrder = pre ++ B :: post)
    (hend : post.flatMap (·.rounds) = postR ++ [r₀])
    (hB : B.rounds = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ k)) (hj : johOk π r = true)
    (hbat : batPriceOk π r k = true) (ho : π.nums.ownMask = false) :
    ∃ dB dt, (D.ds₁.drop (pre.flatMap (·.rounds)).length).take
        (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt ∧
      TileAt (frameAt D (allOf D) key ft) π (numAt F.t₁ F.t₂ 0) r ((2 : ℝ≥0∞)⁻¹ ^ k)
        (0 + nTrees (D.ds₁.take (pre.flatMap (·.rounds)).length)) dB dt := by
  have hA := roundsOfData F file D h
  have e : F.roundsDeclaredByBlocks.1 = (pre.flatMap (·.rounds)) ++
      ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ (postR ++ [r₀])) := by
    show F.first.blocksInOrder.flatMap (·.rounds) = _
    rw [hfl, List.flatMap_append, List.flatMap_cons, hB, hend]
  have hAs : List.Forall₂ RoundAsG D.ds₁ ((pre.flatMap (·.rounds)) ++
      ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ postR)) := by
    have ed : F.roundsDeclaredByBlocks.1.dropLast = (pre.flatMap (·.rounds)) ++
        ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ postR) := by
      rw [e]
      simp only [← List.append_assoc, List.dropLast_concat]
    rw [← ed]
    exact hA.1
  have hL := (forall₂_cut _ _ _ hAs).length_eq
  have hrs : H2U.roundsOfNums π.nums = some (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds :=
    VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts π hp
  have hpos : 0 < (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length := by
    obtain ⟨_, _, _, R, _, _, hR⟩ := H2K.Made.rounds_top π.nums _ hrs
    rw [hR]
    exact Nat.succ_pos _
  obtain ⟨dB, dt, hlist⟩ : ∃ dB dt, (D.ds₁.drop (pre.flatMap (·.rounds)).length).take
      (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt := by
    cases hq : (D.ds₁.drop (pre.flatMap (·.rounds)).length).take
        (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length with
    | nil =>
      rw [hq, List.length_nil] at hL
      omega
    | cons x y => exact ⟨x, y, rfl⟩
  have hw := (wsAt_cons π hp).1
  have hAt : AtPlace (frameAt D (allOf D) key ft) π (numAt F.t₁ F.t₂ 0) Sg.lstJ Sg.flC Sg.flZ
      Sg.flZ (fun s => r s.st) (0 + nTrees (D.ds₁.take (pre.flatMap (·.rounds)).length)) dB dt
      (errJ π r dt) :=
    atPlace_firstJ F file D h key ft π r (pre.flatMap (·.rounds)) postR r₀ e dB dt hlist.symm hfree
      (H2K.JointK.early_of_planOk π hp) (H2K.JointK.answers_of_planOk π hp) hp
      (H2K.Made.spendOk_of_planOk π hp) hj ho _ _ hw
  refine ⟨dB, dt, hlist, hAt, errJ_small hC hAt.like ?_⟩
  obtain ⟨a₀, rest₀, _, _, _, e1, _⟩ := hC
  exact H2K.Pin.batBelow_like π r k a₀ rest₀ e1 dB dt hAt.like hbat

/-! ## The piece that the description's own tiling holds -/

/-- **The first chain's piece number pre.length of `piecesAt`, its fields in hand**: block, nothing
put back, base, data; its errors are the family's at that number; and `TileAt` there. -/
theorem tile_piece₁ {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
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
    (pre : List (Block F.S₁ F.Cl)) (B b' : Block F.S₁ F.Cl) (post : List (Block F.S₁ F.Cl))
    (postR : List Fmt.DeclaredRound) (r₀ : Fmt.DeclaredRound)
    (hfl : F.first.blocksInOrder = b₁ :: l₁) (hcut : b₁ :: l₁ = pre ++ B :: b' :: post)
    (hend : (b' :: post).flatMap (·.rounds) = postR ++ [r₀])
    (hB : B.rounds = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ k)) (hj : johOk π r = true)
    (hbat : batPriceOk π r k = true) (ho : π.nums.ownMask = false) :
    ∃ p dB dt,
      ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁)[pre.length]? =
        some p ∧
      p.b = held B ∧ p.back = [] ∧
      p.base = 0 + nTrees (D.ds₁.take (pre.flatMap (·.rounds)).length) ∧ p.ds = dB :: dt ∧
      (D.ds₁.drop (pre.flatMap (·.rounds)).length).take
        (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt ∧
      (∀ ε : Err (uLT (ckP .two) (dB :: dt)),
        (∀ ds', ds' = dB :: dt → HEq (rest₁ (0 + pre.length) ds').err ε) → HEq p.err ε) ∧
      0 + nTrees (D.ds₁.take (pre.flatMap (·.rounds)).length) = baseAt F.t₁ F.t₂ 0 π ∧
      TileAt (frameAt D (allOf D) D.key₁ 0) π (numAt F.t₁ F.t₂ 0) r ((2 : ℝ≥0∞)⁻¹ ^ k)
        (0 + nTrees (D.ds₁.take (pre.flatMap (·.rounds)).length)) dB dt := by
  obtain ⟨dB, dt, hlist, hAt, hsm⟩ := atPlace_tile₁ F file D h D.key₁ 0 π r k pre B (b' :: post)
    postR r₀ (hfl.trans hcut) hend hB hfree hp hC hj hbat ho
  have hL' : held (P := F.XiPub) b₁ :: l₁.map held =
      pre.map held ++ held B :: held b' :: post.map held := by
    have := congrArg (List.map (held (P := F.XiPub))) hcut
    simpa using this
  have hat := cutRow_at rest₁ [sealRound] (held B) (held b') (post.map held) (pre.map held)
    (held b₁) (l₁.map held) 0 0 D.ds₁ hL'
  rw [List.length_map] at hat
  have hlb' := leftBehind_eq (pre.map (held (P := F.XiPub))) 0 D.ds₁
  have hsum : ((pre.map (held (P := F.XiPub))).map (·.rounds.length)).sum =
      (pre.flatMap (·.rounds)).length := by
    rw [List.length_flatMap, List.map_map]
    rfl
  rw [hsum] at hlb'
  have hds : (leftBehind (pre.map (held (P := F.XiPub))) 0 D.ds₁).2.take
      (held (P := F.XiPub) B).rounds.length = dB :: dt := by
    rw [hlb']
    show (D.ds₁.drop (pre.flatMap (·.rounds)).length).take B.rounds.length = dB :: dt
    rw [hB]
    exact hlist
  have hb0 : baseAt F.t₁ F.t₂ 0 π =
      0 + nTrees (D.ds₁.take (pre.flatMap (·.rounds)).length) := by
    have h0 := hAt.numOwn 0
    rw [Nat.add_zero, Nat.add_zero] at h0
    exact h0
  refine ⟨_, dB, dt, hat, rfl, rfl, ?_, hds, hlist, fun ε hε => hε _ hds, hb0.symm, hAt, hsm⟩
  show (leftBehind (pre.map (held (P := F.XiPub))) 0 D.ds₁).1 = _
  rw [hlb']

/-- **Where that piece ends**: the number of the first tree behind it is the trees of the data as
far
as the block's last round. (The piece is pinned by its number in the row.) -/
theorem tile_end₁ {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
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
    (pre : List (Block F.S₁ F.Cl)) (B b' : Block F.S₁ F.Cl) (post : List (Block F.S₁ F.Cl))
    (postR : List Fmt.DeclaredRound) (r₀ : Fmt.DeclaredRound)
    (hfl : F.first.blocksInOrder = b₁ :: l₁) (hcut : b₁ :: l₁ = pre ++ B :: b' :: post)
    (hend : (b' :: post).flatMap (·.rounds) = postR ++ [r₀])
    (hB : B.rounds = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ k)) (hj : johOk π r = true)
    (hbat : batPriceOk π r k = true) (ho : π.nums.ownMask = false) :
    ∀ p,
      ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁)[pre.length]? =
        some p →
      p.base + p.trees = 0 + nTrees (D.ds₁.take ((pre.flatMap (·.rounds)).length +
        (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length)) := by
  obtain ⟨p', dB, dt, hrow, _, _, hpbase, hpds, hlist, _⟩ :=
    tile_piece₁ F file D h b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd π r k pre B b' post postR r₀
      hfl hcut hend hB hfree hp hC hj hbat ho
  intro p hp'
  obtain rfl : p' = p := Option.some.inj (hrow.symm.trans hp')
  have ht : p'.trees = nTrees p'.ds := rfl
  rw [ht, hpbase, hpds, ← hlist, List.take_add, VerifiableInference.Desc.K12.Coin.nTrees_app,
    Nat.add_assoc]

/-! ## The game there, in the form that the rule asks of the first chain's row -/

/-- **The game with nothing promised of the record, first arm, in the form `Leads`, at whatever
block sits on the kind's behind the two doors.** That the family's errors at that number are "BAT"'s
count times the sampler's number and the place's own errors is a premise (`herr`). -/
theorem game_at_tile₁V {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
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
    (enter : F.S₁ → Except String T12) (leave : F.S₁ → T12 → Except String F.S₁)
    (pre : List (Block F.S₁ F.Cl)) (B b' : Block F.S₁ F.Cl) (post : List (Block F.S₁ F.Cl))
    (postR : List Fmt.DeclaredRound) (r₀ : Fmt.DeclaredRound)
    (hfl : F.first.blocksInOrder = b₁ :: l₁) (hcut : b₁ :: l₁ = pre ++ B :: b' :: post)
    (hend : (b' :: post).flatMap (·.rounds) = postR ++ [r₀])
    (hS : Sits B (proximityTestKind guardedProximityTestParts π : Block T12 Unit) enter leave)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ k)) (hj : johOk π r = true)
    (hbat : batPriceOk π r k = true) (ho : π.nums.ownMask = false)
    (hlb : ownLabelsFreeB π = true) (rd : ℕ → ℕ)
    (herr : ∀ dB dt, (D.ds₁.drop (pre.flatMap (·.rounds)).length).take
        (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt →
      ∀ ds', ds' = dB :: dt → HEq (rest₁ (0 + pre.length) ds').err
        ((batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) :
          Err (uLT (ckP .two) (dB :: dt)))) :
    ∃ p dB dt,
      ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁)[pre.length]? =
        some p ∧
      p.b = held B ∧
      p.base = 0 + nTrees (D.ds₁.take (pre.flatMap (·.rounds)).length) ∧ p.ds = dB :: dt ∧
      HEq p.err ((batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) :
        Err (uLT (ckP .two) (dB :: dt))) ∧
      Err.Below (s := uLT (ckP .two) (dB :: dt))
        (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) ((2 : ℝ≥0∞)⁻¹ ^ k) ∧
      p.ior.red.Leads (fun _ => True)
        (fun a b => (∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
          QN π (NTuple (frameAt D (allOf D) D.key₁ 0) π
            (nuOf π (nlAt π (numAt F.t₁ F.t₂ 0 (.own 0))) t) (fun s => r s.st) rd) (t, a.2)) ∧
          b.1 = (a.1.1, b.1.2))
        p.err := by
  obtain ⟨p, dB, dt, hrow, hpb, hp0, hpbase, hpds, hlist, hperr, hb0, hAt, hsm⟩ :=
    tile_piece₁ F file D h b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd π r k pre B b' post postR r₀
      hfl hcut hend hS.rounds hfree hp hC hj hbat ho
  refine ⟨p, dB, dt, hrow, hpb, hpbase, hpds, hperr _ (herr dB dt hlist), hsm, ?_⟩
  exact k12_game_sitsV F.XiPub F.S₁ F.Cl enter leave _ W π (numAt F.t₁ F.t₂ 0)
    Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) rd
    (0 + nTrees (D.ds₁.take (pre.flatMap (·.rounds)).length)) dB dt _ (errJ π r dt) B hS p hpb hp0
    hpbase hpds (hperr _ (herr dB dt hlist)) _ r hAt (fun _ => rfl) hj
    (H2K.Made.batOneOk_of_planOk guardedProximityTestParts π hp) (Nat.le_refl _)
    (by rw [hb0]; exact labelsPub_own π 0 F.t₁ F.t₂ hlb)

/-! ## With the step's own yes, at whatever errors the family lays -/

/-- **At a piece whose errors are at least the pair**, round by round: the game with the step's own
yes in the conclusion (`k12_game_sitsVY`, SitsYes.lean), at the piece's own errors. -/
theorem game_piece_sitsVY_le (P S Cl' : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (Fr : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ)
    (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT) (e : ℕ) (εt : Err (uLT (ckP .two) dt))
    (B : Block S Cl') (hS : Sits B (proximityTestKind guardedProximityTestParts π : Block T12 Unit) enter leave)
    (p : Piece (ckP .two) Fr (P × S) Cl' W) (hb : p.b = held (P := P) B) (h0 : p.back = [])
    (hbase : p.base = base) (hds : p.ds = dB :: dt)
    (hε : ∀ ε₀ : Err (uLT (ckP .two) p.ds),
      HEq ε₀ ((e, εt) : Err (uLT (ckP .two) (dB :: dt))) → Err.le ε₀ p.err)
    (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ)
    (hA : AtPlace Fr π num Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) base dB dt εt)
    (hj : johOk π r = true) (hb1 : H2K.First.batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e) (hpl : LabelsPub π num nl base) :
    p.ior.red.Leads (fun _ => True)
      (fun a b => ((∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
          QN π (NTuple Fr π (nuOf π nl t) (fun s => r s.st) rd) (t, a.2)) ∧
        StepYes Fr.ft (proximityTestKind guardedProximityTestParts π : Block T12 Unit) enter leave a.1.2 b.1.2) ∧
        b.1 = (a.1.1, b.1.2))
      p.err := by
  obtain ⟨pb, pbase, pds, pback, pext, perr⟩ := p
  dsimp only at hb h0 hbase hds hε
  subst hds
  have h := k12_game_sitsVY P S Cl' enter leave Fr W π num Sg.lstJ Sg.flC Sg.flZ Sg.flZ
    (fun s => r s.st) rd base dB dt e εt B hS
    (⟨pb, pbase, dB :: dt, pback, pext, (e, εt)⟩ : Piece (ckP .two) Fr (P × S) Cl' W) hb h0 hbase
    rfl HEq.rfl nl r hA (fun _ => rfl) hj hb1 hle hpl
  exact h.mono_err (hε _ HEq.rfl)

/-- **At the first row's piece, WHATEVER the family of extractors and errors lays there**, if only
its errors are at least "BAT"'s count times the sampler's number and the place's own errors, round
by round (`herr`); and that pair is below 2⁻¹ ^ k. -/
theorem game_at_tile₁VY_le {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
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
    (enter : F.S₁ → Except String T12) (leave : F.S₁ → T12 → Except String F.S₁)
    (pre : List (Block F.S₁ F.Cl)) (B b' : Block F.S₁ F.Cl) (post : List (Block F.S₁ F.Cl))
    (postR : List Fmt.DeclaredRound) (r₀ : Fmt.DeclaredRound)
    (hfl : F.first.blocksInOrder = b₁ :: l₁) (hcut : b₁ :: l₁ = pre ++ B :: b' :: post)
    (hend : (b' :: post).flatMap (·.rounds) = postR ++ [r₀])
    (hS : Sits B (proximityTestKind guardedProximityTestParts π : Block T12 Unit) enter leave)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ k)) (hj : johOk π r = true)
    (hbat : batPriceOk π r k = true) (ho : π.nums.ownMask = false)
    (hlb : ownLabelsFreeB π = true) (rd : ℕ → ℕ)
    (herr : ∀ dB dt, (D.ds₁.drop (pre.flatMap (·.rounds)).length).take
        (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt →
      Err.le (s := uLT (ckP .two) (dB :: dt))
        (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt)
        (rest₁ (0 + pre.length) (dB :: dt)).err) :
    ∃ p dB dt,
      ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁)[pre.length]? =
        some p ∧
      p.b = held B ∧
      p.base = 0 + nTrees (D.ds₁.take (pre.flatMap (·.rounds)).length) ∧ p.ds = dB :: dt ∧
      HEq p.err (rest₁ (0 + pre.length) (dB :: dt)).err ∧
      Err.Below (s := uLT (ckP .two) (dB :: dt))
        (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) ((2 : ℝ≥0∞)⁻¹ ^ k) ∧
      p.ior.red.Leads (fun _ => True)
        (fun a b => ((∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
            QN π (NTuple (frameAt D (allOf D) D.key₁ 0) π
              (nuOf π (nlAt π (numAt F.t₁ F.t₂ 0 (.own 0))) t) (fun s => r s.st) rd) (t, a.2)) ∧
          StepYes (frameAt D (allOf D) D.key₁ 0).ft (proximityTestKind guardedProximityTestParts π : Block T12 Unit) enter leave
            a.1.2 b.1.2) ∧
          b.1 = (a.1.1, b.1.2))
        p.err := by
  obtain ⟨p, dB, dt, hrow, hpb, hp0, hpbase, hpds, hlist, hperr, hb0, hAt, hsm⟩ :=
    tile_piece₁ F file D h b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd π r k pre B b' post postR r₀
      hfl hcut hend hS.rounds hfree hp hC hj hbat ho
  have hpe : HEq p.err (rest₁ (0 + pre.length) (dB :: dt)).err :=
    hperr _ fun ds' e => by
      subst e
      exact HEq.rfl
  refine ⟨p, dB, dt, hrow, hpb, hpbase, hpds, hpe, hsm, ?_⟩
  exact game_piece_sitsVY_le F.XiPub F.S₁ F.Cl enter leave _ W π (numAt F.t₁ F.t₂ 0) rd
    (0 + nTrees (D.ds₁.take (pre.flatMap (·.rounds)).length)) dB dt _ (errJ π r dt) B hS p hpb hp0
    hpbase hpds (fun ε₀ h0 => le_of_heq hpds ε₀ p.err _ _ h0 hpe (herr dB dt hlist)) _ r hAt hj
    (H2K.Made.batOneOk_of_planOk guardedProximityTestParts π hp) (Nat.le_refl _)
    (by rw [hb0]; exact labelsPub_own π 0 F.t₁ F.t₂ hlb)

/-- **WHERE EVERY PIECE's ERRORS ARE THE CAP** (`AtCap`, Johnson/Desc/Sound/BoundsAtCap.lean): no
premise on the errors is left: the game stands at the piece's own errors, the cap. -/
theorem game_at_tile₁VY_cap {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
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
    (d wEnd : W) (π : P12) (r : Fmt.M1.Stage → ℕ)
    (enter : F.S₁ → Except String T12) (leave : F.S₁ → T12 → Except String F.S₁)
    (pre : List (Block F.S₁ F.Cl)) (B b' : Block F.S₁ F.Cl) (post : List (Block F.S₁ F.Cl))
    (postR : List Fmt.DeclaredRound) (r₀ : Fmt.DeclaredRound)
    (hfl : F.first.blocksInOrder = b₁ :: l₁) (hcut : b₁ :: l₁ = pre ++ B :: b' :: post)
    (hend : (b' :: post).flatMap (·.rounds) = postR ++ [r₀])
    (hS : Sits B (proximityTestKind guardedProximityTestParts π : Block T12 Unit) enter leave)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ 128)) (hj : johOk π r = true)
    (hbat : batPriceOk π r 128 = true) (ho : π.nums.ownMask = false)
    (hlb : ownLabelsFreeB π = true) (rd : ℕ → ℕ) (hcap : AtCap rest₁) :
    ∃ p,
      ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₁ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₁)[pre.length]? =
        some p ∧
      p.b = held B ∧
      p.base = 0 + nTrees (D.ds₁.take (pre.flatMap (·.rounds)).length) ∧
      p.ior.red.Leads (fun _ => True)
        (fun a b => ((∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
            QN π (NTuple (frameAt D (allOf D) D.key₁ 0) π
              (nuOf π (nlAt π (numAt F.t₁ F.t₂ 0 (.own 0))) t) (fun s => r s.st) rd) (t, a.2)) ∧
          StepYes (frameAt D (allOf D) D.key₁ 0).ft (proximityTestKind guardedProximityTestParts π : Block T12 Unit) enter leave
            a.1.2 b.1.2) ∧
          b.1 = (a.1.1, b.1.2))
        p.err := by
  obtain ⟨p, dB, dt, hrow, hpb, hpbase, _, _, _, hK⟩ :=
    game_at_tile₁VY_le F file D h b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd π r 128 enter leave
      pre B b' post postR r₀ hfl hcut hend hS hfree hp hC hj hbat ho hlb rd fun dB dt hc => by
        obtain ⟨dB', dt', hc', _, hsm⟩ := atPlace_tile₁ F file D h D.key₁ 0 π r 128 pre B
          (b' :: post) postR r₀ (hfl.trans hcut) hend hS.rounds hfree hp hC hj hbat ho
        obtain ⟨rfl, rfl⟩ := List.cons.inj (hc.symm.trans hc')
        rw [hcap (0 + pre.length) (dB :: dt)]
        exact Err.le_cap_of_below_inv 128 _ hsm
  exact ⟨p, hrow, hpb, hpbase, hK⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.atPlace_tile₁
#print axioms VerifiableInference.Desc.K12.Coin.tile_piece₁
#print axioms VerifiableInference.Desc.K12.Coin.tile_end₁
#print axioms VerifiableInference.Desc.K12.Coin.game_at_tile₁V
#print axioms VerifiableInference.Desc.K12.Coin.game_piece_sitsVY_le
#print axioms VerifiableInference.Desc.K12.Coin.game_at_tile₁VY_le
#print axioms VerifiableInference.Desc.K12.Coin.game_at_tile₁VY_cap
