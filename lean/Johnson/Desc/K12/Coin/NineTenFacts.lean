-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Coin.LawAtTileOwn
import Johnson.Desc.K12.Coin.GameAt
import Johnson.Desc.K12.Coin.FirstBook
import Johnson.Desc.K12.Law.BeforeMore
import Johnson.Desc.K12.Law.FileWord
/-
Johnson/Desc/K12/Coin/NineTenFacts.lean: WHAT A LEDGER OF A SHARED CHAIN ASKS OF THE PLAN AND OF THE
PIECE AT A PROXIMITY TEST's BLOCK, AS ONE LEAN STRUCTURE FOR EACH ARM, AND WHO PAYS IT AT A
DESCRIPTION's OWN PIECE. GENERAL IN THE DESCRIPTION: it serves the proof file's and the key file's
seats alike. The askers: nine_paid | ten_paid (Johnson/Desc/Sound/NineAt.lean |
TenAt.lean): their binders h0 · hds · hb · hA · hj · hb1 · ho · hP · n2 · n3 · hft (he | ha1 | hp |
hnum are fields of hA): by a reading of these two files; and, by report
alone, nine_at_K | ten_at_K (K14/Law/LedgerNineTen.lean) with the same binders. None of their
files is imported: THE FIT IS BY READING UNTIL THE CALL IS TYPED.
FACTS ON VALUES: IT PAYS NO LAW. NO SOUNDNESS AND NO LEVEL
IS CLAIMED. NOTHING ON HIDING. NO NEW MATHEMATICS. (The general half of an earlier
version of Johnson/Loose/H2K12/NineTenAtLaid.lean, to the letter.)
  ownLabelsB_of_free   the test on the labels with «n < free» gives the test without.
  pins_at_tile₂        general in the arm: F.planOk · the shared chain's flat list cut at B · B.before =
      π.before · B's rounds are the block's · free = the roots declared in front ⇒ n2 ∧ n3 at F.t₁ +
      free: n3 by n3_numAt (Johnson/Desc/K12/Law/BeforeMore.lean), off the plan's test
      beforeOk.
  NineFacts | TenFacts twelve fields: back · ds · alike · place (AtPlace | AtPlaceOwn at the Johnson
      letters, the radii r, the place's own errors errJ π r dt) · small (the whole own entry is below
      2⁻¹ ^ 128 round by round) · joh · batOne · labels · own · n2 · n3 · ft.
  nine_facts_tile₂ | ten_facts_tile₂   at piecesAt's second row's piece number pre.length.
WHAT IS NOT HERE: herr (the askers' ε is a free letter, met by choice: not x.err) · hr | hle (rfl |
le_refl at these letters) · ten_paid's hPay · h1 · hlog (pays_at_tile, LawAtTileOwn.lean, off
TenFacts.place and .small) · every premise on the table, the seam, the members.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's
end.
-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes.Maker (RDT WholeD uLT)
open _root_.Run (ckP bsRound)
open _root_.Iop (Err)
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.Pub (johOk batV0 batPriceOk)
open Johnson.G.OfPlan (rootsOf)
open scoped ENNReal

theorem ownLabelsB_of_free (π : P12) (h : Coin.ownLabelsFreeB π = true) :
    Coin.ownLabelsB π = true := by
  unfold Coin.ownLabelsFreeB at h
  unfold Coin.ownLabelsB
  cases hs : π.nums.stages with
  | nil =>
    rw [hs] at h
    simp at h
  | cons a rest =>
    rw [hs] at h
    simp only [List.all_eq_true] at h ⊢
    rintro ⟨sh, src⟩ ho
    have h1 := h ⟨sh, src⟩ ho
    cases src with
    | own n =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1 ⊢
      exact h1.1
    | taken c n => exact h1

/-- The two pins on the numbering, off the plan. -/
theorem pins_at_tile₂ {Xi : Type} (F : FileDescription Xi) (hF : F.planOk = true) (π : P12)
    (pre : List (Block F.S₂ F.Cl)) (B : Block F.S₂ F.Cl) (post : List (Block F.S₂ F.Cl))
    (hfl : F.shared.blocksInOrder = pre ++ B :: post) (hbef : B.before = π.before)
    (hB : B.rounds = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds))) :
    (∀ n, n < π.nums.free → VerifiableInference.Desc.numAt F.t₁ F.t₂ 1 (.own n) < F.t₁ + π.nums.free) ∧
      ∀ c' n, (c' + 1, n) ∈ π.before → VerifiableInference.Desc.numAt F.t₁ F.t₂ 1 (.taken c' n) < F.t₁ + π.nums.free := by
  refine ⟨fun n hn => ?_, fun c' n hm => ?_⟩
  · show F.t₁ + n < F.t₁ + π.nums.free
    omega
  · have hb := (H2K.Made.plan_gives F hF).1.2.1
    rw [hfl] at hb
    have hDs : VerifiableInference.Desc.chainOf F.roundsDeclaredByBlocks (1 + 1) = pre.flatMap (·.rounds) ++
        ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ post.flatMap (·.rounds)) := by
      show F.shared.blocksInOrder.flatMap (·.rounds) = _
      rw [hfl, List.flatMap_append, List.flatMap_cons, hB]
    have hlen : (pre.flatMap (·.rounds)).length = 0 + VerifiableInference.Desc.roundsIn pre := by
      rw [List.length_flatMap, Nat.zero_add]
      rfl
    have h3 := H2K.Made.n3_numAt π _ (VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts π hp) F.roundsDeclaredByBlocks _ 1
      0 pre B post hbef hB hb _ _ hDs hlen (by omega) c' n hm
    rw [hfree]
    exact h3

/-- **What the ledger's block 9 asks of the plan and the piece.** K: the seat as the chain's text lays it. -/
structure NineFacts {P₁ S Cl W : Type} (Fr : Frame) (π : P12) (r : Fmt.M1.Stage → ℕ) (t₁ t₂ : ℕ)
    (K : Block S Unit) (x : Piece (ckP .two) Fr (P₁ × S) Cl W) (dB : RDT) (dt : List RDT) :
    Prop where
  back : x.back = []
  ds : x.ds = dB :: dt
  alike : Coin.Alike (held (P := P₁) K) x.b
  place : Coin.AtPlace Fr π (VerifiableInference.Desc.numAt t₁ t₂ 1) OnBytes.Slice.Sg.lstJ OnBytes.Slice.Sg.flC OnBytes.Slice.Sg.flZ
    OnBytes.Slice.Sg.flZ (fun s => r s.st) x.base dB dt
    (Coin.errJ π r dt)
  small : Err.Below (s := uLT (ckP .two) (dB :: dt))
    (batV0 π r * (bsRound .two dB.entry dB.kind).w, Coin.errJ π r dt) ((2 : ℝ≥0∞)⁻¹ ^ 128)
  joh : johOk π r = true
  batOne : H2K.First.batOneOk π = true
  labels : Coin.ownLabelsB π = true
  own : π.nums.ownMask = false
  n2 : ∀ n, n < π.nums.free → VerifiableInference.Desc.numAt t₁ t₂ 1 (.own n) < x.base
  n3 : ∀ c' n, (c' + 1, n) ∈ π.before → VerifiableInference.Desc.numAt t₁ t₂ 1 (.taken c' n) < x.base
  ft : π.nums.firstTree = 0

/-- **What the ledger's block 10 asks of the plan and the piece.** -/
structure TenFacts {P₁ S Cl W : Type} (Fr : Frame) (π : P12) (r : Fmt.M1.Stage → ℕ) (t₁ t₂ : ℕ)
    (K : Block S Unit) (x : Piece (ckP .two) Fr (P₁ × S) Cl W) (dB : RDT) (dt : List RDT) :
    Prop where
  back : x.back = []
  ds : x.ds = dB :: dt
  alike : Coin.Alike (held (P := P₁) K) x.b
  place : Coin.AtPlaceOwn Fr π (VerifiableInference.Desc.numAt t₁ t₂ 1) OnBytes.Slice.Sg.lstJ OnBytes.Slice.Sg.flC OnBytes.Slice.Sg.flZ
    OnBytes.Slice.Sg.flZ (fun s => r s.st) x.base dB dt
    (Coin.errJ π r dt)
  small : Err.Below (s := uLT (ckP .two) (dB :: dt))
    (batV0 π r * (bsRound .two dB.entry dB.kind).w, Coin.errJ π r dt) ((2 : ℝ≥0∞)⁻¹ ^ 128)
  joh : johOk π r = true
  batOne : H2K.First.batOneOk π = true
  labels : Coin.ownLabelsB π = true
  own : π.nums.ownMask = true
  n2 : ∀ n, n < π.nums.free → VerifiableInference.Desc.numAt t₁ t₂ 1 (.own n) < x.base
  n3 : ∀ c' n, (c' + 1, n) ∈ π.before → VerifiableInference.Desc.numAt t₁ t₂ 1 (.taken c' n) < x.base
  ft : π.nums.firstTree = 0


theorem nine_facts_tile₂ {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (hF : F.planOk = true)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (Sound.allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (Sound.allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (Sound.allOf D) D.key₃ F.lastChainFirstTreeNumber)
        ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (π : P12) (r : Fmt.M1.Stage → ℕ)
    (enter : F.S₂ → Except String T12) (leave : F.S₂ → T12 → Except String F.S₂)
    (pre : List (Block F.S₂ F.Cl)) (B b' : Block F.S₂ F.Cl) (post : List (Block F.S₂ F.Cl))
    (hfl : F.shared.blocksInOrder = b₂ :: l₂) (hcut : b₂ :: l₂ = pre ++ B :: b' :: post)
    (hal : Coin.Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) B)
    (hbef : B.before = π.before)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : Coin.ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ 128)) (hj : johOk π r = true)
    (hbat : batPriceOk π r 128 = true) (ho : π.nums.ownMask = false)
    (hP : Coin.ownLabelsB π = true) (hft : π.nums.firstTree = 0) :
    ∃ x dB dt,
      ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₂)[pre.length]? =
        some x ∧
      NineFacts (frameAt D (Sound.allOf D) D.key₂ 0) π r F.t₁ F.t₂
        ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) x dB dt := by
  obtain ⟨x, dB, dt, hrow, hxb, hx0, hxbase, hxds, _, _, _, _, hAt, hsm⟩ :=
    Coin.tile_piece₂ F file D h b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd π r 128 pre B b' post hfl
      hcut hal.rounds hfree hp hC hj hbat ho
  have hb : x.base = F.t₁ + π.nums.free := by
    have h0 := hAt.numOwn 0
    rw [Nat.add_zero, Nat.add_zero] at h0
    rw [hxbase, ← h0]
    rfl
  obtain ⟨p2, p3⟩ := pins_at_tile₂ F hF π pre B (b' :: post) (hfl.trans hcut) hbef hal.rounds hp hfree
  refine ⟨x, dB, dt, hrow, hx0, hxds, ?_, ?_, hsm, hj,
    H2K.Made.batOneOk_of_planOk guardedProximityTestParts π hp, hP, ho, ?_, ?_, hft⟩
  · rw [hxb]
    exact hal.held
  · rw [hxbase]
    exact hAt
  · rw [hb]
    exact p2
  · rw [hb]
    exact p3


theorem ten_facts_tile₂ {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (hF : F.planOk = true)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (Sound.allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (Sound.allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (Sound.allOf D) D.key₃ F.lastChainFirstTreeNumber)
        ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (π : P12) (r : Fmt.M1.Stage → ℕ)
    (enter : F.S₂ → Except String T12) (leave : F.S₂ → T12 → Except String F.S₂)
    (pre : List (Block F.S₂ F.Cl)) (B b' : Block F.S₂ F.Cl) (post : List (Block F.S₂ F.Cl))
    (hfl : F.shared.blocksInOrder = b₂ :: l₂) (hcut : b₂ :: l₂ = pre ++ B :: b' :: post)
    (hal : Coin.Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) B)
    (hbef : B.before = π.before)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : Coin.ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ 128)) (hj : johOk π r = true)
    (hbat : batPriceOk π r 128 = true) (ho : π.nums.ownMask = true)
    (hP : Coin.ownLabelsB π = true) (hft : π.nums.firstTree = 0) :
    ∃ x dB dt,
      ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₂)[pre.length]? =
        some x ∧
      TenFacts (frameAt D (Sound.allOf D) D.key₂ 0) π r F.t₁ F.t₂
        ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) x dB dt := by
  obtain ⟨x, dB, dt, hrow, hxb, hx0, hxbase, hxds, _, _, _, _, hAt, hsm⟩ :=
    Coin.tile_pieceOwn₂ F file D h b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd π r 128 pre B b' post hfl
      hcut hal.rounds hfree hp hC hj hbat ho
  have hb : x.base = F.t₁ + π.nums.free := by
    have h0 := hAt.numOwn 0
    rw [Nat.add_zero, Nat.add_zero] at h0
    rw [hxbase, ← h0]
    rfl
  obtain ⟨p2, p3⟩ := pins_at_tile₂ F hF π pre B (b' :: post) (hfl.trans hcut) hbef hal.rounds hp hfree
  refine ⟨x, dB, dt, hrow, hx0, hxds, ?_, ?_, hsm, hj,
    H2K.Made.batOneOk_of_planOk guardedProximityTestParts π hp, hP, ho, ?_, ?_, hft⟩
  · rw [hxb]
    exact hal.held
  · rw [hxbase]
    exact hAt
  · rw [hb]
    exact p2
  · rw [hb]
    exact p3

end H2K.JointK

#print axioms H2K.JointK.ownLabelsB_of_free
#print axioms H2K.JointK.pins_at_tile₂
#print axioms H2K.JointK.nine_facts_tile₂
#print axioms H2K.JointK.ten_facts_tile₂
