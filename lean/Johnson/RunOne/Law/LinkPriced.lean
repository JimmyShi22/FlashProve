-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/LinkPriced.lean: It stands on Johnson/RunOne/Sound/.
THE SIX SEATS OF EACH LOOKUP'S LINK, WITH THEIR ERRORS PRICED:
fk_link_low (LinkAtLow.lean) at the bound 2⁻¹ ^ target, where the piece of the kind's block has the
typed lookup's errors along the maps. Its two premises on errors fall. The five other pieces of a
link have no round, so no error. The typed lookup's errors along the maps are below the planner's
target (lam_below, Johnson/Desc/First/Look/KeyLaw/BelowAt.lean), where the planner's own rounds for
the lookup hold: LookHeld (same file), a condition on public numbers.

Main names:
  declared_of_block, declared_at_cut: at the maker's pieces of any description that seals last and
    whose data are made, the stretch of a block of the kind "lookup" has the planner's entries,
    round by round.
  tiled_owed, quiet_below: in a tiled row every piece is owed just its stretch; a piece whose block
    declares no round has no error. link_quiet: so five of a link's six.
  fk_k3_below: the typed lookup's errors along the maps, at the piece of the kind's block.
  fk_link_priced: THE SIX SEATS OF LOOKUP NUMBER l.

Object: the six blocks at the places 2 + (6 · l + j), j < 6, of (FK X N P).first.blocksInOrder
(Johnson/RunOne/Sound/KeyAtFK.lean), which are lookupLink's (fk_link_at, fk_K3_at, fk_layer_at:
Johnson/RunOne/Sound/KeyMapAtFK.lean).
User: fk_chain₁_priced (Chain1Priced.lean), at every lookup of the plan; fk_link_own (OwnRest.lean).
Letters: X, N, P: the description's source and the two records of places · the data D and the three
flat lists' heads and tails · the three chains' rests · the rows A0, rs · the decoder, its
condition, what else rides (dec, cond, Oth: they read the riding part with the description's public
part of the instance beside it: TK (H₁ X N P)), the words, the matrix (wd, mx) · the two ledgers
lo, lk in front of the first link · Ex, what else the promise keeps · idxN, the index-mask message's
number · st0.

Limits. Those of LinkAtLow.lean's fk_link_low, but for the two premises on errors, in whose place
stand: LookHeld at the lookup's face · the piece of the kind's block has the typed lookup's errors
along the maps (a choice of whoever names the rests). That a key's plan gives LookHeld is not shown
here (in scope, at the key file's own description: AtFreeCfg.lean, ReadAtO.lean). The
target counts a round's proof of work. A bound round by round, no sum.

-/
import Johnson.RunOne.Law.LinkAtLow
import Johnson.Desc.First.Look.KeyLaw.BelowAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace Johnson.RunOne.Law.LinkPriced
open Iop OnBytes OnBytes.Slice OnBytes.Params OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open _root_.Run.PQ (CK)
open OnBytes.Flat.Held (sideR)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (FirstState Claim Source layerOrder lookupSeat lookupPlace)
open Johnson.RunOne.Sound (FK H₁ fk_link_at fk_K3_at fk_layer_at fk_sealLast stretchAtPieces)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.PromKeyD
open Johnson.RunOne.Law.SeatsAtFK
open Johnson.RunOne.Law.LinkSeats
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtFK
open Johnson.RunOne.Law.LinkAtCut
open Johnson.RunOne.Law.LinkAtLow

/-! ## The stretch has the planner's entries -/

/-- At the kind's block. -/
theorem declared_of_block {S Cl : Type} (σ : SeatG S Cl) (before : List (ℕ × ℕ)) (bits : ℕ)
    (guests : List (VerifiableInference.Desc.First.Look.Guest S Cl)) (p : PG)
    (num : Fmt.TreeSource → ℕ) (ds : List RDT) (hok : (lookupKind σ before bits guests p).planOk = true)
    (hl : ds.length = (lookupKind σ before bits guests p).rounds.length)
    (h : Along (RoundIs num) (lookupKind σ before bits guests p).rounds ds) :
    p.face.ok = true ∧ ∃ es, p.entries = some es ∧ List.Forall₂ AsDeclared ds es := by
  have hok' : p.planOk before bits guests = true := hok
  unfold PG.planOk at hok'
  simp only [Bool.and_eq_true] at hok'
  obtain ⟨⟨⟨⟨k1, k2⟩, -⟩, -⟩, -⟩ := hok'
  obtain ⟨es, he⟩ := Option.isSome_iff_exists.1 k2
  have hr : (lookupKind σ before bits guests p).rounds =
      es.map fun e => ({ entry := e } : Fmt.DeclaredRound) := by
    show (p.entries.getD []).map _ = _
    rw [he]
    rfl
  rw [hr] at h hl
  rw [List.length_map] at hl
  exact ⟨k1, es, he, declared_of_along num es ds hl h⟩

/-- In a tiled row every piece is owed just its stretch. -/
theorem tiled_owed {C : CK} {F : Frame} {S Cl W : Type} : ∀ (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (i : ℕ) (q : Piece C F S Cl W), Tiled p l →
    (p :: l)[i]? = some q → q.Owed
  | p, [], 0, q, h, hq => by
    have h' : p.Owed ∧ p.Listed := h
    obtain rfl : p = q := Option.some.inj hq
    exact h'.1
  | _, [], _ + 1, _, _, hq => by cases hq
  | p, r :: l, 0, q, h, hq => by
    have h' : p.Owed ∧ p.Listed ∧ p.back = [] ∧ r.base = p.base + p.trees ∧ Tiled r l := h
    obtain rfl : p = q := Option.some.inj hq
    exact h'.1
  | p, r :: l, i + 1, q, h, hq => by
    have h' : p.Owed ∧ p.Listed ∧ p.back = [] ∧ r.base = p.base + p.trees ∧ Tiled r l := h
    exact tiled_owed r l i q h'.2.2.2.2 hq

/-- A piece that is owed just its stretch and whose block declares no round has no error. -/
theorem quiet_below {C : CK} {F : Frame} {S Cl W : Type} (p : Piece C F S Cl W) (h : p.Owed)
    (hr : p.b.rounds = []) (ε : ℝ≥0∞) : Err.Below p.err ε := by
  have h1 := h.1
  rw [hr] at h1
  have h2 : p.ds = [] := List.length_eq_zero_iff.1 (Nat.eq_zero_of_add_eq_zero_right h1)
  obtain ⟨b, base, ds, back, ext, err⟩ := p
  dsimp only at h2
  subst h2
  exact trivial

/-- **At the maker's pieces of any description that seals last and whose data are made**: the
stretch of a block of the kind "lookup" that passes its own test on the plan and is not the first
chain's last block. -/
theorem declared_at_cut {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (hD : F.data file = .ok D) (hs : F.sealLast = true)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (h₁ : F.first.blocksInOrder = b₁ :: l₁) (h₂ : F.shared.blocksInOrder = b₂ :: l₂) (h₃ : F.second.blocksInOrder = b₃ :: l₃)
    (rest₁) (rest₂) (rest₃) (d wEnd : W) (i : ℕ) (σ : SeatG F.S₁ F.Cl) (before : List (ℕ × ℕ))
    (bits : ℕ) (guests : List (VerifiableInference.Desc.First.Look.Guest F.S₁ F.Cl)) (pg : PG)
    (hb : F.first.blocksInOrder[i]? = some (lookupKind σ before bits guests pg))
    (hnext : i + 1 < F.first.blocksInOrder.length)
    (hok : (lookupKind σ before bits guests pg).planOk = true) :
    let T := piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd
    ∀ p, (T.p₁ :: T.l₁)[i]? = some p →
      pg.face.ok = true ∧ ∃ es, pg.entries = some es ∧ List.Forall₂ AsDeclared p.ds es := by
  intro T p hp
  obtain ⟨hO, hF, -⟩ := paidAtDesc Xi W F file D hD hs (ckP .two) b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃ rest₁
    rest₂ rest₃ d wEnd
  have hlen : (T.p₁ :: T.l₁).length = F.first.blocksInOrder.length := by
    have e := congrArg List.length hO.b₁
    simpa using e
  have hi : i < T.l₁.length := by
    have e : (T.p₁ :: T.l₁).length = T.l₁.length + 1 := rfl
    omega
  obtain ⟨hw, hbk⟩ := tiled_at T.p₁ T.l₁ i p hF.tiled₁ hp hi
  have hpb : p.b = liftP _ (below (lookupKind σ before bits guests pg)) :=
    block_at (T.p₁ :: T.l₁) F.first.blocksInOrder hO.b₁ i p _ hp hb
  have hal := (stretchAtPieces F file D hD (ckP .two) b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃ rest₁ rest₂ rest₃
    d wEnd).1 p (List.mem_of_getElem? hp)
  have hw1 := hw.1
  rw [hpb] at hal hw1
  rw [hbk] at hw1
  exact declared_of_block σ before bits guests pg _ p.ds hok hw1 hal

/-- Of a link's six blocks all but the kind's own declare no round. -/
theorem link_quiet (one : OneTime) (set : Setting) (i : ℕ) (x : VerifiableInference.Desc.Key.Lookup)
    : ∀ j, j < 6 → j ≠ 2 →
    ∀ c, (VerifiableInference.Desc.Key.lookupLink one set i x).blocksInOrder[j]? = some c → c.rounds = []
  | 0, _, _, c, hc => by
    obtain rfl := Option.some.inj hc
    rfl
  | 1, _, _, c, hc => by
    obtain rfl := Option.some.inj hc
    rfl
  | 2, _, h, _, _ => absurd rfl h
  | 3, _, _, c, hc => by
    obtain rfl := Option.some.inj hc
    rfl
  | 4, _, _, c, hc => by
    obtain rfl := Option.some.inj hc
    rfl
  | 5, _, _, c, hc => by
    obtain rfl := Option.some.inj hc
    rfl
  | _ + 6, h, _, _, _ => absurd h (by omega)

/-! ## The six seats -/

variable (X : Source) (N : H2U.PlaceNums) (P : VerifiableInference.Desc.Key.LaterPlaces)

local notation "one" => X.Y.k.oneTime
local notation "idM" => X.Y.k.oneTime.ranges.messageId
local notation "mM" => Wf.matrixOf X.Y.k.oneTime.lin
local notation "nL" => X.Y.k.oneTime.ranges.lookups.length

variable {W : Type} {idxN : ℕ} {M Wp : Type} {wd : M → Means.Words GE} {mx : M → ℕ → ℕ → GE}
  {lo lk : Ledger} {Ex : FirstState → Prop}

set_option maxHeartbeats 1600000 in
/-- **The typed lookup's errors along the maps, at the piece of the kind's block, are below the
target.** -/
theorem fk_k3_below (hp : (FK X N P).planOk = true) (file : String) (D : WholeD)
    (hD : (FK X N P).data file = .ok D)
    (b₁ : Block (FK X N P).S₁ (FK X N P).Cl) (l₁ : List (Block (FK X N P).S₁ (FK X N P).Cl))
    (b₂ : Block (FK X N P).S₂ (FK X N P).Cl) (l₂ : List (Block (FK X N P).S₂ (FK X N P).Cl))
    (b₃ : Block (FK X N P).S₃ (FK X N P).Cl) (l₃ : List (Block (FK X N P).S₃ (FK X N P).Cl))
    (h₁ : (FK X N P).first.blocksInOrder = b₁ :: l₁) (h₂ : (FK X N P).shared.blocksInOrder = b₂ :: l₂)
    (h₃ : (FK X N P).second.blocksInOrder = b₃ :: l₃) (rest₁) (rest₂) (rest₃) (d wEnd : W)
    {dec : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Option M}
    {cond : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Prop} {Oth : TK (H₁ X N P) → M ×
        Wp → Prop}
    (l : ℕ) (hl : l < nL)
    (hL : LookHeld X.set (faceOfLkp (Wf.lookupOf idM mM (Lof one l)))) (st0 : TK (H₁ X N P)) :
    let T := piecesAt (ckP .two) (FK X N P) D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd
    ∀ p, (T.p₁ :: T.l₁)[2 + 6 * l + 2]? = some p →
      ∀ hds : List.Forall₂ MadeOf p.ds (shapeG (faceOfLkp (Wf.lookupOf idM mM (Lof one l)))),
        Err.Below ((mapsAt (Fr := frameAt D (allOf D) D.key₁ 0) one idM mM (Lof one)
          (handed (cntO idM mM (Lof one)) lo) (handed (cntK idM mM (Lof one)) lk) idxN l
          (Lk6.adm_of_tests idM mM _ (tests_at (fk_admitted X N P hp) hl).2.1
            (tests_at (fk_admitted X N P hp) hl).2.2)
          (d_le (tests_at (fk_admitted X N P hp) hl).2.1) st0 p.ds hds).err
          (kAt one idM mM (Lof one) (handed (cntO idM mM (Lof one)) lo)
            (handed (cntK idM mM (Lof one)) lk) idxN wd mx dec cond nL l Wp Oth).err)
          ((2 : ℝ≥0∞)⁻¹ ^ X.set.target) := by
  intro T p hq hds
  have hs := fk_sealLast X N P
  have hx := look_at one l hl
  have h2 := fk_K3_at X N P l _ hx
  have h3 := fk_layer_at X N P l _ hx
  have hnext : 2 + (6 * l + 2) + 1 < (FK X N P).first.blocksInOrder.length := by
    have e : 2 + (6 * l + 2) + 1 = 2 + (6 * l + 3) := by omega
    rw [e]
    exact (List.getElem?_eq_some_iff.1 h3).1
  have hq' : (T.p₁ :: T.l₁)[2 + (6 * l + 2)]? = some p := by
    rw [← Nat.add_assoc]
    exact hq
  obtain ⟨hok, es, he, hd⟩ := declared_at_cut (FK X N P) file D hD hs b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃
    rest₁ rest₂ rest₃ d wEnd (2 + (6 * l + 2)) lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace X.set l
        _) h2
    hnext (fk_block_ok X N P hp _ _ h2) p hq'
  have he' : entriesG X.set .once (faceOfLkp (Wf.lookupOf idM mM (Lof one l))) = some es := he
  unfold entriesG at he'
  obtain ⟨c1, c2, c3⟩ := hL
  cases hf : finish X.set .once (planLookup (faceOfLkp (Wf.lookupOf idM mM (Lof one l))).size) with
  | error e =>
    rw [hf] at he'
    cases he'
  | ok Q =>
    rw [hf] at he'
    obtain rfl : Q.rounds.map (·.entry) = es := Option.some.inj he'
    obtain ⟨s1, s2⟩ := c3 Q hf
    have hadm := Lk6.adm_of_tests idM mM _ (tests_at (fk_admitted X N P hp) hl).2.1
      (tests_at (fk_admitted X N P hp) hl).2.2
    exact lam_below _ st0 _ _ _ (faceIsK (TK (H₁ X N P)) idM mM (Lof one l) _ st0 hadm
      (d_le (tests_at (fk_admitted X N P hp) hl).2.1)) hok hadm X.set c1 c2 Q hf s1 s2 p.ds hd _

/-- **THE SIX SEATS OF THE LINK OF LOOKUP NUMBER l, WITH THEIR ERRORS PRICED.** -/
theorem fk_link_priced (hp : (FK X N P).planOk = true) (file : String) (D : WholeD)
    (hD : (FK X N P).data file = .ok D)
    (b₁ : Block (FK X N P).S₁ (FK X N P).Cl) (l₁ : List (Block (FK X N P).S₁ (FK X N P).Cl))
    (b₂ : Block (FK X N P).S₂ (FK X N P).Cl) (l₂ : List (Block (FK X N P).S₂ (FK X N P).Cl))
    (b₃ : Block (FK X N P).S₃ (FK X N P).Cl) (l₃ : List (Block (FK X N P).S₃ (FK X N P).Cl))
    (h₁ : (FK X N P).first.blocksInOrder = b₁ :: l₁) (h₂ : (FK X N P).shared.blocksInOrder = b₂ :: l₂)
    (h₃ : (FK X N P).second.blocksInOrder = b₃ :: l₃) (rest₁) (rest₂) (rest₃) (d wEnd : W)
    {dec : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Option M}
    {cond : TK (H₁ X N P) × (frameAt D (allOf D) D.key₁ 0).E.Str → Prop} {Oth : TK (H₁ X N P) → M ×
        Wp → Prop}
    (l : ℕ) (hl : l < nL)
    (A0 : JointRow (H₁ X N P × FirstState) (frameAt D (allOf D) D.key₁ 0))
    (rs : List (JointRow (H₁ X N P × FirstState) (frameAt D (allOf D) D.key₁ 0))) (hidx : idxN ≠ 1)
    (hE : Kept one idM mM (Lof one) Ex)
    (hr : ∀ j ≤ 6, keyRowAt A0 rs (2 + 6 * l + j) =
      upF fun p₀ => (rows7 p₀ one X.set idM mM (Lof one) (handed (cntO idM mM (Lof one)) lo)
        (handed (cntK idM mM (Lof one)) lk) idxN wd mx dec cond nL
        (PromL one idM mM (Lof one) idxN nL lo lk Ex) l Wp Oth j))
    (hB : Blind dec cond Oth) (st0 : TK (H₁ X N P)) (hw : Nonempty (M × Wp))
    (hL : LookHeld X.set (faceOfLkp (Wf.lookupOf idM mM (Lof one l)))) :
    let T := piecesAt (ckP .two) (FK X N P) D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd
    (∀ p, (T.p₁ :: T.l₁)[2]? = some p → LowDec dec cond p.base) →
    (∀ p, (T.p₁ :: T.l₁)[2 + 6 * l + 2]? = some p →
      ∀ hds : List.Forall₂ MadeOf p.ds (shapeG (faceOfLkp (Wf.lookupOf idM mM (Lof one l)))),
        p.err = (mapsAt (Fr := frameAt D (allOf D) D.key₁ 0) one idM mM (Lof one)
          (handed (cntO idM mM (Lof one)) lo) (handed (cntK idM mM (Lof one)) lk) idxN l
          (Lk6.adm_of_tests idM mM _ (tests_at (fk_admitted X N P hp) hl).2.1
            (tests_at (fk_admitted X N P hp) hl).2.2)
          (d_le (tests_at (fk_admitted X N P hp) hl).2.1) st0 p.ds hds).err
          (kAt one idM mM (Lof one) (handed (cntO idM mM (Lof one)) lo)
            (handed (cntK idM mM (Lof one)) lk) idxN wd mx dec cond nL l Wp Oth).err) →
    ∀ j < 6, SeatGood ((2 : ℝ≥0∞)⁻¹ ^ X.set.target) A0 (T.p₁ :: T.l₁) rs (2 + (6 * l + j)) := by
  intro T hlow hown
  have hs := fk_sealLast X N P
  obtain ⟨hO, hF, -⟩ := paidAtDesc _ W (FK X N P) file D hD hs (ckP .two) b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂
    h₃ rest₁ rest₂ rest₃ d wEnd
  have hx := look_at one l hl
  have h2 := fk_K3_at X N P l _ hx
  have h3 := fk_layer_at X N P l _ hx
  have hnext : 2 + (6 * l + 2) + 1 < (FK X N P).first.blocksInOrder.length := by
    have e : 2 + (6 * l + 2) + 1 = 2 + (6 * l + 3) := by omega
    rw [e]
    exact (List.getElem?_eq_some_iff.1 h3).1
  have hmade := made_at_cut (FK X N P) file D hD hs b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃ rest₁ rest₂ rest₃
    d wEnd (2 + (6 * l + 2)) lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace X.set l _) h2 hnext
    (fk_block_ok X N P hp _ _ h2) rfl
  refine fk_link_low X N P hp file D hD b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃ rest₁ rest₂ rest₃ d wEnd
    l hl _ A0 rs hidx hE hr hB st0 hw hlow (fun j hj p hq => ?_) fun p hq hds => ?_
  · by_cases e2 : j = 2
    · subst e2
      have hq' : (T.p₁ :: T.l₁)[2 + (6 * l + 2)]? = some p := by
        rw [← Nat.add_assoc]
        exact hq
      rw [hown p hq (hmade p hq').2]
      exact fk_k3_below X N P hp file D hD b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃ rest₁ rest₂ rest₃ d wEnd l
        hl hL st0 p hq (hmade p hq').2
    · have hq' : (T.p₁ :: T.l₁)[2 + (6 * l + j)]? = some p := by
        rw [← Nat.add_assoc]
        exact hq
      have hlt : 2 + (6 * l + j) < (FK X N P).first.blocksInOrder.length := by
        have e : (T.p₁ :: T.l₁).length = (FK X N P).first.blocksInOrder.length := by
          have e0 := congrArg List.length hO.b₁
          simpa using e0
        rw [← e]
        exact (List.getElem?_eq_some_iff.1 hq').1
      have hc : (FK X N P).first.blocksInOrder[2 + (6 * l + j)]? =
          some ((FK X N P).first.blocksInOrder[2 + (6 * l + j)]'hlt) := List.getElem?_eq_getElem hlt
      have hb := block_at (T.p₁ :: T.l₁) (FK X N P).first.blocksInOrder hO.b₁ _ p _ hq' hc
      refine quiet_below p (tiled_owed T.p₁ T.l₁ _ p hF.tiled₁ hq') ?_ _
      rw [hb]
      show ((FK X N P).first.blocksInOrder[2 + (6 * l + j)]'hlt).rounds = []
      exact link_quiet one X.set l _ j hj e2 _
        ((fk_link_at X N P l j hj _ hx).symm.trans hc)
  · rw [hown p hq hds]
    exact Err.le_refl _

end Johnson.RunOne.Law.LinkPriced

#print axioms Johnson.RunOne.Law.LinkPriced.declared_of_block
#print axioms Johnson.RunOne.Law.LinkPriced.tiled_owed
#print axioms Johnson.RunOne.Law.LinkPriced.quiet_below
#print axioms Johnson.RunOne.Law.LinkPriced.declared_at_cut
#print axioms Johnson.RunOne.Law.LinkPriced.link_quiet
#print axioms Johnson.RunOne.Law.LinkPriced.fk_k3_below
#print axioms Johnson.RunOne.Law.LinkPriced.fk_link_priced
