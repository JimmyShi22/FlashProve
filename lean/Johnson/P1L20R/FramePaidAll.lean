-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FramePaidAll.lean:
THREE OF THE TEN FIELDS OF FrameOwedAll (FrameKindAtAll.lean) HOLD AT THE HEAD OUTRIGHT;
so the share of the kind "frame" on the first chain, at the seated term, from a shorter structure.

  front_book        the promise in front, at a statement that bears no mark, holds the test bookAt
  size_is_base      general: at numbers that are filled off what the sub-protocols
                    tell: the book holds just as many trees as the piece's base says
  data_atAll        FrameOwedAll.data: LaidAt.atDepth
  numbers_atAll     the constant's numbers are of the make "filled off what the sub-protocols tell"
  still_atAll       FrameOwedAll.still: none_between_at (FrameNoneAt.lean) at these numbers
  size_atAll        FrameOwedAll.size
  FrameOwed7        WHAT IS LEFT: seven fields: low, whole, carryElseLaid, carryElseClear, kn,
                    sealTie, behindTies
  frame_kind_of7    h.Kind L KindName.frame from FrameOwed7

Called from other files: base_is_told (Johnson/Top/H0/Walk/FrameBase.lean), threeCap_fits and
threeCap_ofDesc (Johnson/Goal/Skeleton/TheThree.lean), LaidAt.atDepth (Johnson/P5J/FourAtMg.lean),
At.told_is (Johnson/P5J/LettersAt.lean).

Limits. No field of FrameOwed7 is shown here. A member of the head is proved at storedPublicFiles and zGap alone
(at secondHashFunction; side library AtFullSide/Top/). No soundness statement.

-/
import Johnson.P1L20R.FrameKindAtAll
import Johnson.P1L20R.FrameNoneAt
import Johnson.Top.H0.Walk.FrameBase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers flatPlacesOf bookAt onAt treesTold
  borderOf)
open VerifiableInference.Desc.First.K2Caller (rest)
open Johnson.Desc.First.Walk (layFront)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)
open P5J (AtMgA Free F0T)

/-- The promise in front, at a statement that bears no mark, holds the test on the book. -/
theorem front_book {P W : Type} {N : Numbers} {Mg : Meaning P W} {links : List ModelPart}
    {ps : List Place} {k : ℕ} {a : P × S} {y : Strs} (hu : a.2.failed = none)
    (h : FrontAt N Mg links ps k a y) : bookAt N ps[k]? a.2 = true := by
  unfold FrontAt onAt at h
  rcases h.2 with h' | ⟨h1, -⟩
  · exact absurd hu h'
  · simp only [Bool.and_eq_true] at h1
    exact h1.2

/-- **The book holds just as many trees as the piece's base says**, at numbers that are filled off
what the sub-protocols tell. -/
theorem size_is_base {C : CK} {W Xi P' W' : Type} (G : FileDescription Xi) (file : String) (D : WholeD)
    (hD : G.data file = .ok D) {all : List LeftT} {X₁ X₂ : Type} (R : ThreeAt C D all G X₁ X₂ W)
    (hO : OfDesc G R) (ht : Tiled R.p₁ R.l₁) (hd : rowData R.p₁ R.l₁ = D.ds₁)
    (hsh : ∀ b ∈ G.first.blocksInOrder, b.shaped = true) (h0 : R.p₁.base = 0) {k : ℕ}
    {q : Piece C (frameAt D all D.key₁ R.ft₁) (G.XiPub × G.S₁) G.Cl W}
    (hq : (R.p₁ :: R.l₁)[k]? = some q) (N₀ : Numbers) {Mg : Meaning P' W'} {links : List ModelPart}
    {ps : List Place} (hn : ps.Nodup) (hk : k ≤ ps.length) {a : P' × S} {y : Strs}
    (hu : a.2.failed = none)
    (h : FrontAt (N₀.withTold ps (G.first.blocksInOrder.map fun b => b.oracles.flatten)) Mg links ps k a y) :
    a.2.book.trees.size = q.base := by
  have hb := front_book hu h
  unfold bookAt at hb
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  rw [hb.1.1, base_is_told G file D hD R hO ht hd hsh h0 hq]
  exact congrArg (treesTold _) (borderOf_le hn hk)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **FrameOwedAll.data.** -/
theorem data_atAll (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (F0T OnBytes.secondHashFunction Zp Np cF).data "proof file" = .ok (D.at frS.P.T.a) := by
  rw [P5J.LaidAt.atDepth h.scope h.laid]
  exact h.laid.data

/-- The numbers in front of "filled off what the sub-protocols tell", at the constant. -/
noncomputable abbrev n0All (Zp : ProofFile.Pub) (cF : Chain S Cl) : Numbers :=
  (P5T.numbersOf (P5J.At.pseats Zp)).withRows (P5J.At.shape Zp)
    (VerifiableInference.Desc.First.possAt cF.blocksInOrder P5J.At.links.length) P5J.At.links.length

/-- **The constant's numbers are filled off what the sub-protocols tell.** -/
theorem numbers_atAll (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (dmOf h).N = (n0All Zp cF).withTold (flatPlacesOf linksFull true)
      (cF.blocksInOrder.map fun b => b.oracles.flatten) := by
  show P5J.At.N Zp cF = _
  unfold P5J.At.N
  rw [P5J.At.told_is]
  rfl

/-- **FrameOwedAll.still.** -/
theorem still_atAll (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    NoneBetween (dmOf h).N (flatPlacesOf linksFull true) 0 ∧
      (∀ l, l < 25 → NoneBetween (dmOf h).N (flatPlacesOf linksFull true) (14 * l + 1)) ∧
      ∀ l, l < 25 → NoneBetween (dmOf h).N (flatPlacesOf linksFull true) (clearIx l) := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  rw [numbers_atAll h]
  exact none_between_at h.scope h.reads O (n0All Zp cF) List.flatten rfl

set_option maxHeartbeats 4000000 in
/-- **FrameOwedAll.size**: an equality. -/
theorem size_atAll (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (Kn : ℕ → ProofFile.InstPub × S → Strs → Prop) :
    ∀ k, k ∈ our51 → ∀ q, (h.toAtMg.row L)[k]? = some q → ∀ p s y,
      InAt9 (dmOf h) Kn k (p, s) y → s.book.trees.size = q.base := by
  intro k hk q hq p s y hI
  obtain ⟨pk, hpk, -, -⟩ := idle_at hk
  have hkl : k ≤ (flatPlacesOf linksFull true).length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.1 hpk).1
  have hF := hI.2.1
  rw [numbers_atAll h] at hF
  have Ft := threeCap_fits L.e₁ L.e₂ L.e₃ L.dW L.wEnd (data_atAll h) h.laid.planOk q₁ q₂ q₃
  exact size_is_base (F0T OnBytes.secondHashFunction Zp Np cF) "proof file" (D.at frS.P.T.a) (data_atAll h)
    (threeCap (F0T OnBytes.secondHashFunction Zp Np cF) (D.at frS.P.T.a) L.c₁ L.k₁ L.c₂ L.k₂ L.c₃ L.k₃ L.e₁
      L.e₂ L.e₃ L.dW L.wEnd)
    (threeCap_ofDesc L.e₁ L.e₂ L.e₃ L.dW L.wEnd (data_atAll h) h.laid.planOk q₁ q₂ q₃)
    Ft.tiled₁ Ft.data₁
    (fun b hb => (((FileDescription.planOk_ok _).1 h.laid.planOk).blocks₁ b hb).2) Ft.base₁ hq
    (n0All Zp cF) places_nodup_full hkl hI.1 hF

/-- **WHAT IS LEFT IN FRONT OF THE FRAME's LAW AT THE SEATED TERM.** -/
structure FrameOwed7 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) : Prop where
  /-- the OOD-sampled oracle messages whose pin is open in front of each of the 51 sit in trees
  below the piece's base -/
  low : ∀ k, k ∈ our51 → ∀ q, (h.toAtMg.row L)[k]? = some q →
    LowAt (dmOf h).N (openL9 k) q.base
  /-- the files' whole data, as the sentence on the carried word reads them -/
  whole : ∃ Dw, ProofFile.wholeAt Zp = some Dw ∧
    ∀ k, k ∈ our51 → ∀ q, (h.toAtMg.row L)[k]? = some q → q.base ≤ Dw.t₁
  /-- the carried word's sentence over "laid", where the next code switch does not stand at a link
  -/
  carryElseLaid : ∀ l, l < 25 → ∀ q, (h.toAtMg.row L)[14 * l + 1]? = some q → ∀ m,
    openP9 (14 * l + 1 + 1) (.carry m) → (ProofFile.pAtK2 Zp m).stands ≠ .link →
    GoesBack (StepRel (Yes (layFront l)) q.base (InAt9 (dmOf h) (KnTight 0) (14 * l + 1)))
      ((dmOf h).cr1 m)
  /-- the like over "cleared" -/
  carryElseClear : ∀ l, l < 25 → ∀ fs f,
    Johnson.Desc.First.Walk.Seat.framesOf Zp.p.built.links Zp.first Zp.p.X = .ok fs →
    fs[l]? = some f → ∀ q, (h.toAtMg.row L)[clearIx l]? = some q → ∀ m,
    openP9 (clearIx l + 1) (.carry m) → (ProofFile.pAtK2 Zp m).stands ≠ .link →
    GoesBack (StepRel (Yes f.clear) q.base (InAt9 (dmOf h) (KnTight 0) (clearIx l)))
      ((dmOf h).cr1 m)
  /-- of every statement that is reached in front of one of the 51 numbers and bears no mark: the
  book is in order from tree 0 on, it fits, the carried rows name messages that have a place -/
  kn : ∀ k a, h.toAtMg.rch k a → a.1.2.failed = none →
    KnTight 0 k (a.1.1, a.1.2) (strsOf (FrAll D) a.2)
  /-- the seal's tie (other files' to show) -/
  sealTie : ∀ q, (h.toAtMg.row L)[357]? = some q →
    TiedAtR (Fr := FrAll D) (dmOf h).N (mgAll (dmOf h) mgBase) linksFull
      (flatPlacesOf linksFull true) (fun a => a) h.toAtMg.rch 357 (q.withMap (h.toAtMg.ex L 357))
  /-- the 25 ties behind the batching (other files' to show) -/
  behindTies : ∀ l, l < 25 → ∀ q, (h.toAtMg.row L)[behindIx l]? = some q →
    TiedAtR (Fr := FrAll D) (dmOf h).N (mgAll (dmOf h) mgBase) linksFull
      (flatPlacesOf linksFull true) (fun a => a) h.toAtMg.rch (behindIx l)
      (q.withMap (h.toAtMg.ex L (behindIx l)))

/-- **THE KIND "frame" AT THE SEATED TERM, from the seven.** -/
theorem frame_kind_of7 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (W : FrameOwed7 h L) : h.Kind L KindName.frame :=
  frame_kind_atAll h L q₁ q₂ q₃
    { data := ⟨_, data_atAll h⟩
      low := W.low
      whole := W.whole
      size := fun k hk q hq p s y hI => Nat.le_of_eq (size_atAll h L q₁ q₂ q₃ _ k hk q hq p s y hI)
      carryElseLaid := W.carryElseLaid
      carryElseClear := W.carryElseClear
      still := still_atAll h
      kn := W.kn
      sealTie := W.sealTie
      behindTies := W.behindTies }

end

end P1L20

#print axioms P1L20.size_is_base
#print axioms P1L20.data_atAll
#print axioms P1L20.numbers_atAll
#print axioms P1L20.still_atAll
#print axioms P1L20.size_atAll
#print axioms P1L20.frame_kind_of7
