-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FrameFourAll.lean: THE SHARE OF THE KIND "frame" ON THE FIRST CHAIN,
AT THE SEATED TERM, IN THE FORM P5J.AtMgA.Kind (Johnson/P5J/RowsAtAll.lean), FROM FOUR DEBTS AND TWO
PUBLIC TESTS: three more fields of FrameOwed7b (FrameEndsAll.lean) are shown at the head.

  base_le_t1        general: in a row of pieces that tiles the first chain a piece's
                    base is at most the data's number of first-chain trees
  whole_atAll       FrameOwed7b.whole: the files' whole data, as the sentence on the carried word
                    reads them, ARE the head's D (wholeAt_of_laid,
                    Johnson/Top/H0/Opts/WholeOfLaid.lean), and the 51 bases lie within
  standOurB_full    the written list asks, in front of each of the 51 but "cleared" 24, that the
                    chain stand between two links or in a link of the sort "layers" or "attention":
                    by Lean's kernel
  not_head_at       so a statement in front of one of these does not stand at the head's link
  fenceEnds_atAll   FrameOwed7b.fenceEnds: the fence at the state that the way in
                    returns (fence_of_in_doorData, Johnson/Top/H0/Walk/FrameCarryFenceEnds.lean)
                    from the tight list, size_atAll, whole_atAll, ft_at_switch and not_head_at
  FrameOwed4        WHAT IS LEFT: low, kn, sealTie, behindTies; and, on public data, a test with
                    code and an equation: spots (spotsFitB Zp) and links25 (the request's shape has
                    25 links), which
                    stands24 (Johnson/Top/H0/K2Caller/Stands24.lean) spends
  frame_kind_of4    h.Kind L KindName.frame from FrameOwed4

Limits. No field of FrameOwed4 is shown here. A member of the head is proved at storedPublicFiles and zGap alone
(at secondHashFunction; side library AtFullSide/Top/). No soundness statement.

-/
import Johnson.P1L20R.FrameEndsAll
import Johnson.Top.H0.Walk.FrameCarryFenceEnds
import Johnson.Top.H0.Opts.WholeOfLaid
import Johnson.Top.H0.K2Caller.Stands24

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
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers flatPlacesOf shapeAt standOf
  standAt Stand)
open VerifiableInference.Desc.First.K2Caller (rest doorZ carryAtZ spotsFitB stands24)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)
open P5J (AtMgA Free F0T)

/-- The trees of the stretches, added up, are the trees of the stretches' data, appended. -/
theorem sum_flat {α : Type} (Ls : List α) (g : α → List RDT) :
    ((Ls.flatMap g).map (·.trees.length)).sum =
      (Ls.map fun p => ((g p).map (·.trees.length)).sum).sum := by
  induction Ls with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      ih]

/-- **A piece's base is at most the data's number of first-chain trees.** -/
theorem base_le_t1 {C : CK} {W Xi : Type} {G : FileDescription Xi} {D : WholeD} {all : List LeftT}
    {X₁ X₂ : Type} (R : ThreeAt C D all G X₁ X₂ W) (ht : Tiled R.p₁ R.l₁)
    (hd : rowData R.p₁ R.l₁ = D.ds₁) (h0 : R.p₁.base = 0) {k : ℕ}
    {q : Piece C (frameAt D all D.key₁ R.ft₁) (G.XiPub × G.S₁) G.Cl W}
    (hq : (R.p₁ :: R.l₁)[k]? = some q) : q.base ≤ D.t₁ := by
  rw [OnBytes.Road.K4.tiled_base R.l₁ R.p₁ ht k q hq, h0, Nat.zero_add]
  have e : D.t₁ = ((R.p₁ :: R.l₁).map (·.trees)).sum := by
    show (D.ds₁.map (·.trees.length)).sum = _
    rw [← hd]
    exact sum_flat (R.p₁ :: R.l₁) (·.ds)
  rw [e, List.map_take]
  exact Nat.le.intro (List.sum_take_add_sum_drop _ k)

/-- A test with code: in front of each of the 51 but "cleared" 24 the written list asks that the
chain stand between two links, or in a link of the sort "layers" or "attention". -/
def standOurB : Bool :=
  our51.all fun k =>
    k == clearIx 24 ||
      match (flatPlacesOf linksFull true)[k]? with
      | some p => standAt linksFull p == .between || standAt linksFull p == .link .layers ||
          standAt linksFull p == .link .attention
      | none => false

set_option maxRecDepth 1000000 in
theorem standOurB_full : standOurB = true := by decide +kernel

/-- **A statement in front of one of these does not stand at the head's link.** -/
theorem not_head_at {P W : Type} {N : Numbers} {Mg : Meaning P W} {k : ℕ} (hk : k ∈ our51)
    (hne : k ≠ clearIx 24) {a : P × S} {y : Strs} (hu : a.2.failed = none)
    (h : FrontAt N Mg linksFull (flatPlacesOf linksFull true) k a y) :
    ∀ b, a.2.here ≠ .head b := by
  intro b hb
  have hs := front_shape hu h
  have hc := List.all_eq_true.1 standOurB_full k hk
  rw [Bool.or_eq_true] at hc
  rcases hc with hc | hc
  · exact hne (eq_of_beq hc)
  · cases hp : (flatPlacesOf linksFull true)[k]? with
    | none =>
      rw [hp] at hc
      cases hc
    | some p =>
      rw [hp] at hc hs
      unfold shapeAt at hs
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hs hc
      have e := hs.1.1
      have e' : standOf a.2 = .link .head ∨ standOf a.2 = .headFront := by
        unfold standOf
        rw [hb]
        by_cases hi : a.2.inLink = true <;> simp [hi]
      rcases hc with (hc | hc) | hc <;> rcases e' with e' | e' <;> rw [e', hc] at e <;> cases e

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

set_option maxHeartbeats 4000000 in
/-- **FrameOwed7b.whole.** -/
theorem whole_atAll (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) :
    ProofFile.wholeAt Zp = some D ∧
      ∀ (k : ℕ), ∀ q, (h.toAtMg.row L)[k]? = some q → Piece.base q ≤ D.t₁ := by
  refine ⟨P1M2.wholeAt_of_laid h.laid, fun k q hq => ?_⟩
  have Ft := threeCap_fits L.e₁ L.e₂ L.e₃ L.dW L.wEnd (data_atAll h) h.laid.planOk q₁ q₂ q₃
  have hb := base_le_t1
    (threeCap (F0T OnBytes.secondHashFunction Zp Np cF) (D.at frS.P.T.a) L.c₁ L.k₁ L.c₂ L.k₂ L.c₃ L.k₃ L.e₁
      L.e₂ L.e₃ L.dW L.wEnd) Ft.tiled₁ Ft.data₁ Ft.base₁ hq
  exact Nat.le_trans hb
    (Nat.le_of_eq (congrArg (fun E : WholeD => E.t₁) (P5J.LaidAt.atDepth h.scope h.laid)))

/-- **FrameOwed7b.fenceEnds**, wherever the next code switch stands. -/
theorem fenceEnds_atAll (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (h24 : (ProofFile.pAtK2 Zp 24).stands ≠ .head) :
    ∀ k, k ∈ our51 → ∀ q, (h.toAtMg.row L)[k]? = some q → ∀ m, openP9 (k + 1) (.carry m) →
      ∀ p s y s', InAt9 (dmOf h) (KnTight 0) k (p, s) y → doorZ Zp m s = some s' →
      CarryFence Zp m q.base s' := by
  intro k hk q hq m hm
  obtain ⟨hW, hB⟩ := whole_atAll h L q₁ q₂ q₃
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  refine fence_of_in_doorData Zp D hW m q.base (hB k q hq) (InAt9 (dmOf h) (KnTight 0) k)
    (fun p s y hI => ?_) (fun hst p s y hI => ?_)
  · obtain ⟨a, b, c'⟩ := kn_at9 hI hk
    exact ⟨by rw [ft_at_switch O.pub m]; exact a, b, c',
      Nat.le_of_eq (size_atAll h L q₁ q₂ q₃ _ k hk q hq p s y hI)⟩
  · refine not_head_at hk (fun e => ?_) hI.1 hI.2.1
    subst e
    obtain rfl := carry_clear_is (by decide : 24 < 25) hm
    exact h24 hst

/-- **WHAT IS LEFT IN FRONT OF THE FRAME's LAW AT THE SEATED TERM.** -/
structure FrameOwed4 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) : Prop where
  /-- a test with code on public data: no two code switches open the same group, and each is of the
  sort (link, output head, finish) that its segment's number asks -/
  spots : spotsFitB Zp = true
  /-- a fact on public data: the request's shape has 25 links -/
  links25 : Zp.s₀.check.frame.shape.link.length = 25
  /-- the OOD-sampled oracle messages whose pin is open in front of each of the 51 sit in trees
  below the piece's base -/
  low : ∀ k, k ∈ our51 → ∀ q, (h.toAtMg.row L)[k]? = some q →
    LowAt (dmOf h).N (openL9 k) q.base
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

/-- **THE KIND "frame" AT THE SEATED TERM, from these.** -/
theorem frame_kind_of4 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (W : FrameOwed4 h L) : h.Kind L KindName.frame :=
  frame_kind_of7b h L q₁ q₂ q₃
    { low := W.low
      whole := ⟨D, (whole_atAll h L q₁ q₂ q₃).1,
        fun k _ q hq => (whole_atAll h L q₁ q₂ q₃).2 k q hq⟩
      fenceEnds := fun k hk q hq m hm _ =>
        fenceEnds_atAll h L q₁ q₂ q₃ (stands24 W.spots W.links25) k hk q hq m hm
      stands24 := stands24 W.spots W.links25
      kn := W.kn
      sealTie := W.sealTie
      behindTies := W.behindTies }

end

end P1L20

#print axioms P1L20.base_le_t1
#print axioms P1L20.standOurB_full
#print axioms P1L20.not_head_at
#print axioms P1L20.whole_atAll
#print axioms P1L20.fenceEnds_atAll
#print axioms P1L20.frame_kind_of4
