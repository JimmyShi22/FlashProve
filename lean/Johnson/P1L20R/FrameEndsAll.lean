-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FrameEndsAll.lean:
the two fields of FrameOwed7 (FramePaidAll.lean) on the carried word's sentence where
the next code switch does not stand at a link, FROM LIGHTER FACTS, by another file's lemmas
(Johnson/Top/H0/Walk/FrameCarryEnds.lean).

  front_shape       the promise in front, at a statement that bears no mark, holds the test shapeAt
  standClearB_full  the written list asks, in front of "cleared" l at l < 24, that a link of the
                    sort "layers" or "attention" stand open: by Lean's kernel
  not_head_front    so a statement in front of "cleared" l, l < 24, does not stand at the head's
                    link
  not_head_behind   behind an accepting "cleared" the state does not stand at the output head
  FrameOwed7b       WHAT IS LEFT: seven fields: in the place of the two sentences: fenceEnds (the
                    fence at the state that the sentence's way in returns) and stands24 (the last
                    segment's next switch does not stand at the head)
  frame_kind_of7b   h.Kind L KindName.frame from FrameOwed7b

Limits. No field of FrameOwed7b is shown here. No soundness statement.

-/
import Johnson.P1L20R.FramePaidAll
import Johnson.Top.H0.Walk.FrameCarryEnds

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
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers flatPlacesOf shapeAt onAt standOf
  standAt Stand)
open VerifiableInference.Desc.First.K2Caller (rest doorZ carryAtZ)
open Johnson.Desc.First.Walk (layFront)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)
open P5J (AtMgA Free F0T)

/-- The promise in front, at a statement that bears no mark, holds the test on where the chain
stands. -/
theorem front_shape {P W : Type} {N : Numbers} {Mg : Meaning P W} {links : List ModelPart}
    {ps : List Place} {k : ℕ} {a : P × S} {y : Strs} (hu : a.2.failed = none)
    (h : FrontAt N Mg links ps k a y) : shapeAt links ps[k]? a.2 = true := by
  unfold FrontAt onAt at h
  rcases h.2 with h' | ⟨h1, -⟩
  · exact absurd hu h'
  · simp only [Bool.and_eq_true] at h1
    exact h1.1.1.1.1.1

/-- A test with code: in front of "cleared" l, l < 24, the written list asks that a link of the sort
"layers" or "attention" stand open. -/
def standClearB : Bool :=
  (List.range 24).all fun l =>
    match (flatPlacesOf linksFull true)[clearIx l]? with
    | some p => standAt linksFull p == .link .layers || standAt linksFull p == .link .attention
    | none => false

set_option maxRecDepth 1000000 in
theorem standClearB_full : standClearB = true := by decide +kernel

/-- **A statement in front of "cleared" l, l < 24, does not stand at the head's link.** -/
theorem not_head_front {P W : Type} {N : Numbers} {Mg : Meaning P W} {l : ℕ} (hl : l < 24)
    {a : P × S} {y : Strs} (hu : a.2.failed = none)
    (h : FrontAt N Mg linksFull (flatPlacesOf linksFull true) (clearIx l) a y) :
    ∀ b, a.2.here ≠ .head b := by
  intro b hb
  have hs := front_shape hu h
  have hc := List.all_eq_true.1 standClearB_full l (List.mem_range.2 hl)
  cases hp : (flatPlacesOf linksFull true)[clearIx l]? with
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
    rcases hc with hc | hc <;> rcases e' with e' | e' <;> rw [e', hc] at e <;> cases e

/-- Behind an accepting "cleared" the state does not stand at the output head. -/
theorem not_head_behind {Zp : ProofFile.Pub} {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    {f : Johnson.Desc.First.Walk.Seat.LinkFrame} {l : ℕ}
    (hfs : Johnson.Desc.First.Walk.Seat.framesOf Zp.p.built.links Zp.first Zp.p.X = .ok fs)
    (hf : fs[l]? = some f) {s t : S} (h : f.clear s = .ok t) : ∀ b, t.here ≠ .head b := by
  obtain ⟨_, Xl, counts, left, e, _⟩ :=
    Johnson.Desc.First.Walk.Seat.framesOf_row hfs (List.mem_of_getElem? hf)
  rw [e] at h
  have hw := (wayLike_cleared h).hereV
  rw [(rest_cleared h).2] at hw
  intro b hh
  rw [hh] at hw
  cases hw

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **WHAT IS LEFT IN FRONT OF THE FRAME's LAW AT THE SEATED TERM**, the two sentences at the ends
cut down. -/
structure FrameOwed7b (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) : Prop where
  /-- the OOD-sampled oracle messages whose pin is open in front of each of the 51 sit in trees
  below the piece's base -/
  low : ∀ k, k ∈ our51 → ∀ q, (h.toAtMg.row L)[k]? = some q →
    LowAt (dmOf h).N (openL9 k) q.base
  /-- the files' whole data, as the sentence on the carried word reads them -/
  whole : ∃ Dw, ProofFile.wholeAt Zp = some Dw ∧
    ∀ k, k ∈ our51 → ∀ q, (h.toAtMg.row L)[k]? = some q → q.base ≤ Dw.t₁
  /-- the fence at the state that the sentence's way in returns, where the next code switch does
  not stand at a link -/
  fenceEnds : ∀ k, k ∈ our51 → ∀ q, (h.toAtMg.row L)[k]? = some q → ∀ m,
    openP9 (k + 1) (.carry m) → (ProofFile.pAtK2 Zp m).stands ≠ .link → ∀ p s y s',
    InAt9 (dmOf h) (KnTight 0) k (p, s) y → doorZ Zp m s = some s' →
    CarryFence Zp m q.base s'
  /-- the last segment's next code switch does not stand at the head -/
  stands24 : (ProofFile.pAtK2 Zp 24).stands ≠ .head
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

/-- **THE KIND "frame" AT THE SEATED TERM, from these seven.** -/
theorem frame_kind_of7b (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (W : FrameOwed7b h L) : h.Kind L KindName.frame :=
  frame_kind_of7 h L q₁ q₂ q₃
    { low := W.low
      whole := W.whole
      carryElseLaid := fun l hl q hq m hm hs =>
        carry_goesBack_sameZ Zp Z.lay m (Yes (layFront l))
          (fun _ _ e => (Johnson.Desc.First.Walk.Law.layFront_ok e).1) q.base _
          (W.fenceEnds _ (mem_our_laid hl) q hq m hm hs)
      carryElseClear := fun l hl fs f hfs hf q hq m hm hs => by
        obtain rfl := carry_clear_is hl hm
        have hw : ∀ s t, Yes f.clear s t → WayLike (rest s) (rest t) := fun s t e => by
          obtain ⟨_, Xl, counts, left, e', _⟩ :=
            Johnson.Desc.First.Walk.Seat.framesOf_row hfs (List.mem_of_getElem? hf)
          have e2 : f.clear s = .ok t := e
          rw [e'] at e2
          exact wayLike_cleared e2
        cases hst : (ProofFile.pAtK2 Zp m).stands with
        | link => exact absurd hst hs
        | head =>
          have h24 : m < 24 := by
            rcases Nat.lt_or_ge m 24 with h' | h'
            · exact h'
            · obtain rfl : m = 24 := by omega
              exact absurd hst W.stands24
          exact carry_goesBack_head Zp Z.lay m hst (Yes f.clear) hw q.base _
            (fun p s t y e hI => ⟨not_head_front h24 hI.1 hI.2.1, not_head_behind hfs hf e⟩)
            (W.fenceEnds _ (mem_our_clear hl) q hq m hm hs)
        | finish =>
          exact carry_goesBack_finish Zp Z.lay m hst (Yes f.clear) hw q.base _
            (W.fenceEnds _ (mem_our_clear hl) q hq m hm hs)
      kn := W.kn
      sealTie := W.sealTie
      behindTies := W.behindTies }

end

end P1L20

#print axioms P1L20.standClearB_full
#print axioms P1L20.not_head_front
#print axioms P1L20.not_head_behind
#print axioms P1L20.frame_kind_of7b
