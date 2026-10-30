-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/AtSeats/ArmAtRch.lean: THE SENTENCE `ArmOk J` (Johnson/Desc/K1/Law/ArmOk.lean: J, where the open
link's frame announces its second commitment) ALONG THE STATES THAT THE VERIFIER REACHES ON THE PROOF
FILE's FIRST CHAIN, AT ALL HUNDRED BORDERS OF K1's FIFTY LATER PLACES: at three of a link's four borders
FROM THE GOALS' SCOPE ALONE, WHATEVER J IS; at the fourth (in front of the reads) it is J.
OBJECT: `Reach 0 c.blocksInOrder start`, `RchAt` (Johnson/Top/H0/Walk/); the open link's frame's field `moment`.
USER: the third clause of the binder hFacts of K01_law's fifty later places, at xb := xbK Bs.G₀ J
(Johnson/Desc/K1/Law/K01FiftyPaid.lean): its second conjunct. (The first: tablesOk_at_rch_all,
Johnson/Desc/AtSeats/TablesAtHead.lean.)
LETTERS: P pp lay F Z Bs base c A B (an opening's); J; l, d, j; a.
HOW: BY POSITION, ON THE ROAD OF Johnson/Desc/AtSeats/TablesAtRch.lean: in every link the order is: K1
(reads), K8, K1 (digits).
  `commitOwn_momentUp`, `momentAny_commitAtS`   ON ANY ROUNDS: an accept of a later commitment at moment
                   m: the frame stands at m in front and at m + 1 behind (`laterOwn_ok`,
                   `joinOwnP_frame`: Johnson/Desc/K1/Law/FrameAtLater.lean has the like on two rounds)
  `MomentAny`, `momentAny_blkL`   the same at the place (l, d)
  `link_putTl`, `link_small`   the approximate range proof's sub-protocol leaves the open link
  `moment_behind_reads` (2) · `moment_front_digits` (2) · `moment_behind_digits` (3)   along Reach
  `armOk_three_rchAt`   **the three idle borders, along RchAt, whatever J**
  `armOk_at_rch`     **all hundred borders**, under hJ: J at the reached states in front of the 25 reads'
                   places (inside the promise, with no mark)
What is not claimed. J at any state. That the scope can be met. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.TablesAtRch
import Johnson.Desc.K1.Law.ArmOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Johnson.Desc.First.Walk.Tied (Reach RchAt rchAt_raw stepYes_decide)
open VerifiableInference.Desc (Block Chain FileDescription KindName)
open VerifiableInference.Desc.First (S Numbers Meaning flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull onQ Frame)
open VerifiableInference.Desc.Keeps (Decides)
open OnBytes.Model.Stages (LinkH)
open IM (Open k1Ix k1Reads)
open ProofFile (Cl)

/-! ## 1 The frame's moment over a later commitment, on any rounds -/

section
variable {Cl' : Type}

theorem commitOwn_momentUp (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (s s' : Owing (L3.St (_root_.Desc.Plain.DState Unit))) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitOwn P link moment arrays : Block _ Cl').decide s rs gs = .ok s') :
    s'.held.L.check.frame.moment = s.held.L.check.frame.moment + 1 := by
  unfold commitOwn at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · obtain ⟨t, ht, rfl⟩ := (map_ok _ _ _).1 h
      unfold L3.commitStep at ht
      obtain ⟨_, _, ht⟩ := (bind_ok _ _ _).1 ht
      obtain ⟨⟨check, w⟩, h2, ht⟩ := (bind_ok _ _ _).1 ht
      obtain ⟨⟨L, F⟩, h3, ht⟩ := (bind_ok _ _ _).1 ht
      have e : ({ s.held with L := L, F := F, w := w } : L3.St (_root_.Desc.Plain.DState Unit)) = t := by
        simpa [pure, Except.pure] using ht
      obtain ⟨ids, d₁, f', a1, a2, a3⟩ := laterOwn_ok P s.owed _ _ _ _ _ h2
      have hf : f' = _ := joinOwnP_frame _ _ _ _ _ _ a2
      unfold L3.commitBehind at h3
      obtain ⟨F₁, _, h3⟩ := (bind_ok _ _ _).1 h3
      split at h3
      · have e3 := (Prod.mk.inj (Except.ok.inj h3)).1
        rw [← e, ← e3, a3, hf]
      · cases h3
  · cases h

/-- An accept of B, on any rounds: the frame stands at m in front and at m + 1 behind. -/
def MomentAny (m : ℕ) (B : Block S Cl') : Prop :=
  ∀ (s s' : S) rs gs, B.decide s rs gs = .ok s' →
    ∃ L L', s.link? = some L ∧ s'.link? = some L' ∧ L.check.frame.moment = m ∧
      L'.check.frame.moment = m + 1

theorem momentAny_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    MomentAny moment (commitAtS P link moment arrays : Block S Cl') := by
  intro s s' rs gs h
  obtain ⟨L₀, a₀, em⟩ := commitAtS_moment P link moment arrays s s' rs gs h
  unfold commitAtS at h
  dsimp only at h
  split at h
  · rename_i L F tl hL _ _
    obtain ⟨y, hy, rfl⟩ := (map_ok _ _ _).1 h
    obtain rfl : L₀ = L := Option.some.inj (a₀.symm.trans hL)
    have e := commitOwn_momentUp P link moment arrays _ y rs gs hy
    exact ⟨L₀, y.held.L, hL, link_put s _ L₀ _ _ hL, em, by rw [e]; exact congrArg (· + 1) em⟩
  · cases h

theorem momentAny_laterAt (q : Params.First) (gp : _root_.Desc.Plain.GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) :
    MomentAny moment (laterAt q gp link piece moment arrays : Block S Cl') :=
  momentAny_commitAtS _ _ _ _

theorem momentAny_joined (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (nm : String)
    (q : Block S Cl') (hq : Decides LookSame q) :
    MomentAny moment (Block.andThen nm (commitAtS P link moment arrays) q) := by
  intro s s' rs gs e
  have e' : ((commitAtS P link moment arrays : Block S Cl').decide s
      (rs.take (commitAtS P link moment arrays : Block S Cl').rounds.length)
      (gs.take (commitAtS P link moment arrays : Block S Cl').openings)).bind (fun s₁ =>
      q.decide s₁ (rs.drop (commitAtS P link moment arrays : Block S Cl').rounds.length)
        (gs.drop (commitAtS P link moment arrays : Block S Cl').openings)) = .ok s' := e
  obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 e'
  obtain ⟨L, L', a, b, e1, e2⟩ := momentAny_commitAtS P link moment arrays s s₁ _ _ h1
  exact ⟨L, L', a, (hq _ _ _ _ h2).link.trans b, e1, e2⟩

end

theorem momentAny_blkL (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) : MomentAny (momL d) (blkL Z G l d X arrs) := by
  cases d with
  | true => exact momentAny_laterAt _ _ _ _ _ _
  | false => exact momentAny_joined _ _ _ _ _ _ (lookSame_k1Quiet G l X)

/-! ## 2 The approximate range proof's sub-protocol leaves the open link -/

theorem link_putTl (s : S) (tl : HTailF2) : (s.putTl tl).link? = s.link? := by
  unfold S.putTl
  cases ha : s.here with
  | head a =>
    by_cases ho : a.opened = true <;> simp [S.link?, ha, ho]
  | lay a => simp [S.link?, ha]
  | att a => simp [S.link?, ha]
  | between => simp [S.link?, ha]
  | fin a => simp [S.link?, ha]
  | mem a => simp [S.link?, ha]

theorem link_small (p : First.K8.ParW) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : (First.K8.whole p).decide s rs gs = .ok s') :
    s'.link? = s.link? := by
  have hd' : (First.K8.approximateRangeProofDrawKind (Cl := Claim) First.K8.atS p.toPar).decide s rs gs = .ok s' := hd
  obtain ⟨r, rfl⟩ := First.K8.decide_one _ p.toPar s s' rs gs hd'
  obtain ⟨tl, ht, hm⟩ := (First.K8.decide_atS_iff p.toPar s s' r gs).1 hd'
  rw [hm.2.2.2.2.2.2.2.2]
  exact link_putTl s _

/-! ## 3 The walk -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

theorem moment_behind_reads (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (14 * l + k1Ix l false + 2 + 1) a) :
    ∃ L, a.2.link? = some L ∧ L.check.frame.moment = 2 := by
  obtain ⟨b, Xl, reads, hb, _, hla⟩ := k01_flat_reads hS hR O l hl
  cases h with
  | @succ _ z s s' b' _ hb' hy =>
    obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    obtain ⟨_, L', _, e, _, em⟩ := momentAny_blkL Z Bs.G₀ l false Xl reads s s' rs gs
      ((IM.yes_alone hla (fun e => nomatch e) s s' rs gs).1 hd).1
    exact ⟨L', e, em⟩

theorem moment_front_digits (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (14 * l + k1Ix l false + 2 + 1 + 1) a) :
    ∃ L, a.2.link? = some L ∧ L.check.frame.moment = 2 := by
  obtain ⟨b, Xl, hb, hla⟩ := k8_flat hS hR O l hl
  cases h with
  | @succ _ z s s' b' h0 hb' hy =>
    obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    obtain ⟨L, e, em⟩ := moment_behind_reads hS hR O l hl (z, s) h0
    exact ⟨L, (link_small _ s s' rs gs
      ((IM.yes_alone hla (fun e => nomatch e) s s' rs gs).1 hd).1).trans e, em⟩

theorem moment_behind_digits (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (14 * l + k1Ix l false + 2 + 1 + 1 + 1) a) :
    ∃ L, a.2.link? = some L ∧ L.check.frame.moment = 3 := by
  obtain ⟨b, digits, hb, hla⟩ := k01_flat_digits hS hR O l hl
  have hix : 14 * l + k1Ix l true + 2 = 14 * l + k1Ix l false + 2 + 1 + 1 := by
    rw [k1Ix_true]
    omega
  rw [hix] at hb
  obtain ⟨_, Xl, _, _, _, _⟩ := k01_flat_reads hS hR O l hl
  cases h with
  | @succ _ z s s' b' h0 hb' hy =>
    obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    obtain ⟨_, L', _, e, _, em⟩ := momentAny_blkL Z Bs.G₀ l true Xl digits s s' rs gs
      ((IM.yes_alone hla (fun e => nomatch e) s s' rs gs).1 hd).1
    exact ⟨L', e, em⟩

/-- Where the open link's frame stands at a moment other than 1. -/
theorem armOk_of_moment (J : S → Prop) {s : S} {m : ℕ} (hm : m ≠ 1)
    (h : ∃ L, s.link? = some L ∧ L.check.frame.moment = m) : ArmOk J s := by
  obtain ⟨L, e, em⟩ := h
  refine armOk_idle J s fun L₂ e₂ => ?_
  obtain rfl : L = L₂ := Option.some.inj (e.symm.trans e₂)
  rw [em]
  exact hm

/-- **The three idle borders, along "reached at the description's first chain", whatever J.** -/
theorem armOk_three_rchAt (J : S → Prop) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Str : Type} (l : ℕ) (hl : l < 25)
    (j : ℕ) (hj : j = 14 * l + k1Ix l false + 2 + 1 ∨ j = 14 * l + k1Ix l true + 2 ∨
      j = 14 * l + k1Ix l true + 2 + 1) (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c) j a) : ArmOk J a.1.2 := by
  have hr := rchAt_raw h
  have hix : 14 * l + k1Ix l true + 2 = 14 * l + k1Ix l false + 2 + 1 + 1 := by
    rw [k1Ix_true]
    omega
  rcases hj with rfl | rfl | rfl
  · exact armOk_of_moment J (by decide) (moment_behind_reads hS hR O l hl a.1 hr)
  · rw [hix] at hr
    exact armOk_of_moment J (by decide) (moment_front_digits hS hR O l hl a.1 hr)
  · rw [hix] at hr
    exact armOk_of_moment J (by decide) (moment_behind_digits hS hR O l hl a.1 hr)

/-- **All hundred borders**: hFacts' third clause's second conjunct, in its own letters. -/
theorem armOk_at_rch (J : S → Prop) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {W : Type} {Fr : Frame}
    (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (hJ : ∀ l, l < 25 → ∀ a : (ProofFile.InstPub × S) × Fr.E.Str,
      RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
        (14 * l + k1Ix l false + 2) a →
      onQ N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) (14 * l + k1Ix l false + 2) a →
      a.1.2.failed = none → J a.1.2) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ j,
      (j = 14 * l + k1Ix l d + 2 ∨ j = 14 * l + k1Ix l d + 2 + 1) →
      ∀ a : (ProofFile.InstPub × S) × Fr.E.Str,
      RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
        j a →
      onQ N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) j a → a.1.2.failed = none →
      ArmOk J a.1.2 := by
  intro l hl d j hj a hr hon hm
  cases d with
  | true =>
    exact armOk_three_rchAt J hS hR O l hl j
      (hj.elim (fun e => .inr (.inl e)) fun e => .inr (.inr e)) a hr
  | false =>
    rcases hj with rfl | rfl
    · exact fun _ => hJ l hl a hr hon hm
    · exact armOk_three_rchAt J hS hR O l hl _ (.inl rfl) a hr

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.commitOwn_momentUp
#print axioms VerifiableInference.Desc.K1.momentAny_blkL
#print axioms VerifiableInference.Desc.K1.link_small
#print axioms VerifiableInference.Desc.K1.moment_behind_reads
#print axioms VerifiableInference.Desc.K1.moment_front_digits
#print axioms VerifiableInference.Desc.K1.moment_behind_digits
#print axioms VerifiableInference.Desc.K1.armOk_three_rchAt
#print axioms VerifiableInference.Desc.K1.armOk_at_rch
