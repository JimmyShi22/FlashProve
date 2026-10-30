-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/K5AtLater.lean: **k5_at_later**: it pays the
binder hK5 of k01_fifty_at9 (K01FiftyAt9.lean, this folder) in the proof of k01_fifty_atBase
(Johnson/Desc/K1/Law/K01FiftyAtBase.lean): over an accept of a later
commitment's sub-protocol (a link's reads or its digits) attention's two public tests "K5.okAt" and
"K5.plain" of that link stay true. NO PREMISE IS LEFT.
OBJECT: `blkL Z G l d X arrs` (LaterOne.lean) and the two Bools `H2K5.Door.okThereB`,
`plainThereB` (Johnson/Desc/First/Att/Door/OkThereB.lean, PlainThereB.lean).
USER: the top of K01_law's fifty later places (its binder hK5).
LETTERS: Dm, dk, Mg₀ (the meaning beneath), Z, Bs; l, d, X, arrs; x, x', y, q.
HOW. Both Bools read two readers of the verifier's state alone: the open ledger (S.fork?) and what
an attention segment's own rounds handed on (S.heard5?).
  the commitment   CALLED: `commitAtS_slots` (Johnson/Desc/K1/KeepsSlots.lean: the
                   ledger's slots stay) and `commitAtS_shapes` (Johnson/Desc/K1/KeepsShapes.lean: each
                   array keeps its numbers of rows and columns); its three writes leave heard5?
                   (`heard5_put`)
  the step without a round behind the reads   `lookSame_k1Quiet` (LookAtLater.lean: the ledger
                   stays) and `heard5_k1Quiet`
  a link that is no attention link   no part answers at the two names: the test is the one of the
                   meaning beneath (`First.pubAll_else`); at `mgBase` it is false, so nothing is asked
  `K5Same s s'`      the two Bools answer at s' as at s, at every letter
  `LaterK5 B`        an accept of B on two rounds gives K5Same; `laterK5_blkL`
  `k5_at_later_of`   the binder at a letter Mg₀ for the meaning beneath, under hb: Mg₀'s own test at a
                   name of a link goes from x to x'
  `k5_at_later`      **the binder, to the letter, at mgBase**
What is not claimed. That either test holds at any state. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.RestAtPlus13
import Johnson.Desc.K1.Law.K01FiftyR
import Johnson.Desc.K1.KeepsSlots
import Johnson.Desc.K1.KeepsShapes
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.Sound.MgBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf pubAll
  pubAll_else)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll mgBase d13)
open VerifiableInference.Desc.K13.Law (plus13 plus13_hand)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.Keeps (Decides)
open OnBytes.Model.Stages (LinkH)
open H2K5.Door (okThereB plainThereB heardSlotsB stretchB formB sumB wideB heardPlainB k5Item)

variable {Cl : Type}

/-! ## 1 The two Bools read the ledger's slots, one array's width, and what was handed on -/

theorem k5_stretch_same {F F' : Fork} (h : F'.gotF = F.gotF) (a n : Nat) :
    stretchB F' a n = stretchB F a n := by
  unfold stretchB
  rw [h]

theorem k5_form_same {F F' : Fork} (h : F'.gotF = F.gotF) (f : Aff) : formB F' f = formB F f := by
  unfold formB
  rw [h]

theorem k5_sum_same {F F' : Fork} (h : F'.gotF = F.gotF)
    (hh : VerifiableInference.Desc.Part.MaskedSum.Heard) (n : Nat) : sumB F' hh n = sumB F hh n := by
  unfold sumB
  rw [k5_form_same h, k5_stretch_same h, k5_stretch_same h]

theorem k5_slots_same {F F' : Fork} (h : F'.gotF = F.gotF) (g : First.Att.P.Geo)
    (hd : First.Att.P.Heard) : heardSlotsB F' g hd = heardSlotsB F g hd := by
  unfold heardSlotsB
  simp only [k5_stretch_same h, k5_sum_same h]

theorem k5_sized_same {F F' : Fork} (h : PscRun.SlotsSame F F') :
    H2K5.Door.sizedB F' = H2K5.Door.sizedB F := by
  unfold H2K5.Door.sizedB
  rw [h.vp, h.mf, h.gotF, h.ns]

theorem k5_wide_eq (U : Fork) (i n : Nat) :
    wideB U i n = ((U.trees.map fun T => (T.R, T.K))[i]?).any fun p => p.2 == n := by
  rw [Array.getElem?_map]
  unfold wideB
  cases U.trees[i]? <;> rfl

theorem k5_wide_same {F F' : Fork} (h : ShapesSame F F') (i n : Nat) :
    wideB F' i n = wideB F i n := by
  have h' : (F'.trees.map fun T => (T.R, T.K)) = F.trees.map fun T => (T.R, T.K) := h
  rw [k5_wide_eq, k5_wide_eq, h']

/-- **The two Bools answer at s' as at s.** -/
def K5Same (s s' : S) : Prop :=
  (∀ g, okThereB g s' = okThereB g s) ∧ ∀ i n, plainThereB i n s' = plainThereB i n s

theorem K5Same.trans {a b c : S} (h : K5Same a b) (k : K5Same b c) : K5Same a c :=
  ⟨fun g => (k.1 g).trans (h.1 g), fun i n => (k.2 i n).trans (h.2 i n)⟩

/-- Where both readers answer the same. -/
theorem k5Same_same {s s' : S} (hf : s'.fork? = s.fork?) (h5 : s'.heard5? = s.heard5?) :
    K5Same s s' :=
  ⟨fun g => by unfold okThereB; rw [hf, h5], fun i n => by unfold plainThereB; rw [hf, h5]⟩

/-- Where the ledger behind has the slots and the arrays' shapes of the ledger in front. -/
theorem k5Same_of {s s' : S} {F F' : Fork} (a : s.fork? = some F) (b : s'.fork? = some F')
    (hs : PscRun.SlotsSame F F') (hp : ShapesSame F F') (h5 : s'.heard5? = s.heard5?) :
    K5Same s s' := by
  refine ⟨fun g => ?_, fun i n => ?_⟩
  · unfold okThereB
    rw [a, b, h5]
    cases s.heard5? with
    | none => rfl
    | some h =>
      show (H2K5.Door.sizedB F' && heardSlotsB F' g h) = (H2K5.Door.sizedB F && heardSlotsB F g h)
      rw [k5_sized_same hs, k5_slots_same hs.gotF]
  · unfold plainThereB
    rw [a, b, h5]
    cases s.heard5? with
    | none => rfl
    | some h =>
      show (heardPlainB h && wideB F' i n) = (heardPlainB h && wideB F i n)
      rw [k5_wide_same hp]

/-! ## 2 The commitment -/

/-- The commitment's three writes leave what an attention segment's own rounds handed on. -/
theorem heard5_put (s : S) (w : _root_.Desc.Plain.DState Unit) (L' : LinkCtx) (F' : Fork) :
    (((laid s w).putLink L').putFork F').heard5? = s.heard5? := by
  cases hs : s.here with
  | lay a => simp [S.putFork, S.putLink, S.heard5?, laid, hs]
  | att a => simp [S.putFork, S.putLink, S.heard5?, laid, hs]
  | head a =>
    by_cases ho : a.opened = true <;> simp [S.putFork, S.putLink, S.heard5?, laid, hs, ho]
  | between => simp [S.putFork, S.putLink, S.heard5?, laid, hs]
  | fin a => simp [S.putFork, S.putLink, S.heard5?, laid, hs]
  | mem a => simp [S.putFork, S.putLink, S.heard5?, laid, hs]

theorem k5Same_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') : K5Same s s' := by
  obtain ⟨_, F, _, y, _, hF, _, e, hs⟩ := commitAtS_slots h
  obtain ⟨_, F₂, _, y₂, _, hF₂, _, e₂, hp⟩ := commitAtS_shapes h
  have b : s'.fork? = some y.F := by
    rw [e]
    exact fork_putK s _ _ F _ hF
  have b₂ : s'.fork? = some y₂.F := by
    rw [e₂]
    exact fork_putK s _ _ F₂ _ hF₂
  obtain rfl : F = F₂ := Option.some.inj (hF.symm.trans hF₂)
  have ey : y₂.F = y.F := Option.some.inj (b₂.symm.trans b)
  rw [ey] at hp
  have h5 : s'.heard5? = s.heard5? := by
    rw [e]
    exact heard5_put s _ _ _
  exact k5Same_of hF b hs hp h5

/-! ## 3 The step without a round behind the reads' commitment -/

theorem heard5_k1Quiet (G : ProofFile.Ground) (l : Nat) (X : LinkH) :
    Decides (fun s s' : S => s'.heard5? = s.heard5?) (IM.k1Quiet G l X) := by
  refine k1Quiet_decides _ (fun P s rs gs s' h => ?_) (fun P s rs gs s' h => ?_)
    (fun A s s' h => ?_) G l X
  · obtain ⟨a, own, tl', ha, _, _, rfl⟩ := K8.ReadsQuiet.layers_ok h
    simp [S.heard5?, ha]
  · obtain ⟨a, cov, x, t, tl', ha, _, _, _, _, _, rfl⟩ := K8.ReadsQuiet.head_ok h
    simp [S.heard5?, ha]
  · obtain ⟨a, t, tl, ha, rfl⟩ := Meaning.K2.readsAtSO_eq h
    simp [S.heard5?, ha]

/-! ## 4 The sub-protocol at (l, d) -/

/-- An accept of B on two rounds leaves the two Bools. -/
def LaterK5 (B : Block S Cl) : Prop :=
  ∀ (s s' : S) rs gs, rs.length = 2 → B.decide s rs gs = .ok s' → K5Same s s'

theorem laterK5_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    LaterK5 (commitAtS P link moment arrays : Block S Cl) :=
  fun s s' rs gs _ h => k5Same_commitAtS P link moment arrays s s' rs gs h

theorem laterK5_laterAt (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (link piece moment : Nat) (arrays : Option (List Nat)) :
    LaterK5 (laterAt q gp link piece moment arrays : Block S Cl) :=
  laterK5_commitAtS _ _ _ _

theorem laterK5_joined (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (nm : String)
    (q : Block S Cl) (hq : Decides LookSame q)
    (h5 : Decides (fun s s' : S => s'.heard5? = s.heard5?) q) :
    LaterK5 (Block.andThen nm (commitAtS P link moment arrays) q) := by
  intro s s' rs gs h2 h
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ := joined_yes P link moment arrays nm q s s' r₁ r₂ gs h
  exact (k5Same_commitAtS P link moment arrays s s₁ _ gs₁ h1).trans
    (k5Same_same (hq _ _ _ _ h3).fork (h5 _ _ _ _ h3))

theorem laterK5_k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) (X : LinkH) (pr : Nat)
    (reads : Option (List Nat)) : LaterK5 (IM.k1Reads Z G l X pr reads) :=
  laterK5_joined _ _ _ _ _ _ (lookSame_k1Quiet G l X) (heard5_k1Quiet G l X)

theorem laterK5_blkL (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) : LaterK5 (blkL Z G l d X arrs) := by
  cases d with
  | true => exact laterK5_laterAt _ _ _ _ _ _
  | false => exact laterK5_k1Reads _ _ _ _ _ _

/-! ## 5 The binder -/

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

/-- At a link that is no attention link the two names fall to the meaning beneath. -/
theorem k5_names_else (m : ℕ) (n : String) (hn : n = "K5.okAt" ∨ n = "K5.plain")
    (hatt : Dm.pubD.d5.isAtt m = false) (a : ProofFile.InstPub × S) :
    pubAll Dm.pubD (plus13 (d13 Dm) dk Mg₀).pub (.more (some m) n) a =
      Mg₀.pub (.more (some m) n) a := by
  have h5 : k5Item Dm.pubD.d5 (.more (some m) n) = false := by
    show (Dm.pubD.d5.isAtt m && _) = false
    rw [hatt]
    rfl
  have hc : K13.Law.cA13 (.more (some m) n) = false := rfl
  have hl : First.FillBare.leftItem Dm.pubD.links (.more (some m) n) = false := by
    show (_ && (n == "K4.rowsBare" || n == "K4.lookLeft")) = false
    rcases hn with rfl | rfl <;> exact Bool.and_eq_false_iff.2 (Or.inr rfl)
  have hs : First.FillSent.sentItem (.more (some m) n) = false := by
    rcases hn with rfl | rfl <;> rfl
  have hs1 : First.FillSent.sent1Item (.more (some m) n) = false := by
    rcases hn with rfl | rfl <;> rfl
  rw [pubAll_else Dm.pubD _ (.more (some m) n) rfl rfl rfl rfl rfl rfl h5 hs hs1 hl rfl a]
  exact plus13_hand (d13 Dm) dk Mg₀ _ hc a

/-- The two names' tests go over a step that leaves the two Bools. -/
theorem k5_pub_kept
    (hb : ∀ m n (x x' : ProofFile.InstPub × S), Mg₀.pub (.more (some m) n) x = true →
      Mg₀.pub (.more (some m) n) x' = true)
    (l : ℕ) (q : Pub) (hq : k5At l q = true) (x x' : ProofFile.InstPub × S) (hK : K5Same x.2 x'.2)
    (h0 : (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub q x = true) :
    (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub q x' = true := by
  rw [pub_plus13] at h0 ⊢
  cases q with
  | more sg n =>
    cases sg with
    | none => cases hq
    | some m =>
      have hq' : (m == l && (n == "K5.okAt" || n == "K5.plain")) = true := hq
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hq'
      obtain ⟨-, hn⟩ := hq'
      cases hatt : Dm.pubD.d5.isAtt m with
      | true =>
        rcases hn with rfl | rfl
        · rw [First.pubAll_more_okAt _ _ m hatt] at h0 ⊢
          simp only [hK.1]
          exact h0
        · rw [First.pubAll_more_plain _ _ m hatt] at h0 ⊢
          simp only [hK.2]
          exact h0
      | false =>
        rw [k5_names_else Dm dk Mg₀ m n hn hatt] at h0 ⊢
        exact hb m n x x' h0
  | _ => cases hq

/-- **The binder hK5 at a letter for the meaning beneath.** -/
theorem k5_at_later_of
    (hb : ∀ m n (x x' : ProofFile.InstPub × S), Mg₀.pub (.more (some m) n) x = true →
      Mg₀.pub (.more (some m) n) x' = true)
    (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y q,
      YesOf (blkL Z Bs.G₀ l d X arrs) x x' →
      InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true) (noL l d) x y → k5At l q = true →
      (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)).pub q x = true → (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)).pub q x' = true := by
  intro l _ d X arrs _ x x' y q hy _ hq h0
  obtain ⟨_, rs, gs, hfit, hd⟩ := hy
  have hlen : (rs.map noDigest).length = 2 := by
    rw [List.length_map, Keeps.fit_length _ _ hfit, rounds_blkL]
  exact k5_pub_kept Dm dk Mg₀ hb l q hq x x' (laterK5_blkL Z Bs.G₀ l d X arrs _ _ _ gs hlen hd) h0

/-- **WHAT PAYS THE BINDER hK5 OF k01_fifty_at9 IN k01_fifty_atBase.** -/
theorem k5_at_later (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y q,
      YesOf (blkL Z Bs.G₀ l d X arrs) x x' →
      InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull (flatPlacesOf linksFull true) (noL l d) x y → k5At l q = true →
      (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)).pub q x = true → (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)).pub q x' = true :=
  k5_at_later_of Dm dk mgBase (fun _ _ _ _ h => h) Z Bs

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.laterK5_blkL
#print axioms VerifiableInference.Desc.K1.k5_at_later_of
#print axioms VerifiableInference.Desc.K1.k5_at_later
