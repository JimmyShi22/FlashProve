-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12PaysOfLaw210.lean: The key file's tables, row 2.10
(the proximity test on Omega's group G_omega; the test's second arm): THE JOIN, WITH THE «law» OF
THE WAY BACK AS A LETTER: what the door `keepsAt_k12₂` asks of whoever pays the row (`Pays`,
Johnson/RunOne/Law/K12AtField.lean), from the test's law with nothing promised (`k12_gameVO`,
Johnson/Desc/K12/Coin/GameLabelsOwn.lean), the premise hlaw (in the form of the conclusion of
`back_210`, K12Back210.lean) and the riders (`back_210`, KeyRide23.lean).
Statements and proofs: rows of calls. At the letters of K12Back210.lean: the tables' terms at the
name (baseAt · readAt · On₂ · Cl₂) unfold to these.
Why apart from K12Pays210.lean: this file does not stand over the seam's cone; hlaw is paid there by
one call.
What it is not, first.
  (0) NO EXAMPLE IS SHOWN: that the premises hold together at any state or list of rounds is not
    said.
  (1) A JOIN: it pays no debt on the verifier's state and none on the list of rounds: each is a
    binder, under «∀ a, on 10 a →» where it names the state; hlaw besides under the piece's own
    accepting run.
  (2) THE INVARIANT BEHIND (on₂ … 11) IS A PREMISE HERE (fwd), in the form of
    `fwd_210_name` (K12FwdName.lean).
  (3) «on» IS A LETTER with two ties (hin · hbk): `Pays` has one letter for both borders, and some
    debts have their payer off the history alone: the caller fills on k := On₂ k ∧ (k = 10 → the
    history).
  (4) That the row's look-up at 10 gives a stretch dB :: dt with nothing put behind is the caller's.
  (5) It fills no field of the tables. No soundness is claimed. Nothing on hiding.
Main names.
  `pays_gameVO`: the second arm's law is a law such as `Pays` asks: the like of
    `pays_gameV` (K12PaysGameV.lean; the first arm). General in every letter.
  `smpStay_omega`: an acceptance of the test inside Omega's doors leaves every sampled message
    (`SmpStay`).
  `common_210`: the riders' ten facts (`Common`): five off the piece's acceptance, two off the
    invariant (omegaIn · in₁), three premises (omega · num₁ · evalIn).
  `i2_of_law`: the last clause of `Pays` at the row.
  `pays_of_law`: `Pays`.

-/
import Johnson.RunOne.Law.K12AtField
import Johnson.RunOne.Law.K12RidingStays
import Johnson.RunOne.Law.KeyRide23
import Johnson.RunOne.KeyFillSeed
import Johnson.RunOne.KeyFillBaseAt
import Johnson.Desc.K12.Coin.GameLabelsOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12PaysOfLaw210
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound (Frame strsOf Piece held pieceOf Rest)
open VerifiableInference.Desc.Plain (held_decide piece_decides_at)
open VerifiableInference.Desc.K1 (SmpStay)
open Cb Johnson.Pack OnBytes.Maker
open _root_.Run (ckP bsRound)
open _root_.Iop (Err)
open Johnson.Top.H (csKey)
open Johnson.RunOne Johnson.RunOne.KeyRows23
open H2K.Pub (PayPub)
open Johnson.RunOne.Law.K12AtField (Pays)
open Johnson.RunOne.Law.KeyRide23 (Common ins210)
open Johnson.RunOne.Law.KeyRideTools (LayTies)

/-! ## 1 The second arm's law is a law such as `Pays` asks -/

section
variable {W H S Cl : Type} {Fr : Frame} (π : P12) (R : S → T12 → Prop) (R' : S → T12 → S → Prop)
  (B' : Block (H × S) Cl) (on L : ℕ → (H × S) × Fr.E.Str → Prop) (n : ℕ) (t₁ t₂ ch : ℕ)
  (Lc mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (dB : RDT) (dt : List RDT) (e v₀ : ℕ)
  (εt : Err (uLT (ckP .two) dt)) (x' : Rest (ckP .two) Fr (H × S) W (dB :: dt))

/-- **Nothing is owed of the verifier's state in front: the second arm.** -/
theorem pays_gameVO
    (hA : AtPlaceOwn Fr π (numAt t₁ t₂ ch) Lc mC mS mW rad (numAt t₁ t₂ ch (.own π.nums.free)) dB
      dt εt)
    (hP : PayPub π rad dB.entry.rows v₀) (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0])
    (hlog : dB.entry.logN ≤ 64) (hv : v₀ * (bsRound .two dB.entry dB.kind).w ≤ e)
    (ho : π.nums.ownMask = true) (hPl : ownLabelsB π = true) (hne : H2K.Made.firstNe π = true)
    (hfr : 0 < π.nums.free)
    (hle : Err.le ((e, εt) : Err (uLT (ckP .two) (dB :: dt))) x'.err)
    (h2 : ∀ a τ b, on n a →
      (pieceOf B' (numAt t₁ t₂ ch (.own π.nums.free)) (dB :: dt) [] x').ior.red.out a τ = some b →
      (∃ t t', R a.1.2 t ∧ (R' a.1.2 t' b.1.2 ∧ b.1.1 = a.1.1) ∧
        QO Fr π t₁ t₂ ch rad rd (t, a.2)) →
      on (n + 1) b ∧ (L (n + 1) b → L n a)) :
    Pays Fr π R R' B' on L n (numAt t₁ t₂ ch (.own π.nums.free)) (dB :: dt) [] x' :=
  ⟨(e, εt), _, _,
    k12_gameVO Fr W π t₁ t₂ ch Lc mC mS mW rad rd dB dt (fun _ _ w => w) e v₀ εt hA hP h1 hlog hv ho
      hPl hne hfr,
    hle, fun _ _ _ _ => trivial, h2⟩

end

/-! ## 2 What the riders read -/

/-- **An acceptance of the test inside Omega's doors leaves every sampled message.** -/
theorem smpStay_omega (π : P12) (he : π.early = true) (ha : π.answers = 1) (d d' : St₂)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (Block.inside (Seat.enter (·.gOmega) (fun _ => none)) (proximityTestKind guardedProximityTestParts π : Block T12 Unit)
      Seat.leave).decide d rs gs = .ok d') : SmpStay d.st d'.st ∧ d'.loc = d.loc := by
  obtain ⟨hc, hs, _, hl, _⟩ := seat_leaves (·.gOmega) (fun _ => none) π he ha d d' rs gs h
  refine ⟨⟨hc, fun o x hx hsd => ?_⟩, hl⟩
  have e := hs o (Array.getElem?_eq_some_iff.1 hx).1 (by simp)
  rw [hx] at e
  obtain ⟨x', hx', ex⟩ := Option.map_eq_some_iff.1 e
  exact ⟨x', hx', congrArg (·.1) ex, (congrArg (·.2.1) ex).trans hsd, congrArg (·.2.2) ex⟩

variable {XI Cells Rec : Type} (F : FileDescription XI) (Fr₂ : Frame)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells)
  (recOf : VerifiableInference.Desc.Key.Xi → Option Rec) (orc₁ : ℕ → Option ℕ)
  (tab : Cells → ℕ → ℕ → OnBytes.F) (S : LinShape) (K₁ : KPlan)
  (enc : (Nat → E) → Nat → E) (rad a₀ : Nat) (coll : Strs → Rec → Prop)
  (last₁ : VerifiableInference.Desc.Key.FirstState → Bool) (off₂ : Nat → Nat)

theorem pinned_10 : pinned (open₂ 10) = [0, 2, 4, 5] := by decide

/-- **The riders' ten facts at row 2.10.** -/
theorem common_210 {Cl W : Type} (π : P12) (p : Piece (ckP .two) Fr₂ (P₂ × St₂) Cl W)
    (Bb : Block St₂ Cl) (hb : p.b = held Bb)
    (hal : Coin.Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside
      (Seat.enter (·.gOmega) (fun _ => none)) Seat.leave) Bb)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hSm : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).SmOnly)
    (x y : (P₂ × St₂) × Fr₂.E.Str) (τ : Iop.Tr (uLT (ckP .two) p.ds))
    (hout : p.ior.red.out x τ = some y)
    (hon : on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 10 x)
    (hpins : ∀ k ∈ pinned (open₂ 10), (atSix k).1 < p.base)
    (hm2 : ∃ z : OnBytes.Oracle, x.1.2.st.oracles[2]? = some z ∧ z.sampled = true)
    (hnum₁ : ∀ k ∈ [0, 2], ∀ o, K₁.orc k = some o → ∀ j, K₁.num o = some j → j ∈ [0, 2, 4])
    (heval : ∀ rw, (readers₂ S).eval x.1.1 = some rw →
      ∃ Gr, Means.RowIn ((readers₂ S).st₁ x.1.1) Gr rw ∧
        ∀ o ∈ Gr.members.toList, ∀ j, K₁.num o = some j → j ∈ [0, 2, 4]) :
    Common F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      [0, 2, 4] x.1 y.1 (strsOf Fr₂ x.2) (strsOf Fr₂ y.2) := by
  obtain ⟨_, _, hfree, _⟩ := id (hon.resolve_left (fun h => h trivial))
  have he := H2K.JointK.early_of_planOk π hp
  have ha := H2K.JointK.answers_of_planOk π hp
  have hd := piece_decides_at p x τ y hout
  rw [hb] at hd
  obtain ⟨e1, hB⟩ := held_decide Bb x.1 _ _ y.1 hd
  rw [hal.decide] at hB
  obtain ⟨hstay, hloc⟩ := smpStay_omega π he ha x.1.2 y.1.2 _ _ hB
  have h024 : ∀ k ∈ [0, 2, 4], k ∈ pinned (open₂ 10) := by rw [pinned_10]; decide
  have ride : ∀ k ∈ [0, 2, 4],
      (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp y.1 (atSix k).1
          (atSix k).2 =
        (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp x.1 (atSix k).1
          (atSix k).2 ∧
      wordOf F (strsOf Fr₂ y.2) (atSix k).1 (atSix k).2 =
        wordOf F (strsOf Fr₂ x.2) (atSix k).1 (atSix k).2 := fun k hk =>
    K12RidingStays.riding_stays₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁) F
      Fr₂ hSm (·.gOmega) (fun _ => none) π he ha p Bb hb hal x y τ hout (atSix k).1 (atSix k).2
      (fun o ho => by
        have earr : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).arr (atSix k).1
            (atSix k).2 = k := hfree.arr k (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
          rcases hk with rfl | rfl | rfl <;> decide)
        rw [earr] at ho
        obtain ⟨z, hz, _⟩ := hm2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl
        · exact absurd ho (by simp [orc₂])
        · exact absurd ho (by simp [orc₂])
        · have e2 : o = 2 := by simpa [orc₂] using ho.symm
          subst e2
          exact ⟨(Array.getElem?_eq_some_iff.1 hz).1, by simp⟩)
      (hpins k (h024 k hk))
  exact
    { handed := e1
      smp := fun k hk => (ride k hk).1
      word := fun k hk => (ride k hk).2
      stay := hstay
      omega := hm2
      omegaIn := hfree.samples 4 (by rw [pinned_10]; decide) 2 rfl
      in₁ := hfree.in₁.1
      num₁ := hnum₁
      evalIn := heval
      psi := by rw [hloc] }

/-! ## 3 The last clause of `Pays`, and `Pays` -/

/-- **The last clause of `Pays` at row 2.10, from the «law» of the way back.** -/
theorem i2_of_law {Cl W : Type} (π : P12) (t₁ t₂ : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (on : ℕ → (P₂ × St₂) × Fr₂.E.Str → Prop)
    (hin : ∀ a, on 10 a →
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 10 a)
    (hbk : ∀ b,
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 11 b →
      on 11 b)
    (Bb : Block St₂ Cl)
    (fwd : ∀ a c rs gs,
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 10 a →
      (held Bb : Block (P₂ × St₂) Cl).decide a.1 rs gs = .ok c.1 →
      StrsStay F atSix (open₂ 10) (strsOf Fr₂ a.2) (strsOf Fr₂ c.2) →
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 11 c)
    (hal : Coin.Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside
      (Seat.enter (·.gOmega) (fun _ => none)) Seat.leave) Bb)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hSm : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).SmOnly)
    (base : ℕ) (hpins : ∀ k ∈ pinned (open₂ 10), (atSix k).1 < base)
    (ds : List RDT) (back : List Fmt.RoundView) (x' : Rest (ckP .two) Fr₂ (P₂ × St₂) W ds)
    (hlaw : ∀ a τ b, on 10 a →
      (pieceOf (held Bb) base ds back x').ior.red.out a τ = some b →
      (∃ t t', Seat.enter (·.gOmega) (fun _ => none) a.1.2 = .ok t ∧
        (Seat.leave a.1.2 t' = .ok b.1.2 ∧ b.1.1 = a.1.1) ∧
        QO Fr₂ π t₁ t₂ 1 (fun s => r s.st) rdN (t, a.2)) →
      ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab),
        rw.ins = [KItem.claim 2 "FoldO", .srow 5, .pin 5] →
        KItem.pin 4 ∈ rw.outs ++ rw.ctx →
        (∀ i ∈ rw.outs ++ rw.ctx,
          i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
            (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) b.1
            (strsOf Fr₂ b.2) w) →
        ∀ i ∈ rw.ins,
          i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
            (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) a.1
            (strsOf Fr₂ a.2) (layAt atSix [5] tbl w))
    (hm2 : ∀ a, on 10 a → ∃ x : OnBytes.Oracle, a.1.2.st.oracles[2]? = some x ∧ x.sampled = true)
    (hnum₁ : ∀ k ∈ [0, 2], ∀ o, K₁.orc k = some o → ∀ j, K₁.num o = some j → j ∈ [0, 2, 4])
    (heval : ∀ a, on 10 a → ∀ rw, (readers₂ S).eval a.1.1 = some rw →
      ∃ Gr, Means.RowIn ((readers₂ S).st₁ a.1.1) Gr rw ∧
        ∀ o ∈ Gr.members.toList, ∀ j, K₁.num o = some j → j ∈ [0, 2, 4]) :
    ∀ a τ b, on 10 a → (pieceOf (held Bb) base ds back x').ior.red.out a τ = some b →
      (∃ t t', Seat.enter (·.gOmega) (fun _ => none) a.1.2 = .ok t ∧
        (Seat.leave a.1.2 t' = .ok b.1.2 ∧ b.1.1 = a.1.1) ∧
        QO Fr₂ π t₁ t₂ 1 (fun s => r s.st) rdN (t, a.2)) →
      on (10 + 1) b ∧
        (L₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
        (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad (10 + 1) b →
        L₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
        (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad 10 a) := by
  intro a τ b ha hout hq
  have hon := hin a ha
  obtain ⟨_, _, hfree, _⟩ := id (hon.resolve_left (fun h => h trivial))
  have hSt := strsStay_of_out F Fr₂ atSix (pieceOf (held Bb) base ds back x') (open₂ 10) hpins a b τ
    hout
  refine ⟨hbk b (fwd a b _ _ hon (piece_decides_at _ a τ b hout) hSt), ?_⟩
  rintro ⟨w, hw⟩
  obtain ⟨tbl, law⟩ := hlaw a τ b ha hout hq
  have C := common_210 F Fr₂ decT recOf orc₁ tab S K₁ enc rad a₀ coll last₁ off₂ π
    (pieceOf (held Bb) base ds back x') Bb rfl hal hp hSm a b τ hout hon hpins (hm2 a ha)
    hnum₁ (heval a ha)
  have T : LayTies (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) [5] [0, 2, 4] :=
    { arr := fun k hk => hfree.arr k (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> decide)
      reads := fun v k hk => hfree.reads v k (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> decide)
      off := by decide
      apart := by
        intro k hk k' hk' e
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk hk'
        subst hk
        rcases hk' with rfl | rfl | rfl <;> exact absurd e (by decide) }
  let r10 : KRow := { ins := ins210, ctx := [KItem.pin 4, KItem.srow 4], lays := [5] }
  have e11 : open₂ (10 + 1) = stepOpen (open₂ 10) r10 := by decide
  have hw' : relAt F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
      (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad)
      (stepOpen (open₂ 10) r10) b.1 (strsOf Fr₂ b.2) w := e11 ▸ hw
  exact ⟨layAt atSix [5] tbl w,
    KeyRide23.back_210 OnBytes.Model.Reading.gl enc rad r10 rfl rfl tbl T rfl a.1 b.1
      (strsOf Fr₂ a.2) (strsOf Fr₂ b.2) w C (law r10 w rfl (by simp [r10])) hw'⟩

/-- **`Pays` at row 2.10, from the «law» of the way back.** -/
theorem pays_of_law {Cl W : Type} (π : P12) (t₁ t₂ : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (on : ℕ → (P₂ × St₂) × Fr₂.E.Str → Prop)
    (hin : ∀ a, on 10 a →
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 10 a)
    (hbk : ∀ b,
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 11 b →
      on 11 b)
    (Bb : Block St₂ Cl)
    (fwd : ∀ a c rs gs,
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 10 a →
      (held Bb : Block (P₂ × St₂) Cl).decide a.1 rs gs = .ok c.1 →
      StrsStay F atSix (open₂ 10) (strsOf Fr₂ a.2) (strsOf Fr₂ c.2) →
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 11 c)
    (hal : Coin.Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside
      (Seat.enter (·.gOmega) (fun _ => none)) Seat.leave) Bb)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hSm : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).SmOnly)
    (base : ℕ) (hpins : ∀ k ∈ pinned (open₂ 10), (atSix k).1 < base)
    (dB : RDT) (dt : List RDT) (x' : Rest (ckP .two) Fr₂ (P₂ × St₂) W (dB :: dt))
    (hlaw : ∀ a τ b, on 10 a →
      (pieceOf (held Bb) base (dB :: dt) [] x').ior.red.out a τ = some b →
      (∃ t t', Seat.enter (·.gOmega) (fun _ => none) a.1.2 = .ok t ∧
        (Seat.leave a.1.2 t' = .ok b.1.2 ∧ b.1.1 = a.1.1) ∧
        QO Fr₂ π t₁ t₂ 1 (fun s => r s.st) rdN (t, a.2)) →
      ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab),
        rw.ins = [KItem.claim 2 "FoldO", .srow 5, .pin 5] →
        KItem.pin 4 ∈ rw.outs ++ rw.ctx →
        (∀ i ∈ rw.outs ++ rw.ctx,
          i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
            (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) b.1
            (strsOf Fr₂ b.2) w) →
        ∀ i ∈ rw.ins,
          i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
            (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) a.1
            (strsOf Fr₂ a.2) (layAt atSix [5] tbl w))
    (hm2 : ∀ a, on 10 a → ∃ x : OnBytes.Oracle, a.1.2.st.oracles[2]? = some x ∧ x.sampled = true)
    (hnum₁ : ∀ k ∈ [0, 2], ∀ o, K₁.orc k = some o → ∀ j, K₁.num o = some j → j ∈ [0, 2, 4])
    (heval : ∀ a, on 10 a → ∀ rw, (readers₂ S).eval a.1.1 = some rw →
      ∃ Gr, Means.RowIn ((readers₂ S).st₁ a.1.1) Gr rw ∧
        ∀ o ∈ Gr.members.toList, ∀ j, K₁.num o = some j → j ∈ [0, 2, 4])
    (hbase : base = numAt t₁ t₂ 1 (.own π.nums.free))
    (Lc mC mS mW : Sg → ℕ → ℕ) (e v₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
    (hA : AtPlaceOwn Fr₂ π (numAt t₁ t₂ 1) Lc mC mS mW (fun s => r s.st)
      (numAt t₁ t₂ 1 (.own π.nums.free)) dB dt εt)
    (hP : PayPub π (fun s => r s.st) dB.entry.rows v₀)
    (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0]) (hlog64 : dB.entry.logN ≤ 64)
    (hv : v₀ * (bsRound .two dB.entry dB.kind).w ≤ e)
    (ho : π.nums.ownMask = true) (hPl : ownLabelsB π = true) (hne : H2K.Made.firstNe π = true)
    (hfr : 0 < π.nums.free)
    (hle : Err.le ((e, εt) : Err (uLT (ckP .two) (dB :: dt))) x'.err) :
    Pays Fr₂ π (fun s t => Seat.enter (·.gOmega) (fun _ => none) s = .ok t)
      (fun s t s' => Seat.leave s t = .ok s') (held Bb : Block (P₂ × St₂) Cl) on
      (L₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
        (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) 10 base (dB :: dt) []
      x' := by
  subst hbase
  exact pays_gameVO π _ _ _ on _ 10 t₁ t₂ 1 Lc mC mS mW (fun s => r s.st) rdN dB
    dt e v₀ εt x' hA hP h1 hlog64 hv ho hPl hne hfr hle
    (i2_of_law F Fr₂ decT recOf orc₁ tab S K₁ enc rad a₀ coll last₁ off₂ π t₁ t₂ r rdN on hin hbk Bb
      fwd hal hp hSm _ hpins (dB :: dt) [] x' hlaw hm2 hnum₁ heval)

end Johnson.RunOne.Law.K12PaysOfLaw210

#print axioms Johnson.RunOne.Law.K12PaysOfLaw210.pays_gameVO
#print axioms Johnson.RunOne.Law.K12PaysOfLaw210.smpStay_omega
#print axioms Johnson.RunOne.Law.K12PaysOfLaw210.common_210
#print axioms Johnson.RunOne.Law.K12PaysOfLaw210.i2_of_law
#print axioms Johnson.RunOne.Law.K12PaysOfLaw210.pays_of_law
