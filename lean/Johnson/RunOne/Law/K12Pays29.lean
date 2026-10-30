-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Pays29.lean: The key file's
tables, row 2.9 (the proximity test on the folded row's group G_u): THE JOIN: `Pays`
(K12AtField.lean) AT THE ROW. Statements and proofs; each proof is calls. After the text at row 2.10
(K12PaysOfLaw210.lean), at
this
row's letters; stated at K12Back29.lean's letters (general in F · Fr₂ · decT · recOf · orc₁ · tab ·
S · K₁ …): the tables' terms at the name unfold to these.
WHAT IT IS NOT, FIRST. IT IS A JOIN: IT MOVES NO DEBT BUT «law», «ride» AND THE RIDING MEMBERS'
STAYING, WHICH IT SPENDS. The promise's half is A PREMISE (fwd), in the form of fwd_29_name
(K12FwdName.lean). `CoreLeft` (left) stays the heaviest premise. It pays no field of the tables. No
soundness is claimed. Nothing
on
hiding.
  `stays_U`: an «accept» of the test inside U's doors leaves every sampled message, the chain's own
    letters and every other group (`seat_leaves`, SamplesThrough.lean), where the first mask is not
    sampled.
  `rides_29`: the out-of-domain (OOD) sample and the committed word at the seats of the messages 0 ·
  2 ·
    4 · 5 stay across the piece's «accept» (`riding_stays₂`).
  `common_29`: `Common` (KeyRide23.lean) at ks := [0, 2, 4, 5].
  `i2_of_law29`: the last clause of `Pays`, from the «law» of the way back as a letter (hlaw:
    `back_29`'s conclusion, sign for sign): first half: `piece_decides_at` · `strsStay_of_out` ·
    fwd; second half: `back_29` (KeyRide23.lean: relAt_back_to with ride_29 laid in).
  `pays_of_law29`: `Pays`, by `pays_gameV` (K12PaysGameV.lean: the first arm's law).
  `pays_29`: the same with hlaw paid by `back_29` (K12Back29.lean): ITS
  DEBTS STAND UNDER THE
    PIECE's ACCEPTING RUN, so that their payer can spend it.
ALSO: `shape29_facts` · `unsampled_of_msgIs` ·
`Debts29S` · `pays_29S`: `Pays` at the row
OVER `back_29S` (K12Members29.lean): «left» member by member; eight binders of `pays_29` fall to the
invariant's own test on the state's shape. THIS ROW's «on» IS ITS OWN LETTER: nobody may chain this
row's `Pays` and row 2.10's at one «on». The claim 2 "record" of the tables is the claim on the OOD
sample's rows. hal is `pays_gameV`'s to pay (halC_29: declared nowhere in this library);
hi · hSm · hlog · told · h1 h2 lie in KeyAt2932Scope.lean.
-/
import Johnson.RunOne.Law.K12PaysGameV
import Johnson.RunOne.Law.K12Back29
import Johnson.RunOne.Law.KeyRide23
import Johnson.RunOne.Law.K12Members29
import Johnson.RunOne.Law.K12Law32Core

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12Pays29
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound (Frame strsOf Piece held pieceOf Rest smpSt)
open H2K.Pin (strOf layOf)
open H2K.Pub (sgOf)
open VerifiableInference.Desc.Plain (held_decide piece_decides_at)
open VerifiableInference.Desc.K1 (SmpStay)
open Cb Johnson.Pack OnBytes.Maker
open _root_.Run (ckP bsRound)
open _root_.Iop (Err)
open Johnson.Top.H (csKey)
open Johnson.RunOne Johnson.RunOne.KeyRows23
open LPFD.CandLaid
open H2K.Pin (tabP NTuple)
open H2K.Pub (johOk batV0)
open H2K.First (batOneOk)
open Johnson.RunOne.Law.K12AtField (Pays)
open Johnson.RunOne.Law.K12Law29Core (i3 i5)
open Johnson.RunOne.Law.KeyRide23 (Common ins29 pinned29)
open Johnson.RunOne.Law.KeyRideTools (LayTies)

/-! ## 1 What the riders read -/

/-- **An «accept» of the test inside U's doors leaves what it does not test.** -/
theorem stays_U (π : P12) (he : π.early = true) (ha : π.answers = 1) (d d' : St₂)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (Block.inside (Seat.enter (·.gU) (·.firstMask)) (proximityTestKind guardedProximityTestParts π : Block T12 Unit)
      Seat.leave).decide d rs gs = .ok d')
    (hmk : ∀ o x, d.loc.firstMask = some o → d.st.oracles[o]? = some x → x.sampled = false) :
    SmpStay d.st d'.st ∧ d'.loc = d.loc ∧
      ∀ q, q < d.st.groups.size → q ≠ d.loc.gU → d'.st.groups[q]? = d.st.groups[q]? := by
  obtain ⟨hc, hs, hg, hl, _⟩ := seat_leaves (·.gU) (·.firstMask) π he ha d d' rs gs h
  refine ⟨⟨hc, fun o x hx hsd => ?_⟩, hl, hg⟩
  have e := hs o (Array.getElem?_eq_some_iff.1 hx).1 (fun hm => by
    rw [hmk o x hm hx] at hsd
    exact absurd hsd (by simp))
  rw [hx] at e
  obtain ⟨x', hx', ex⟩ := Option.map_eq_some_iff.1 e
  exact ⟨x', hx', congrArg (·.1) ex, (congrArg (·.2.1) ex).trans hsd, congrArg (·.2.2) ex⟩

variable {XI Cells Rec : Type} (F : FileDescription XI) (Fr₂ : Frame)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells)
  (recOf : VerifiableInference.Desc.Key.Xi → Option Rec) (orc₁ : ℕ → Option ℕ)
  (tab : Cells → ℕ → ℕ → OnBytes.F) (S : LinShape) (K₁ : KPlan)
  (enc : (Nat → E) → Nat → E) (rad a₀ : Nat) (coll : Strs → Rec → Prop)
  (last₁ : VerifiableInference.Desc.Key.FirstState → Bool) (off₂ : Nat → Nat)

/-- **The four riding messages' OOD samples and committed words stay.** -/
theorem rides_29 {Cl W : Type} (π : P12) (p : Piece (ckP .two) Fr₂ (P₂ × St₂) Cl W)
    (Bb : Block St₂ Cl) (hb : p.b = held Bb)
    (hal : Coin.Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside
      (Seat.enter (·.gU) (·.firstMask)) Seat.leave) Bb)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hSm : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).SmOnly)
    (x y : (P₂ × St₂) × Fr₂.E.Str) (τ : Iop.Tr (uLT (ckP .two) p.ds))
    (hout : p.ior.red.out x τ = some y)
    (hon : on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 9 x)
    (hpins : ∀ k ∈ pinned (open₂ 9), (atSix k).1 < p.base)
    (hm2 : ∃ z : OnBytes.Oracle, x.1.2.st.oracles[2]? = some z ∧ z.sampled = true)
    (hm3 : ∃ z : OnBytes.Oracle, x.1.2.st.oracles[3]? = some z ∧ z.sampled = true)
    (hmk : ∀ o z, x.1.2.loc.firstMask = some o → x.1.2.st.oracles[o]? = some z →
      z.sampled = false) :
    ∀ k ∈ [0, 2, 4, 5],
      (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp y.1 (atSix k).1
          (atSix k).2 =
        (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp x.1 (atSix k).1
          (atSix k).2 ∧
      wordOf F (strsOf Fr₂ y.2) (atSix k).1 (atSix k).2 =
        wordOf F (strsOf Fr₂ x.2) (atSix k).1 (atSix k).2 := by
  obtain ⟨_, _, hfree, _⟩ := id (hon.resolve_left (fun h => h trivial))
  have there : ∀ o, (∃ z : OnBytes.Oracle, x.1.2.st.oracles[o]? = some z ∧ z.sampled = true) →
      o < x.1.2.st.oracles.size ∧ x.1.2.loc.firstMask ≠ some o := by
    rintro o ⟨z, hz, hs⟩
    refine ⟨(Array.getElem?_eq_some_iff.1 hz).1, fun hm => ?_⟩
    rw [hmk o z hm hz] at hs
    exact absurd hs (by simp)
  intro k hk
  refine K12RidingStays.riding_stays₂
    (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁) F Fr₂ hSm (·.gU)
    (·.firstMask) π (H2K.JointK.early_of_planOk π hp)
    (H2K.JointK.answers_of_planOk π hp) p Bb hb hal x y τ hout (atSix k).1 (atSix k).2
    (fun o ho => ?_) (hpins k (by
      rw [pinned29]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
      omega))
  have earr : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).arr (atSix k).1
      (atSix k).2 = k := hfree.arr k (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> decide)
  rw [earr] at ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact absurd ho (by simp [orc₂])
  · exact absurd ho (by simp [orc₂])
  · have e2 : o = 2 := by simpa [orc₂] using ho.symm
    subst e2
    exact there 2 hm2
  · have e3 : o = 3 := by simpa [orc₂] using ho.symm
    subst e3
    exact there 3 hm3

/-- **The riders' ten facts at row 2.9.** -/
theorem common_29 {Cl W : Type} (π : P12) (p : Piece (ckP .two) Fr₂ (P₂ × St₂) Cl W)
    (Bb : Block St₂ Cl) (hb : p.b = held Bb)
    (hal : Coin.Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside
      (Seat.enter (·.gU) (·.firstMask)) Seat.leave) Bb)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hSm : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).SmOnly)
    (x y : (P₂ × St₂) × Fr₂.E.Str) (τ : Iop.Tr (uLT (ckP .two) p.ds))
    (hout : p.ior.red.out x τ = some y)
    (hon : on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 9 x)
    (hpins : ∀ k ∈ pinned (open₂ 9), (atSix k).1 < p.base)
    (hm2 : ∃ z : OnBytes.Oracle, x.1.2.st.oracles[2]? = some z ∧ z.sampled = true)
    (hm3 : ∃ z : OnBytes.Oracle, x.1.2.st.oracles[3]? = some z ∧ z.sampled = true)
    (hmk : ∀ o z, x.1.2.loc.firstMask = some o → x.1.2.st.oracles[o]? = some z →
      z.sampled = false)
    (hnum₁ : ∀ k ∈ [0, 2], ∀ o, K₁.orc k = some o → ∀ j, K₁.num o = some j → j ∈ [0, 2, 4, 5])
    (heval : ∀ rw, (readers₂ S).eval x.1.1 = some rw →
      ∃ Gr, Means.RowIn ((readers₂ S).st₁ x.1.1) Gr rw ∧
        ∀ o ∈ Gr.members.toList, ∀ j, K₁.num o = some j → j ∈ [0, 2, 4, 5]) :
    Common F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
        [0, 2, 4, 5] x.1 y.1 (strsOf Fr₂ x.2) (strsOf Fr₂ y.2) ∧
      y.1.2.loc = x.1.2.loc ∧
      ∀ q, q < x.1.2.st.groups.size → q ≠ x.1.2.loc.gU →
        y.1.2.st.groups[q]? = x.1.2.st.groups[q]? := by
  obtain ⟨_, _, hfree, _⟩ := id (hon.resolve_left (fun h => h trivial))
  have hd := piece_decides_at p x τ y hout
  rw [hb] at hd
  obtain ⟨e1, hB⟩ := held_decide Bb x.1 _ _ y.1 hd
  rw [hal.decide] at hB
  obtain ⟨hstay, hloc, hgr⟩ := stays_U π (H2K.JointK.early_of_planOk π hp)
    (H2K.JointK.answers_of_planOk π hp) x.1.2 y.1.2 _ _ hB hmk
  have ride := rides_29 F Fr₂ decT recOf orc₁ tab S K₁ enc rad a₀ coll last₁ off₂ π p Bb hb hal hp
    hSm x y τ hout hon hpins hm2 hm3 hmk
  have up : ∀ k ∈ [0, 2, 4], k ∈ [0, 2, 4, 5] := by decide
  exact ⟨
    { handed := e1
      smp := fun k hk => (ride k (up k hk)).1
      word := fun k hk => (ride k (up k hk)).2
      stay := hstay
      omega := hm2
      omegaIn := hfree.samples 4 (by rw [pinned29]; decide) 2 rfl
      in₁ := hfree.in₁.1
      num₁ := hnum₁
      evalIn := heval
      psi := by rw [hloc] }, hloc, hgr⟩

/-! ## 2 The last clause of `Pays`, and `Pays` -/

/-- **The last clause of `Pays` at row 2.9, from the «law» of the way back.** -/
theorem i2_of_law29 {Cl W : Type} (π : P12) (lo : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (on : ℕ → (P₂ × St₂) × Fr₂.E.Str → Prop)
    (hin : ∀ a, on 9 a →
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 9 a)
    (hbk : ∀ b,
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 10 b →
      on 10 b)
    (Bb : Block St₂ Cl)
    (fwd : ∀ a c rs gs,
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 9 a →
      (held Bb : Block (P₂ × St₂) Cl).decide a.1 rs gs = .ok c.1 →
      StrsStay F atSix (open₂ 9) (strsOf Fr₂ a.2) (strsOf Fr₂ c.2) →
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 10 c)
    (hal : Coin.Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside
      (Seat.enter (·.gU) (·.firstMask)) Seat.leave) Bb)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hSm : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).SmOnly)
    (base : ℕ) (hpins : ∀ k ∈ pinned (open₂ 9), (atSix k).1 < base)
    (ds : List RDT) (back : List Fmt.RoundView) (x' : Rest (ckP .two) Fr₂ (P₂ × St₂) W ds)
    (hlaw : ∀ a τ b, on 9 a →
      (pieceOf (held Bb) base ds back x').ior.red.out a τ = some b →
      (∃ t t', Seat.enter (·.gU) (·.firstMask) a.1.2 = .ok t ∧
        (Seat.leave a.1.2 t' = .ok b.1.2 ∧ b.1.1 = a.1.1) ∧
        QN π (NTuple Fr₂ π (nuOf π (nlAt π lo) t) (fun s => r s.st) rdN) (t, a.2)) →
      ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab),
        rw.ins = [KItem.claim 2 "record", .claim 2 "columns", .claim 2 "FoldU", .srow 3, .pin 3] →
        KItem.pin 5 ∈ rw.outs ++ rw.ctx →
        (∀ i ∈ rw.outs ++ rw.ctx,
          i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
            (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) b.1
            (strsOf Fr₂ b.2) w) →
        ∀ i ∈ rw.ins,
          i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
            (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) a.1
            (strsOf Fr₂ a.2) (layAt atSix [3] tbl w))
    (hm2 : ∀ a, on 9 a → ∃ x : OnBytes.Oracle, a.1.2.st.oracles[2]? = some x ∧ x.sampled = true)
    (hm3 : ∀ a, on 9 a → ∃ x : OnBytes.Oracle, a.1.2.st.oracles[3]? = some x ∧ x.sampled = true)
    (hmk : ∀ a, on 9 a → ∀ o x, a.1.2.loc.firstMask = some o → a.1.2.st.oracles[o]? = some x →
      x.sampled = false)
    (htwo : ∀ a, on 9 a → a.1.2.loc.gOmega ≠ a.1.2.loc.gU ∧
      a.1.2.loc.gOmega < a.1.2.st.groups.size)
    (hmemO : ∀ a, on 9 a → ∀ G₀, a.1.2.st.groups[a.1.2.loc.gOmega]? = some G₀ →
      ∀ o ∈ G₀.members.toList, o = 2 ∨ o = 3)
    (hnum₁ : ∀ k ∈ [0, 2], ∀ o, K₁.orc k = some o → ∀ j, K₁.num o = some j → j ∈ [0, 2, 4, 5])
    (heval : ∀ a, on 9 a → ∀ rw, (readers₂ S).eval a.1.1 = some rw →
      ∃ Gr, Means.RowIn ((readers₂ S).st₁ a.1.1) Gr rw ∧
        ∀ o ∈ Gr.members.toList, ∀ j, K₁.num o = some j → j ∈ [0, 2, 4, 5]) :
    ∀ a τ b, on 9 a → (pieceOf (held Bb) base ds back x').ior.red.out a τ = some b →
      (∃ t t', Seat.enter (·.gU) (·.firstMask) a.1.2 = .ok t ∧
        (Seat.leave a.1.2 t' = .ok b.1.2 ∧ b.1.1 = a.1.1) ∧
        QN π (NTuple Fr₂ π (nuOf π (nlAt π lo) t) (fun s => r s.st) rdN) (t, a.2)) →
      on (9 + 1) b ∧
        (L₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
        (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad (9 + 1) b →
        L₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
        (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad 9 a) := by
  intro a τ b ha hout hq
  have hon := hin a ha
  obtain ⟨_, _, hfree, _⟩ := id (hon.resolve_left (fun h => h trivial))
  have hSt := strsStay_of_out F Fr₂ atSix (pieceOf (held Bb) base ds back x') (open₂ 9) hpins a b τ
    hout
  refine ⟨hbk b (fwd a b _ _ hon (piece_decides_at _ a τ b hout) hSt), ?_⟩
  rintro ⟨w, hw⟩
  obtain ⟨tbl, law⟩ := hlaw a τ b ha hout hq
  obtain ⟨C, hloc, hgr⟩ := common_29 F Fr₂ decT recOf orc₁ tab S K₁ enc rad a₀ coll last₁ off₂ π
    (pieceOf (held Bb) base ds back x') Bb rfl hal hp hSm a b τ hout hon hpins (hm2 a ha) (hm3 a ha)
    (hmk a ha) hnum₁ (heval a ha)
  have r5 := rides_29 F Fr₂ decT recOf orc₁ tab S K₁ enc rad a₀ coll last₁ off₂ π
    (pieceOf (held Bb) base ds back x') Bb rfl hal hp hSm a b τ hout hon hpins (hm2 a ha) (hm3 a ha)
    (hmk a ha) 5 (by decide)
  have T : LayTies (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) [3] [0, 2, 4, 5] :=
    { arr := fun k hk => hfree.arr k (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> decide)
      reads := fun v k hk => hfree.reads v k (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> decide)
      off := by decide
      apart := by
        intro k hk k' hk' e
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk hk'
        subst hk
        rcases hk' with rfl | rfl | rfl | rfl <;> exact absurd e (by decide) }
  let r9 : KRow := { ins := ins29, ctx := [KItem.pin 5, KItem.srow 5], lays := [3] }
  have e10 : open₂ (9 + 1) = stepOpen (open₂ 9) r9 := by decide
  have hw' : relAt F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
      (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad)
      (stepOpen (open₂ 9) r9) b.1 (strsOf Fr₂ b.2) w := e10 ▸ hw
  obtain ⟨hne, hlt⟩ := htwo a ha
  exact ⟨layAt atSix [3] tbl w,
    KeyRide23.back_29 OnBytes.Model.Reading.gl enc rad r9 rfl rfl tbl T rfl a.1 b.1
      (strsOf Fr₂ a.2) (strsOf Fr₂ b.2) w C r5.1 r5.2 (hm3 a ha)
      (hfree.samples 5 (by rw [pinned29]; decide) 3 rfl) (by rw [hloc])
      (fun G' hG' => ⟨G', by rw [← hgr _ hlt hne]; exact hG', rfl⟩)
      (hfree.rowsIn (by decide)).2 (hmemO a ha) (law r9 w rfl (by simp [r9])) hw'⟩

/-- **`Pays` at row 2.9, from the «law» of the way back.** -/
theorem pays_of_law29 {Cl W : Type} (π : P12) (lo : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (on : ℕ → (P₂ × St₂) × Fr₂.E.Str → Prop)
    (hin : ∀ a, on 9 a →
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 9 a)
    (hbk : ∀ b,
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 10 b →
      on 10 b)
    (Bb : Block St₂ Cl)
    (fwd : ∀ a c rs gs,
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 9 a →
      (held Bb : Block (P₂ × St₂) Cl).decide a.1 rs gs = .ok c.1 →
      StrsStay F atSix (open₂ 9) (strsOf Fr₂ a.2) (strsOf Fr₂ c.2) →
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 10 c)
    (hal : Coin.Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside
      (Seat.enter (·.gU) (·.firstMask)) Seat.leave) Bb)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hSm : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).SmOnly)
    (base : ℕ) (hpins : ∀ k ∈ pinned (open₂ 9), (atSix k).1 < base)
    (dB : RDT) (dt : List RDT) (x' : Rest (ckP .two) Fr₂ (P₂ × St₂) W (dB :: dt))
    (hlaw : ∀ a τ b, on 9 a →
      (pieceOf (held Bb) base (dB :: dt) [] x').ior.red.out a τ = some b →
      (∃ t t', Seat.enter (·.gU) (·.firstMask) a.1.2 = .ok t ∧
        (Seat.leave a.1.2 t' = .ok b.1.2 ∧ b.1.1 = a.1.1) ∧
        QN π (NTuple Fr₂ π (nuOf π (nlAt π lo) t) (fun s => r s.st) rdN) (t, a.2)) →
      ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab),
        rw.ins = [KItem.claim 2 "record", .claim 2 "columns", .claim 2 "FoldU", .srow 3, .pin 3] →
        KItem.pin 5 ∈ rw.outs ++ rw.ctx →
        (∀ i ∈ rw.outs ++ rw.ctx,
          i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
            (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) b.1
            (strsOf Fr₂ b.2) w) →
        ∀ i ∈ rw.ins,
          i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
            (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) a.1
            (strsOf Fr₂ a.2) (layAt atSix [3] tbl w))
    (hm2 : ∀ a, on 9 a → ∃ x : OnBytes.Oracle, a.1.2.st.oracles[2]? = some x ∧ x.sampled = true)
    (hm3 : ∀ a, on 9 a → ∃ x : OnBytes.Oracle, a.1.2.st.oracles[3]? = some x ∧ x.sampled = true)
    (hmk : ∀ a, on 9 a → ∀ o x, a.1.2.loc.firstMask = some o → a.1.2.st.oracles[o]? = some x →
      x.sampled = false)
    (htwo : ∀ a, on 9 a → a.1.2.loc.gOmega ≠ a.1.2.loc.gU ∧
      a.1.2.loc.gOmega < a.1.2.st.groups.size)
    (hmemO : ∀ a, on 9 a → ∀ G₀, a.1.2.st.groups[a.1.2.loc.gOmega]? = some G₀ →
      ∀ o ∈ G₀.members.toList, o = 2 ∨ o = 3)
    (hnum₁ : ∀ k ∈ [0, 2], ∀ o, K₁.orc k = some o → ∀ j, K₁.num o = some j → j ∈ [0, 2, 4, 5])
    (heval : ∀ a, on 9 a → ∀ rw, (readers₂ S).eval a.1.1 = some rw →
      ∃ Gr, Means.RowIn ((readers₂ S).st₁ a.1.1) Gr rw ∧
        ∀ o ∈ Gr.members.toList, ∀ j, K₁.num o = some j → j ∈ [0, 2, 4, 5])
    (num : Fmt.TreeSource → ℕ)
    (hA : AtPlace Fr₂ π num Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) base dB dt (errJ π r dt))
    (hj : johOk π r = true) (hb1 : batOneOk π = true) (hpl : LabelsPub π num (nlAt π lo) base)
    (hle : Err.le ((batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) :
      Err (uLT (ckP .two) (dB :: dt))) x'.err) :
    Pays Fr₂ π (fun s t => Seat.enter (·.gU) (·.firstMask) s = .ok t)
      (fun s t s' => Seat.leave s t = .ok s') (held Bb : Block (P₂ × St₂) Cl) on
      (L₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
        (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) 9 base (dB :: dt) []
      x' :=
  K12PaysGameV.pays_gameV π _ _ _ on _ 9 num (nlAt π lo) Sg.lstJ Sg.flC Sg.flZ Sg.flZ
    (fun s => r s.st) rdN base dB dt _ (errJ π r dt) x' r hA (fun _ => rfl) hj hb1 (Nat.le_refl _)
    hpl hle
    (i2_of_law29 F Fr₂ decT recOf orc₁ tab S K₁ enc rad a₀ coll last₁ off₂ π lo r rdN on hin hbk Bb
      fwd hal hp hSm base hpins (dB :: dt) [] x' hlaw hm2 hm3 hmk htwo hmemO hnum₁ heval)

/-! ## 3 With the «law» paid by `back_29` -/

/-- **What `back_29` owes of the verifier's state in front**, in one proposition: `CoreLeft` behind
the door in · the OOD seeds' tie and «every leaf is shown» at the group's two members · no open row
is marked as a sample row · the group's members and the count of its open rows · message 0 is
sampled and has sample rows. -/
def Debts29 (π : P12) (lo : ℕ) (r : Fmt.M1.Stage → ℕ)
    (smp : (P₂ × St₂) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem) (a : (P₂ × St₂) × Fr₂.E.Str) : Prop :=
  (∀ t, Seat.enter (·.gU) (·.firstMask) a.1.2 = .ok t →
    CoreLeft csKey F Fr₂ π (fun z => lo + z) (fun s => r s.st) smp mem
      (fun z => z = ⟨sixS, i3⟩ ∨ z = ⟨sixS, i5⟩) t a.2 a.1 (strsOf Fr₂ a.2)) ∧
  (∀ i : Fin six.length, i = i3 ∨ i = i5 → ∀ σ : (OmAt csKey six i).Smp,
    smp a.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
      (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
      seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i a.1 ρ σ.2) ∧
  (∀ i : Fin six.length, i = i3 ∨ i = i5 →
    Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ a.2) i) ∧
  Means.OpenKinds a.1.2.st ∧
  (∀ G0, a.1.2.st.groups[a.1.2.loc.gU]? = some G0 →
    (∀ o ∈ G0.members.toList, o = 0 ∨ o = 3) ∧ 0 ∈ G0.members.toList ∧
      S.fold.index.answers + S.fold.columns + 1 ≤ G0.rows.size) ∧
  ∃ x0 : OnBytes.Oracle, a.1.2.st.oracles[0]? = some x0 ∧ x0.sampled = true ∧
    x0.sampleRows.size ≠ 0

/-- **`Pays` at row 2.9.** The debts on the verifier's state stand under the piece's accepting
run. -/
theorem pays_29 {Cl W : Type} (π : P12) (lo : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : (P₂ × St₂) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (on : ℕ → (P₂ × St₂) × Fr₂.E.Str → Prop)
    (hin : ∀ a, on 9 a →
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 9 a)
    (hbk : ∀ b,
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 10 b →
      on 10 b)
    (Bb : Block St₂ Cl)
    (fwd : ∀ a c rs gs,
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 9 a →
      (held Bb : Block (P₂ × St₂) Cl).decide a.1 rs gs = .ok c.1 →
      StrsStay F atSix (open₂ 9) (strsOf Fr₂ a.2) (strsOf Fr₂ c.2) →
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 10 c)
    (hal : Coin.Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside
      (Seat.enter (·.gU) (·.firstMask)) Seat.leave) Bb)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hSm : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).SmOnly)
    (base : ℕ) (hpins : ∀ k ∈ pinned (open₂ 9), (atSix k).1 < base)
    (dB : RDT) (dt : List RDT) (x' : Rest (ckP .two) Fr₂ (P₂ × St₂) W (dB :: dt))
    (hm2 : ∀ a, on 9 a → ∃ x : OnBytes.Oracle, a.1.2.st.oracles[2]? = some x ∧ x.sampled = true)
    (hm3 : ∀ a, on 9 a → ∃ x : OnBytes.Oracle, a.1.2.st.oracles[3]? = some x ∧ x.sampled = true)
    (hmk : ∀ a, on 9 a → ∀ o x, a.1.2.loc.firstMask = some o → a.1.2.st.oracles[o]? = some x →
      x.sampled = false)
    (htwo : ∀ a, on 9 a → a.1.2.loc.gOmega ≠ a.1.2.loc.gU ∧
      a.1.2.loc.gOmega < a.1.2.st.groups.size)
    (hmemO : ∀ a, on 9 a → ∀ G₀, a.1.2.st.groups[a.1.2.loc.gOmega]? = some G₀ →
      ∀ o ∈ G₀.members.toList, o = 2 ∨ o = 3)
    (hnum₁ : ∀ k ∈ [0, 2], ∀ o, K₁.orc k = some o → ∀ j, K₁.num o = some j → j ∈ [0, 2, 4, 5])
    (heval : ∀ a, on 9 a → ∀ rw, (readers₂ S).eval a.1.1 = some rw →
      ∃ Gr, Means.RowIn ((readers₂ S).st₁ a.1.1) Gr rw ∧
        ∀ o ∈ Gr.members.toList, ∀ j, K₁.num o = some j → j ∈ [0, 2, 4, 5])
    (num : Fmt.TreeSource → ℕ)
    (hA : AtPlace Fr₂ π num Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) base dB dt (errJ π r dt))
    (hj : johOk π r = true) (hb1 : batOneOk π = true) (hpl : LabelsPub π num (nlAt π lo) base)
    (hle : Err.le ((batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) :
      Err (uLT (ckP .two) (dB :: dt))) x'.err)
    (hft : π.nums.firstTree = 0)
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂)
    (hlog : ∀ i : Fin six.length, i = i3 ∨ i = i5 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i3 ∨ i = i5 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hmem0 : mem 0 = some ⟨sixS, i3⟩) (hmem3 : mem 3 = some ⟨sixS, i5⟩)
    (h1 : S.fold.index.answers ≠ 0) (h2 : S.fold.columns ≠ 0)
    (hE : ∀ a τ b, on 9 a →
      (pieceOf (held Bb) base (dB :: dt) [] x').ior.red.out a τ = some b →
      Debts29 F Fr₂ orc₁ S π lo r smp mem a) :
    Pays Fr₂ π (fun s t => Seat.enter (·.gU) (·.firstMask) s = .ok t)
      (fun s t s' => Seat.leave s t = .ok s') (held Bb : Block (P₂ × St₂) Cl) on
      (L₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
        (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) 9 base (dB :: dt) []
      x' := by
  refine pays_of_law29 F Fr₂ decT recOf orc₁ tab S K₁ enc rad a₀ coll last₁ off₂ π lo r rdN on hin
    hbk Bb fwd hal hp hSm base hpins dB dt x' (fun a τ b ha hout hq => ?_) hm2 hm3 hmk htwo hmemO
    hnum₁ heval num hA hj hb1 hpl hle
  obtain ⟨left, hsm, hsh, hK, hgrp, x0, hx, hsmd, hss⟩ := hE a τ b ha hout
  have hon := hin a ha
  obtain ⟨_, _, hfree, _⟩ := id (hon.resolve_left (fun h => h trivial))
  exact K12Back29.back_29 F Fr₂ decT recOf orc₁ tab S K₁ enc rad a₀ coll last₁ off₂ π lo r rdN smp
    mem rd hrd (pieceOf (held Bb) base (dB :: dt) [] x') Bb rfl hal a b τ hout hq hft hon hj hp left
    hi hlog told hsm hsh hmem0 hmem3 hK hgrp h1 h2 x0 hx hsmd hss hSm
    (fun o ho => by
      have earr : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).arr (atSix 5).1
          (atSix 5).2 = 5 := hfree.arr 5 (by decide)
      rw [earr] at ho
      have e3 : o = 3 := by simpa [orc₂] using ho.symm
      subst e3
      obtain ⟨z, hz, hs⟩ := hm3 a ha
      refine ⟨(Array.getElem?_eq_some_iff.1 hz).1, fun hm => ?_⟩
      rw [hmk a ha 3 z hm hz] at hs
      exact absurd hs (by simp))
    (hpins 5 (by rw [pinned29]; decide))

/-! ## 4 With «left» member by member, and the state's shape read off the invariant -/

/-- **What the invariant's test on the state's shape says at border 9** (the tables' files' shape₂,
Johnson/RunOne/BorderShapes/LKFU/Shape23.lean), opened once: the two groups' numbers · the first mask's
number · messages 0 · 2 · 3 are sampled, with a sample rows each; message 1 is not · G_u's and
G_omega's members and open rows · two groups. After `shape32_facts`; opened in
those files' own way (`guard_29`, Johnson/RunOne/KeyBookAtSeats.lean): a bare simp over all eighteen
clauses ran out of time here. -/
theorem shape29_facts (S : LinShape) (a : ℕ) (d : St₂)
    (h : LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 9 d) = true) :
    d.loc.gU = 0 ∧ d.loc.gOmega = 1 ∧ d.loc.firstMask = some 1 ∧
      LKFU.Shape23.msgIs d.st 0 (some a) false = true ∧
      LKFU.Shape23.msgIs d.st 1 none false = true ∧
      LKFU.Shape23.msgIs d.st 2 (some a) false = true ∧
      LKFU.Shape23.msgIs d.st 3 (some a) false = true ∧
      LKFU.Shape23.grpIs d.st 0 [0, 3] (S.fold.index.answers + 1) S.fold.columns false = true ∧
      LKFU.Shape23.grpIs d.st 1 [2, 3] 1 0 false = true ∧ d.st.groups.size = 2 := by
  simp only [LKFU.Shape23.ok, LKFU.Shape23.shape₂, List.all_cons, List.all_nil, Bool.and_eq_true,
    Bool.and_true] at h
  obtain ⟨-, -, h3, -, -, -, h7, h8, h9, -, h11, -, h13, h14, -⟩ := h
  rw [if_neg (by decide)] at h7 h8
  have g : d.loc.gU = 0 ∧ d.loc.gOmega = 1 := by simpa using h7
  have mk : d.loc.firstMask = some 1 := by simpa using (Bool.and_eq_true_iff.1 h8).2
  have m01 : LKFU.Shape23.msgIs d.st 0 (some a) false = true ∧
      LKFU.Shape23.msgIs d.st 1 none false = true := by simpa using h9
  have m23 : LKFU.Shape23.msgIs d.st 2 (some a) false = true ∧
      LKFU.Shape23.msgIs d.st 3 (some a) false = true := by simpa using h11
  exact ⟨g.1, g.2, mk, m01.1, m01.2, m23.1, m23.2, by simpa using h13, by simpa using h14,
    by simpa using h3⟩

/-- A message that the shape's test books as «without a sample» is not sampled. NEAR KIN:
`rdr_of_msgIs` (Johnson/RunOne/Law/K12Shape29.lean): the same premise ⊢ its `Rdr`, which holds this
and more; that file stands outside this one's cone. -/
theorem unsampled_of_msgIs (st : Statement) (o : ℕ) (sp : Bool)
    (h : LKFU.Shape23.msgIs st o none sp = true) (x : OnBytes.Oracle)
    (hx : st.oracles[o]? = some x) : x.sampled = false := by
  unfold LKFU.Shape23.msgIs at h
  rw [hx] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  exact h.1.1

/-- **What `back_29S` (K12Members29.lean) still owes of the verifier's state and the strings in
front**, a field a debt. -/
structure Debts29S (π : P12) (nl : ℕ → ℕ) (oNo : Sound.Mem → ℕ)
    (x : (P₂ × St₂) × Fr₂.E.Str) : Prop where
  /-- the state's codes are the key file's -/
  cod : x.1.2.st.codes = csKey
  /-- the sendings' invariant at U's message -/
  seed0 : ∃ ρ yv, K1.SeedIs csKey (six.get i3).1 x.1.2.st 0 ρ yv
  /-- … and at the shared split's masks' -/
  seed3 : ∃ ρ yv, K1.SeedIs csKey (six.get i5).1 x.1.2.st 3 ρ yv
  /-- the split's masks' tree is no deeper than the first stage's mask code -/
  dep : ∀ t, Seat.enter (·.gU) (·.firstMask) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
    (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
    (D.mems.get j).id = 3 → (D.mems.get j).tsh.logN ≤ s.Z.a
  /-- clause (7), the word, at U -/
  word0 : ∀ t, Seat.enter (·.gU) (·.firstMask) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
    (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
    (D.mems.get j).id = 0 →
    HEq (strOf csKey (six.get i3).1 (six.get i3).2 (layOf (D.mems.get j))
        (W0 Fr₂ (nuOf π nl t) D.book x.2 (D.mems.get j).t).1
        (W0 Fr₂ (nuOf π nl t) D.book x.2 (D.mems.get j).t).2)
      (Sound.wordsOf F csKey sixS.l sixS.seat (strsOf Fr₂ x.2) i3)
  /-- … and at the split's masks -/
  word3 : ∀ t, Seat.enter (·.gU) (·.firstMask) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
    (D : H2K.First.Plain), Fixes π t s rest G0 Ly D → ∀ j : Fin D.mems.length,
    (D.mems.get j).id = 3 →
    HEq (strOf csKey (six.get i5).1 (six.get i5).2 (layOf (D.mems.get j))
        (W0 Fr₂ (nuOf π nl t) D.book x.2 (D.mems.get j).t).1
        (W0 Fr₂ (nuOf π nl t) D.book x.2 (D.mems.get j).t).2)
      (Sound.wordsOf F csKey sixS.l sixS.seat (strsOf Fr₂ x.2) i5)
  /-- the OOD seeds' tie of the tables' files' bridge, at the reading smpSt -/
  sm : ∀ i : Fin six.length, i = i3 ∨ i = i5 → ∀ σ : (OmAt csKey six i).Smp,
    (smpSt csKey oNo fun a : P₂ × St₂ => a.2.st) x.1 sixS i = some σ →
    ∃ ρ : (OmAt csKey six i).Z.D,
      (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
      seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i x.1 ρ σ.2
  /-- every leaf is shown, in Sound.ShownAt's form -/
  shown : ∀ i : Fin six.length, i = i3 ∨ i = i5 →
    Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ x.2) i
  /-- no open row of the statement is marked as a sample row -/
  kinds : Means.OpenKinds x.1.2.st

/-- **`Pays` at row 2.9 over `back_29S`**: «left» member by member; AND EIGHT BINDERS OF
`pays_29` FALL TO THE INVARIANT's OWN TEST ON THE STATE's SHAPE (`shape29_facts`): hm2 · hm3 · hmk ·
htwo · hmemO ·
the
group (hgm · hgrp) · «message 0 is sampled and has sample rows». «The place's first tree is 0» is no
binder. What stays of the state: `Debts29S`, under the piece's accepting run. -/
theorem pays_29S {Cl W : Type} (π : P12) (lo : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (oNo : Sound.Mem → ℕ)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (on : ℕ → (P₂ × St₂) × Fr₂.E.Str → Prop)
    (hin : ∀ a, on 9 a →
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 9 a)
    (hbk : ∀ b,
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 10 b →
      on 10 b)
    (Bb : Block St₂ Cl)
    (fwd : ∀ a c rs gs,
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 9 a →
      (held Bb : Block (P₂ × St₂) Cl).decide a.1 rs gs = .ok c.1 →
      StrsStay F atSix (open₂ 9) (strsOf Fr₂ a.2) (strsOf Fr₂ c.2) →
      on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a₀ coll last₁ off₂ 10 c)
    (hal : Coin.Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside
      (Seat.enter (·.gU) (·.firstMask)) Seat.leave) Bb)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hSm : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).SmOnly)
    (base : ℕ) (hpins : ∀ k ∈ pinned (open₂ 9), (atSix k).1 < base)
    (dB : RDT) (dt : List RDT) (x' : Rest (ckP .two) Fr₂ (P₂ × St₂) W (dB :: dt))
    (hnum₁ : ∀ k ∈ [0, 2], ∀ o, K₁.orc k = some o → ∀ j, K₁.num o = some j → j ∈ [0, 2, 4, 5])
    (heval : ∀ a, on 9 a → ∀ rw, (readers₂ S).eval a.1.1 = some rw →
      ∃ Gr, Means.RowIn ((readers₂ S).st₁ a.1.1) Gr rw ∧
        ∀ o ∈ Gr.members.toList, ∀ j, K₁.num o = some j → j ∈ [0, 2, 4, 5])
    (num : Fmt.TreeSource → ℕ)
    (hA : AtPlace Fr₂ π num Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) base dB dt (errJ π r dt))
    (hj : johOk π r = true) (hb1 : batOneOk π = true) (hpl : LabelsPub π num (nlAt π lo) base)
    (hle : Err.le ((batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) :
      Err (uLT (ckP .two) (dB :: dt))) x'.err)
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂)
    (hlog : ∀ i : Fin six.length, i = i3 ∨ i = i5 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i3 ∨ i = i5 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hmem0 : mem 0 = some ⟨sixS, i3⟩) (hmem3 : mem 3 = some ⟨sixS, i5⟩)
    (h1 : S.fold.index.answers ≠ 0) (h2 : S.fold.columns ≠ 0)
    (ho0 : oNo ⟨sixS, i3⟩ = 0) (ho3 : oNo ⟨sixS, i5⟩ = 3)
    (hU : ¬ (0 < (six.get i3).1.mainRows ∧ 0 < (six.get i3).1.maskRows) ∧
      ((0 < (six.get i3).1.maskRows ∨ (six.get i3).1.mainDeg = 3) ∨
        ((six.get i3).1.maskRows = 0 ∧ (six.get i3).1.mainDeg = 1)) ∧
      0 < (six.get i3).1.mainRows ∧
      ((six.get i3).1.maskRows = 0 → csKey.mask.size ≤ (six.get i3).1.maskCode))
    (hSp : ¬ (0 < (six.get i5).1.mainRows ∧ 0 < (six.get i5).1.maskRows) ∧
      ((0 < (six.get i5).1.maskRows ∨ (six.get i5).1.mainDeg = 3) ∨
        ((six.get i5).1.maskRows = 0 ∧ (six.get i5).1.mainDeg = 1)) ∧
      0 < (six.get i5).1.maskRows ∧ csKey.base.size ≤ (six.get i5).1.code)
    (hf0 : ∀ s rest, π.nums.stages = s :: rest →
      r (sgOf s).st < ((six.get i3).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i3).1))
    (hf3 : ∀ s rest, π.nums.stages = s :: rest →
      r (sgOf s).st < ((six.get i5).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i5).1))
    (ha0 : a₀ ≠ 0)
    (hE : ∀ a τ b, on 9 a →
      (pieceOf (held Bb) base (dB :: dt) [] x').ior.red.out a τ = some b →
      Debts29S F Fr₂ orc₁ π (nlAt π lo) oNo a) :
    Pays Fr₂ π (fun s t => Seat.enter (·.gU) (·.firstMask) s = .ok t)
      (fun s t s' => Seat.leave s t = .ok s') (held Bb : Block (P₂ × St₂) Cl) on
      (L₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
        (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) 9 base (dB :: dt) []
      x' := by
  have sf := fun a (ha : on 9 a) =>
    shape29_facts S a₀ a.1.2 (id ((hin a ha).resolve_left (fun h => h trivial))).1
  have smpd : ∀ a, on 9 a → ∀ o, o = 2 ∨ o = 3 →
      ∃ z : OnBytes.Oracle, a.1.2.st.oracles[o]? = some z ∧ z.sampled = true := by
    intro a ha o ho
    obtain ⟨_, _, _, _, _, c2, c3, _⟩ := sf a ha
    rcases ho with rfl | rfl
    · obtain ⟨z, e1, e2, _⟩ := K12Law32Core.msgIs_facts _ _ _ c2
      exact ⟨z, e1, e2⟩
    · obtain ⟨z, e1, e2, _⟩ := K12Law32Core.msgIs_facts _ _ _ c3
      exact ⟨z, e1, e2⟩
  have hmk : ∀ a, on 9 a → ∀ o z, a.1.2.loc.firstMask = some o → a.1.2.st.oracles[o]? = some z →
      z.sampled = false := by
    intro a ha o z ho hz
    obtain ⟨_, _, c8, _, c1, _⟩ := sf a ha
    obtain rfl : 1 = o := Option.some.inj (c8.symm.trans ho)
    exact unsampled_of_msgIs _ _ _ c1 z hz
  refine pays_of_law29 F Fr₂ decT recOf orc₁ tab S K₁ enc rad a₀ coll last₁ off₂ π lo r rdN on hin
    hbk Bb fwd hal hp hSm base hpins dB dt x' (fun a τ b ha hout hq => ?_)
    (fun a ha => smpd a ha 2 (Or.inl rfl)) (fun a ha => smpd a ha 3 (Or.inr rfl)) hmk
    (fun a ha => ?_) (fun a ha => ?_) hnum₁ heval num hA hj hb1 hpl hle
  · obtain ⟨c7, _, _, c0, _, _, _, c13, _, _⟩ := sf a ha
    have E := hE a τ b ha hout
    have hon := hin a ha
    obtain ⟨_, _, hfree, _⟩ := id (hon.resolve_left (fun h => h trivial))
    obtain ⟨x0, hx, hsmd, hsz⟩ := K12Law32Core.msgIs_facts _ _ _ c0
    obtain ⟨G, hG, hGm, hGr⟩ := K12Law32Core.grpIs_facts _ _ _ _ _ _ c13
    have one : ∀ G0, a.1.2.st.groups[a.1.2.loc.gU]? = some G0 → G0 = G := by
      intro G0 h0
      rw [c7, hG] at h0
      exact (Option.some.inj h0).symm
    exact K12Members29.back_29S F Fr₂ decT recOf orc₁ tab S K₁ enc rad a₀ coll last₁ off₂ π
      (nlAt π lo) r rdN oNo mem rd hrd (pieceOf (held Bb) base (dB :: dt) [] x') Bb rfl hal a b τ
      hout hq hon hj hp E.cod (fun G0 h0 => by rw [one G0 h0]; exact hGm) E.seed0 E.seed3 ho0 ho3 hU
      hSp E.dep hf0 hf3 E.word0 E.word3 hi hlog told E.sm E.shown hmem0 hmem3 E.kinds
      (fun G0 h0 => by
        rw [one G0 h0, hGm, hGr]
        exact ⟨by simp, by simp, by omega⟩)
      h1 h2 x0 hx hsmd (by rw [hsz]; exact ha0) hSm
      (fun o ho => by
        have earr : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).arr (atSix 5).1
            (atSix 5).2 = 5 := hfree.arr 5 (by decide)
        rw [earr] at ho
        have e3 : o = 3 := by simpa [orc₂] using ho.symm
        subst e3
        obtain ⟨z, hz, hs⟩ := smpd a ha 3 (Or.inr rfl)
        refine ⟨(Array.getElem?_eq_some_iff.1 hz).1, fun hm => ?_⟩
        rw [hmk a ha 3 z hm hz] at hs
        exact absurd hs (by simp))
      (hpins 5 (by rw [pinned29]; decide))
  · obtain ⟨c7, c7', _, _, _, _, _, _, _, c3⟩ := sf a ha
    rw [c7, c7', c3]
    exact ⟨by decide, by decide⟩
  · obtain ⟨_, c7', _, _, _, _, _, _, c14, _⟩ := sf a ha
    exact KeyRide23.hmem_of_shape a.1 c7' _ _ _ c14

end Johnson.RunOne.Law.K12Pays29

#print axioms Johnson.RunOne.Law.K12Pays29.stays_U
#print axioms Johnson.RunOne.Law.K12Pays29.rides_29
#print axioms Johnson.RunOne.Law.K12Pays29.common_29
#print axioms Johnson.RunOne.Law.K12Pays29.i2_of_law29
#print axioms Johnson.RunOne.Law.K12Pays29.pays_of_law29
#print axioms Johnson.RunOne.Law.K12Pays29.pays_29
#print axioms Johnson.RunOne.Law.K12Pays29.shape29_facts
#print axioms Johnson.RunOne.Law.K12Pays29.unsampled_of_msgIs
#print axioms Johnson.RunOne.Law.K12Pays29.pays_29S
