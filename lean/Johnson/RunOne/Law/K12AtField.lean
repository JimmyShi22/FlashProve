-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12AtField.lean: IT SHOWS THAT THE DOOR TAKES THE LAW, AND NOTHING ON WHETHER A FIELD CAN BE PAID: whatever law in the plain form holds of the proximity test's block at its own record becomes `KeepsAt on L ‹the maker's row of a chain› n` (Johnson/Top/Fire/Code/RowPieces.lean), for whatever tables on and L, wherever the chain's n-th block stands over that block; and so at the four proximity tests of a key file. Under premises by name. Statements with proofs.
OBJECT. The n-th piece of the maker's own cut of a chain of a file's description F, where the chain's n-th block is `bareB B` and B stands over `proximityTestKind guardedProximityTestParts π` (Johnson/Desc/K12/Coin/Over.lean: Over). At `Key.descriptionFromSource X N P`: the ranges' test, the folded row's test, Omega's test, the own group's test.
USER. Whoever pays the field of such a piece at given tables.
LETTERS. The description F (in § 2), the tables on and L, the place π, the seat's two relations R (entering) and R' (leaving) are free. Premises by name: hO (B stands over the kind's block), hb (the block stands at n), hpay (`Pays`).

  kp: the kind's block's piece at a given base, stretch, "put behind" and errors, with an idle extractor.
  Pays: at the maker's own base, stretch and "put behind" there are errors ε, a promise Pr and a conclusion Qk with: THE LAW: kp there Leads from Pr to Qk at ε · ε is at most the row's errors · (I1) the table's promise in front gives Pr at the record that the seat's entering makes · (I2) WHERE THE MAKER's PIECE PUTS OUT b AT SOME TRANSCRIPT: the table's promise in front, the entering, the leaving and Qk give the table's promise behind, and "the claim behind gives the claim in front". (Without "puts out" the strings behind would be tied to nothing: the two laws named below conclude on the statement in front alone: at tables whose promise behind reads the strings nothing could then pay.)
  keepsAt_k12₁, keepsAt_k12₂, keepsAt_k12₃: the statement, chain by chain, general in the description. WHAT THEY ADD to Johnson/Top/Fire/Code/PieceSame.lean's keepsAt_of_law₁₂₃, which want a law at the maker's piece, at the chain's state: a law AT THE KIND's OWN RECORD serves, because the seat stands over the kind's block (Coin/Over.lean: leads_over; Johnson/RunOne/Law/K12SeatsHeld.lean: over_held). No detour through a seat of a rule of composition: `Keeps` is a `Leads` by definition; the law's piece over the seat is a `pieceOf`; K12SeatsHeld.lean's held P B is the `held (bareB B)` of Johnson/Desc/Sound/PaidAtDesc.lean.
  pays_lawY, pays_lawYO: WHICH LAW is the payer's choice: Johnson/Desc/K12/Coin/LawY.lean's k12_lawY and k12_lawYO are two (at a stretch dB :: dt with nothing put behind; Pr := FirstOpens | FirstOpensOwn and the batching's converse; Qk := the law's conclusion at the record in front). A law with a lighter promise is another.
  rng_at, rng_at_15, U_at, O_at, own_at: where the description's flat lists are cⱼ :: kⱼ the four blocks stand at their numbers (Johnson/RunOne/Sound/KeyMapAtFK.lean: fk_rng_at; Johnson/RunOne/Law/K12SeatsAt.lean; these lemmas' description is this one pulled along a map of instances, which leaves the chains as they are); at a plan with two lookups the first number is 15; the last is 2.
  keepsAt_rng, keepsAt_rng_15, keepsAt_U, keepsAt_O, keepsAt_own: the doors at these four, hO and hb paid: five terms whose types Lean infers: hpay stays.
Limits. A field alone is worth nothing: at large errors, or at tables whose promise holds nowhere, it holds for nothing. hpay holds all the weight, and it is not shown that it can be met at any tables: that a law's own frame, base and stretch are the maker's is the payer's to show; (I2) holds the whole way from "some near words meet the batched claim" to the tables' items. The numbers of the two tests of the shared chain are terms, not numerals; Omega's test wants P.O = some nO. Nothing on soundness, nothing on hiding.

-/
import Johnson.Top.Fire.Code.PieceSame
import Johnson.RunOne.Law.K12SeatsHeld
import Johnson.RunOne.Law.K12SeatsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12AtField
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Key (FirstState Claim enterRanges leaveRanges rangesTest rangesParams enterAndAsk)
open Johnson.RunOne.Sound
open Johnson.RunOne.Law.K12SeatsLaw (over_same seated_recl seated_ownAt)
open Johnson.RunOne.Law.K12SeatsAt (tableBlocks fk_U_at fk_O_at fk_own_at)
open LPFD (KeepsAt keepsAt_of_law₁ keepsAt_of_law₂ keepsAt_of_law₃)

/-! ## 1 What is owed -/

/-- The kind's block's piece, with an idle extractor. -/
abbrev kp (W : Type) (Fr : Frame) (π : P12) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    (ε : Err (uLT (ckP .two) ds)) : Piece (ckP .two) Fr T12 Unit W :=
  ⟨proximityTestKind guardedProximityTestParts π, base, ds, back, fun _ _ w => w, ε⟩

/-- **What is owed at the maker's own base, stretch and "put behind"**: a law of the kind's block's piece there, at errors that are at most the row's, and the two implications at the tables. H: what is handed to the chain. R, R': the seat's entering and leaving. B', x': the maker's piece's block and its extractor with its errors: the second implication is owed only WHERE THAT PIECE PUTS OUT b AT SOME TRANSCRIPT τ: without that clause nothing would tie the strings behind (b.2) to those in front. -/
def Pays {W H S Cl : Type} (Fr : Frame) (π : P12) (R : S → T12 → Prop) (R' : S → T12 → S → Prop)
    (B' : Block (H × S) Cl) (on L : ℕ → (H × S) × Fr.E.Str → Prop) (n base : ℕ) (ds : List RDT)
    (back : List Fmt.RoundView) (x' : Rest (ckP .two) Fr (H × S) W ds) : Prop :=
  ∃ (ε : Err (uLT (ckP .two) ds)) (Pr : T12 × Fr.E.Str → Prop) (Qk : T12 × Fr.E.Str → T12 × Fr.E.Str → Prop),
    (kp W Fr π base ds back ε).ior.red.Leads Pr Qk ε ∧ Err.le ε x'.err ∧
    (∀ a, on n a → ∀ t, R a.1.2 t → Pr (t, a.2)) ∧
    ∀ a τ b, on n a → (pieceOf B' base ds back x').ior.red.out a τ = some b →
      (∃ t t', R a.1.2 t ∧ (R' a.1.2 t' b.1.2 ∧ b.1.1 = a.1.1) ∧ Qk (t, a.2) (t', b.2)) →
      on (n + 1) b ∧ (L (n + 1) b → L n a)

section
variable {W H S Cl : Type} {Fr : Frame} (π : P12) (R : S → T12 → Prop) (R' : S → T12 → S → Prop)
  (B' : Block (H × S) Cl) (on L : ℕ → (H × S) × Fr.E.Str → Prop) (n : ℕ)
  (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (Lc mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
  (base : ℕ) (dB : RDT) (dt : List RDT) (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt)) (Nn : ConclK Fr)
  (x' : Rest (ckP .two) Fr (H × S) W (dB :: dt))

/-- The law of the proximity test in the plain form is such a law: first arm. -/
theorem pays_lawY (hA : AtPlace Fr π num Lc mC mS mW rad base dB dt εt)
    (hle : Err.le (pieceT Fr W π base dB dt e₀ εt).err x'.err)
    (h1 : ∀ a, on n a → ∀ t, R a.1.2 t →
      FirstOpens π num no base t ∧ BatAtY Fr W π no rad rd base dB dt e₀ εt Nn (t, a.2))
    (h2 : ∀ a τ b, on n a → (pieceOf B' base (dB :: dt) [] x').ior.red.out a τ = some b →
      (∃ t t', R a.1.2 t ∧ (R' a.1.2 t' b.1.2 ∧ b.1.1 = a.1.1) ∧ QN π Nn (t, a.2)) →
      on (n + 1) b ∧ (L (n + 1) b → L n a)) :
    Pays Fr π R R' B' on L n base (dB :: dt) [] x' :=
  ⟨(pieceT Fr W π base dB dt e₀ εt).err, _, _,
    k12_lawY Fr W π num no Lc mC mS mW rad rd base dB dt e₀ εt Nn hA, hle, h1, h2⟩

/-- Second arm. -/
theorem pays_lawYO (hA : AtPlaceOwn Fr π num Lc mC mS mW rad base dB dt εt)
    (hle : Err.le (pieceT Fr W π base dB dt e₀ εt).err x'.err)
    (h1 : ∀ a, on n a → ∀ t, R a.1.2 t →
      FirstOpensOwn π num no base t ∧ BatAtY Fr W π no rad rd base dB dt e₀ εt Nn (t, a.2))
    (h2 : ∀ a τ b, on n a → (pieceOf B' base (dB :: dt) [] x').ior.red.out a τ = some b →
      (∃ t t', R a.1.2 t ∧ (R' a.1.2 t' b.1.2 ∧ b.1.1 = a.1.1) ∧ QN π Nn (t, a.2)) →
      on (n + 1) b ∧ (L (n + 1) b → L n a)) :
    Pays Fr π R R' B' on L n base (dB :: dt) [] x' :=
  ⟨(pieceT Fr W π base dB dt e₀ εt).err, _, _,
    k12_lawYO Fr W π num no Lc mC mS mW rad rd base dB dt e₀ εt Nn hA, hle, h1, h2⟩

end

/-! ## 2 The three doors, general in the description -/

section
variable {Xi W : Type} (F : FileDescription Xi) (D : WholeD)
  (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
  (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
  (dW wEnd : W)

/-- **The door takes the law: chain 1.** -/
theorem keepsAt_k12₁ (π : P12) (B : Block F.S₁ F.Cl) (R : F.S₁ → T12 → Prop) (R' : F.S₁ → T12 → F.S₁ → Prop)
    (hO : ∀ base ds back ε, Over (kp W (frameAt D (allOf D) D.key₁ 0) π base ds back ε) B R R')
    (on L : ℕ → (F.XiPub × F.S₁) × (frameAt D (allOf D) D.key₁ 0).E.Str → Prop) (n : ℕ)
    (hb : (c₁ :: k₁)[n]? = some (bareB B))
    (hpay : ∀ (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView),
      ((atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ ::
        (atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)[n]? =
        some (pieceOf (held (bareB B)) base ds back (rest₁ n ds)) →
      Pays (frameAt D (allOf D) D.key₁ 0) π R R' (held (bareB B)) on L n base ds back (rest₁ n ds)) :
    KeepsAt on L
      ((atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ ::
        (atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) n :=
  keepsAt_of_law₁ (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd on L n
    fun b base ds back hb' hp => by
      obtain rfl := Option.some.inj (hb.symm.trans hb')
      obtain ⟨ε, Pr, Qk, hlaw, hle, h1, h2⟩ := hpay base ds back hp
      refine ⟨⟨fun _ _ w => w, ε⟩, ?_, hle⟩
      exact Iop.Reduction.Leads.conseq
        (leads_over _ _ _ _ (K12SeatsHeld.over_held (P := F.XiPub) _ (hO base ds back ε)) Pr Qk hlaw)
        h1 fun a τ b ha hout hq => h2 a τ b ha hout hq

/-- **The door takes the law: chain 2.** -/
theorem keepsAt_k12₂ (π : P12) (B : Block F.S₂ F.Cl) (R : F.S₂ → T12 → Prop) (R' : F.S₂ → T12 → F.S₂ → Prop)
    (hO : ∀ base ds back ε, Over (kp W (frameAt D (allOf D) D.key₂ 0) π base ds back ε) B R R')
    (on L : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (frameAt D (allOf D) D.key₂ 0).E.Str → Prop) (n : ℕ)
    (hb : (c₂ :: k₂)[n]? = some (bareB B))
    (hpay : ∀ (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView),
      ((atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[n]? =
        some (pieceOf (held (bareB B)) base ds back (rest₂ n ds)) →
      Pays (frameAt D (allOf D) D.key₂ 0) π R R' (held (bareB B)) on L n base ds back (rest₂ n ds)) :
    KeepsAt on L
      ((atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ ::
        (atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) n :=
  keepsAt_of_law₂ (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd on L n
    fun b base ds back hb' hp => by
      obtain rfl := Option.some.inj (hb.symm.trans hb')
      obtain ⟨ε, Pr, Qk, hlaw, hle, h1, h2⟩ := hpay base ds back hp
      refine ⟨⟨fun _ _ w => w, ε⟩, ?_, hle⟩
      exact Iop.Reduction.Leads.conseq
        (leads_over _ _ _ _ (K12SeatsHeld.over_held (P := (F.XiPub × F.S₁)) _ (hO base ds back ε)) Pr Qk hlaw)
        h1 fun a τ b ha hout hq => h2 a τ b ha hout hq

/-- **The door takes the law: chain 3.** -/
theorem keepsAt_k12₃ (π : P12) (B : Block F.S₃ F.Cl) (R : F.S₃ → T12 → Prop) (R' : F.S₃ → T12 → F.S₃ → Prop)
    (hO : ∀ base ds back ε, Over (kp W (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) π base ds back ε) B R R')
    (on L : ℕ → ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber).E.Str → Prop) (n : ℕ)
    (hb : (c₃ :: k₃)[n]? = some (bareB B))
    (hpay : ∀ (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView),
      ((atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ ::
        (atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)[n]? =
        some (pieceOf (held (bareB B)) base ds back (rest₃ n ds)) →
      Pays (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) π R R' (held (bareB B)) on L n base ds back (rest₃ n ds)) :
    KeepsAt on L
      ((atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ ::
        (atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃) n :=
  keepsAt_of_law₃ (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd on L n
    fun b base ds back hb' hp => by
      obtain rfl := Option.some.inj (hb.symm.trans hb')
      obtain ⟨ε, Pr, Qk, hlaw, hle, h1, h2⟩ := hpay base ds back hp
      refine ⟨⟨fun _ _ w => w, ε⟩, ?_, hle⟩
      exact Iop.Reduction.Leads.conseq
        (leads_over _ _ _ _ (K12SeatsHeld.over_held (P := (F.XiPub × F.S₁ × F.S₂)) _ (hO base ds back ε)) Pr Qk hlaw)
        h1 fun a τ b ha hout hq => h2 a τ b ha hout hq

end

/-! ## 3 The four proximity tests of a key file -/

section
variable {W : Type} (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces) (D : WholeD)
  (c₁ : Block (Key.descriptionFromSource X N P).S₁ (Key.descriptionFromSource X N P).Cl) (k₁ : List (Block (Key.descriptionFromSource X N P).S₁ (Key.descriptionFromSource X N P).Cl))
  (c₂ : Block (Key.descriptionFromSource X N P).S₂ (Key.descriptionFromSource X N P).Cl) (k₂ : List (Block (Key.descriptionFromSource X N P).S₂ (Key.descriptionFromSource X N P).Cl))
  (c₃ : Block (Key.descriptionFromSource X N P).S₃ (Key.descriptionFromSource X N P).Cl) (k₃ : List (Block (Key.descriptionFromSource X N P).S₃ (Key.descriptionFromSource X N P).Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0)
    ((Key.descriptionFromSource X N P).XiPub × (Key.descriptionFromSource X N P).S₁) W ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0)
    (((Key.descriptionFromSource X N P).XiPub × (Key.descriptionFromSource X N P).S₁) × (Key.descriptionFromSource X N P).S₂) W ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₃ (Key.descriptionFromSource X N P).lastChainFirstTreeNumber)
    (((Key.descriptionFromSource X N P).XiPub × (Key.descriptionFromSource X N P).S₁ × (Key.descriptionFromSource X N P).S₂) × (Key.descriptionFromSource X N P).S₃) W ds)
  (dW wEnd : W)

/-- The ranges' test's block stands at its number. -/
theorem rng_at (hf : (Key.descriptionFromSource X N P).first.blocksInOrder = c₁ :: k₁) :
    (c₁ :: k₁)[2 + 6 * (Key.lookupsOf X.Y.k.oneTime).length + 1]? = some (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Claim)) :=
  (congrArg (fun l => l[2 + 6 * (Key.lookupsOf X.Y.k.oneTime).length + 1]?) hf).symm.trans (fk_rng_at X N P)

/-- At a plan with two lookups the number is 15. -/
theorem rng_at_15 (hf : (Key.descriptionFromSource X N P).first.blocksInOrder = c₁ :: k₁)
    (hl : (Key.lookupsOf X.Y.k.oneTime).length = 2) : (c₁ :: k₁)[15]? = some (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Claim)) := by
  have h := rng_at X N P c₁ k₁ hf
  rw [hl] at h
  exact h

/-- The folded row's test's block stands at its number. -/
theorem U_at (hf : (Key.descriptionFromSource X N P).shared.blocksInOrder = c₂ :: k₂) :
    (c₂ :: k₂)[1 + ((tableBlocks X P).length + 0)]? = some (bareB (Block.retype (Cl := Unit) (Cl' := Key.Claim)
      (Seat.onGu (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U))))) :=
  (congrArg (fun l => l[1 + ((tableBlocks X P).length + 0)]?) hf).symm.trans (fk_U_at X N P)

/-- Omega's test's. -/
theorem O_at (hf : (Key.descriptionFromSource X N P).shared.blocksInOrder = c₂ :: k₂) (nO : H2U.PlaceNums) (hO : P.O = some nO) :
    (c₂ :: k₂)[1 + ((tableBlocks X P).length + 1)]? = some (bareB (Block.retype (Cl := Unit) (Cl' := Key.Claim)
      (Seat.onGomega (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO))))) :=
  (congrArg (fun l => l[1 + ((tableBlocks X P).length + 1)]?) hf).symm.trans (fk_O_at X N P nO hO)

/-- The own group's test's. -/
theorem own_at (hf : (Key.descriptionFromSource X N P).second.blocksInOrder = c₃ :: k₃) :
    (c₃ :: k₃)[2]? = some (bareB (Block.retype (Cl := Unit) (Cl' := Key.Claim)
      (Third.ownAt (Seat.onOwn (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) : Block T12 Unit))))) :=
  (congrArg (fun l => l[2]?) hf).symm.trans (fk_own_at X N P)

/-- The ranges' test. -/
def keepsAt_rng (on L) (hf : (Key.descriptionFromSource X N P).first.blocksInOrder = c₁ :: k₁) :=
  keepsAt_k12₁ (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd (rangesParams N) _ _ _
    (fun _ _ _ _ => RngOverCoin.over_keyD X.Y.k.oneTime N _ rfl) on L _ (rng_at X N P c₁ k₁ hf)

/-- The ranges' test at a plan with two lookups: at the number 15. -/
def keepsAt_rng_15 (on L) (hf : (Key.descriptionFromSource X N P).first.blocksInOrder = c₁ :: k₁)
    (hl : (Key.lookupsOf X.Y.k.oneTime).length = 2) :=
  keepsAt_k12₁ (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd (rangesParams N) _ _ _
    (fun _ _ _ _ => RngOverCoin.over_keyD X.Y.k.oneTime N _ rfl) on L 15 (rng_at_15 X N P c₁ k₁ hf hl)

/-- The folded row's test. -/
def keepsAt_U (on L) (hf : (Key.descriptionFromSource X N P).shared.blocksInOrder = c₂ :: k₂) :=
  keepsAt_k12₂ (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) _ _ _
    (fun _ _ _ _ => over_same _ (seated_recl _) (over_inside _ _ _)) on L _ (U_at X N P c₂ k₂ hf)

/-- Omega's test. -/
def keepsAt_O (on L) (hf : (Key.descriptionFromSource X N P).shared.blocksInOrder = c₂ :: k₂) (nO : H2U.PlaceNums) (hO : P.O = some nO) :=
  keepsAt_k12₂ (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) _ _ _
    (fun _ _ _ _ => over_same _ (seated_recl _) (over_inside _ _ _)) on L _ (O_at X N P c₂ k₂ hf nO hO)

/-- The own group's test: at the number 2. -/
def keepsAt_own (on L) (hf : (Key.descriptionFromSource X N P).second.blocksInOrder = c₃ :: k₃) :=
  keepsAt_k12₃ (Key.descriptionFromSource X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) _ _ _
    (fun _ _ _ _ => over_same _ ((seated_ownAt _).trans (seated_recl _)) (over_inside _ _ _)) on L 2
    (own_at X N P c₃ k₃ hf)

end

end Johnson.RunOne.Law.K12AtField

#print axioms Johnson.RunOne.Law.K12AtField.pays_lawY
#print axioms Johnson.RunOne.Law.K12AtField.pays_lawYO
#print axioms Johnson.RunOne.Law.K12AtField.keepsAt_k12₁
#print axioms Johnson.RunOne.Law.K12AtField.keepsAt_k12₂
#print axioms Johnson.RunOne.Law.K12AtField.keepsAt_k12₃
#print axioms Johnson.RunOne.Law.K12AtField.rng_at
#print axioms Johnson.RunOne.Law.K12AtField.rng_at_15
#print axioms Johnson.RunOne.Law.K12AtField.U_at
#print axioms Johnson.RunOne.Law.K12AtField.O_at
#print axioms Johnson.RunOne.Law.K12AtField.own_at
#print axioms Johnson.RunOne.Law.K12AtField.keepsAt_rng
#print axioms Johnson.RunOne.Law.K12AtField.keepsAt_rng_15
#print axioms Johnson.RunOne.Law.K12AtField.keepsAt_U
#print axioms Johnson.RunOne.Law.K12AtField.keepsAt_O
#print axioms Johnson.RunOne.Law.K12AtField.keepsAt_own
