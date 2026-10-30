-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyNewAtSend2Paid.lean: THEOREMS: calls. **The key file, the shared chain, rows 2.2 | 2.5: (New, hnew) with nothing left but what the tables' filler holds**: new22 | new25 (Johnson/RunOne/KeyNewAtSend2.lean) with their two premises on numbers (base = 6 | 7 · d₁.trees.length = 1 | 2) paid by the closed facts base22 | base25 · seed22_key_held | seed25_key_held (Johnson/Top/Fire/Code/Rows2SeedRound.lean), over the bridge row_parts₂. IT PAYS NO FIELD OF THE TABLES: IT PAYS A PREMISE OF A CALL IN ANOTHER FILE.
  new22' | new25'   the scope's four · planOk · wantedOk · the data · «the data are the written data» · the shared chain's head q₂ · the row's piece 2 | 5 has the stretch [d₁, d₂] ⊢ hnew at New := Key.ShownAt (Fk X N P) atSix 3 | ∀ j ∈ [4, 5], Key.ShownAt (Fk X N P) atSix j.
  row_has₂          GENERAL IN THE DESCRIPTION: the shared row has a piece at every n ≤ k₂.length, with the maker's stretch.
  met22 | met25     IS IT EMPTY? under the other premises of new22' | new25' there ARE b base d₁ d₂ back that meet the equation on the row's piece (data22_of | data25_of, Johnson/Top/Fire/Code/Rows2SeedRound.lean: the stretch is two rounds' data).
IS IT EMPTY? Every other premise is public and is one that r2_7_at_name takes. The conclusion's own «∀ x τ x'» is met idly where the piece never accepts: that is the user's matter. In met22 | met25 b stands under ∃: that it is the sending's sub-protocol is rounds22 | rounds25 (Johnson/Top/Fire/Code/Rows2SeedRound.lean), not said here.
Limits. One configuration (the written data). Nothing on soundness.

-/
import Johnson.RunOne.KeyNewAtSend2
import Johnson.Top.Fire.Code.Rows2SeedRound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

namespace Johnson.RunOne.KeyNew2
open OnBytes.Maker OnBytes.Flat OnBytes.Slice
open _root_.Run (ckP)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (Where Source LaterPlaces madeAt sourceOf)
open VerifiableInference.Desc.K1 (sendPiece)
open Johnson.RunOne.KeyRows23 (Fk fr₂ atSix)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.G (writtenKFull)
open Lk6.AtPlan (keyFull)

section
variable {Xi W : Type} (F : FileDescription Xi) (D : WholeD)
    (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
    (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (dW wEnd : W)

/-- **The row has a piece at n, with the maker's stretch.** -/
theorem row_has₂ (n : ℕ) (hn : n ≤ k₂.length) (ds : List RDT) (hc : LPFD.cutDs D.ds₂ c₂ k₂ n = ds) :
    ∃ (b : Block F.S₂ F.Cl) (base : ℕ) (back : List _root_.Fmt.RoundView),
      ((atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[n]? = some (pieceOf (held b) base ds back (rest₂ n ds)) := by
  have hlen : n < ((atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂).length := by
    rw [List.length_cons, LPFD.rowLen₂]
    omega
  obtain ⟨b, base, ds', back, -, e⟩ := LPFD.rowGet₂ (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd n _ (List.getElem?_eq_getElem hlen)
  have hrow := (List.getElem?_eq_getElem hlen).trans (congrArg some e)
  obtain ⟨-, ed⟩ := row_parts₂ F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd n b base ds' back hrow
  obtain rfl : ds' = ds := ed.symm.trans ((LPFD.cutDs_held k₂ n _ c₂).trans hc)
  exact ⟨b, base, back, hrow⟩

end

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD) {W W' : Type}
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) ((Fk X N P).XiPub × (Fk X N P).S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₂ 0) (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₃ (Fk X N P).lastChainFirstTreeNumber)
      (((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N P).S₂) × (Fk X N P).S₃) W ds)
    (dW wEnd : W)
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}

/-- **ROW 2.2: (New, hnew), the two numbers paid.** -/
theorem new22' (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = writtenKFull)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂)
    (b : Block (Fk X N P).S₂ (Fk X N P).Cl) (base : ℕ) (d₁ d₂ : RDT) (back : List _root_.Fmt.RoundView)
    (hrow : ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[2]? = some (pieceOf (held b) base [d₁, d₂] back (rest₂ 2 [d₁, d₂]))) (co e : ℕ)
    (on : (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) × (fr₂ (DK.at frS.P.T.a)).E.Str → Prop) :
    ∀ x τ x', on x →
      (sendPiece (W := W') (F := fr₂ (DK.at frS.P.T.a)) (held b : Block (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) (Fk X N P).Cl) base d₁ d₂ co e).ior.red.out x τ = some x' →
      VerifiableInference.Desc.Key.ShownAt (Fk X N P) atSix 3 (strsOf (fr₂ (DK.at frS.P.T.a)) x'.2) := by
  obtain ⟨eb, ed⟩ := row_parts₂ (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 2 b base [d₁, d₂] back hrow
  have hkey : X.chains.made.sized.key = keyFull :=
    (congrArg (·.made.sized.key) (Johnson.RunOne.KeyLetters.chains_of hX)).trans (Johnson.RunOne.Law.KeyInScope.key_in_scope hZ hP hm)
  exact new22 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hZ hP hm hX hp hwant hdata hDK b base d₁ d₂ back hrow
    (eb.symm.trans (LPFD.base22 c₂ k₂ hZ hP hm hX hp hwant hDK q₂))
    (LPFD.seed22_key_held X N P "key file" (DK.at frS.P.T.a) c₂ k₂ hkey hdata hp q₂ d₁ d₂ ed).2.2.1 co e on

/-- **ROW 2.5: (New, hnew), the two numbers paid.** -/
theorem new25' (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = writtenKFull)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂)
    (b : Block (Fk X N P).S₂ (Fk X N P).Cl) (base : ℕ) (d₁ d₂ : RDT) (back : List _root_.Fmt.RoundView)
    (hrow : ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[5]? = some (pieceOf (held b) base [d₁, d₂] back (rest₂ 5 [d₁, d₂]))) (co e : ℕ)
    (on : (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) × (fr₂ (DK.at frS.P.T.a)).E.Str → Prop) :
    ∀ x τ x', on x →
      (sendPiece (W := W') (F := fr₂ (DK.at frS.P.T.a)) (held b : Block (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) (Fk X N P).Cl) base d₁ d₂ co e).ior.red.out x τ = some x' →
      ∀ j ∈ [4, 5], VerifiableInference.Desc.Key.ShownAt (Fk X N P) atSix j (strsOf (fr₂ (DK.at frS.P.T.a)) x'.2) := by
  obtain ⟨eb, ed⟩ := row_parts₂ (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 5 b base [d₁, d₂] back hrow
  have hkey : X.chains.made.sized.key = keyFull :=
    (congrArg (·.made.sized.key) (Johnson.RunOne.KeyLetters.chains_of hX)).trans (Johnson.RunOne.Law.KeyInScope.key_in_scope hZ hP hm)
  exact new25 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hZ hP hm hX hp hwant hdata hDK b base d₁ d₂ back hrow
    (eb.symm.trans (LPFD.base25 c₂ k₂ hZ hP hm hX hp hwant hDK q₂))
    (LPFD.seed25_key_held X N P "key file" (DK.at frS.P.T.a) c₂ k₂ hkey hdata hp q₂ d₁ d₂ ed).2.2.1 co e on

/-- **new22''s premise on the row's piece can be met**, under its other premises. -/
theorem met22 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a))
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) :
    ∃ (b : Block (Fk X N P).S₂ (Fk X N P).Cl) (base : ℕ) (d₁ d₂ : RDT) (back : List _root_.Fmt.RoundView),
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[2]? = some (pieceOf (held b) base [d₁, d₂] back (rest₂ 2 [d₁, d₂])) := by
  have hk : k₂.length = 11 := by
    have h := (LPFD.lengths_in_scope hZ hP hm hX hp hwant).2.1
    rw [q₂] at h
    simpa using h
  obtain ⟨-, d₁, d₂, -, hc, -⟩ := LPFD.data22_of X N P "key file" (DK.at frS.P.T.a) c₂ k₂ hdata hp q₂
  obtain ⟨b, base, back, h⟩ := row_has₂ (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 2 (by omega) [d₁, d₂] hc
  exact ⟨b, base, d₁, d₂, back, h⟩

/-- **new25''s premise on the row's piece can be met**, under its other premises. -/
theorem met25 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a))
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) :
    ∃ (b : Block (Fk X N P).S₂ (Fk X N P).Cl) (base : ℕ) (d₁ d₂ : RDT) (back : List _root_.Fmt.RoundView),
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[5]? = some (pieceOf (held b) base [d₁, d₂] back (rest₂ 5 [d₁, d₂])) := by
  have hk : k₂.length = 11 := by
    have h := (LPFD.lengths_in_scope hZ hP hm hX hp hwant).2.1
    rw [q₂] at h
    simpa using h
  obtain ⟨d₁, d₂, hc, -⟩ := LPFD.data25_of X N P "key file" (DK.at frS.P.T.a) c₂ k₂ hdata hp q₂
  obtain ⟨b, base, back, h⟩ := row_has₂ (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 5 (by omega) [d₁, d₂] hc
  exact ⟨b, base, d₁, d₂, back, h⟩

end

end Johnson.RunOne.KeyNew2

#print axioms Johnson.RunOne.KeyNew2.row_has₂
#print axioms Johnson.RunOne.KeyNew2.met22
#print axioms Johnson.RunOne.KeyNew2.met25
#print axioms Johnson.RunOne.KeyNew2.new22'
#print axioms Johnson.RunOne.KeyNew2.new25'
