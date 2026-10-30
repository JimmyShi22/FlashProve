-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyNewAtSend2.lean: THEOREMS: calls, and a few rewritings. **The key file, the shared chain, rows 2.2 ("send o_u") and 2.5 ("send o_omega"): behind the sending's piece every leaf of the new messages' trees is shown**: the premise (New, hnew) of the laws keeps₂_send2_seat | keeps₂_send5_seat (Johnson/RunOne/KeyRowsBackAtSeat.lean), with New as yes22_seat | yes25_seat (Johnson/RunOne/KeyRow22AtSeat.lean) ask it. IT PAYS NO FIELD OF THE TABLES: IT PAYS A PREMISE OF A CALL IN ANOTHER FILE.
OBJECT. VerifiableInference.Desc.K1.sendPiece at the base and the two rounds' data of the maker's piece number 2 | 5 of the shared chain. USER. Whoever writes r2_2 | r2_5 at name. LETTERS. X N P · DK · the maker's cut and rests · b base d₁ d₂ back.
  shown_row₂    GENERAL IN THE DESCRIPTION: every piece of the maker's row of the shared chain shows all (Piece.ShownAll), at every list of members whose seats fit: cutShown (Johnson/Desc/Sound/ShownOfData.lean), called at the row itself. (Kin: shown_at₁ of Johnson/Top/Fire/Code/RowShownAt.lean, at the first chain, by a membership lemma; here the equation «the row's n-th piece is p» is the membership.)
  row_parts₂    GENERAL IN THE DESCRIPTION: the base and the stretch in the equation «the row's n-th piece is pieceOf (held b) base ds back …» ARE the maker's cutBase | cutDs at n (LPFD.rowAt₂): the bridge to facts that are stated of cutBase | cutDs.
  shown_send₂   GENERAL IN THE DESCRIPTION: no fault at the seat (j, t) · at_ k = (j, t) · the row's n-th piece has base «base» and the stretch [d₁, d₂] · j = base + i · the stretch sends more than i trees ⊢ behind K1's piece at that base and stretch every leaf of seat k is shown, in the tables' sense (Key.ShownAt).
  new22 | new25 IN THE GOALS' SCOPE, at Fk X N P · fr₂ (DK.at frS.P.T.a) · atSix: the row's piece 2 | 5 · base = 6 | 7 · d₁.trees.length = 1 | 2 ⊢ hnew, at New := Key.ShownAt … atSix 3 | ∀ j ∈ [4, 5], Key.ShownAt … atSix j. The invariant in front is a letter «on»: it is not read.
KIN. shownSame | shownAtSend | shownAtCut (Johnson/Desc/K14/Law/LedgerShown.lean): the general half, under Three.IsCut, as far as Sound's ShownAll at K1's piece. seatFits_one_scope (Johnson/RunOne/KeyFillSeed2At.lean) hands SeatFits at a one-member list of the six outright; here fits_one at six_at's «no fault» does.
PREMISES THAT OTHERS PAY. base = 6 | 7 and d₁.trees.length = 1 | 2: closed facts on the written data. The scope's four, planOk, wantedOk, the data, «the data are the written data»: as in r2_7_at_name.
IS IT EMPTY? The premises speak of public data alone. That they can be met together is not shown here: see Johnson/RunOne/KeyNewAtSend2Paid.lean (new22' | new25' · met22 | met25), which imports more.
What is not claimed. That any state of the verifier is reached. Anything of the tenant at (6, 1) (the first mask). Nothing on soundness.

-/
import Johnson.Top.Fire.Code.RowShownAt
import Johnson.Top.Fire.Code.RowsNine
import Johnson.RunOne.KeyTenInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

namespace Johnson.RunOne.KeyNew2
open OnBytes.Maker OnBytes.Flat OnBytes.Slice
open _root_.Run (ckP)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (Where Source LaterPlaces madeAt sourceOf out_behind')
open VerifiableInference.Desc.K1 (sendPiece)
open Johnson.RunOne.KeyRows23 (Fk fr₂ atSix)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.Top.H (csKey shU shO shSp)
open Johnson.G (writtenKFull)

section
variable {Xi W : Type} (F : FileDescription Xi) (D : WholeD)
    (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
    (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (dW wEnd : W)

/-- **Every piece of the maker's row of the shared chain shows all**, at every list of members whose seats fit. -/
theorem shown_row₂ (file : String) (hp : F.planOk = true) (hdata : F.data file = .ok D)
    (cs : OnBytes.Codes) (m : List (OnBytes.OracleShape × ℕ)) (fam : Fin m.length → ℕ × ℕ) (fits : VerifiableInference.Desc.Sound.SeatFits F cs m fam)
    (n : ℕ) (p) (hrow : ((atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[n]? = some p) :
    VerifiableInference.Desc.Sound.Piece.ShownAll p F cs m fam :=
  cutShown (ckP .two) _ _ _ _ rest₂ [] D (k₂.map held) (held c₂) 0 D.t₁ D.ds₂ rfl (shape_own₂ _) _ F cs m fam fits
    (oraclesAreOk _ F file D hdata (sentFit_of_planOk _ hp) (blocksOk_ok.2 (F.planOk_ok.1 hp).blocks₁) (blocksOk_ok.2 (F.planOk_ok.1 hp).blocks₂)) p
    (List.mem_of_getElem? hrow)

/-- **The base and the stretch of the row's n-th piece are the maker's.** -/
theorem row_parts₂ (n : ℕ) (b : Block F.S₂ F.Cl) (base : ℕ) (ds : List RDT) (back : List _root_.Fmt.RoundView)
    (hrow : ((atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[n]? = some (pieceOf (held b) base ds back (rest₂ n ds))) :
    LPFD.cutBase D.t₁ D.ds₂ (held c₂ : Block ((F.XiPub × F.S₁) × F.S₂) F.Cl) (k₂.map held) n = base ∧
      LPFD.cutDs D.ds₂ (held c₂ : Block ((F.XiPub × F.S₁) × F.S₂) F.Cl) (k₂.map held) n = ds := by
  obtain ⟨b', -, e⟩ := LPFD.rowAt₂ (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd n _ hrow
  exact ⟨(congrArg (·.base) e).symm, (congrArg (·.ds) e).symm⟩

/-- **Behind K1's piece at the base and the stretch of the row's n-th piece, every leaf of a seat whose tree the stretch sends is shown**, in the tables' sense. -/
theorem shown_send₂ {W' : Type} (file : String) (hp : F.planOk = true) (hdata : F.data file = .ok D)
    (cs : OnBytes.Codes) (s : OnBytes.OracleShape) (j t : ℕ) (tag : String) (nf : seatFaultAt F cs tag s j t = none)
    (at_ : Where) (k : ℕ) (hk : at_ k = (j, t))
    (n : ℕ) (b : Block F.S₂ F.Cl) (base : ℕ) (d₁ d₂ : RDT) (back : List _root_.Fmt.RoundView)
    (hrow : ((atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[n]? = some (pieceOf (held b) base [d₁, d₂] back (rest₂ n [d₁, d₂])))
    (i : ℕ) (hj : j = base + i) (hi : i < nTrees [d₁, d₂]) (co e : ℕ)
    (x x' : ((F.XiPub × F.S₁) × F.S₂) × (frameAt D (allOf D) D.key₂ 0).E.Str) (τ)
    (hx : (sendPiece (W := W') (F := frameAt D (allOf D) D.key₂ 0) (held b : Block ((F.XiPub × F.S₁) × F.S₂) F.Cl) base d₁ d₂ co e).ior.red.out x τ = some x') :
    VerifiableInference.Desc.Key.ShownAt F at_ k (strsOf (frameAt D (allOf D) D.key₂ 0) x'.2) := by
  obtain ⟨sh, hsh⟩ := treeShT_some_of_lt [d₁, d₂] i hi
  rw [out_behind' (frameAt D (allOf D) D.key₂ 0) _ x x' τ hx]
  exact LPFD.shown_tie F cs [(s, 0)] (fun _ => (j, t)) (LPFD.fits_one F cs s 0 j t tag nf) at_ k ⟨0, Nat.one_pos⟩ hk.symm _
    (shown_row₂ F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd file hp hdata cs [(s, 0)] (fun _ => (j, t)) (LPFD.fits_one F cs s 0 j t tag nf) n _ hrow
      x.2 τ ⟨0, Nat.one_pos⟩ i sh hj hsh)

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

/-- **ROW 2.2: (New, hnew).** Behind the sending of o_u every leaf of the seat atSix 3 = (6, 0) is shown. -/
theorem new22 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = writtenKFull)
    (b : Block (Fk X N P).S₂ (Fk X N P).Cl) (base : ℕ) (d₁ d₂ : RDT) (back : List _root_.Fmt.RoundView)
    (hrow : ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[2]? = some (pieceOf (held b) base [d₁, d₂] back (rest₂ 2 [d₁, d₂])))
    (hbase : base = 6) (htrees : d₁.trees.length = 1) (co e : ℕ)
    (on : (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) × (fr₂ (DK.at frS.P.T.a)).E.Str → Prop) :
    ∀ x τ x', on x →
      (sendPiece (W := W') (F := fr₂ (DK.at frS.P.T.a)) (held b : Block (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) (Fk X N P).Cl) base d₁ d₂ co e).ior.red.out x τ = some x' →
      VerifiableInference.Desc.Key.ShownAt (Fk X N P) atSix 3 (strsOf (fr₂ (DK.at frS.P.T.a)) x'.2) := by
  intro x τ x' _ hx
  have nf := ((Johnson.RunOne.KeyLetters.six_at hZ hP hm hX hp hwant (hDK ▸ hdata)).1 "" "" "").1
  exact shown_send₂ (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd "key file" hp hdata csKey shU 6 0 "" nf atSix 3 rfl
    2 b base d₁ d₂ back hrow 0 hbase.symm (by rw [nTrees_cons]; omega) co e x x' τ hx

/-- **ROW 2.5: (New, hnew).** Behind the sending of o_omega and o_sp every leaf of the seats atSix 4 = (7, 0) and atSix 5 = (8, 0) is shown. -/
theorem new25 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = writtenKFull)
    (b : Block (Fk X N P).S₂ (Fk X N P).Cl) (base : ℕ) (d₁ d₂ : RDT) (back : List _root_.Fmt.RoundView)
    (hrow : ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[5]? = some (pieceOf (held b) base [d₁, d₂] back (rest₂ 5 [d₁, d₂])))
    (hbase : base = 7) (htrees : d₁.trees.length = 2) (co e : ℕ)
    (on : (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) × (fr₂ (DK.at frS.P.T.a)).E.Str → Prop) :
    ∀ x τ x', on x →
      (sendPiece (W := W') (F := fr₂ (DK.at frS.P.T.a)) (held b : Block (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) (Fk X N P).Cl) base d₁ d₂ co e).ior.red.out x τ = some x' →
      ∀ j ∈ [4, 5], VerifiableInference.Desc.Key.ShownAt (Fk X N P) atSix j (strsOf (fr₂ (DK.at frS.P.T.a)) x'.2) := by
  intro x τ x' _ hx j hj
  obtain ⟨-, nf4, nf5⟩ := (Johnson.RunOne.KeyLetters.six_at hZ hP hm hX hp hwant (hDK ▸ hdata)).1 "" "" ""
  rcases List.mem_cons.1 hj with rfl | hj
  · exact shown_send₂ (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd "key file" hp hdata csKey shO 7 0 "" nf4 atSix 4 rfl
      5 b base d₁ d₂ back hrow 0 hbase.symm (by rw [nTrees_cons]; omega) co e x x' τ hx
  · obtain rfl : j = 5 := List.mem_singleton.1 hj
    exact shown_send₂ (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd "key file" hp hdata csKey shSp 8 0 "" nf5 atSix 5 rfl
      5 b base d₁ d₂ back hrow 1 (by rw [hbase]) (by rw [nTrees_cons]; omega) co e x x' τ hx

end

end Johnson.RunOne.KeyNew2

#print axioms Johnson.RunOne.KeyNew2.shown_row₂
#print axioms Johnson.RunOne.KeyNew2.row_parts₂
#print axioms Johnson.RunOne.KeyNew2.shown_send₂
#print axioms Johnson.RunOne.KeyNew2.new22
#print axioms Johnson.RunOne.KeyNew2.new25
