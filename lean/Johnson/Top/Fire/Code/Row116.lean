-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row116.lean: A SECOND TRACER (beside Row10.lean): THE KEY FILE's ROW 1.16 (batt.1.batt: the kind K13's batching: A TEST WITH A DRAW) TAKEN THE WHOLE ROAD UP TO THE FIELD r1_16 OF The35 (The35.lean).
EVERY UNPAID THING IS A NAMED FIELD OF ONE STRUCTURE: Owed116. «back» has the promise in front (Johnson/Desc/K13/Law/GoodAny.lean).
OBJECT: The35.r1_16: KeepsAt On₁' Cl₁ ‹the maker's own row of chain 1› 16 · USER: the35_of_21's caller (The21.r1_16 is one of its 21 fields) · LETTERS: X N P · the maker's cut and rests · B at_ R coll · the stretch dZ d0 ds · rw (how the tables' witness is read as the law's).
THE ROAD: goodIn_any (Johnson/Desc/K13/Law/GoodAny.lean) at the description's own sixteenth block, held (byBatt_held: PAID) ⟹ [batt_good: a change of relations] Piece.GoodIn at the tables' R₁ 16 | R₁ 17 ⟹ [keepsAt_good₁: keeps_of_goodIn;
keepsAt_at₁] KeepsAt On₁ Cl₁ row 16 ⟹ [KeepsAt.reached · rowBlocksF₁] the history woven in.
  bareOf · block16   (BOTH STAND IN Johnson/RunOne/KeyStep16.lean) PAID: under hl the first chain's sixteenth block IS bareOf (Key.batchTableRows (·.keys) one pieces (rootsBefore D (batchRound D))): THE SEAT AS Chain.blocksInOrder LAYS IT: its test on the plan is the stricter by «&& b.hasNoClaimsAndNothingAfter»; its decision is the seat's
  ByBatt.bare · byBatt_seat   PAID: the law's premise on the block, at that block as a piece holds it
  open₁_16 | open₁_17   PAID: what is open: unmarked · pinT · pin 0 · srow 0 with kclaims 0 · kclaims 1 in front, with pile behind
  common · pin116       the law's letter Pin := THE TABLES' FOUR RIDING ITEMS, at one witness
  Owed116      WHAT IS OWED: hl · long · stretch · declared · len · det · back · stays · pileGives · givesClaims · le
  good116_of   PROVED FROM Owed116: THE KIND K13's LAW CALLED AT THE KEY FILE's OWN BLOCK 16, AT THE KEY's OWN LENS, OVER FirstState: GoodIn from the tables' promise at 16 to that at 17, at the tables' own relations
  r1_16_of     PROVED FROM Owed116 AND q₁ (through good116_of)
  the21_with_16   THE FIT: r1_16_of's conclusion IS The21's field r1_16, by Lean's own check of types
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.The35
import Johnson.Desc.K13.Law.RowBatt
import Johnson.Desc.Key.KeyBattBy
import Johnson.RunOne.KeyStep16

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace LPFD
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃ seam₁_at_fk seam₂_at_fk ends_at_fk)
open Johnson.RunOne.KeyRows1 (FirstLetters firstOn_of firstClaim_of CollCell ReadsL open₁)
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₃)

open Johnson.RunOne.KeyRows1 (on₁ R₁ L₁ meaning₁At n₁ n₁_two)
open OnBytes.Params (OneTime Setting)


/-- The law's premise reads the decision alone: it rides. -/
theorem _root_.VerifiableInference.Desc.K13.Law.ByBatt.bare {T Cl : Type} {b : Block T Cl} {P : K13.Where} {partF : T → Option K13.Part} {rowB : T → List TensorRow}
    (h : K13.Law.ByBatt b P partF rowB) : K13.Law.ByBatt (bareOf b) P partF rowB := ⟨fun t t' rs gs hd => h.yes t t' rs gs hd⟩

/-- **The premise on the block, at the seat as the chain lays it and as a piece holds it.** -/
theorem byBatt_seat (one : OneTime) (sent : Nat) :
    K13.Law.ByBatt (held (P := Xi) (bareOf (batchTableRows (Cl := Claim) (fun x : LookupRecord => x.keys) one pieces sent))) (batchWhere one pieces sent)
      (fun a => (pileOpt (fun x : LookupRecord => x.keys) one a.2).bind (K13.Law.partIn (batchLens (β := LookupRecord)))) (fun a => K13.Law.rowOut (batchLens (β := LookupRecord)) a.2) :=
  ((byBatt_batch (fun x : LookupRecord => x.keys) one pieces sent).bare).held


/-- The four items that ride across the batching. -/
def common : List KItem := [.unmarked, .pinT, .pin 0, .srow 0]

theorem open₁_16 : open₁ 2 16 = common ++ [.kclaims 0, .kclaims 1] := by decide +kernel
theorem open₁_17 : open₁ 2 17 = common ++ [.pile] := by decide +kernel

section
variable {Cells M Smp Rec : Type} (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD) {W : Type}
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
    (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
    (coll : Strs → Rec → Prop) (off₂ off₃ : ℕ → ℕ)


/-- The law's letter Pin: the tables' four items that ride across, at one witness. -/
def pin116 (a : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str) (w : Wit Cells Unit M) : Prop :=
  relAt (Fk X N P) B.h₁ at_ (meaning₁At (oneAt X) R) common a.1 (strsOf (fr₁ (DK.at frS.P.T.a)) a.2) w

/-- The seat, its numbers, and the law's two readers at the statement that a piece carries. -/
abbrev seat116 : Block FirstState Claim := bareOf (batchTableRows (fun x : LookupRecord => x.keys) (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1)))
abbrev where116 : K13.Where := batchWhere (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
abbrev part116 (a : Xi × FirstState) : Option K13.Part := (pileOpt (fun x : LookupRecord => x.keys) (oneAt X) a.2).bind (K13.Law.partIn (batchLens (β := LookupRecord)))
abbrev row116 (a : Xi × FirstState) : List TensorRow := K13.Law.rowOut (batchLens (β := LookupRecord)) a.2

/-- The law's own piece at the maker's base. -/
abbrev piece116 (dZ d0 : RDT) (ds : List RDT) : Piece (ckP .two) (fr₁ (DK.at frS.P.T.a)) (Xi × FirstState) Claim (Wit Cells Unit M) :=
  K13.Law.pieceAt (fr₁ (DK.at frS.P.T.a)) (held (seat116 X)) (where116 X).rows
    (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 16) dZ d0 ds

/-- **WHAT IS OWED AT ROW 1.16, FIELD BY FIELD.** -/
structure Owed116 (x₀ x₁ : Lookup) {nR k : ℕ} (dZ d0 : RDT) (ds : List RDT) (rw : Wit Cells Unit M → K13.Law.Wit GE nR k) : Prop where
  /-- PUBLIC: the plan's lookups are a list of two (as The35's hl) -/
  hl : lookupsOf (oneAt X) = [x₀, x₁]
  /-- PUBLIC: blocks stand behind the sixteenth (by KeyTenAt's flat_length under hw: 19) -/
  long : 16 < k₁.length
  /-- THE DATA: the maker's stretch at 16 is the batching's: sigma's round, epsilon's, the variables' -/
  stretch : cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 16 = dZ :: d0 :: ds
  /-- THE DATA: the law's own test on the plan's written rounds -/
  declared : K13.Law.Declared (where116 X) dZ d0 ds
  len : ds.length = k
  /-- THE LAW's hdet: two witnesses with the tables' four items agree on the matrix and on the index masks' ledger's entries -/
  det : ∀ a p w w', On₁ X N P (DK.at frS.P.T.a) B at_ R coll 16 a → part116 X a.1 = some p → pin116 X N P DK B at_ R a w → pin116 X N P DK B at_ R a w' →
    K13.Law.AgreeAt p.indexMasks (rw w) (rw w')
  /-- THE LAW's hback: UNDER THE PROMISE IN FRONT, at a yes the tables' four items go back -/
  back : ∀ a τ b' w, On₁ X N P (DK.at frS.P.T.a) B at_ R coll 16 a → (piece116 (Cells := Cells) (M := M) X N P DK c₁ k₁ dZ d0 ds).ior.red.out a τ = some b' → pin116 X N P DK B at_ R b' w → pin116 X N P DK B at_ R a w
  /-- THE LAW's hon: at a yes the promise at 16 gives the promise at 17 -/
  stays : ∀ a τ b', On₁ X N P (DK.at frS.P.T.a) B at_ R coll 16 a → (piece116 (Cells := Cells) (M := M) X N P DK c₁ k₁ dZ d0 ds).ior.red.out a τ = some b' → On₁ X N P (DK.at frS.P.T.a) B at_ R coll 17 b'
  /-- THE TIE BEHIND: the tables' item «pile» at 17 says that the law's row behind is true -/
  pileGives : ∀ a τ b' w, On₁ X N P (DK.at frS.P.T.a) B at_ R coll 16 a → (piece116 (Cells := Cells) (M := M) X N P DK c₁ k₁ dZ d0 ds).ior.red.out a τ = some b' →
    (meaning₁At (oneAt X) R).pile b'.1 (strsOf (fr₁ (DK.at frS.P.T.a)) b'.2) w → ∀ r ∈ row116 b'.1, K13.Law.Holds K13.Law.ρg (rw w) r
  /-- THE TIE IN FRONT: that all rows of the laid pile are true says the tables' items «kclaims 0» and «kclaims 1» at 16 -/
  givesClaims : ∀ a τ b' w, On₁ X N P (DK.at frS.P.T.a) B at_ R coll 16 a → (piece116 (Cells := Cells) (M := M) X N P DK c₁ k₁ dZ d0 ds).ior.red.out a τ = some b' →
    (∀ p, part116 X a.1 = some p → ∀ r ∈ p.pile, K13.Law.Holds K13.Law.ρg (rw w) r) →
    ∀ l, l < 2 → (meaning₁At (oneAt X) R).kclaims l a.1 (strsOf (fr₁ (DK.at frS.P.T.a)) a.2) w
  /-- THE ERRORS: the law's own are at most the maker's rest's -/
  le : Err.le ((K13.Law.mapsOf dZ d0 ds).err (K13.Law.errK (where116 X).rows ds.length)) (rest₁ 16 (dZ :: d0 :: ds)).err

/-- **THE KIND K13's LAW, CALLED AT THE KEY FILE's OWN BLOCK 16, AT THE KEY's OWN LENS, OVER FirstState**: the piece of the held seat at the law's own errors is GoodIn FROM THE TABLES' PROMISE AT 16 TO THAT AT 17, AT THE TABLES' OWN RELATIONS AT BOTH BORDERS: goodIn_any (Johnson/Desc/K13/Law/GoodAny.lean; through RowBatt.batt_good) at byBatt_seat. No letter of the law is left: on | on' | Pin | rw | partF | rowB are the tables'. -/
theorem good116_of (x₀ x₁ : Lookup) {nR k : ℕ} (dZ d0 : RDT) (ds : List RDT) (rw : Wit Cells Unit M → K13.Law.Wit GE nR k) (H : Owed116 X N P DK c₁ k₁ rest₁ B at_ R coll x₀ x₁ dZ d0 ds rw) :
    (piece116 (Cells := Cells) (M := M) X N P DK c₁ k₁ dZ d0 ds).GoodIn (On₁ X N P (DK.at frS.P.T.a) B at_ R coll 16) (On₁ X N P (DK.at frS.P.T.a) B at_ R coll 17) (R₁ (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R 16) (R₁ (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R 17) := by
  have hn : n₁ (oneAt X) = 2 := n₁_two _ x₀ x₁ H.hl
  have hby : K13.Law.ByBatt (held (P := Xi) (seat116 X)) (where116 X) (part116 X) row116 :=
    byBatt_seat (oneAt X) (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
  refine K13.Law.batt_good _ (where116 X) _ _ dZ d0 ds H.declared k H.len (part116 X) row116 hby rw (pin116 X N P DK B at_ R) _ _ H.det H.back H.stays _ _ ?_ ?_
  · intro a τ b' w ha hb' _ hR
    have hR' : relAt (Fk X N P) B.h₁ at_ (meaning₁At (oneAt X) R) (open₁ (n₁ (oneAt X)) 17) b'.1 (strsOf (fr₁ (DK.at frS.P.T.a)) b'.2) w := hR
    rw [hn, open₁_17] at hR'
    exact ⟨fun i hi => hR' i (List.mem_append_left _ hi), H.pileGives a τ b' w ha hb' (hR' .pile (by simp))⟩
  · intro a τ b' w ha hb' _ _ hL
    show relAt (Fk X N P) B.h₁ at_ (meaning₁At (oneAt X) R) (open₁ (n₁ (oneAt X)) 16) a.1 (strsOf (fr₁ (DK.at frS.P.T.a)) a.2) w
    rw [hn, open₁_16]
    intro i hi
    rcases List.mem_append.1 hi with hc | hk
    · exact hL.1 i hc
    · have hg := H.givesClaims a τ b' w ha hb' hL.2
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl
      · exact hg 0 (by omega)
      · exact hg 1 (by omega)

theorem r1_16_of (x₀ x₁ : Lookup) {nR k : ℕ} (dZ d0 : RDT) (ds : List RDT) (rw : Wit Cells Unit M → K13.Law.Wit GE nR k)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (H : Owed116 X N P DK c₁ k₁ rest₁ B at_ R coll x₀ x₁ dZ d0 ds rw) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 16 := by
  have G := good116_of X N P DK c₁ k₁ rest₁ B at_ R coll x₀ x₁ dZ d0 ds rw H
  exact KeepsAt.reached _ _ (rowBlocksF₁ q₁ 16)
    (keepsAt_good₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd
      (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) (fun j => R₁ (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R j) 16 (seat116 X)
      (fun b hb => block16 (oneAt X) X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ H.hl b (by rw [← q₁] at hb; exact hb))
      (dZ :: d0 :: ds) H.stretch (cutPut_inner _ _ 16 (by simpa using H.long))
      ⟨fun _ _ w => w, (K13.Law.mapsOf dZ d0 ds).err (K13.Law.errK (where116 X).rows ds.length)⟩ G H.le)

/-- **THE FIT, BY LEAN's OWN CHECK OF TYPES**: what r1_16_of ends in IS the field r1_16 of The21 (and of The35): a The21 with that one field laid anew from Owed116. (It fills nothing else: the other twenty are handed in.) -/
theorem the21_with_16 (x₀ x₁ : Lookup) {nR k : ℕ} (dZ d0 : RDT) (ds : List RDT) (rw : Wit Cells Unit M → K13.Law.Wit GE nR k)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (H : Owed116 X N P DK c₁ k₁ rest₁ B at_ R coll x₀ x₁ dZ d0 ds rw)
    (T : The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃) :
    The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃ :=
  { T with r1_16 := r1_16_of X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R coll x₀ x₁ dZ d0 ds rw q₁ H }

end

end LPFD

#print axioms LPFD.byBatt_seat
#print axioms LPFD.open₁_16
#print axioms LPFD.good116_of
#print axioms LPFD.r1_16_of
#print axioms LPFD.the21_with_16
