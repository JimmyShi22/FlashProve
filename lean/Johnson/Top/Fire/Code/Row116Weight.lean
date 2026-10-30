-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row116Weight.lean: THE KEY FILE's ROW 1.16: THE WEIGHT BESIDE THE LAW (Weight116: det · pileGives · givesClaims), AT ONE NAMED READING OF OUR WITNESS AS THE LAW's: rw116 := KeyCoinK13.witOf at the table's own matOf | mkOf.
  rw116            our witness as the kind K13's law's: the matrix read off the cells, the mask entries read off the messages: in the law's field
  on16_parts       what the promise at 16 holds (the record bears no mark)
  part116_says     what the law's reader in front gives: the part behind layPile and the chain's coming to its end, field by field
  det_paid         **det, PAID FROM THE PROMISE ALONE**: two witnesses with our four items agree on the matrix (pinT_one, Johnson/Desc/Key/KeyFrames.lean) and on message 0's mask entries (pin_one, Johnson/Desc/Msg.lean, at the promise's NoColl; the promise's ReadsPinned; the book-keeping's «the index masks' number is 0»)
  pileGives_paid   **pileGives, PAID** under hsame (the tables' letter «same» IS sameGl: two words are one element of the field): by seat_says · batt_row_psi · tensorRowHolds_iff_k13
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row116Paid
import Johnson.Desc.Key.KeyCoinK13
import Johnson.Desc.Key.KeyBattRow

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

open OnBytes.Params (OneTime Setting)
open Johnson.RunOne.KeyRows1

theorem rowOfLinClaim_member (r : TensorRow) : rowOfLinClaim (memberClaim r) = r := by
  cases r with
  | mk g psi masks target =>
    simp only [rowOfLinClaim, memberClaim, List.map_map, Function.comp_def, List.map_id']

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


/-- **Our witness, read as the law's.** -/
def rw116 (w : Wit Cells Unit M) : K13.Law.Wit GE (plan₁ (oneAt X)).m.rows (where116 X).lin.kCol :=
  Key.witOf (plan₁ (oneAt X)).m (matOf (plan₁ (oneAt X)) R w) (mkOf (plan₁ (oneAt X)) R w)

theorem on16_parts (a : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str) (ha : On₁ X N P (DK.at frS.P.T.a) B at_ R coll 16 a) :
    shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) 2 (slots₁ (oneAt X)) 16 a.1.2 = true ∧
      free₁ (Fk X N P) B.h₁ at_ (oneAt X) R coll 16 a.1 (strsOf (fr₁ (DK.at frS.P.T.a)) a.2) ∧
      NoColl (Fk X N P) B.h₁ (at_ 0).1 (at_ 0).2 a.1 (strsOf (fr₁ (DK.at frS.P.T.a)) a.2) := by
  have hn : n₁ (oneAt X) = 2 := on₁_two (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll 16 a ha
  have h : onAt (Fk X N P) B.h₁ at_ (meaning₁At (oneAt X) R) (shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) 16)
      (free₁ (Fk X N P) B.h₁ at_ (oneAt X) R coll 16) (open₁ (n₁ (oneAt X)) 16) a.1 (strsOf (fr₁ (DK.at frS.P.T.a)) a.2) := ha
  rw [hn] at h
  obtain ⟨h1, _, h3, h4⟩ := h.elim (fun hx => absurd rfl hx) id
  exact ⟨h1, h3, h4 0 (by rw [pinned_16]; exact List.mem_singleton.2 rfl)⟩

theorem part116_says (a : Xi × FirstState) (p : K13.Part) (h : part116 X a = some p) :
    ∃ rows, layPile (fun x : LookupRecord => x.keys) (oneAt X) a.2 = .ok { a.2 with pile := rows } ∧ a.2.atEnd = false ∧ p.indexMasks = a.2.idx ∧ p.pile = rows := by
  have h' : (pileOpt (fun x : LookupRecord => x.keys) (oneAt X) a.2).bind (K13.Law.partIn (batchLens (β := LookupRecord))) = some p := h
  unfold pileOpt at h'
  cases hl : layPile (fun x : LookupRecord => x.keys) (oneAt X) a.2 with
  | error e => rw [hl] at h'; cases h'
  | ok t =>
    rw [hl] at h'
    obtain ⟨rows, rfl⟩ := layPile_says _ _ _ _ hl
    have h2 : ((batchLens (β := LookupRecord)).enter { a.2 with pile := rows }).bind (batchLens (β := LookupRecord)).get? = some p := h'
    cases he : (batchLens (β := LookupRecord)).enter { a.2 with pile := rows } with
    | none => rw [he] at h2; cases h2
    | some t₂ =>
      rw [he] at h2
      obtain ⟨hend, rfl⟩ := (lens_enter _ _).1 he
      obtain ⟨_, rfl⟩ := (lens_get _ _).1 h2
      exact ⟨rows, rfl, hend, rfl, rfl⟩

/-- **det, paid from the promise alone.** -/
theorem det_paid : ∀ a p w w', On₁ X N P (DK.at frS.P.T.a) B at_ R coll 16 a → part116 X a.1 = some p → pin116 X N P DK B at_ R a w → pin116 X N P DK B at_ R a w' →
    K13.Law.AgreeAt p.indexMasks (rw116 X R w) (rw116 X R w') := by
  intro a p w w' ha hp hw hw'
  obtain ⟨hsh, hfree, hnc⟩ := on16_parts X N P DK B at_ R coll a ha
  obtain ⟨rows, _, _, hidx, _⟩ := part116_says X a.1 p hp
  have hcells : w.cells = w'.cells := pinT_one B.h₁ a.1 _ w w' (hw .pinT (by decide)) (hw' .pinT (by decide))
  have hmsg := pin_one (Fk X N P) B.h₁ (at_ 0).1 (at_ 0).2 a.1 _ w w' hnc (hw (.pin 0) (by decide)) (hw' (.pin 0) (by decide))
  have hrp : ReadsPinned B.h₁ at_ R [0, 1, 2] := hfree.2.1.2
  have hof : R.of w 0 = R.of w' 0 := by rw [hrp w 0 (by decide), hrp w' 0 (by decide)]; exact hmsg
  have h0 : a.1.2.idx = 0 := by
    have ht : ties₁ (oneAt X) 16 a.1.2 = true := ((shape₁_iff _ _ _ _ _ _ _).1 hsh).1
    unfold ties₁ tiesA at ht
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at ht
    rcases ht.1.1.1.2 with h | h
    · exact absurd h (by decide)
    · exact h
  rw [hidx, h0]
  refine ⟨?_, fun i => ?_⟩
  · show (Key.witOf _ (matOf (plan₁ (oneAt X)) R w) _).mat = (Key.witOf _ (matOf (plan₁ (oneAt X)) R w') _).mat
    unfold matOf
    rw [hcells]
    rfl
  · show readE (R.val (R.of w 0) .mask i) = readE (R.val (R.of w' 0) .mask i)
    rw [hof]

/-- **pileGives, paid**, where the tables' «same» is the field's. -/
theorem pileGives_paid (hsame : R.same = sameGl) (dZ d0 : RDT) (ds : List RDT) :
    ∀ a τ b' w, On₁ X N P (DK.at frS.P.T.a) B at_ R coll 16 a → (piece116 (Cells := Cells) (M := M) X N P DK c₁ k₁ dZ d0 ds).ior.red.out a τ = some b' →
      (meaning₁At (oneAt X) R).pile b'.1 (strsOf (fr₁ (DK.at frS.P.T.a)) b'.2) w → ∀ r ∈ row116 b'.1, K13.Law.Holds K13.Law.ρg (rw116 X R w) r := by
  intro a τ b' w _ hb' hpile r hr
  obtain ⟨_, rs, gs, hs⟩ := seat_yes X N P DK c₁ k₁ dZ d0 ds a b' τ hb'
  obtain ⟨⟨p', s'⟩, y'⟩ := b'
  obtain ⟨rows, out, msg, rs', _, _, hbt, rfl⟩ := seat_says (Cl := Claim) (fun x : LookupRecord => x.keys) (oneAt X) pieces _ a.1.2 s' rs gs hs
  obtain ⟨x, hx, hT⟩ := hpile
  have ex : x = out.1 := by
    have : some (rowOfLinClaim (memberClaim out.1)) = some x := hx
    rw [rowOfLinClaim_member] at this
    exact (Option.some.inj this).symm
  have er : r = out.1 := by
    have : r ∈ [First.rowOfClaim (memberClaim out.1)] := hr
    rw [K13.Law.rowOfClaim_member] at this
    exact List.mem_singleton.1 this
  subst ex
  rw [er]
  rw [hsame] at hT
  exact (tensorRowHolds_iff_k13 (plan₁ (oneAt X)).m _ _ out.1 (batt_row_psi hbt)).1 hT

end

end LPFD

#print axioms LPFD.det_paid
#print axioms LPFD.pileGives_paid
