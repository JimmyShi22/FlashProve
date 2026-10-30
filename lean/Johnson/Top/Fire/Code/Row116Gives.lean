-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row116Gives.lean: THE KEY FILE's ROW 1.16: THE THIRD OF THE WEIGHT: givesClaims, PAID: in front of the batching: if every row of the laid pile holds in the law's coin at rw116 w, then our two items kclaims 0 | 1 hold at w.
  part116_of       at a yes of layPile from a state that has not come to its end the law's reader in front gives a part, whose pile is the laid one
  keys_in_pile     what our reader keysAt reads at lookup l lies in the laid pile, member for member (by KeyPend.pend_law, called)
  done_at          the book-keeping at border 16 (core₁'s doneB) hands: the lookup L · the list ks that keysAt reads · ks.length = L.parts.length
  givesClaims_paid **PAID** under hsame (the tables' «same» is sameGl): by these, batt_pile_psi and tensorRowHolds_iff_k13 backwards
  weight116_of     Weight116 at rw116 FROM: hsame · le
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row116Weight
import Johnson.Desc.Key.KeyPileSays

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

theorem part116_of (X : Source) (a : Xi × FirstState) (rows : List TensorRow)
    (hlay : layPile (fun x : LookupRecord => x.keys) (oneAt X) a.2 = .ok { a.2 with pile := rows }) (hend : a.2.atEnd = false) :
    ∃ p, part116 X a = some p ∧ p.pile = rows := by
  refine ⟨{ owed := a.2.debt, heard := none, indexMasks := a.2.idx, pile := rows, msg := a.2.msgW, ids := a.2.ids, lin := a.2.lin, d := a.2.d }, ?_, rfl⟩
  show (pileOpt (fun x : LookupRecord => x.keys) (oneAt X) a.2).bind (K13.Law.partIn (batchLens (β := LookupRecord))) = _
  unfold pileOpt
  rw [hlay]
  show ((batchLens (β := LookupRecord)).enter { a.2 with pile := rows }).bind (batchLens (β := LookupRecord)).get? = _
  have he : (batchLens (β := LookupRecord)).enter ({ a.2 with pile := rows } : FirstState) = some { a.2 with pile := rows, atEnd := true } :=
    (lens_enter _ _).2 ⟨hend, rfl⟩
  rw [he]
  exact (lens_get _ _).2 ⟨rfl, rfl⟩

/-- What our reader reads at lookup l lies in the laid pile. (By KeyPend.pend_law, called.) -/
theorem keys_in_pile (one : OneTime) (s : FirstState) (rows : List TensorRow)
    (hlay : layPile (fun x : LookupRecord => x.keys) one s = .ok { s with pile := rows }) (l : Nat) (ks : List TensorRow)
    (hk : (readers₁ one).keysAt s l = some ks) : ∀ x ∈ ks, x ∈ rows := by
  obtain ⟨rowss, e, hlen, hrow⟩ := pend_law _ _ _ _ hlay
  have er : rows = rowss.flatten := congrArg (·.pile) e
  have hk' : (s.base.keys[l]?).bind (Johnson.RunOne.KeyReaders.pendingOf one l) = some ks := hk
  have hl : l < rowss.length := by
    rw [hlen]
    cases hc : s.base.keys[l]? with
    | none => rw [hc] at hk'; cases hk'
    | some cs =>
      rw [hc] at hk'
      have hk2 : (one.ranges.lookups[l]?).map (fun L => (L.parts.zip cs).map fun x => Wf.pendingRow (Wf.matrixOf one.lin) L x.1 x.2 (Wf.eqPlaces (Wf.matrixOf one.lin) x.2.point)) = some ks := hk'
      cases hL : one.ranges.lookups[l]? with
      | none => rw [hL] at hk2; cases hk2
      | some L => exact (List.getElem?_eq_some_iff.1 hL).1
  have hR := hrow l rowss[l] (List.getElem?_eq_getElem hl)
  have eR : rowss[l] = ks := Option.some.inj (hR.symm.trans hk')
  intro x hx
  rw [er]
  exact List.mem_flatten.2 ⟨rowss[l], List.getElem_mem hl, eR ▸ hx⟩

/-- What the book-keeping at border 16 hands for lookup l < 2. -/
theorem done_at (one : OneTime) (s : FirstState) (h : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 16 s = true) (l : Nat) (hl : l < 2) :
    ∃ L ks, (plan₁ one).lookups[l]? = some L ∧ (readers₁ one).keysAt s l = some ks ∧ ks.length = L.parts.length := by
  have hd : doneB (plan₁ one) (readers₁ one) 2 2 s = true := by
    simp only [core₁] at h
    simp at h
    exact h.1.2
  unfold doneB at hd
  have h1 := List.all_eq_true.1 hd l (List.mem_range.2 hl)
  simp only [hl, if_true, Bool.and_eq_true] at h1
  cases hk : (readers₁ one).keysAt s l with
  | none => rw [hk] at h1; exact absurd h1.2 (by simp)
  | some ks =>
    cases hL : (plan₁ one).lookups[l]? with
    | none => rw [hk, hL] at h1; exact absurd h1.2 (by simp)
    | some L =>
      rw [hk, hL] at h1
      exact ⟨L, ks, rfl, rfl, beq_iff_eq.1 h1.2⟩

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


/-- **givesClaims, paid**, where the tables' «same» is the field's. -/
theorem givesClaims_paid (hsame : R.same = sameGl) (dZ d0 : RDT) (ds : List RDT) :
    ∀ a τ b' w, On₁ X N P (DK.at frS.P.T.a) B at_ R coll 16 a → (piece116 (Cells := Cells) (M := M) X N P DK c₁ k₁ dZ d0 ds).ior.red.out a τ = some b' →
      (∀ p, part116 X a.1 = some p → ∀ r ∈ p.pile, K13.Law.Holds K13.Law.ρg (rw116 X R w) r) →
      ∀ l, l < 2 → (meaning₁At (oneAt X) R).kclaims l a.1 (strsOf (fr₁ (DK.at frS.P.T.a)) a.2) w := by
  intro a τ b' w ha hb' hrows l hl
  obtain ⟨_, rs, gs, hs⟩ := seat_yes X N P DK c₁ k₁ dZ d0 ds a b' τ hb'
  obtain ⟨rows, out, msg, rs', hlay, hend, hbt, _⟩ := seat_says (Cl := Claim) (fun x : LookupRecord => x.keys) (oneAt X) pieces _ a.1.2 b'.1.2 rs gs hs
  obtain ⟨p, hp, hpile⟩ := part116_of X a.1 rows hlay hend
  obtain ⟨hsh, _, _⟩ := on16_parts X N P DK B at_ R coll a ha
  obtain ⟨L, ks, hL, hk, hlen⟩ := done_at (oneAt X) a.1.2 ((shape₁_iff _ _ _ _ _ _ _).1 hsh).2 l hl
  refine ⟨L, ks, hL, hk, hlen, fun x hx => ?_⟩
  have hxr : x ∈ rows := keys_in_pile (oneAt X) a.1.2 rows hlay l ks hk x hx
  rw [hsame]
  exact (tensorRowHolds_iff_k13 (plan₁ (oneAt X)).m _ _ x (batt_pile_psi hbt x hxr)).2 (hrows p hp x (hpile ▸ hxr))

/-- **THE WEIGHT, at rw116, from hsame and the numbers.** -/
theorem weight116_of (hsame : R.same = sameGl) (dZ d0 : RDT) (ds : List RDT)
    (hle : Err.le ((K13.Law.mapsOf dZ d0 ds).err (K13.Law.errK (where116 X).rows ds.length)) (rest₁ 16 (dZ :: d0 :: ds)).err) :
    Weight116 X N P DK c₁ k₁ rest₁ B at_ R coll dZ d0 ds (rw116 X R) where
  det := det_paid X N P DK B at_ R coll
  pileGives := pileGives_paid X N P DK c₁ k₁ B at_ R coll hsame dZ d0 ds
  givesClaims := givesClaims_paid X N P DK c₁ k₁ B at_ R coll hsame dZ d0 ds
  le := hle

end

end LPFD

#print axioms LPFD.keys_in_pile
#print axioms LPFD.givesClaims_paid
#print axioms LPFD.weight116_of
