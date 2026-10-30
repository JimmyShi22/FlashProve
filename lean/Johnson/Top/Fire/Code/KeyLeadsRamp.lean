-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyLeadsRamp.lean, general in the instance's type (`keyLeadsOn_of_below instK S …`): at the full size: ON THE PLAIN ROAD: THE RAMP TO THE CAP: whoever holds the key file's debt in the rule's own coin AT HIS OWN ERRORS, each piece's at most a share of 2^-128 of its rounds' challenges, holds it AT THE CAP.

Why. `KeyLeadsCap` (KeyLeads.lean) asks every piece's errors to BE the cap outright. Files that pay block by block hold `EachLeads` at their pieces' own counts, with «these are at most εs» beside. In form such files can pay, given a ramp. A piece's reduction reads neither its extractor nor its errors; a law is monotone in the errors (`Leads.mono_err`);
every list below 2^-128 is at most the cap (`Err.le_cap_of_below_inv`, Iop/ErrCap.lean): so the ramp is one walk along the maker's cut.
Main names.
  `toCap rest`: the pieces' letter with the same extractors and the cap for errors. `atCap_toCap`.
  `eachLeads_toCap`: ALONG THE MAKER's CUT (`cutRow`): `EachBelow (2⁻¹ ^ 128)` and `EachLeads on Q j` at `rest` give `EachLeads on Q j` at `toCap rest`: at any places.
  `KeyLeadsBelow F instK A E rK DK file`: `KeyLeadsCap`'s list, to the letter, with «each piece's errors are at most 2⁻¹ ^ 128» thrice in place of «are the cap».
  `keyLeadsCap_of_below`: IT GIVES `KeyLeadsCap`. (`Glues` reads of the pieces the rows' lengths alone: RowLengths.lean; «tie» reads none.)
  `keyLeadsBelow_of_cap`: THE RAMP LOSES NOTHING: the other way (`eachBelow_atCap₁ | ₂ | ₃`, Johnson/Desc/Sound/BoundsAtCap.lean): the two statements are one.
  `keyLeadsBelow_of_debt`: THE ROWS' COIN HAS THE SAME RAMP: `KeyDebt … (2⁻¹ ^ 128) …` (rows with `Keeps` at the payer's own errors) pays `KeyLeadsBelow`.
  `keyLeadsOn_of_below`: the same over a set of descriptions.
Limits. BOOK-KEEPING: NOTHING IS PAID. The bound is 2⁻¹ ^ 128 at every piece of all three chains (one leaf: no second bound for the shared chain). The pieces must be the maker's (`piecesAt`): files whose pieces are a letter under `OfDesc` lay them there first.

-/
import Johnson.Top.Fire.Code.KeyLeads
import Johnson.Top.Fire.Code.RowLengths

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

section
variable {C : _root_.Run.PQ.CK} {Fr : Frame} {S Cl W : Type}

/-- The pieces' letter with the same extractors and the cap for errors. -/
def toCap (rest : (i : ℕ) → (ds : List RDT) → Rest C Fr S W ds) : (i : ℕ) → (ds : List RDT) → Rest C Fr S W ds :=
  restCap fun i ds => (rest i ds).ext

theorem atCap_toCap (rest : (i : ℕ) → (ds : List RDT) → Rest C Fr S W ds) : AtCap (toCap rest) := atCap_restCap _

/-- **The ramp, along the maker's cut.** -/
theorem eachLeads_toCap (rest : (i : ℕ) → (ds : List RDT) → Rest C Fr S W ds) (putBack : List _root_.Fmt.RoundView)
    (on : ℕ → S × Fr.E.Str → Prop) (Q : ℕ → S × Fr.E.Str → S × Fr.E.Str → Prop) :
    ∀ (l : List (Block S Cl)) (j i base : ℕ) (ds : List RDT) (b : Block S Cl),
      EachBelow ((2 : ℝ≥0∞)⁻¹ ^ 128) ((cutRow rest putBack i base ds b l).1 :: (cutRow rest putBack i base ds b l).2) →
      EachLeads on Q j ((cutRow rest putBack i base ds b l).1 :: (cutRow rest putBack i base ds b l).2) →
      EachLeads on Q j ((cutRow (toCap rest) putBack i base ds b l).1 :: (cutRow (toCap rest) putBack i base ds b l).2)
  | [], _, _, _, _, _, hb, h =>
    ⟨h.1.mono_err (Err.le_cap_of_below_inv 128 _ (hb _ List.mem_cons_self)), h.2.1, trivial⟩
  | b' :: l, j, i, _, _, _, hb, h =>
    ⟨h.1.mono_err (Err.le_cap_of_below_inv 128 _ (hb _ List.mem_cons_self)), h.2.1,
      eachLeads_toCap rest putBack on Q l (j + 1) (i + 1) _ _ b' (fun q hq => hb q (List.mem_cons_of_mem _ hq)) h.2.2⟩

end

/-- **The key file's debt in the rule's own coin, at the payer's own errors, each piece's at most 2⁻¹ ^ 128.** -/
def KeyLeadsBelow {XiK : Type} (F : FileDescription XiK) (instK : RecFull → XiK)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (rK : RecFull) (DK : WholeD) (file : String) : Prop :=
  ∃ (W : Type)
    (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
    (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₃ F.lastChainFirstTreeNumber)
      ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (dW wEnd : W)
    (Pl : PPlaces (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂) ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
    (M : RecFull × (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str → (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop)
    (L₁ : (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop)
    (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop)
    (_ : (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str),
    F.data file = .ok (DK.at frS.P.T.a) ∧
    F.first.blocksInOrder = c₁ :: k₁ ∧ F.shared.blocksInOrder = c₂ :: k₂ ∧ F.second.blocksInOrder = c₃ :: k₃ ∧
    EachLeads Pl.on₁ Pl.Q₁ 0 ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) ∧
    EachLeads Pl.on₂ Pl.Q₂ 0 ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) ∧
    EachLeads Pl.on₃ Pl.Q₃ 0 ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃) ∧
    Glues (atDesc (F.pull instK) (piecesAt (ckP .two) (F.pull instK) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)) Pl M L₁ L₂ ∧
    (∀ rec (y : (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str) (τ : Tr (chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty).sh) (s₁ : F.S₁) (s₂ : F.S₂) (s₃ : F.S₃)
      (z : (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str),
      F.okStart (instK rec) = true →
      silK rec ((chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty).msgF τ).2 ((chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty).msgJ τ).2 ((chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty).msg3 τ).2 = true →
      F.fin (instK rec) s₁ s₂ s₃ = true →
      (Pl.on₁ 0 ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).in₁ (instK rec), (y, fun _ => [])) → M (rec, y) ((F.pub (instK rec), s₁), z)) →
      (lettersAt A (relationsAndEncodingOfClaims A E)).conf.coll y rec.1 ∨ (lettersAt A (relationsAndEncodingOfClaims A E)).conf.D y rec ≠ none) ∧
    EachBelow ((2 : ℝ≥0∞)⁻¹ ^ 128) ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) ∧
    EachBelow ((2 : ℝ≥0∞)⁻¹ ^ 128) ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) ∧
    EachBelow ((2 : ℝ≥0∞)⁻¹ ^ 128) ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)


set_option maxHeartbeats 4000000 in
/-- **It gives the debt at the cap.** -/
theorem keyLeadsCap_of_below {XiK : Type} (F : FileDescription XiK) (instK : RecFull → XiK)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (rK : RecFull) (DK : WholeD) (file : String)
    (h : KeyLeadsBelow F instK A E rK DK file) : KeyLeadsCap F instK A E rK DK file := by
  obtain ⟨W, c₁, k₁, c₂, k₂, c₃, k₃, rest₁, rest₂, rest₃, dW, wEnd, Pl, M, L₁, L₂, dS, data, q₁, q₂, q₃, e₁, e₂, e₃, G, tie, b₁, b₂, b₃⟩ := h
  have n₁ := (rowLen₁ (ckP .two) (F.pull instK) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (toCap rest₁) (toCap rest₂) (toCap rest₃) dW wEnd).trans (rowLen₁ (ckP .two) (F.pull instK) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd).symm
  have n₂ := (rowLen₂ (ckP .two) (F.pull instK) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (toCap rest₁) (toCap rest₂) (toCap rest₃) dW wEnd).trans (rowLen₂ (ckP .two) (F.pull instK) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd).symm
  have n₃ := (rowLen₃ (ckP .two) (F.pull instK) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (toCap rest₁) (toCap rest₂) (toCap rest₃) dW wEnd).trans (rowLen₃ (ckP .two) (F.pull instK) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd).symm
  refine ⟨W, c₁, k₁, c₂, k₂, c₃, k₃, toCap rest₁, toCap rest₂, toCap rest₃, dW, wEnd, Pl, M, L₁, L₂, dS, data, q₁, q₂, q₃,
    eachLeads_toCap rest₁ _ _ _ _ 0 _ _ _ _ b₁ e₁, eachLeads_toCap rest₂ _ _ _ _ 0 _ _ _ _ b₂ e₂, eachLeads_toCap rest₃ _ _ _ _ 0 _ _ _ _ b₃ e₃,
    ⟨fun x y b h₀ hs => G.g₁ x y b h₀ ((congrArg (fun n => Reduction.steps Pl.Q₁ 0 n _ b) n₁).mp hs),
      fun a b h₀ hs => G.g₂ a b h₀ ((congrArg (fun n => Reduction.steps Pl.Q₂ 0 n _ b) n₂).mp hs),
      fun a s b hi h₀ hs hf => G.g₃ a s b hi h₀ ((congrArg (fun n => Reduction.steps Pl.Q₃ 0 n _ b) n₃).mp hs) hf⟩,
    tie, atCap_toCap _, atCap_toCap _, atCap_toCap _⟩

/-- **The ramp loses nothing**: the debt at the cap is a debt at errors of at most 2⁻¹ ^ 128. -/
theorem keyLeadsBelow_of_cap {XiK : Type} (F : FileDescription XiK) (instK : RecFull → XiK)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (rK : RecFull) (DK : WholeD) (file : String)
    (h : KeyLeadsCap F instK A E rK DK file) : KeyLeadsBelow F instK A E rK DK file := by
  obtain ⟨W, c₁, k₁, c₂, k₂, c₃, k₃, rest₁, rest₂, rest₃, dW, wEnd, Pl, M, L₁, L₂, dS, data, q₁, q₂, q₃, e₁, e₂, e₃, G, tie, a₁, a₂, a₃⟩ := h
  exact ⟨W, c₁, k₁, c₂, k₂, c₃, k₃, rest₁, rest₂, rest₃, dW, wEnd, Pl, M, L₁, L₂, dS, data, q₁, q₂, q₃, e₁, e₂, e₃, G, tie,
    eachBelow_atCap₁ F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd _ le_rfl a₁,
    eachBelow_atCap₂ F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd _ le_rfl a₂,
    eachBelow_atCap₃ F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd _ le_rfl a₃⟩

/-- **The rows' coin has the same ramp**: the debt in rows AT THE PAYER's OWN ERRORS, at the bound 2⁻¹ ^ 128 (`KeyDebt`, KeyDebt.lean), pays the debt in the rule's own coin, at every record of the key. -/
theorem keyLeadsBelow_of_debt {XiK : Type} (F : FileDescription XiK) (instK : RecFull → XiK)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (rK : RecFull) (DK : WholeD) (file : String)
    (h : KeyDebt F instK A E DK ((2 : ℝ≥0∞)⁻¹ ^ 128) file) : KeyLeadsBelow F instK A E rK DK file := by
  obtain ⟨W, c₁, k₁, c₂, k₂, c₃, k₃, rest₁, rest₂, rest₃, dW, wEnd, dS, on₁, L₁, on₂, L₂, on₃, L₃, data, _, q₁, q₂, q₃, rows, b₁, b₂, b₃⟩ := h
  exact ⟨W, c₁, k₁, c₂, k₂, c₃, k₃, rest₁, rest₂, rest₃, dW, wEnd, plRows F DK on₁ L₁ on₂ L₂ on₃ L₃, mRows F instK DK L₁, l₁Rows F DK L₂, l₂Rows F DK L₃, dS,
    data, q₁, q₂, q₃, EachKeeps.leads _ 0 rows.keeps₁, EachKeeps.leads _ 0 rows.keeps₂, EachKeeps.leads _ 0 rows.keeps₃,
    glues_of_rows rows,
    fun rec y _ s₁ _ _ z hok _ _ h => tie_of_rows rows rec y ((F.pub (instK rec), s₁), z) hok h,
    b₁, b₂, b₃⟩

/-- The same over a set of descriptions. -/
theorem keyLeadsOn_of_below {XiK : Type} (instK : RecFull → XiK) (S : FileDescription XiK → Prop)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (rK : RecFull)
    (h : ∀ (F : FileDescription XiK) (DK : WholeD), S F → F.data "key file" = .ok (DK.at frS.P.T.a) → F.planOk = true →
      KeyLeadsBelow F instK A E rK DK "key file") : KeyLeadsOn instK S A E rK :=
  fun F DK hs hD hp => keyLeadsCap_of_below F instK A E rK DK "key file" (h F DK hs hD hp)

end LPFD

#print axioms LPFD.atCap_toCap
#print axioms LPFD.eachLeads_toCap
#print axioms LPFD.KeyLeadsBelow
#print axioms LPFD.keyLeadsCap_of_below
#print axioms LPFD.keyLeadsBelow_of_cap
#print axioms LPFD.keyLeadsBelow_of_debt
#print axioms LPFD.keyLeadsOn_of_below
