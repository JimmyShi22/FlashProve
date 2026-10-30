-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyOfRows.lean (the type of requests is a letter Xr, in `RowsOwed` too; THE CONCLUSION STANDS AT EVERY RECORD Tl OF THE FRAME's LETTERS, as in KeyPlain.lean; the public files Z and the test on the planner's bytes are not in the rule: in their place «Tl.depthReqT = 0»; the first boundary's two facts are asked as far as the rule needs; `Glues` along the records alone; M over the records): at the full size: ON THE PLAIN ROAD: FROM THE KEY FILE's ROWS OF A TABLE OF JOINTS TO ITS NAMED HYPOTHESIS ON SOUNDNESS AT EVERY RECORD OF THE FRAME's LETTERS WITH THE DESCRIPTION's OWN DECISION.

What a table gives. For each of the three chains, at each boundary i (in front of block i; the last behind the last block): a PROMISE `on i` and a CLAIM `L i`: two propositions on the statement there (the carried record; the stored table and the file's trees).
What is asked, `RowsOwed`:
  keeps₁ keeps₂ keeps₃   ONE LAW A BLOCK (`EachKeeps`, Johnson/Desc/Plain/FoldChain.lean): under the promise in front the prover has lost towards: the promise behind holds, and if the claim behind is true so is the claim in front.
  seam₁                  at the first chain's end, under its last promise: the shared chain's first promise holds at its first record, and its first claim there gives the first chain's last claim.
  seam₂                  at the shared chain's end, likewise towards the third chain, WHERE IT HAS A FIRST RECORD: «there is a first record and the first claim holds of it» gives the shared chain's last claim.
  ends                   behind the last block, under the last promise, the last claim is true: nothing is left open.
  firstOn · firstClaim   the first boundary in the frame's terms, AT THE RECORDS WHOSE INSTANCE PASSES THE DESCRIPTION's TEST ON THE INSTANCE ALONE: no collision at the record's seed AND A TABLE THAT DOES NOT DECODE give the first promise (so a promise may hold of false statements alone); the first
                         claim gives that the stored table decodes with the record.
  below₁ below₂ below₃   three bounds at εs.
Main names. `plRows`: the places of three tables (a block's relation: «the promise behind, and claim behind → claim in front»). `glues_of_rows`: **`Glues` FROM THE TWO SEAMS AND THE END**, at M := the first claim at the first record, L₁ := the shared chain's first claim, L₂ := «the third chain has a first
record and its first claim holds». `tie_of_rows`: **«tie» FROM THE FIRST BOUNDARY's TWO FACTS**: no reader of the record, no premise that a map is one to one. `keySound_of_rows`: the five facts on values and `RowsOwed` give: there are the three equations
of shapes, and under the three bounds `CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize Tl)` holds at every record Tl with runK = `gatedFileDecision b (F.pull instK).run`, b = true, `Tl.depthReqT = 0`, `Tl.εs = εs`.
THE SILLY TABLES. All claims «true»: firstClaim then says that every stored table decodes: false at a real decoder. All promises «false»: firstOn fails wherever a table has no collision. All claims «false»: `ends` fails under a promise that can be met. A verifier that refuses all meets keeps for
nothing, as soundness alone must allow. [Arguments; no theorem.]
THE DESCRIPTION's LAST TEST IS READ NOWHERE HERE (nor the silent rounds' test; its test on the instance is handed to the first boundary's two facts): whatever of soundness leans on a clause of the last test cannot be paid through this file: such a clause must stand as a block's own test, or «tie» be typed at an M that reads the first
chain's end.
Limits. A JOINING: NO ROW IS WRITTEN, NO LAW IS PAID; no member of `RowsOwed` is known. The boundaries are those between the description's own blocks as the maker cuts them (`piecesAt`). Over the description's format. The limits of KeyPlain.lean's head. Nothing on completeness or hiding.

-/
import Johnson.Top.Fire.Code.KeyPlain

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
variable {XiK : Type} (F : FileDescription XiK) (instK : RecFull → XiK)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD) (εs : ℝ≥0∞)
    {W : Type}
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
    (on₁ L₁ : ℕ → (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop) (on₂ L₂ : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop) (on₃ L₃ : ℕ → ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop)

/-- The places of three tables of rows. -/
def plRows : PPlaces (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) :=
  ⟨on₁, fun i a b => on₁ (i + 1) b ∧ (L₁ (i + 1) b → L₁ i a), on₂, fun i a b => on₂ (i + 1) b ∧ (L₂ (i + 1) b → L₂ i a),
    on₃, fun i a b => on₃ (i + 1) b ∧ (L₃ (i + 1) b → L₃ i a)⟩

/-- The first chain's claim M, over the records: the first claim, at the record's first record. It does not read the chain's end. -/
def mRows : RecFull × (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str → (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop :=
  fun a _ => L₁ 0 ((F.pub (instK a.1), F.start₁ (F.pub (instK a.1))), (a.2, fun _ => []))

/-- What is claimed of what the first chain hands on: the shared chain's first claim, at its first record. -/
def l₁Rows : (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop := fun b => L₂ 0 ((b.1, F.start₂ b.1.1), b.2)

/-- What is claimed of what the shared chain hands on: the third chain has a first record, and its first claim holds of it. -/
def l₂Rows : (F.XiPub × F.S₁ × F.S₂) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop :=
  fun a => ∃ s, (F.start₃ a.1.1 a.1.2.1 a.1.2.2).toOption = some s ∧ L₃ 0 ((a.1, s), a.2)

/-- **What is asked of the key file's rows.** -/
structure RowsOwed : Prop where
  keeps₁ : EachKeeps on₁ L₁ 0 ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)
  keeps₂ : EachKeeps on₂ L₂ 0 ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)
  keeps₃ : EachKeeps on₃ L₃ 0 ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)
  seam₁ : ∀ b : (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str, on₁ (0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁.length) b →
    on₂ 0 ((b.1, F.start₂ b.1.1), b.2) ∧ (L₂ 0 ((b.1, F.start₂ b.1.1), b.2) → L₁ (0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁.length) b)
  seam₂ : ∀ b : ((F.XiPub × F.S₁) × F.S₂) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str, on₂ (0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂.length) b →
    (∀ s, (F.start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s → on₃ 0 (((b.1.1.1, b.1.1.2, b.1.2), s), b.2)) ∧
      ((∃ s, (F.start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s ∧ L₃ 0 (((b.1.1.1, b.1.1.2, b.1.2), s), b.2)) →
        L₂ (0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂.length) b)
  ends : ∀ b : ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str, on₃ (0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃.length) b → L₃ (0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃.length) b
  firstOn : ∀ rec (y : (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str), F.okStart (instK rec) = true → ¬ (lettersAt A (relationsAndEncodingOfClaims A E)).conf.coll y rec.1 → (lettersAt A (relationsAndEncodingOfClaims A E)).conf.D y rec = none →
    on₁ 0 ((F.pub (instK rec), F.start₁ (F.pub (instK rec))), (y, fun _ => []))
  firstClaim : ∀ rec (y : (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str), F.okStart (instK rec) = true → ¬ (lettersAt A (relationsAndEncodingOfClaims A E)).conf.coll y rec.1 →
    L₁ 0 ((F.pub (instK rec), F.start₁ (F.pub (instK rec))), (y, fun _ => [])) → (lettersAt A (relationsAndEncodingOfClaims A E)).conf.D y rec ≠ none

variable {F instK A E DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd on₁ L₁ on₂ L₂ on₃ L₃}

/-- **`Glues` from the two seams and the end.** -/
theorem glues_of_rows (h : RowsOwed F instK A E DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd on₁ L₁ on₂ L₂ on₃ L₃) :
    Glues (atDesc (F.pull instK) (piecesAt (ckP .two) (F.pull instK) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)) (plRows F DK on₁ L₁ on₂ L₂ on₃ L₃) (mRows F instK DK L₁) (l₁Rows F DK L₂) (l₂Rows F DK L₃) where
  g₁ := fun x y b _ hs =>
    have k := steps_keeps on₁ L₁ _ 0 _ b hs
    have s := h.seam₁ b k.1
    ⟨s.1, fun hl => k.2 (s.2 hl)⟩
  g₂ := fun a b _ hs =>
    have k := steps_keeps on₂ L₂ _ 0 _ b hs
    have s := h.seam₂ b k.1
    ⟨fun s₃ e => by
        obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 e
        exact s.1 t ht,
      fun hl => k.2 (s.2 hl)⟩
  g₃ := fun a s b e _ hs _ => by
    have k := steps_keeps on₃ L₃ _ 0 _ b hs
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 e
    exact ⟨t, ht, k.2 (h.ends b k.1)⟩

/-- **«tie» from the first boundary's two facts.** -/
theorem tie_of_rows (h : RowsOwed F instK A E DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd on₁ L₁ on₂ L₂ on₃ L₃)
    (rec : RecFull) (y : (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str) (e : (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str)
    (hok : F.okStart (instK rec) = true)
    (hm : on₁ 0 ((F.pub (instK rec), F.start₁ (F.pub (instK rec))), (y, fun _ => [])) → mRows F instK DK L₁ (rec, y) e) :
    (lettersAt A (relationsAndEncodingOfClaims A E)).conf.coll y rec.1 ∨ (lettersAt A (relationsAndEncodingOfClaims A E)).conf.D y rec ≠ none := by
  by_cases hcoll : (lettersAt A (relationsAndEncodingOfClaims A E)).conf.coll y rec.1
  · exact Or.inl hcoll
  · by_cases hD : (lettersAt A (relationsAndEncodingOfClaims A E)).conf.D y rec = none
    · exact Or.inr (h.firstClaim rec y hok hcoll (hm (h.firstOn rec y hok hcoll hD)))
    · exact Or.inr hD

end

set_option maxHeartbeats 4000000 in
/-- **From the key file's rows to its hypothesis on soundness, at every record of the frame's letters whose decision on the key file is the description's own behind an open gate, whose key file's request tree has one leaf and whose bound is εs.** -/
theorem keySound_of_rows {XiK : Type} (F : FileDescription XiK) (instK : RecFull → XiK)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD) (εs : ℝ≥0∞)
    {W : Type} (file : String)
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
    (data : F.data file = .ok (DK.at frS.P.T.a)) (sealed : F.sealLast = true)
    (head₁ : F.first.blocksInOrder = c₁ :: k₁) (head₂ : F.shared.blocksInOrder = c₂ :: k₂) (head₃ : F.second.blocksInOrder = c₃ :: k₃)
    (on₁ L₁ : ℕ → (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop) (on₂ L₂ : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop) (on₃ L₃ : ℕ → ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop)
    (rows : RowsOwed F instK A E DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd on₁ L₁ on₂ L₂ on₃ L₃)
    (dS : (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str) :
    ∃ (h₁ : (rowIOR (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁).shape = uLT (ckP .two) (DK.at frS.P.T.a).ds₁)
      (h₂ : (rowIOR (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂).shape = uLT (ckP .two) (DK.at frS.P.T.a).ds₂)
      (h₃ : (rowIOR (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃).shape = uLT (ckP .two) (DK.at frS.P.T.a).ds₃),
      Err.Below (errOwn (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁ (DK.at frS.P.T.a).ds₁ h₁) εs →
      Err.Below (errOwn (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂ (DK.at frS.P.T.a).ds₂ h₂) εs →
      Err.Below (errOwn (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃ (DK.at frS.P.T.a).ds₃ h₃) εs →
      ∀ {DP : WholeD} {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
        {runP : Xr × RecFull → PQ.View → PQ.View → PQ.View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
        {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ} {early : Xr → Xr} {salt K : ℕ}
        {b : Bool} (_ : b = true) (_ : runK = gatedFileDecision b (F.pull instK).run)
        {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
        (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
        (_ : Tl.depthReqT = 0) (_ : Tl.εs = εs),
        CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize Tl) := by
  obtain ⟨h₁, h₂, h₃⟩ := shapesOfData (ckP .two) F file (DK.at frS.P.T.a) data sealed c₁ k₁ c₂ k₂ c₃ k₃ head₁ head₂ head₃ rest₁ rest₂ rest₃ dW wEnd
  refine ⟨h₁, h₂, h₃, fun b₁ b₂ b₃ DP runK runP ds xs dec rK rP depthReq early salt K b hb er P Tl hd hε => ?_⟩
  subst hε
  exact keySound_plain_of_F F instK A E DK file c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd (plRows F DK on₁ L₁ on₂ L₂ on₃ L₃) h₁ h₂ h₃
    (mRows F instK DK L₁) (l₁Rows F DK L₂) (l₂Rows F DK L₃) Tl.εs dS hb er Tl
    ⟨data, sealed, head₁, head₂, head₃, EachKeeps.leads _ 0 rows.keeps₁, EachKeeps.leads _ 0 rows.keeps₂, EachKeeps.leads _ 0 rows.keeps₃,
      glues_of_rows rows,
      fun rec y _ s₁ _ _ z hok _ _ h => tie_of_rows rows rec y ((F.pub (instK rec), s₁), z) hok h,
      b₁, b₂, by rw [hd]; simp, b₃⟩

end LPFD

#print axioms LPFD.glues_of_rows
#print axioms LPFD.tie_of_rows
#print axioms LPFD.keySound_of_rows
