-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12FwdFacts.lean: ROW 1.15 OF THE KEY FILE's TABLES: THE PROMISE's HALF (the premise «fwd» of gives_of_halves, Johnson/RunOne/Law/K12GivesHalves.lean) FROM FOUR FACTS AT THE BLOCK's OWN decide's YES: in the form in which the tables' files state what a block owes (emptyRow_keeps' hdec, Johnson/Desc/Key/KeyKeeps.lean). One statement; its proof is one call of onAt_fwd_sub (KeyQuietSub.lean). IT MOVES THE WEIGHT; IT PAYS NONE.
OBJECT. gives_of_halves' premise fwd. USER. Whoever fills Left15 | Left15J by the two halves.
LETTERS. The35.lean's. Premises: hl: the plan has two lookups: so that the table's open sets at the borders 15 and 16 can be evaluated (they are typed at the plan's number of lookups) · hdec: wherever the 15th block, as the piece holds it, decides a ↦ b:
  (marked) the reader «marked» says the same of both states [at today's readers it is constantly false: idle, kept for the form];
  (smp) at each pin still open behind, the reading's sample is the same in front and behind: A PREMISE THAT SPEAKS OF THE TABLES' LETTER B.h₁: the tables' one payer of such facts (ReadsO) wants the whole array of messages and the whole book unturned: a proximity test turns both: the local premise for the tests' rows is SmOnly (smp_15, K12Facts15.lean, takes it);
  (shape) the book-keeping's step: shape₁ at 15 in front gives shape₁ at 16 behind;
  (free) the promise's last letter's step, under the book-keeping in front (so that a payer may spend the ties) and the strings' staying: IT HOLDS A PREMISE ON THE READING's recOf (FreeAt).

  pins_sub: at two lookups the pins open at 16 are among those open at 15: by evaluation.
  fwd_of_facts: the statement.
"What was handed rides" (b.1 = a.1) is NOT among the facts: onAt_fwd_sub takes two states and spends no such equation.
Limits. hdec is shown of no block.
(Where this
and lean/THEOREM.md differ, the page holds.)
Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12GivesHalves
import Johnson.RunOne.Law.KeyQuietSub

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace Johnson.RunOne.Law.K12AtThe21
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
open VerifiableInference.Desc.K12
open Johnson.RunOne.Sound (bareB)
open Johnson.RunOne.KeyRows1 (n₁ R₁ open₁ plan₁ readers₁ book₁ slots₁ free₁ meaning₁At)
open LPFD

theorem pins_sub : ∀ k ∈ pinned (open₁ 2 16), k ∈ pinned (open₁ 2 15) := by decide

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
    (coll : Strs → Rec → Prop) (notBad : List OnBytes.E → Strs → Prop) (off₂ off₃ : ℕ → ℕ)

/-- **The promise's half of row 1.15 from four facts at decide's yes.** -/
theorem fwd_of_facts (hl : (lookupsOf X.Y.k.oneTime).length = 2)
    (hdec : ∀ a rs gs b, (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a rs gs = .ok b →
      (readers₁ (oneAt X)).marked a.2 = (readers₁ (oneAt X)).marked b.2 ∧
      (shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) 15 a.2 = true → ∀ y, free₁ (Fk X N P) B.h₁ at_ (oneAt X) R coll 15 a y → ∀ k ∈ pinned (open₁ (n₁ (oneAt X)) 16), B.h₁.smp a (at_ k).1 (at_ k).2 = B.h₁.smp b (at_ k).1 (at_ k).2) ∧
      (shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) 15 a.2 = true → shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) 16 b.2 = true) ∧
      (shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) 15 a.2 = true → ∀ y y', StrsStay (Fk X N P) at_ (open₁ (n₁ (oneAt X)) 15) y y' → free₁ (Fk X N P) B.h₁ at_ (oneAt X) R coll 15 a y → free₁ (Fk X N P) B.h₁ at_ (oneAt X) R coll 16 b y')) :
    ∀ a b rs gs, (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) 15 a → (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a.1 rs gs = .ok b.1 →
      StrsStay (Fk X N P) at_ (open₁ (n₁ (oneAt X)) 15) (strsOf (fr₁ (DK.at frS.P.T.a)) a.2) (strsOf (fr₁ (DK.at frS.P.T.a)) b.2) → (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) 16 b := by
  intro a b rs gs ha hd Hy
  obtain ⟨h1, h2, h3, h4⟩ := hdec a.1 rs gs b.1 hd
  have hn : n₁ (oneAt X) = 2 := hl
  exact KeyQuietSub.onAt_fwd_sub (Fk X N P) B.h₁ at_ (meaning₁At (oneAt X) R) _ _ _ _ (open₁ (n₁ (oneAt X)) 15) (open₁ (n₁ (oneAt X)) 16)
    (by rw [hn]; exact pins_sub) a.1 b.1 _ _ (fun hu => h1.trans hu) (fun hs hf => h2 hs _ hf) Hy (fun hs => h4 hs _ _ Hy) h3 ha

end

end Johnson.RunOne.Law.K12AtThe21

#print axioms Johnson.RunOne.Law.K12AtThe21.pins_sub
#print axioms Johnson.RunOne.Law.K12AtThe21.fwd_of_facts
