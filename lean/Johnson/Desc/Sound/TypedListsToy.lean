-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/TypedListsToy.lean: A TOY THAT MEETS EVERY PREMISE OF `KeySoundOfLists`
(Johnson/Desc/Sound/TypedLists.lean) with a verifier that accepts: the rule is not empty.

The toy. The configuration `Toy.kc` (Johnson/Desc/Sound/KeyLang.lean): one seed, two answers; a
table decodes with the answer `true` alone; no collision. A key file without a written round: each
chain is one block without a round; the first and the second hand the record on; the third says yes
just where the record's answer is `true`. The typed side: the block that hands its statement on,
twice, and a typed block without a round whose verifier makes the same test.

What is shown. `fits`, `tied`, `first`, `rowFit`, `below_of_zero`: the five premises.
`toy_keySound`: so the rule gives `CompilerSoundnessConditionStatements.keySound` there. `says_yes`, `says_no`: the three folds
in a row say yes at the record with the answer `true` and no at the other; by `Toy.inside` and
`Toy.outside` the first is in the language and the second is not.

Limits. A toy: no round, no error, no tree. It shows that the premises can be met together, and
nothing on the protocol.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.TypedLists
import Johnson.Desc.Sound.QuietGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace VerifiableInference.Desc.Sound.ListsToy
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.OnPublicFiles OnBytes.RunA
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString ExtMap extNone RoundSplits)
open _root_.Iop.Reduction (orOff)

/-- A record of the toy's configuration: the one seed, and an answer. -/
abbrev Rc : Type := Unit × Bool

/-- A file without a written round. -/
def tD : WholeD := ⟨0, [], [], [], id, id, id⟩

/-- The block that hands the record on. -/
def passB : Block Rc Unit := roundlessBlock "pass" 1 none 0 fun s => .ok s

/-- The block that says yes just where the record's answer is `true`. -/
def testB : Block Rc Unit := roundlessBlock "test" 3 none 0 fun s => if s.2 then .ok s else .error "no"

/-- The toy's three chains. -/
def T : Three (ckP .two) (tD.at 0) [] Rc Rc Rc Rc Rc Rc Unit Unit where
  ft₁ := 0
  ft₂ := 0
  ft₃ := 0
  p₁ := quietPiece passB 0 [] fun _ _ w => w
  l₁ := []
  p₂ := quietPiece passB 0 [] fun _ _ w => w
  l₂ := []
  p₃ := quietPiece testB 0 [] fun _ _ w => w
  l₃ := []
  n₁ := "first"
  n₂ := "shared"
  n₃ := "second"
  in₁ := id
  out₁ := fun _ s => s
  in₂ := id
  out₂ := fun _ s => s
  in₃ := some
  fin := fun _ _ => true
  d := ()
  wEnd := ()

/-- A statement read as one of the key file's language. -/
def rdW (a : Rc × (EAll (tD.at 0) []).Str) : Rc × Toy.kc.conf.E0.Str := (a.1, a.2.1)

/-- A statement read at the end. -/
def rdE (_ : Rc × (EAll (tD.at 0) []).Str) : Unit × extNone.Str := ((), ())

/-- The typed block without a round whose verifier says yes just where the answer is `true`. -/
def kTest : BK (jWf Toy.kc.conf) jEnd :=
  ⟨IOR.pure (fun rec : Rc => if rec.2 then some () else none) ⟨fun _ => (), fun q => q.elim⟩,
    fun _ _ _ => (), ()⟩

theorem kTest_good : kTest.Good where
  point := ⟨()⟩
  isLocal := ⟨fun _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ q _ _ _ _ => q.elim⟩
  know := by
    rintro ⟨⟨u, b⟩, y⟩ _
    show ∀ c w, kTest.R.red.out (((u, b) : Rc), y) () = some c → _ →
      (Toy.kc.conf.D y (u, b)).isSome = true
    intro c w hc _
    cases b with
    | false => cases hc
    | true => exact Option.isSome_iff_ne_none.2 ((Toy.inside y).resolve_left fun h => h)

/-- The three typed lists. -/
def K : KeyLists T (jWf Toy.kc.conf) jEnd where
  J₁ := jWf Toy.kc.conf
  J₂ := jWf Toy.kc.conf
  L₁ := .cons rdW id (BK.pass _) (.nil rdW id)
  L₂ := .cons rdW id (BK.pass _) (.nil rdW id)
  L₃ := .cons rdW id kTest (.nil rdE id)

theorem passTie (k : ℕ → ℕ) :
    PieceTie (F := frameAt (tD.at 0) [] k 0) (C := ckP .two)
      (quietPiece passB 0 [] fun _ _ w => w) (BK.pass (jWf Toy.kc.conf)) rdW rdW id id :=
  ⟨fun _ => .nil, fun _ => trivial, fun a τ a' _ ho => by
    have ho' : some (a.1, (quietPiece (C := ckP .two) (F := frameAt (tD.at 0) [] k 0) (W := Unit)
      passB 0 [] fun _ _ w => w).ior.imp a.2 τ) = some a' := ho
    obtain rfl := Option.some.inj ho'
    exact ⟨(), rfl, rfl, fun _ => rfl⟩⟩

theorem testTie (k : ℕ → ℕ) :
    PieceTie (F := frameAt (tD.at 0) [] k 0) (C := ckP .two)
      (quietPiece testB 0 [] fun _ _ w => w) kTest rdW rdE id id :=
  ⟨fun _ => .nil, fun _ => trivial, fun a τ a' _ ho => by
    obtain ⟨⟨u, b⟩, y⟩ := a
    cases b with
    | false => cases ho
    | true => exact ⟨(), rfl, rfl, fun _ => rfl⟩⟩

theorem tied : K.Tied where
  tie₁ := ⟨BK.pass_good _, passTie _, trivial⟩
  tie₂ := ⟨BK.pass_good _, passTie _, trivial⟩
  tie₃ := ⟨kTest_good, testTie _, trivial⟩
  seam₁ := fun _ _ => rfl
  wit₁ := fun _ => rfl
  seam₂ := fun _ _ _ h => by
    obtain rfl := Option.some.inj h
    rfl
  wit₂ := fun _ => rfl
  last := fun _ _ _ => trivial

theorem quietTiled {S : Type} {F : Frame} (b : Block S Unit) (hb : b.rounds = [])
    (e : S × F.E.Str → Iop.Tr (uLT (ckP .two) []) → Unit → Unit) :
    Tiled (quietPiece (C := ckP .two) b 0 [] e) [] :=
  ⟨⟨by rw [hb]; rfl, fun _ _ => by rw [Block.reads, hb]; rfl⟩,
    ⟨fun n sh h => (by cases h), fun d hd => (by cases hd)⟩⟩

theorem fits : T.Fits :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, quietTiled _ rfl _, quietTiled _ rfl _, quietTiled _ rfl _⟩

theorem first (rec : Rc) (y : Toy.kc.conf.E0.Str) :
    K.L₁.rd0 (T.in₁ rec, (y, fun _ => [])) = (rec, y) := rfl

theorem rowFit : RowFit (tD.at 0) [] [] :=
  ⟨fun d hd => (by cases hd), fun d hd => (by cases hd), fun d hd => (by cases hd),
    fun d hd => (by cases hd), fun l hl => (by cases hl)⟩

/-- Every entry of a list of errors is 0. -/
def Zero : {s : Shape} → Err s → Prop
  | [], _ => True
  | _ :: _, (e, ε) => e = 0 ∧ Zero ε

theorem below_of_zero (N : ℕ) (c : ℝ≥0∞) : ∀ {s : Shape} (A : RoundSplits s) (ε : Err s), Zero ε →
    Err.Below (Err.timesShared N A ε) c
  | [], _, _, _ => trivial
  | _ :: _, (a, A), (e, ε), h => by
    obtain ⟨rfl, h⟩ := h
    refine ⟨?_, below_of_zero N c A ε h⟩
    show ((match a.kind with | .lo => 0 | .sh => N * 0 : ℕ) : ℝ≥0∞) ≤ _
    cases a.kind <;> simp

/-- The three folds in a row say yes at the record with the answer `true`. -/
theorem says_yes : runRow T.run₁ T.run₂ T.run₃ ((), true) ⟨[], []⟩ ⟨[], []⟩ ⟨[], []⟩ = true := rfl

/-- They say no at the other. -/
theorem says_no : runRow T.run₁ T.run₂ T.run₃ ((), false) ⟨[], []⟩ ⟨[], []⟩ ⟨[], []⟩ = false := rfl

/-- **The rule at the toy**: all its premises are met. -/
theorem toy_keySound (DP : WholeD) (TFk TJk T3k TFp TJp T3p : Type) (tFk : TFk)
    (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp) (t3p : T3p)
    (silK : Rc → TFk → TJk → T3k → Bool)
    (silP : Toy.kc.conf.X × Rc → TFp → TJp → T3p → Bool)
    (runP : Toy.kc.conf.X × Rc → Fmt.View → Fmt.View → Fmt.View → Bool)
    (eL : LinkProtocolWithLeafCoding Rc 0) (N : ℕ) (early : Toy.kc.conf.X → Toy.kc.conf.X) (late : Option ℕ)
    (P : (filesOf Toy.kc .two tD DP tFk tJk t3k tFp tJp t3p silK (runRow T.run₁ T.run₂ T.run₃) silP
      runP eL N early late).Provers)
    (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Toy.kc .two tD DP tFk tJk t3k tFp tJp t3p silK
                                      (runRow T.run₁ T.run₂ T.run₃) silP runP eL N early late) P)
    (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Toy.kc .two tD DP tFk tJk t3k tFp tJp t3p silK
                                       (runRow T.run₁ T.run₂ T.run₃) silP runP eL N early late) P) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataOfThreeProtocols (filesOf Toy.kc .two tD DP tFk tJk t3k tFp tJp t3p silK
                                                               (runRow T.run₁ T.run₂ T.run₃) silP runP eL N early late) P Tl U) :=
  keySoundOfLists 0 Toy.kc tD DP TFk TJk T3k TFp TJp T3p tFk tJk t3k tFp tJp t3p silK silP runP eL N
    early late [] Rc Rc Rc Rc Rc Unit Unit T K P Tl U fits tied first rowFit
    (below_of_zero _ _ _ _ ⟨rfl, rfl, rfl, trivial⟩)

end VerifiableInference.Desc.Sound.ListsToy

#print axioms VerifiableInference.Desc.Sound.ListsToy.tied
#print axioms VerifiableInference.Desc.Sound.ListsToy.fits
#print axioms VerifiableInference.Desc.Sound.ListsToy.says_yes
#print axioms VerifiableInference.Desc.Sound.ListsToy.says_no
#print axioms VerifiableInference.Desc.Sound.ListsToy.toy_keySound
