-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/Opened.lean: the openings in the typing of a file that was read are as the strict
format asks; the premises stand in the records of the reading.

OnBytes/Maker/TypingAlike.lean has the four records of the strict format (`opened_atA`: the fields
`opened₁`, `opened₂`, `opened₃`, `openedE` of `AfterRuns`, OnBytes/TypedOracleCompiler/Joined/K/Left.lean) under
eleven premises beside the typing's value and the three chains' values. Here these are taken from
three records that other files pay or name.

  `opened_read`   **the four records**, from: the record of the three chains' reading (`ThreeRead`,
                  OnBytes/Maker/ThreeRead.lean), which gives the 32 bytes of each sender's run's
                  value (OnBytes/Maker/RunSize.lean); what is asked of the data and the reading
                  (`ReadFits`, OnBytes/Maker/AcceptAt.lean), which holds the tests `shapesFit` and
                  `sealBare` and that the openings list what was drawn; what is asked of the
                  verifier's messages (`DrawsHeldA`, OnBytes/Maker/AcceptAtA.lean): they give the
                  draws as read but for the digests; the test `saltsFit`; cfg has 32 bytes.

None of the three records is shown here. `DrawsHeldA` is a premise on the oracle functions g,
through the messages that the three chains yield under g.

Not claimed. That the typing returns a value. That a path leads to a root. Nothing on soundness.


-/
import OnBytes.Maker.TypingAlike
import OnBytes.Maker.AcceptAtA
import OnBytes.Maker.RunSize
import OnBytes.Maker.ThreeRead

set_option autoImplicit false

namespace OnBytes.Maker.Page

open OnBytes OnBytes.Maker OnBytes.Proof OnBytes.TieK
open OnBytes.Params (Rounds)
open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening Tag)
open _root_.Run _root_.Run.PQ

section
variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
  (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (a : ℕ) (W : Three.Whole)
  {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool) {I X : Type} {L : BatchProtocolWithLeafBody I X}
  (g : Fam (typedOracleFamily 256 (K + 1) L)) {t : Tag}
  {embP : PlainPart (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ t3).ann →
    PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t)} {xin : Xi → Option X} {cms : List (Dig 256)}

/-- **The four records of the strict format at the typing of a file that was read.** -/
theorem opened_read (sb : ℕ) (cfg : ByteArray)
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (RF : ReadFits a W r S₁ S₂ S₃) (hsalts : saltsFit sb W = true) (hcfg : cfg.size = 32)
    (pF : TF) (pJ : TJ) (p3 : T3) (salt : ByteArray) (path : List ByteArray)
    (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch)
    (h : typeFile C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r = some π) (x : Xi)
    (a' : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₁)
    (b' : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₂)
    (e' : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₃)
    (h₁ : (run₁ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
      (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π).det g = some a')
    (h₂ : (run₂ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
      (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π a').det g = some b')
    (h₃ : (run₃ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
      (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π a' b').det g =
      some e')
    (hρ : DrawsHeldA C (WholeD.of a W) tF tJ t3 r (glue a' b' e').1) :
    TypedOracleCompiler.Joined.Opened (256 + 8 * sb) _ (chainsOf C (WholeD.of a W) tF tJ t3).A₁
        (wire₁ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run)) a'.2.1
        (rd₁ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x π a' b' e')
        (op₁ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) π) ∧
      TypedOracleCompiler.Joined.Opened (256 + 8 * sb) _ (chainsOf C (WholeD.of a W) tF tJ t3).A₂
        (wire₂ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run)) b'.2.1
        (rd₂ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x π a' b' e')
        (op₂ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) π) ∧
      TypedOracleCompiler.Joined.Opened (256 + 8 * sb) _ (chainsOf C (WholeD.of a W) tF tJ t3).A₃
        (wire₃ (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run)) e'.2.1
        (rd₃ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x π a' b' e')
        (op₃ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) π) ∧
      OpenedE (256 + 8 * sb) (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).maxDepth
        (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).ext
        (readE (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) x (glue a' b' e').1) π.ext :=
  opened_atA C K chal a W tF tJ t3 silent run g sb cfg pF pJ p3 salt path r π h x a' b' e' h₁ h₂ h₃
    RF.shape RF.bare hsalts
    (runOfTree_32 W S₁ S₂ S₃ r file _ _ _ _ _ _ _ _ _ T.first_read T.shared_read T.second_read) hcfg
    RF.ls₁ RF.ls₂ RF.ls₃ hρ.d₁ hρ.d₂ hρ.d₃

end

end OnBytes.Maker.Page
