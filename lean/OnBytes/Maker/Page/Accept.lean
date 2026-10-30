-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/Accept.lean: the decision of a file's reduction says yes at the transcripts that
the three chains' values under g give, from the verifier program's own reading, tests on the data,
and the nine fields `GRows`: seven laws on g and two conditions on the instance in a query.

OnBytes/Maker/AcceptAtA.lean gives the decision's yes (`accept_threeA`) from a value of the typing,
what the chains have yielded of roots, `DrawsHeldA`, `ReadFits`, the silent rounds' test and the
run's yes. Here the second comes from the runs' values (OnBytes/Maker/TypingFlags.lean) and the
third from OnBytes/Maker/Page/Runs.lean. The outcome is the decision's yes at three transcripts: one
field of the ten of `AfterRuns` (OnBytes/TypedOracleCompiler/Joined/K/Left.lean); it is no verifier's yes.

The data are a letter W with the equation W = `Three.Whole.of` R₁ R₂ R₃.

Main theorem.
  `accept_of_read`: for any run: from `ThreeRead`, the hypotheses of `draws_of_read`, `ReadFits`,
    the silent rounds' test and the run's yes at all views that are the file's own but for digests.
No letter stands under "there is" in its statement.

What is not claimed. None of the hypotheses: the head of OnBytes/Maker/Page/Runs.lean lists those on
the reading, the data and g, says which reading is meant, and names the letters that nothing ties.
`ReadFits`: OnBytes/Maker/OfThreeChains.lean gives it from the record of the program's reading and
yes. The run's yes: `keyRun_yesA`, `proofRun_yesA` (OnBytes/Maker/ViewsAlike.lean). Nothing on
soundness.


-/
import OnBytes.Maker.Page.Runs
import OnBytes.Maker.TypingFlags

set_option autoImplicit false

namespace OnBytes.Maker.Page

open Rom TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Joined.K TypedOracleCompiler.Compile.Batch
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ _root_.Compile.Joined
open OnBytes.Params (Rounds)
open OnBytes.TwoLaws (ViewAlike)
open OnBytes.Proof (TailPublic FirstEnd SharedEnd TailRead)

variable {file : ByteArray} {i : ℕ} {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead}
  {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds}
  {S₃ : Fmt.SpecX} {R₃ : Rounds} {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag} (C : CK) (K : ℕ)
  (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (a : ℕ) {TF TJ T3 : Type} (tF : TF) (tJ : TJ)
  (t3 : T3)

/-- **The decision's yes at the three chains' transcripts in a row, for any run.** -/
theorem accept_of_read (W : Three.Whole) (hW : W = Three.Whole.of R₁ R₂ R₃) {p : TailPublic}
    {block1 : Blk FirstEnd} {start1 : Start} {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray}
    {n₁ : Fmt.Rand} {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool)
    (run : Xi → View → View → View → Bool)
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁)
    (hR : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) (hs : SmallThree S₁ S₂ S₃ file)
    (hok : okAt a (some (R₁, R₂, R₃)) = true) (f : Fmt.Fld)
    (blocks : ∀ d ∈ (WholeD.of a W).ds₁ ++ ((WholeD.of a W).ds₂ ++ (WholeD.of a W).ds₃),
      (bsRound f d.entry d.kind).b ≤ K)
    (embP : PlainPart (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t)) (xin : Xi → Option X) (cms : List (Dig 256))
    (x : Xi) (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch)
    (g : Fam (typedOracleFamily 256 (K + 1) L)) (sb : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3)
    (salt : ByteArray) (path : List ByteArray)
    (hπ : typeFile C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r = some π)
    (Gr : GRows (L := L) (t := t) (C := C) (K := K) (rF := plainRS TF tF) (rJ := plainRS TJ tJ)
      (r3 := plainRS T3 t3) (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs (WholeD.of a W).ds₁)
      (ds₂ := toRDs (WholeD.of a W).ds₂) (ds₃ := toRDs (WholeD.of a W).ds₃)
      (D := wholeDesc C (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π g Fmt.oracle [] [] S₁
      S₂ S₃ r.first.out r.shared.out r.second.out (R₁.map (·.1)).dropLast)
    (hkit₁ : TypedOracleCompiler.Run.PQ.KitFits S₁.base.plan.field C K chal)
    (hkit₂ : TypedOracleCompiler.Run.PQ.KitFits S₂.base.plan.field C K chal)
    (hkit₃ : TypedOracleCompiler.Run.PQ.KitFits S₃.base.plan.field C K chal)
    (A : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₁)
    (B : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₂)
    (E : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₃)
    (h₁ : (run₁ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) (wqWhole C K chal (WholeD.of a
      W) tF tJ t3 silent run) embP xin cms x π).det g = some A)
    (h₂ : (run₂ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) (wqWhole C K chal (WholeD.of a
      W) tF tJ t3 silent run) embP xin cms x π A).det g = some B)
    (h₃ : (run₃ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) (wqWhole C K chal (WholeD.of a
      W) tF tJ t3 silent run) embP xin cms x π A B).det g = some E) (hr : ReadFits a W r S₁ S₂ S₃)
    (hsil : silent x pF pJ p3 = true)
    (hrun : ∀ v₁ v₂ v₃, ViewAlike (dropSeal r.first.view) v₁ → ViewAlike r.shared.view v₂ →
      ViewAlike r.second.view v₃ → run x v₁ v₂ v₃ = true) :
    (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).accept x
      ((wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).ext.build fun q => (π.ext q).map
        Opening.sym)
      (Tr.app (s := (chainsOf C (WholeD.of a W) tF tJ t3).c₁) (t := (chainsOf C (WholeD.of a W) tF
        tJ t3).c₂ ++ (chainsOf C (WholeD.of a W) tF tJ t3).c₃) (TypedOracleCompiler.Joined.tr₁ (wholeDesc C
                        (WholeD.of a W) tF tJ t3 silent run) (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run)
        π A) (Tr.app (s := (chainsOf C (WholeD.of a W) tF tJ t3).c₂) (t := (chainsOf C (WholeD.of a
        W) tF tJ t3).c₃) (TypedOracleCompiler.Joined.tr₂ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) (wqWhole
                        C K chal (WholeD.of a W) tF tJ t3 silent run) π B) (TypedOracleCompiler.Joined.tr₃ (wholeDesc C (WholeD.of a
                                        W) tF tJ t3 silent run) (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) π E))) = true
          := by
  subst hW
  obtain ⟨fw, kw⟩ := flags_glue_of_det g h₁ h₂ h₃
  exact accept_threeA C K chal a _ tF tJ t3 silent run sb cfg pF pJ p3 salt path r π hπ A B E fw kw
    (draws_of_read C K chal a tF tJ t3 silent run _ rfl T hS₁ hR hs hok f blocks embP xin
      cms x π g sb cfg pF pJ p3 salt path hπ Gr hkit₁ hkit₂ hkit₃ A B E h₁ h₂ h₃) hr x
    hsil hrun

end OnBytes.Maker.Page
