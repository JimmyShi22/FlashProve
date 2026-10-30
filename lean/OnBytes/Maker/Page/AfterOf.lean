-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/AfterOf.lean: the ten conditions of `AfterRuns` on what the compiled verifier of
a whole file checks behind its three chains hold at the typing of a file that was read, for oracle
functions that meet two records.

The ten statements are the fields of `AfterRuns` (OnBytes/TypedOracleCompiler/Joined/K/Left.lean) at the description
and the wire record that OnBytes/Maker/ makes of a file's data: the first chain's seal, the
openings' form (four), the walks (four), the decision. Each follows from a law of another file:

    the seal      `sealAt_of_read` (OnBytes/Maker/Page/Runs.lean)
    the openings  `opened_read` (OnBytes/Maker/Page/Opened.lean), with `draws_of_read`
    the walks     `walks_of` (OnBytes/Maker/WalksOf.lean), with `PageOwes.readOwes`
    the decision  `accept_of_read` (OnBytes/Maker/Page/Accept.lean)

  `after_read`   **the ten statements**, in a row.

The premises. On the oracle functions g: `GRows` (OnBytes/Maker/Page/RunsTools.lean: how g answers
the chains' queries) and `CodeOwes` (OnBytes/Maker/WalksOf.lean: how g answers at a vertex and a
leaf, at the bodies in use), both at the realised oracle. `PageOwes` (OnBytes/Maker/Page/Owes.lean):
the reading, the parameters, tests on the data. The data W are made of the dry run's three lists of
rounds. `typeFile` returns π at the reading r: it holds the test `sameTwice`
(OnBytes/Maker/Tables.lean) that two openings of one place hold one column and salt. The three
chains' values under g. The test on the three silent rounds' messages says yes; the file's decision
says yes at all views that are as the views read but for the digests drawn. The first of the
commitments is the digest of the root in item 0 of the second chain's statement. None is shown here.

Not claimed. The fields of `Left` beside `after` (`laws`, `wire`, `fits`, `saltLen`, `slotLt`,
`pathLen`, `climb`): among them the climb in the request tree and the lengths of the salt and the
path, which the compiled verifier checks behind its chains too. Nothing on soundness
(index binding included), opening-form binding, no two openings of a commitment, correctness of
extraction, what a root fixes or whatever else names a committer or a prover.

-/
import OnBytes.Maker.Page.Owes
import OnBytes.Maker.Page.Opened
import OnBytes.Maker.Page.Accept

set_option autoImplicit false

namespace OnBytes.Maker.Page

open OnBytes OnBytes.Maker OnBytes.Proof OnBytes.TieK
open OnBytes.Params (Rounds)
open OnBytes.TwoLaws (ViewAlike)
open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Joined.K TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening Tag)
open _root_.Run _root_.Run.PQ

section
variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
  {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : Fmt.Rand} {R₃ : Rounds}
  (f : Fmt.Fld) (K a : ℕ) (W : Three.Whole)
  {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool) {I X : Type} {L : BatchProtocolWithLeafBody I X}
  (g : Fam (typedOracleFamily 256 (K + 1) L))
  (embS : (p : OPos (chainsOf (ckP f) (WholeD.of a W) tF tJ t3).sh) →
    OSym (chainsOf (ckP f) (WholeD.of a W) tF tJ t3).sh p → Body L) (embE : SgX → Body L) {t : Tag}
  (embP : PlainPart (chainsOf (ckP f) (WholeD.of a W) tF tJ t3).sh (chainsOf (ckP f) (WholeD.of a W) tF tJ
           t3).ann →
    PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t)) (xin : Xi → Option X) (cms : List (Dig 256))

/-- **The ten statements at the typing of a file that was read.** -/
theorem after_read (sb : ℕ) (cfg : ByteArray)
    (O : PageOwes p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃ g₁ l₁ x₁ n₁ R₃ a
      sb K f cfg) (hW : W = Three.Whole.of R₁ R₂ R₃)
    (pF : TF) (pJ : TJ) (p3 : T3) (salt : ByteArray) (path : List ByteArray)
    (π : OneProtocolProof 256 (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run).batch)
    (h : typeFile (ckP f) a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r = some π) (x : Xi)
    (a' : Out 256 (chainsOf (ckP f) (WholeD.of a W) tF tJ t3).c₁)
    (b' : Out 256 (chainsOf (ckP f) (WholeD.of a W) tF tJ t3).c₂)
    (e' : Out 256 (chainsOf (ckP f) (WholeD.of a W) tF tJ t3).c₃)
    (h₁ : (run₁ t (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run)
      (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π).det g =
        some a')
    (h₂ : (run₂ t (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run)
      (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π a').det g
        = some b')
    (h₃ : (run₃ t (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run)
      (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π a'
        b').det g =
      some e')
    (Gr : GRows (t := t) (C := ckP f) (K := K) (rF := plainRS TF tF)
      (rJ := plainRS TJ tJ) (r3 := plainRS T3 t3) (aJ := RAnn.ofShared .sh _)
      (ds₁ := toRDs (WholeD.of a W).ds₁) (ds₂ := toRDs (WholeD.of a W).ds₂)
      (ds₃ := toRDs (WholeD.of a W).ds₃)
      (D := wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π g
      Fmt.oracle [] [] S₁ S₂ S₃ r.first.out r.shared.out r.second.out
      (R₁.map (·.1)).dropLast)
    (CO : CodeOwes (ckP f) K a W tF tJ t3 g (Fmt.HO Fmt.oracle) embS embE cfg sb)
    (hsil : silent x pF pJ p3 = true)
    (hrun : ∀ v₁ v₂ v₃, ViewAlike (dropSeal r.first.view) v₁ → ViewAlike r.shared.view v₂ →
      ViewAlike r.second.view v₃ → run x v₁ v₂ v₃ = true)
    (hc : ∀ root, Fmt.itemRoot (Params.Shared.statement p.table r.place.root) 0 = some root →
      cms.getD 0 default = bytesToDig root) :
    (∀ ρ₁, a'.2.2 = .loc ρ₁ →
      g (OracleName.g t) (qSeal₁ t (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run) embP π ρ₁
                (rtJ (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run)
                  (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run) π a')) = bytesToDig
            seal1) ∧
      (TypedOracleCompiler.Joined.Opened (256 + 8 * sb) _ (chainsOf (ckP f) (WholeD.of a W) tF tJ t3).A₁
        (wire₁ (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run)) a'.2.1
        (rd₁ (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run) x π a' b' e')
        (op₁ (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run) π) ∧
      TypedOracleCompiler.Joined.Opened (256 + 8 * sb) _ (chainsOf (ckP f) (WholeD.of a W) tF tJ t3).A₂
        (wire₂ (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run)) b'.2.1
        (rd₂ (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run) x π a' b' e')
        (op₂ (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run) π) ∧
      TypedOracleCompiler.Joined.Opened (256 + 8 * sb) _ (chainsOf (ckP f) (WholeD.of a W) tF tJ t3).A₃
        (wire₃ (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run)) e'.2.1
        (rd₃ (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run) x π a' b' e')
        (op₃ (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run) π) ∧
      OpenedE (256 + 8 * sb) (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent
        run).maxDepth
        (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run).ext
        (readE (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run) x (glue a' b' e').1)
            π.ext) ∧
      ((∀ Fs, forestsB _ (chainsOf (ckP f) (WholeD.of a W) tF tJ t3).A₁
          (wire₁ (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run)) (symb₁ embS)
            a'.2.1
          (rd₁ (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run)
            (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run) x π a' b' e')
          (op₁ (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run) π) = some Fs →
        ∀ T ∈ Fs, walkP g T T.reads = true) ∧
      (∀ Fs, forestsB _ (chainsOf (ckP f) (WholeD.of a W) tF tJ t3).A₂
          (wire₂ (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run)) (symb₂ embS)
            b'.2.1
          (rd₂ (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run)
            (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run) x π a' b' e')
          (op₂ (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run) π) = some Fs →
        ∀ T ∈ Fs, walkP g T T.reads = true) ∧
      (∀ Fs, forestsB _ (chainsOf (ckP f) (WholeD.of a W) tF tJ t3).A₃
          (wire₃ (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run)) (symb₃ embS)
            e'.2.1
          (rd₃ (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run)
            (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run) x π a' b' e')
          (op₃ (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run) π) = some Fs →
        ∀ T ∈ Fs, walkP g T T.reads = true) ∧
      ∀ Fe, forestExt (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run).ext embE
        cms
          (readE (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run)
            (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run) x (glue a' b' e').1)
              π.ext =
          some Fe →
        ∀ T ∈ Fe, walkP g T T.reads = true) ∧
      (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run).accept x
        ((wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run).ext.build
          fun q => (π.ext q).map Opening.sym)
        (Tr.app (s := (chainsOf (ckP f) (WholeD.of a W) tF tJ t3).c₁)
          (t := (chainsOf (ckP f) (WholeD.of a W) tF tJ t3).c₂ ++
            (chainsOf (ckP f) (WholeD.of a W) tF tJ t3).c₃)
          (tr₁ (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run)
            (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run) π a')
          (Tr.app (s := (chainsOf (ckP f) (WholeD.of a W) tF tJ t3).c₂)
            (t := (chainsOf (ckP f) (WholeD.of a W) tF tJ t3).c₃)
            (tr₂ (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run)
              (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run) π b')
            (tr₃ (wholeDesc (ckP f) (WholeD.of a W) tF tJ t3 silent run)
              (wqWhole (ckP f) K (chalP f K) (WholeD.of a W) tF tJ t3 silent run) π e'))) = true :=
                by
  subst hW
  have D := draws_of_read (ckP f) K (chalP f K) a tF tJ t3 silent run _ rfl O.read O.spec₁ O.dry3
    O.small O.ok f O.blocks embP xin cms x π g sb cfg pF pJ p3 salt path h Gr O.kit₁ O.kit₂ O.kit₃
    a' b' e' h₁ h₂ h₃
  exact ⟨sealAt_of_read (ckP f) K (chalP f K) a tF tJ t3 silent run _ rfl O.read O.spec₁ O.dry3
      O.small O.ok f O.blocks embP xin cms x π g sb cfg pF pJ p3 salt path h Gr O.kit₁ O.kit₂ O.kit₃
      a' b' e' h₁ h₂ h₃,
    opened_read (ckP f) K (chalP f K) a _ tF tJ t3 silent run g sb cfg O.read O.fits O.salts
      O.cfg32 pF pJ p3 salt path π h x a' b' e' h₁ h₂ h₃ D,
    walks_of (ckP f) K (chalP f K) a _ tF tJ t3 silent run g (Fmt.HO Fmt.oracle) embS embE sb cfg
      pF pJ p3 salt path r π h x a' b' e' h₁ h₂ h₃ O.fits.shape O.readOwes CO (O.hroot cms hc),
    accept_of_read (ckP f) K (chalP f K) a tF tJ t3 _ rfl silent run O.read O.spec₁ O.dry3 O.small
      O.ok f O.blocks embP xin cms x π g sb cfg pF pJ p3 salt path h Gr O.kit₁ O.kit₂ O.kit₃ a' b'
      e' h₁ h₂ h₃ O.fits hsil hrun⟩

end

end OnBytes.Maker.Page
