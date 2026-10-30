-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/K12Lemma.lean: the law of the proximity test joined with the condition on its
chain, at the written view.

Joins `k12_step_accF` (Johnson/Desc/K12/Law/TopF.lean) with `K12Condition`
(Johnson/Desc/K12/Law/ChainHolds.lean, OwnMask.lean). The statement is in the oracle model: the
verifier is shown the written oracles' own columns. Statements and proofs.
Main names:
  `splitT`, `blOf`, `blOf_trL`: a chain's transcript over the list of its rounds, cut back into the
    blocks' transcripts.
  `accK`: the verifier that stands in the lemma, as a function of the transcript τ of the chain's
    written rounds: `Block.step` of `proximityTestKind guardedProximityTestParts p` says yes at the written view, and all tests of
    work on τ pass. The written view has for its rounds the round "BAT" as shown (r0) and then τ's
    rounds, and for its columns, for each declared opening in turn, at the positions that
    `Block.step` itself reads, the written tree's columns: those of the group's trees by the book's
    place, those of each later stage off τ's own switch.
  `FrontK`, `DeepK`: what stands in front of the game, and what is asked of the written rounds of
    the group's trees: depths, widths, and that the mask's oracle is the tree's where a member
    shares the mask's tree.
  `yOf`, `zOf`: the word of the group under test and the word of the first fold's fresh mask rows,
    read off written oracles.
  `accK_acc`: a yes of `accK` at a chain's transcript gives `Chain.Acc` and the tests of work.
  `k12_lemma`: `K12Condition`, `p.early = true`, `p.answers = 1`, and the block's test on the plan
    give the chain c, with `c.Holds` and its errors below εs, such that for every round r0 on which
    the batching returns (row, L, S'), where `gpOk` says yes at the record behind it, and all
    written rounds and oracles W0 of the group's trees by the book's place, with the first mask's
    oracle read off the chain's own first message by any function fM: if no witness stands within
    the chain's radius for the claim "the row read in the field" at the word `yOf`, the prover is
    doomed towards "`accK` says no".
  `k12_lemma_fwd`: the same read forward: a prover that is not doomed has a witness within the
    radius. It is a witness, not the witness: beyond half the distance a word may be near several
    code words.
Limits: No soundness is claimed. Two fields of `K12Condition`, the facts on codes at the radii and
the bound on the errors, are premises here. It does not say that a view which comes from bytes is
the written view; that needs the binding of the Merkle trees up to a collision. It does not say that
`accK` ever says yes: the lemma is not shown to have a yes. At written oracles on which `accK` is
never true, "doomed towards `accK` says no" holds trivially and says nothing. Under named premises
`accK` never fails for form (Johnson/Desc/K12/Law/AccKIff.lean); that the decision says yes at some
transcript is not shown. All tests of work are part of `accK`, not of the block: that the verifier
on files asks them is not shown here. The round "BAT" itself is not among the chain's rounds: εs
says nothing of it. Nothing is said on the converse of the batching (from the batched row's claim to
every pending claim). The word of fresh mask rows is a function of the chain's first message: a
constant function where the mask has come before the test, the message's own oracle where the first
fold brings its mask. The verifier is a fixed text here, no letter: for a block that says yes to
everything `accK_acc` would fail; one that says no to everything meets the lemma by its form. It is
stated of `guardedProximityTestParts` (Johnson/Desc/K12/JoinGuarded.lean): the parts of Johnson/Desc/K12/Join.lean behind
guards, with the base case deciding by Johnson/Desc/Prox/BaseCase.lean. It is not stated of
`proximityTestParts`, the parts of Join.lean themselves. `pubOk`, `spendOk` and `gpOk` were evaluated at the
four proximity tests of the two stored example proofs, the full-size one and the smaller one, and
were true at each [the prints are not in this library]. No statement and no proof of this file
reaches a routine that runs in a context of the program `verify-on-bytes` (`OnBytes.Ctx`,
`OnBytes.Blk`, `OnBytes.Chan`); plain functions of that program, some with names that begin with
`Blk.`, are reached. Nothing here is about hiding.
-/
import Johnson.Desc.K12.Law.TopF
import Johnson.Desc.K12.Law.ViewK
import Johnson.Desc.K12.Law.OwnMask

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (Letters pubOk sgOf writtenOf WR chainFrom K12Condition)
open H2K.First (gpOk gpOf gpL gpG gpP Plain good_of_ok cutOk)
open scoped ENNReal

/-- A transcript of a joined list of rounds, cut in two. -/
def splitT : (ds₁ ds₂ : List PQ.RD) → Tr (PQ.uL (ckP .two) (ds₁ ++ ds₂)) →
    Tr (PQ.uL (ckP .two) ds₁) × Tr (PQ.uL (ckP .two) ds₂)
  | [], _, τ => (⟨⟩, τ)
  | _ :: ds₁, ds₂, (m, c, τ) => ((m, c, (splitT ds₁ ds₂ τ).1), (splitT ds₁ ds₂ τ).2)

theorem splitT_joinT : ∀ (ds₁ ds₂ : List PQ.RD) (a : Tr (PQ.uL (ckP .two) ds₁))
    (b : Tr (PQ.uL (ckP .two) ds₂)), splitT ds₁ ds₂ (joinT ds₁ ds₂ a b) = (a, b)
  | [], _, _, _ => rfl
  | _ :: ds₁, ds₂, (m, c, τ), b => by
    show ((m, c, (splitT ds₁ ds₂ (joinT ds₁ ds₂ τ b)).1), (splitT ds₁ ds₂ (joinT ds₁ ds₂ τ b)).2) =
        _
    rw [splitT_joinT ds₁ ds₂ τ b]
    rfl

/-- The text of `rvSL_joinT` (OnBytes/Slice/WrittenView.lean), to the letter: laid here so that this
file need not import that module. -/
theorem rvSL_joinT' : ∀ (ds₁ ds₂ : List PQ.RD) (τ : Tr (PQ.uL (ckP .two) ds₁))
    (b : Tr (PQ.uL (ckP .two) ds₂)),
    PQ.rvSL (ckP .two) (ds₁ ++ ds₂) (joinT ds₁ ds₂ τ b) =
      PQ.rvSL (ckP .two) ds₁ τ ++ PQ.rvSL (ckP .two) ds₂ b
  | [], _, _, _ => rfl
  | d :: ds₁, ds₂, (m, c, τ), b =>
    congrArg (PQ.rvSL (ckP .two) [d] (m, c, ()) ++ ·) (rvSL_joinT' ds₁ ds₂ τ b)

/-- The text of `rvSL_trL` (OnBytes/Slice/ManyView.lean), to the letter: likewise. -/
theorem rvSL_trL' {s : Sg} (c : Chain s) (b : c.Bl) :
    PQ.rvSL (ckP .two) c.rds (c.trL b) = c.rvs b := by
  induction c with
  | last s e dL dB fu fs εb => rfl
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    show PQ.rvSL (ckP .two) (foldRds s dE dT ++ ([dS, dC] ++ next.rds))
      (joinT (foldRds s dE dT) _ b.1 (joinT [dS, dC] _ b.2.1 (next.trL b.2.2))) =
      PQ.rvSL (ckP .two) (foldRds s dE dT) b.1 ++
        (PQ.rvSL (ckP .two) [dS, dC] b.2.1 ++ next.rvs b.2.2)
    rw [rvSL_joinT', rvSL_joinT', ih]

/-- A chain's transcript over the list of its rounds, cut back into the blocks' transcripts. -/
def blOf : {s : Sg} → (c : Chain s) → Tr (PQ.uL (ckP .two) c.rds) → c.Bl
  | _, .last _ _ _ _ _ _ _ => fun τ => τ
  | _, .step s _ _ _ _ dE dT dS dC _ _ _ _ _ next => fun τ =>
    ((splitT (foldRds s dE dT) ([dS, dC] ++ next.rds) τ).1,
      (splitT [dS, dC] next.rds (splitT (foldRds s dE dT) ([dS, dC] ++ next.rds) τ).2).1,
      blOf next (splitT [dS, dC] next.rds (splitT (foldRds s dE dT) ([dS, dC] ++ next.rds) τ).2).2)

theorem blOf_trL {s : Sg} (c : Chain s) : ∀ b : c.Bl, blOf c (c.trL b) = b := by
  induction c with
  | last s e dL dB fu fs εb => intro b; rfl
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    intro b
    have h1 : splitT (foldRds s dE dT) ([dS, dC] ++ next.rds)
        ((Chain.step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next).trL b) =
        (b.1, joinT [dS, dC] next.rds b.2.1 (next.trL b.2.2)) := splitT_joinT _ _ _ _
    show ((splitT (foldRds s dE dT) ([dS, dC] ++ next.rds) _).1,
      (splitT [dS, dC] next.rds (splitT (foldRds s dE dT) ([dS, dC] ++ next.rds) _).2).1,
      blOf next (splitT [dS, dC] next.rds
        (splitT (foldRds s dE dT) ([dS, dC] ++ next.rds) _).2).2) = b
    rw [h1]
    show (b.1, (splitT [dS, dC] next.rds (joinT [dS, dC] next.rds b.2.1 (next.trL b.2.2))).1,
      blOf next (splitT [dS, dC] next.rds (joinT [dS, dC] next.rds b.2.1 (next.trL b.2.2))).2) = b
    rw [splitT_joinT]
    show (b.1, b.2.1, blOf next (next.trL b.2.2)) = b
    rw [ih]
    rfl

/-- A written round with a written oracle of it. -/
abbrev WO : Type := Σ d : PQ.RD, (wRound d).Orc

/-- The written rounds and oracles of the group's trees, by the book's place, at the transcripts b:
W0's, but at the first mask's tree's place ft what fM reads off the chain's own first message. -/
def wAt {s : Sg} (c : Chain s) (W0 : ℕ → WO) (ft : ℕ) (fM : H2K.Pub.Msg1 c → WO) (b : c.Bl) : ℕ →
    WO :=
  Function.update W0 ft (fM (H2K.Pub.msg1 c b))

theorem ofOrc_congr (M : Mb) (ly : Lay) {u v : WO} (h : u = v) :
    M.ofOrc ly u.1 u.2 = M.ofOrc ly v.1 v.2 := by
  subst h
  rfl

theorem frOf_congr (s : Sg) (a o : ℕ) {u v : WO} (h : u = v) :
    frOf s a o u.1 u.2 = frOf s a o v.1 v.2 := by
  subst h
  rfl

theorem acc_congr {s : Sg} (c : Chain s) (q : GE × (s.cIn.J → GE)) {y y' : s.cIn.Word}
    {z z' : s.cFr.Word} (g : s.cIn.Word) (b : c.Bl) (hy : y = y') (hz : z = z')
    (h : c.Acc q y z g b) : c.Acc q y' z' g b := by
  subst hy
  subst hz
  exact h

/-- The verifier that stands in the lemma. The file's head says what its view is. -/
def accK (p : P12) (F : ℕ) (t0 : T12) (r0 : Fmt.RoundView) {s : Sg} (c : Chain s) (ts : List ℕ)
    (W : c.Bl → ℕ → WO) (τ : Tr (PQ.uL (ckP .two) c.rds)) : Bool :=
  (match (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: PQ.rvSL (ckP .two) c.rds τ)
      (colsOf (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds
        ((r0 :: PQ.rvSL (ckP .two) c.rds τ).map (·.drawn)))
        (srcK p c (blOf c τ) ts fun z x => colW (W (blOf c τ) z).1 (W (blOf c τ) z).2 x)) with
    | .ok _ => true
    | .error _ => false) &&
  PQ.passSL (ckP .two) c.rds (PQ.rhoSL (ckP .two) c.rds τ)

/-- The word of the group under test, read off the written oracles W0 of its members' trees. -/
def yOf (p : P12) (a : Fmt.M1.Stage) (row : GroupRow) (D : Plain)
    (hok : H2K.First.ok (gpL p a row D) = true) (rd : ℕ → ℕ) (W0 : ℕ → WO) : (sgOf a).cIn.Word :=
  (gpG (good_of_ok p a row D hok) rd).word fun j =>
    ((gpG (good_of_ok p a row D hok) rd).mb j).ofOrc
      ((gpP (good_of_ok p a row D hok) rd (fun i => (W0 (D.mems.get i).t).1)
        (W0 D.fresh.t).1).lay j) (W0 (D.mems.get j).t).1 (W0 (D.mems.get j).t).2

/-- The word of the first fold's fresh mask rows, read off a written oracle. -/
def zOf (p : P12) (a : Fmt.M1.Stage) (row : GroupRow) (D : Plain)
    (hok : H2K.First.ok (gpL p a row D) = true) (rd : ℕ → ℕ) (W0 : ℕ → WO) (u : WO) :
    (sgOf a).cFr.Word :=
  frOf (sgOf a) D.fresh.tsh.logN
    (gpP (good_of_ok p a row D hok) rd (fun i => (W0 (D.mems.get i).t).1) (W0 D.fresh.t).1).oF
    u.1 u.2

/-- What stands in front of the game: on "BAT"'s round r0 as shown the batching returns (row, Ly,
S'); gpOk says yes at the record behind it; D is gpOf's value there. -/
structure FrontK (p : P12) (t0 : T12) (a : Fmt.M1.Stage) (r0 : Fmt.RoundView) (e : Fmt.Entry)
    (row : GroupRow) (Ly : GroupLayout) (S' : Statement) (D : Plain) : Prop where
  bat : First.Close.bat t0.st t0.g e (noDigest r0) = .ok (row, Ly, S')
  gp : gpOk p { t0 with st := S', pass := .claim row Ly } = true
  made : gpOf p { t0 with st := S', pass := .claim row Ly } a Ly = some D

/-- What is asked of the letters W0 and fM: the written rounds are as deep as the book's trees;
where a member shares the mask's tree, the mask's oracle is that tree's, whatever the first message.
-/
structure DeepK (D : Plain) {M : Type} (W0 : ℕ → WO) (fM : M → WO) : Prop where
  mems : ∀ i, PQ.posN (W0 (D.mems.get i).t).1.tree = 2 ^ (D.mems.get i).tsh.logN
  fresh : ∀ m, PQ.posN (fM m).1.tree = 2 ^ D.fresh.tsh.logN
  same : ∀ i m, (D.mems.get i).t = D.fresh.t → fM m = W0 D.fresh.t
  /-- the written columns are as wide as the book's trees' (spent in
  Johnson/Desc/K12/Law/AccKIff.lean, not in this file: it bars the letters at which the test of
  `Block.step` on the columns fails for want of width) -/
  wide : (∀ z ∈ D.ts, z ≠ D.fresh.t → PQ.colW (W0 z).1.tree = H2K.First.widthAt D.book z) ∧
    ∀ m, PQ.colW (fM m).1.tree = H2K.First.widthAt D.book D.fresh.t

/-- A yes of `accK` at a chain's transcript gives `Chain.Acc`, and the tests of work: at the place's
chain with any letters X. -/
theorem accK_acc (X : Letters) (p : P12) (t0 : T12) (he : p.early = true) (ha : p.answers = 1)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (hpub : pubOk p t0.st.codes = true)
    :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
      chainFrom X rest a l = some c ∧
      ∀ (F : ℕ) (r0 : Fmt.RoundView) (e : Fmt.Entry) (row : GroupRow) (Ly : GroupLayout) (S' : Statement)
        (D : Plain) (hok : H2K.First.ok (gpL p a row D) = true), FrontK p t0 a r0 e row Ly S' D →
        ∀ (rd : ℕ → ℕ) (W0 : ℕ → WO) (fM : H2K.Pub.Msg1 c → WO), DeepK D W0 fM →
          ∀ b : c.Bl, accK p F t0 r0 c D.ts (wAt c W0 D.fresh.t fM) (c.trL b) = true →
            c.Acc (stmG (sgOf a) row) (yOf p a row D hok rd W0)
              (zOf p a row D hok rd W0 (fM (H2K.Pub.msg1 c b))) (fun _ _ => 0) b ∧
            PQ.passSL (ckP .two) c.rds (PQ.rhoSL (ckP .two) c.rds (c.trL b)) = true := by
  obtain ⟨a, rest, w0, l, c, f1, f2, f3, _, _, hF⟩ :=
    k12_step_accF X p he ha t0 hp hpub (cut_of_planOk p hp)
  refine ⟨a, rest, w0, l, c, f1, f2, f3, ?_⟩
  intro F r0 e row Ly S' D hok hfr rd W0 fM hdp b hacc
  unfold accK at hacc
  rw [Bool.and_eq_true] at hacc
  obtain ⟨hstep, hpass⟩ := hacc
  refine ⟨?_, hpass⟩
  unfold yOf zOf
  rw [blOf_trL, rvSL_trL'] at hstep
  have hWm : ∀ i, wAt c W0 D.fresh.t fM b (D.mems.get i).t = W0 (D.mems.get i).t := by
    intro i
    unfold wAt
    by_cases h : (D.mems.get i).t = D.fresh.t
    · rw [h, Function.update_self, hdp.same i _ h]
    · rw [Function.update_of_ne h]
  have hWf : wAt c W0 D.fresh.t fM b D.fresh.t = fM (H2K.Pub.msg1 c b) := by
    unfold wAt
    rw [Function.update_self]
  split at hstep
  · rename_i x hx
    obtain ⟨tE, n⟩ := x
    obtain ⟨e', r', row', L', S'', G0, g1, g2, _, _, _, g6⟩ := hF F tE _ _ n hx
    have hr' : r' = noDigest r0 := (List.cons.inj g1).1.symm
    subst hr'
    cases bat_unique _ _ _ _ _ _ _ hfr.bat g2
    obtain ⟨D', hok', hD', hall⟩ := g6 hfr.gp
    obtain rfl := Option.some.inj (hD'.symm.trans hfr.made)
    have hA := hall rd (fun z => (wAt c W0 D'.fresh.t fM b z).1)
      (fun z => (wAt c W0 D'.fresh.t fM b z).2)
      (fun i => by
        show PQ.posN (wAt c W0 D'.fresh.t fM b (D'.mems.get i).t).1.tree = _
        rw [hWm i]
        exact hdp.mems i)
      (by
        show PQ.posN (wAt c W0 D'.fresh.t fM b D'.fresh.t).1.tree = _
        rw [hWf]
        exact hdp.fresh _) (fun _ _ => 0) b rfl
      (follows_view p c b _ _ _)
    exact acc_congr c _ _ b
      (congrArg _ (funext fun j => ofOrc_congr _ _ (hWm j))) (frOf_congr _ _ _ hWf) hA
  · cases hstep

/-- The join, under `K12Condition`. -/
theorem k12_lemma {L mC mS mW : Sg → ℕ → ℕ} {rad : Sg → ℕ} {p : P12} {εs : ℝ≥0∞} (t0 : T12)
    (hK : K12Condition L mC mS mW rad p t0.st.codes εs) (he : p.early = true)
    (ha : p.answers = 1) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧ c.rds = l.map WR.rd ∧
      c.rad = rad (sgOf a) ∧ c.Holds ∧ Err.Below c.err εs ∧
      ∀ (F : ℕ) (r0 : Fmt.RoundView) (e : Fmt.Entry) (row : GroupRow) (Ly : GroupLayout) (S' : Statement)
        (D : Plain) (hok : H2K.First.ok (gpL p a row D) = true), FrontK p t0 a r0 e row Ly S' D →
        ∀ (rd : ℕ → ℕ) (W0 : ℕ → WO) (fM : H2K.Pub.Msg1 c → WO), DeepK D W0 fM →
          (∀ w, ¬ (sgOf a).RIn c.rad (stmG (sgOf a) row, yOf p a row D hok rd W0) w) →
          Doomed (PQ.uL (ckP .two) c.rds) c.errL fun τ =>
            accK p F t0 r0 c D.ts (wAt c W0 D.fresh.t fM) τ = false := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, _, e6, hH, e8, hG⟩ := hK.gives_own
  obtain ⟨a', rest', w0', l', c', f1, f2, f3, hA⟩ :=
    accK_acc (.at L mC mS mW rad) p t0 he ha hp hK.pub
  obtain ⟨rfl, rfl⟩ := List.cons.inj (f1.symm.trans e1)
  obtain ⟨rfl, rfl⟩ := List.cons.inj (Option.some.inj (f2.symm.trans e2))
  obtain rfl := Option.some.inj (f3.symm.trans e3)
  refine ⟨a', rest', w0', l', c', e1, e2, e4, e6, hH, e8, ?_⟩
  intro F r0 e row Ly S' D hok hfr rd W0 fM hdp hno
  exact hG _ _ (fun m => zOf p a' row D hok rd W0 (fM m)) (fun _ _ => 0) hno _
    (hA F r0 e row Ly S' D hok hfr rd W0 fM hdp)

/-- The same, read forward. It gives a witness, not the witness: beyond half the distance the word
may be near several code words. -/
theorem k12_lemma_fwd {L mC mS mW : Sg → ℕ → ℕ} {rad : Sg → ℕ} {p : P12} {εs : ℝ≥0∞} (t0 : T12)
    (hK : K12Condition L mC mS mW rad p t0.st.codes εs) (he : p.early = true)
    (ha : p.answers = 1) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧ c.rds = l.map WR.rd ∧
      c.rad = rad (sgOf a) ∧ c.Holds ∧ Err.Below c.err εs ∧
      ∀ (F : ℕ) (r0 : Fmt.RoundView) (e : Fmt.Entry) (row : GroupRow) (Ly : GroupLayout) (S' : Statement)
        (D : Plain) (hok : H2K.First.ok (gpL p a row D) = true), FrontK p t0 a r0 e row Ly S' D →
        ∀ (rd : ℕ → ℕ) (W0 : ℕ → WO) (fM : H2K.Pub.Msg1 c → WO), DeepK D W0 fM →
          (¬ Doomed (PQ.uL (ckP .two) c.rds) c.errL fun τ =>
            accK p F t0 r0 c D.ts (wAt c W0 D.fresh.t fM) τ = false) →
          ∃ w, (sgOf a).RIn c.rad (stmG (sgOf a) row, yOf p a row D hok rd W0) w := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, e6, h⟩ := k12_lemma t0 hK he ha hp
  refine ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, e6, ?_⟩
  intro F r0 e row Ly S' D hok hfr rd W0 fM hdp hnd
  by_contra hno
  exact hnd (h F r0 e row Ly S' D hok hfr rd W0 fM hdp (fun w hw => hno ⟨w, hw⟩))

end H2K.JointK
