-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/StringsPlain.lean: what the field `plains` of a produced proof holds: the plain parts of the
transcript that the compiled prover returns beside it, which is the prover's own strategy run at the
hashed verifier messages, up to the nonces.

Summary. Let π be a produced proof of the scheme, and τ the transcript that the compiled prover
returns with π under the same oracle functions. Then π and τ have the same plain parts, all
proof-of-work tests pass at τ's verifier messages, and τ is the run of the prover's strategy at
these verifier messages, except that in a round with a test a number of at most the search limit is
written in as nonce (`PutsLe`, OnBytes/Prover/Nonces.lean). This holds for any three provers, all
oracle functions and all coins. If the wiring has few trees per round (`FewJ`, `Few0`, fields of
`WiresFit`), the verifier's chain, run under the same oracle functions on π's own fields, yields τ's
verifier messages. No probability occurs.

Main results.
  `key_plains`, `link_plains`, `session_plains`: for a produced proof π of each of the three kinds
    there is a τ such that the compiled prover, at the very terms at which the scheme calls it,
    returns (π, τ) under g, and `PlainAt` holds for the strategy that the prover plays there
    (`h.st.T`, `h.st.Lk`, `h.st.B` at the index, the tables' randomness and OOD seeds, and the run's
    coin) and for its search limits. No premise.
  `key_hashed`, `link_hashed`, `session_hashed`: under `WiresFit W cA` (Johnson/Prover/All/Yes.lean;
    its fields fewT, fewL, fewB are used) there is a τ with: the compiled prover returns (π, τ)
    under g, so it is the τ above, since a run under g has one value · `PlainAt` · the prover does
    not abort at τ.rho · the verifier's chain on π's own salt, rtreq, roots and plains, under g,
    yields τ.rho.
  `PlainAt Q wq σ cap π τ` states: π.plains = τ.plains · all tests pass at τ.rho · `PutsLe cap 0`
    relates σ's run at τ.rho and τ. Here τ is a variable: the definition names no oracle function,
    and each theorem states beside it what ties τ to them.
  `accepts_at`: from `PlainAt` and an acceptance lemma for that strategy (`AccLaw`,
    Johnson/Prover/Law/Defs.lean) that excludes no verifier message, the interactive verifier
    accepts that τ.

Terms: E2E/HidingTerms.lean.

Limits.
- Up to what `put` writes: in a round with a test the plain part of the hashed component is the
  run's with `put n` applied, for a number n of at most the search limit. For an arbitrary wiring
  `put` is a free field. So this is not an equation of plain parts.
- `FewJ` and `Few0` are premises of everything that concerns the verifier's chain. For a wiring with
  more trees in a round's component than the format takes, that chain rejects, while nothing in the
  compiled prover's text asks for few trees: it may still return (no lemma here says that it does).
- The interactive verifier, not the compiled one: that the compiled verifier accepts the proof is
  not proved. The last clause of `yes_of_prove` (OnBytes/Prover/Main.lean) would give it, but asks a
  premise that fails (see Sources). The chain is one step of the compiled verifier and no more.
- All results are for a produced proof. How often one is produced: E2E/StringsAllLinks.lean. No
  theorem here joins the two, nor either with an experiment's view.
- The model: E2E/HidingTerms.lean. Nothing on completeness as such, on soundness or on what is
  hidden.

Sources. Section 1 is another file's proof, cut down. `chain_pass` and `chain_hashed` are `chain_at`
(OnBytes/Prover/Chain.lean) with four of the six fields of its conclusion removed; the two that are
kept (`pass`, `chain`) are proved there case by case by the same steps. That theorem asks that every
leaf's salt in the coins has one length, at all indices. This fails for provers whose dressed coins
hold a shorter string outside the window (`dress`, Johnson/WholeKey/Defs.lean, with an empty
`fill`), such as those of E2E/FiveLeftSilentCaps.lean. So neither it nor `yes_of_prove` can be
applied there. `pass` needs no premise; `chain` needs the two bounds on the numbers of trees and
that there are as many trees as depths (`treesO_len`). If that file comes to state the two
separately, this section should call it. The third fact, "the strategy's own run up to nonces", is
called: `proveX_putsLe` (OnBytes/Prover/Nonces.lean), which has no premise.

Definitions and helper lemmas.
  `chain_pass`: whatever the compiled prover's chain yields, the tests pass.
  `treesO_len`, `chain_hashed`: under `FewJ` and `Few0` the verifier's chain (`chainF`) under the
    same oracle functions, at the kept roots and that transcript's plain parts, yields the same
    verifier messages.
  `PlainAt.puts`: `PlainAt` implies the same with `Puts` (OnBytes/Prover/Inv.lean).
  `plains_of_prove`, `hashed_of_prove`: the two results for one slot.
  `shown_go`: what is given out as a proof is what a run returned, at verifier messages at which the
    prover does not abort.
  `puts_plain`: in a first round without a test the plain part is the run's.


-/
import E2E.StringsHold
import Johnson.Prover.Law.Defs
import OnBytes.Prover.Nonces

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.Shown
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run (chainF)

/-! ## 1. One chain -/

section Chain
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}
variable (g : Fam (typedOracleFamily lam K L)) (t : Tag) (cms : List (Dig lam)) (x : Option X)
  (co : Coins lam L) (cap : ℕ → ℕ)

theorem chain_pass : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : Phase lam) (σ : Strat s Unit) (z : OutP lam L s),
    (chainO t cms x co cap s A W embS embP i ph σ).det g = .ok z →
    RoundsQueryLayout.pass s A W z.1 = true
  | [], _, _, _, _, _, ph, _, z, hz => by
    obtain rfl : ((), (), ph, none) = z := Res.ok.inj hz
    rfl
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m, k), z, hz => by
    cases e : actOf cms (x.map L.early) co.salt a.kind ph with
    | none =>
      rw [det_noFormat g t cms x co cap w W embS embP i ph m k e] at hz
      cases hz
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          rw [det_own g t cms x co cap w W embS embP i ph m k e] at hz
          obtain ⟨q, hq, hq'⟩ := onFsF_eq_ok hz
          obtain ⟨z', hz', rfl⟩ := Res.map_eq_ok hq'
          obtain ⟨hk, -, -⟩ := act_own e
          obtain ⟨-, hgr⟩ := fs_some g _ _ _ _ _ hq
          have ih := chain_pass s A W _ _ (i + 1) _ _ z' hz'
          show (w.pass (w.chal q.2.1) && RoundsQueryLayout.pass s A W z'.1) = true
          rw [ih, Bool.and_true]
          refine pass_lo hk ?_
          rcases hgr with ⟨h1, -⟩ | ⟨u, n, h1, -, h3⟩
          · exact Or.inl h1
          · exact Or.inr ⟨u, h1, h3⟩
        | false =>
          rw [det_shared g t cms x co cap w W embS embP i ph m k e] at hz
          obtain ⟨q, hq, hq'⟩ := onFsF_eq_ok hz
          obtain ⟨z', hz', rfl⟩ := Res.map_eq_ok hq'
          obtain ⟨hk, -, -, -, -⟩ := act_shared e
          obtain ⟨-, hgr⟩ := fs_some g _ _ _ _ _ hq
          have ih := chain_pass s A W _ _ (i + 1) _ _ z' hz'
          show (w.pass (w.chal q.2.1) && RoundsQueryLayout.pass s A W z'.1) = true
          rw [ih, Bool.and_true]
          refine pass_sh hk ?_
          rcases hgr with ⟨h1, -⟩ | ⟨u, n, h1, -, h3⟩
          · exact Or.inl h1
          · exact Or.inr ⟨u, h1, h3⟩
      | join ρ =>
        rw [det_join g t cms x co cap w W embS embP i ph m k e] at hz
        obtain ⟨q, hq, hq'⟩ := onFsF_eq_ok hz
        obtain ⟨z', hz', rfl⟩ := Res.map_eq_ok hq'
        obtain ⟨hk, rfl⟩ := act_join e
        obtain ⟨-, hgr⟩ := fs_some g _ _ _ _ _ hq
        have ih := chain_pass s A W _ _ (i + 1) _ _ z' hz'
        show (w.pass (w.chal q.2.1) && RoundsQueryLayout.pass s A W z'.1) = true
        rw [ih, Bool.and_true]
        refine pass_sh hk ?_
        rcases hgr with ⟨h1, -⟩ | ⟨u, n, h1, -, h3⟩
        · exact Or.inl h1
        · exact Or.inr ⟨u, h1, h3⟩

/-- As many trees as depths. -/
theorem treesO_len {r : Round} (pad : Body L) (sl : ℕ → ℕ → Bits) (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L) (o : r.Orc) : ∀ (k : ℕ) (ds : List ℕ),
    ((treesO (K := K) pad sl posAt emb o k ds).det g).length = ds.length
  | _, [] => rfl
  | k, d :: ds => by
    rw [det_treesO_cons, List.length_cons, List.length_cons,
      treesO_len pad sl posAt emb o (k + 1) ds]

theorem chain_hashed : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : Phase lam) (σ : Strat s Unit) (z : OutP lam L s),
    (chainO t cms x co cap s A W embS embP i ph σ).det g = .ok z → FewJ s A W → Few0 s A W →
    ∀ rq : Dig lam, (∀ r, z.2.2.2 = some r → r = rq) →
    ∃ R : RootsOfChain lam s, chainF g t cms x co.salt rq s A W embP i ph (rootsK s z.2.1)
      (trK s z.2.1 z.1).plains = some (z.1, R, z.2.2.1)
  | [], _, _, _, _, _, ph, _, z, hz, _, _, _, _ => by
    obtain rfl : ((), (), ph, none) = z := Res.ok.inj hz
    exact ⟨(), rfl⟩
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m, k), z, hz, hJ, h0, rq, hrq => by
    cases e : actOf cms (x.map L.early) co.salt a.kind ph with
    | none =>
      rw [det_noFormat g t cms x co cap w W embS embP i ph m k e] at hz
      cases hz
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          rw [det_own g t cms x co cap w W embS embP i ph m k e] at hz
          obtain ⟨q, hq, hq'⟩ := onFsF_eq_ok hz
          obtain ⟨z', hz', rfl⟩ := Res.map_eq_ok hq'
          obtain ⟨hans, -⟩ := fs_some g _ _ _ _ _ hq
          obtain ⟨R', ih⟩ := chain_hashed s A W _ _ (i + 1) _ _ z' hz' hJ.2 h0.2 rq hrq
          have hpl : (a.plain (a.plain.symm ((a.plain m.2).1, q.1))).2 = q.1 := by
            rw [Equiv.apply_symm_apply]
          refine ⟨((none, some ((tJ g co w embS i m).map TreeK.root)), R'), ?_⟩
          show chainF g t cms x co.salt rq (r :: s) (a, A) (w, W) embP i ph
            ((tJ g co w embS i m).map TreeK.root ++ rootsK s z'.2.1)
            (a.plain.symm ((a.plain m.2).1, q.1), (trK s z'.2.1 z'.1).plains) = _
          have hT : takeRt w.depthJ.length
              ((tJ g co w embS i m).map TreeK.root ++ rootsK s z'.2.1) =
                some ((tJ g co w embS i m).map TreeK.root, rootsK s z'.2.1) :=
            takeRt_app (by rw [List.length_map]; exact treesO_len g _ _ _ _ _ 0 _) hJ.1
          simp only [TypedOracleCompiler.Run.chainF, e, hT, hpl]
          rw [show g (OracleName.fb t) (⟨i, h.withLate (lateInstancePart L i x), (tJ g co w embS i m).map TreeK.root,
                    embP (.inl (.inr q.1))⟩ : FbIn lam L t) = q.2 from hans.symm, ih]
          rfl
        | false =>
          rw [det_shared g t cms x co cap w W embS embP i ph m k e] at hz
          obtain ⟨q, hq, hq'⟩ := onFsF_eq_ok hz
          obtain ⟨z', hz', rfl⟩ := Res.map_eq_ok hq'
          obtain ⟨hans, -⟩ := fs_some g _ _ _ _ _ hq
          obtain ⟨R', ih⟩ := chain_hashed s A W _ _ (i + 1) _ _ z' hz' hJ.2 h0.2 rq hrq
          have hpl : (a.plain (a.plain.symm (q.1, (a.plain m.2).2))).1 = q.1 := by
            rw [Equiv.apply_symm_apply]
          refine ⟨((some ((t0 g co w embS i m).map TreeK.root), none), R'), ?_⟩
          show chainF g t cms x co.salt rq (r :: s) (a, A) (w, W) embP i ph
            ((t0 g co w embS i m).map TreeK.root ++ rootsK s z'.2.1)
            (a.plain.symm (q.1, (a.plain m.2).2), (trK s z'.2.1 z'.1).plains) = _
          have hT : takeRt w.depth0.length
              ((t0 g co w embS i m).map TreeK.root ++ rootsK s z'.2.1) =
                some ((t0 g co w embS i m).map TreeK.root, rootsK s z'.2.1) :=
            takeRt_app (by rw [List.length_map]; exact treesO_len g _ _ _ _ _ 0 _) h0.1
          simp only [TypedOracleCompiler.Run.chainF, e, hT, hpl]
          rw [show g (OracleName.fb t) (⟨i, h, (t0 g co w embS i m).map TreeK.root,
                    embP (.inl (.inl q.1))⟩ : FbIn lam L t) = q.2 from hans.symm, ih]
          rfl
      | join ρ =>
        rw [det_join g t cms x co cap w W embS embP i ph m k e] at hz
        obtain ⟨q, hq, hq'⟩ := onFsF_eq_ok hz
        obtain ⟨z', hz', rfl⟩ := Res.map_eq_ok hq'
        obtain ⟨-, rfl⟩ := act_join e
        obtain ⟨hans, -⟩ := fs_some g _ _ _ _ _ hq
        obtain rfl : reqRoot g co (slotV g t co w embS embP i m ρ) = rq := hrq _ rfl
        have hno := (chain_after g t cms x co cap s A W _ _ (i + 1) _ _ z' _ hz' rfl).1
        obtain ⟨R', ih⟩ := chain_hashed s A W _ _ (i + 1) _ _ z' hz' hJ.2 h0.2
          (reqRoot g co (slotV g t co w embS embP i m ρ)) (fun r hr => by rw [hno] at hr; cases hr)
        have hpl : a.plain (a.plain.symm (q.1, (a.plain m.2).2)) = (q.1, (a.plain m.2).2) :=
          Equiv.apply_symm_apply _ _
        refine ⟨((some ((t0 g co w embS i m).map TreeK.root),
          some ((tJ g co w embS i m).map TreeK.root)), R'), ?_⟩
        show chainF g t cms x co.salt _ (r :: s) (a, A) (w, W) embP i (.loc ρ)
          ((tJ g co w embS i m).map TreeK.root ++
            ((t0 g co w embS i m).map TreeK.root ++ rootsK s z'.2.1))
          (a.plain.symm (q.1, (a.plain m.2).2), (trK s z'.2.1 z'.1).plains) = _
        have hTJ : takeRt w.depthJ.length ((tJ g co w embS i m).map TreeK.root ++
            ((t0 g co w embS i m).map TreeK.root ++ rootsK s z'.2.1)) =
              some ((tJ g co w embS i m).map TreeK.root,
                (t0 g co w embS i m).map TreeK.root ++ rootsK s z'.2.1) :=
          takeRt_app (by rw [List.length_map]; exact treesO_len g _ _ _ _ _ 0 _) hJ.1
        have hT0 : takeRt w.depth0.length
            ((t0 g co w embS i m).map TreeK.root ++ rootsK s z'.2.1) =
              some ((t0 g co w embS i m).map TreeK.root, rootsK s z'.2.1) :=
          takeRt_app (by rw [List.length_map]; exact treesO_len g _ _ _ _ _ 0 _) h0.1
        simp only [TypedOracleCompiler.Run.chainF, e, hTJ, hT0, hpl]
        rw [show g (OracleName.fb t) (⟨i, .f4 cms (List.ofFn (reqRoot g co
                    (slotV g t co w embS embP i m ρ))), (t0 g co w embS i m).map TreeK.root,
                  embP (.inl (.inl q.1))⟩ : FbIn lam L t) = q.2 from hans.symm]
        rw [show g (OracleName.g t) (⟨i, ρ, (tJ g co w embS i m).map TreeK.root,
                  embP (.inl (.inr (a.plain m.2).2))⟩ : JoiningRoundQuery lam L t) =
            slotV g t co w embS embP i m ρ from rfl, ih]
        rfl

/-- In a first round without a test the plain part is the run's. -/
theorem puts_plain {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s} {w : WireRB lam K r a}
    {W : RoundsQueryLayout lam K s A} {τ τ' : Tr (r :: s)} (h : Puts (r :: s) (a, A) (w, W) τ τ')
    (hJ : w.grJ = none) (h0 : w.gr0 = none) : τ'.1.2 = τ.1.2 := by
  obtain ⟨m, c, τ⟩ := τ
  obtain ⟨m', c', τ'⟩ := τ'
  rcases h.2.2.1 with e | ⟨u, n, -, hu, -⟩ | ⟨u, n, -, hu, -⟩
  · exact e
  · rw [hJ] at hu
    cases hu
  · rw [h0] at hu
    cases hu

end Chain

/-! ## 2. One slot -/

section One
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}
variable (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeK lam L)
  (σ : Strat Q.loc.shape Unit) (co : Coins lam L) (cap : ℕ → ℕ)

/-- **What the plain parts of a proof π are, relative to a transcript τ**, for the strategy σ and
the search limits. -/
def PlainAt (π : OneProtocolProof lam Q) (τ : Tr Q.loc.shape) : Prop :=
  π.plains = τ.plains ∧ RoundsQueryLayout.pass Q.loc.shape Q.ann wq.sh τ.rho = true ∧
    PutsLe cap 0 Q.loc.shape Q.ann wq.sh (σ.run τ.rho).1 τ

variable {Q wq σ cap} in
/-- It implies the same with `Puts`. -/
theorem PlainAt.puts {π : OneProtocolProof lam Q} {τ : Tr Q.loc.shape} (hp : PlainAt Q wq σ cap π τ) :
    Puts Q.loc.shape Q.ann wq.sh (σ.run τ.rho).1 τ :=
  PutsLe.puts 0 _ _ _ _ _ hp.2.2

theorem plains_of_prove (g : Fam (typedOracleFamily lam K L)) (π : OneProtocolProof lam Q) (τ : Tr Q.loc.shape)
    (h : (proveX t Q wq embS embP xin cms x y xt σ co cap).det g = .ok (π, τ)) :
    PlainAt Q wq σ cap π τ := by
  have hq := proveX_putsLe t Q wq embS embP xin cms x y xt σ co cap g π τ h
  obtain ⟨z, hz, rfl, rfl⟩ := (proveX_ok_iff t Q wq embS embP xin cms x y xt σ co cap g π τ).1 h
  have hc := chain_pass g t cms (xin x) co cap Q.loc.shape Q.ann wq.sh embS embP 0 .first σ z hz
  refine ⟨rfl, ?_, hq⟩
  rw [rho_trK]
  exact hc

/-- **Under `FewJ` and `Few0`, the verifier's chain, run under g on the proof's own fields, yields
τ's verifier messages.** -/
theorem hashed_of_prove (g : Fam (typedOracleFamily lam K L)) (hJ : FewJ Q.loc.shape Q.ann wq.sh)
    (h0 : Few0 Q.loc.shape Q.ann wq.sh) (π : OneProtocolProof lam Q) (τ : Tr Q.loc.shape)
    (h : (proveX t Q wq embS embP xin cms x y xt σ co cap).det g = .ok (π, τ)) :
    ∃ R ph, chainF g t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann wq.sh embP 0 .first π.roots
      π.plains = some (τ.rho, R, ph) := by
  obtain ⟨z, hz, rfl, rfl⟩ := (proveX_ok_iff t Q wq embS embP xin cms x y xt σ co cap g π τ).1 h
  obtain ⟨R, hc⟩ := chain_hashed g t cms (xin x) co cap Q.loc.shape Q.ann wq.sh embS embP 0 .first
    σ z hz hJ h0 (z.2.2.2.getD fun _ => false) (fun r hr => by rw [hr]; rfl)
  rw [rho_trK]
  exact ⟨R, z.2.2.1, hc⟩

/-- **With an acceptance lemma that excludes no verifier message, the interactive verifier accepts
that transcript.** -/
theorem accepts_at {π : OneProtocolProof lam Q} {τ : Tr Q.loc.shape} (hp : PlainAt Q wq σ cap π τ)
    (hA : AccLaw Q wq x y σ ∅) : Q.loc.accept x y τ = true :=
  hA τ hp.2.1 hp.puts (Set.notMem_empty _)

end One

/-! ## 3. The scheme, for any three provers -/

section Whole
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)
  (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))

theorem key_plains (i : I) (c : DrawC lam L Bd aT aL h.KT h.KL) (π : OneProtocolProof lam (batTC L aT))
    (hπ : ((commitAt W S cA h i c).det g).1.piT = some π) :
    ∃ τ, (proveTA W cA (fun _ => (tabG W S h g i c.r c.s).tree) (h.dressT (h.rvT c.κ) c.co) h.capT
        (tabG W S h g i c.r c.s).tree.root (L.recOf i c.r (tabG W S h g i c.r c.s).seed)
        (L.encodeIndex i c.r) (h.st.T i c.r (tabG W S h g i c.r c.s).seed c.κ)).det g = .ok (π, τ) ∧
      PlainAt (batTC L aT) (wTC W) (h.st.T i c.r (tabG W S h g i c.r c.s).seed c.κ) h.capT π τ := by
  rw [det_commitAt] at hπ
  obtain ⟨τ, hτ⟩ := shown_some hπ
  exact ⟨τ, hτ, plains_of_prove _ _ _ _ _ _ _ _ _ _ _ _ _ g π τ hτ⟩

theorem link_plains (i : I) (c : DrawC lam L Bd aT aL h.KT h.KL) (j : ℕ)
    (e : DrawCopy lam L Bd aT aL h.KL) (hj : c.copies[j]? = some e)
    (l : Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL)))
    (hl : ((commitAt W S cA h i c).det g).1.links[j]? = some l) (π : OneProtocolProof lam (batLC L aL))
    (hπ : l.2.2 = some π) :
    ∃ τ, (proveLA W cA
        (fun k => if k = 0 then (tabG W S h g i c.r c.s).tree else (tabG W S h g i e.r e.s).tree)
        (h.dressL (h.rvL e.κ) e.co) h.capL (tabG W S h g i c.r c.s).tree.root
        (tabG W S h g i e.r e.s).tree.root (L.recOf i c.r (tabG W S h g i c.r c.s).seed)
        (L.recOf i e.r (tabG W S h g i e.r e.s).seed) (L.encodeIndex i c.r, L.encodeIndex i e.r)
        (h.st.Lk i (c.r, (tabG W S h g i c.r c.s).seed) (e.r, (tabG W S h g i e.r e.s).seed)
          e.κ)).det g = .ok (π, τ) ∧
      PlainAt (batLC L aL) (wLC W)
        (h.st.Lk i (c.r, (tabG W S h g i c.r c.s).seed) (e.r, (tabG W S h g i e.r e.s).seed) e.κ)
        h.capL π τ := by
  rw [det_commitAt] at hl
  have hl' : (c.copies.map fun e => (linkO W cA h i (tabG W S h g i c.r c.s)
      (tabG W S h g i e.r e.s) e).det g)[j]? = some l := hl
  rw [List.getElem?_map, hj, Option.map_some, det_linkO] at hl'
  obtain rfl := Option.some.inj hl'
  obtain ⟨τ, hτ⟩ := shown_some hπ
  exact ⟨τ, hτ, plains_of_prove _ _ _ _ _ _ _ _ _ _ _ _ _ g π τ hτ⟩

theorem session_plains (i : I) (x : X) (c : DrawC lam L Bd aT aL h.KT h.KL)
    (e : DrawCopy lam L Bd aT aL h.KL) (dP : DrawP lam L Bd aT aL h.KB)
    (hj : c.copies[dP.j]? = some e) (π : OneProtocolProof lam L.onlineBatch)
    (hπ : ((proveAt W cA r₀ h ((commitAt W S cA h i c).det g).2 x dP).det g).piB = some π) :
    ∃ τ, (proveBA W cA r₀ (fun _ => (tabG W S h g i e.r e.s).tree) (h.dressB (h.rvB dP.κ) dP.co)
        h.capB (tabG W S h g i e.r e.s).tree.root x (L.recOf i e.r (tabG W S h g i e.r e.s).seed)
        (L.encodeIndex i e.r)
        (h.st.B i e.r (tabG W S h g i e.r e.s).seed x (h.nm dP.j) dP.κ)).det g = .ok (π, τ) ∧
      PlainAt L.onlineBatch (wBC W) (h.st.B i e.r (tabG W S h g i e.r e.s).seed x (h.nm dP.j) dP.κ)
        h.capB π τ := by
  have ht : ((commitAt W S cA h i c).det g).2.copies[dP.j]? = some (tabG W S h g i e.r e.s) := by
    rw [det_commitAt]
    show (c.copies.map fun e => tabG W S h g i e.r e.s)[dP.j]? = _
    rw [List.getElem?_map, hj]
    rfl
  rw [det_proveAt W cA r₀ h g _ x dP _ ht] at hπ
  obtain ⟨τ, hτ⟩ := shown_some hπ
  have hi : ((commitAt W S cA h i c).det g).2.i = i := by rw [det_commitAt]
  rw [hi] at hτ
  exact ⟨τ, hτ, plains_of_prove _ _ _ _ _ _ _ _ _ _ _ _ _ g π τ hτ⟩

/-- What is given out is what a run returned, at verifier messages at which the prover does not
abort. -/
theorem shown_go {P : Type} {s : Shape} {stop : Rho s → Bool} {r : Res (P × Tr s)} {π : P}
    (h : shown stop r = some π) : ∃ τ, r = .ok (π, τ) ∧ stop τ.rho = false := by
  cases r with
  | noFormat => cases h
  | ranOut j => cases h
  | ok a =>
    have h' : (if stop a.2.rho then none else some a.1) = some π := h
    split at h'
    · cases h'
    · rename_i hn
      obtain rfl := Option.some.inj h'
      exact ⟨a.2, rfl, by simpa using hn⟩

variable (hW : WiresFit W cA)
include hW

theorem key_hashed (i : I) (c : DrawC lam L Bd aT aL h.KT h.KL) (π : OneProtocolProof lam (batTC L aT))
    (hπ : ((commitAt W S cA h i c).det g).1.piT = some π) :
    ∃ τ : Tr (batTC L aT).loc.shape,
      (proveTA W cA (fun _ => (tabG W S h g i c.r c.s).tree) (h.dressT (h.rvT c.κ) c.co) h.capT
        (tabG W S h g i c.r c.s).tree.root (L.recOf i c.r (tabG W S h g i c.r c.s).seed)
        (L.encodeIndex i c.r) (h.st.T i c.r (tabG W S h g i c.r c.s).seed c.κ)).det g = .ok (π, τ) ∧
      PlainAt (batTC L aT) (wTC W) (h.st.T i c.r (tabG W S h g i c.r c.s).seed c.κ) h.capT π τ ∧
      h.st.stopT i c.r (tabG W S h g i c.r c.s).seed τ.rho = false ∧
      ∃ Rt ph, chainF g Tag.test
        (cmsTA cA (tabG W S h g i c.r c.s).tree.root
          (L.recOf i c.r (tabG W S h g i c.r c.s).seed).2) none π.salt π.rtreq
        (batTC L aT).loc.shape (batTC L aT).ann (wTC W).sh id 0 .first π.roots π.plains =
          some (τ.rho, Rt, ph) := by
  rw [det_commitAt] at hπ
  obtain ⟨τ, hτ, hs⟩ := shown_go hπ
  exact ⟨τ, hτ, plains_of_prove _ _ _ _ _ _ _ _ _ _ _ _ _ g π τ hτ, hs,
    hashed_of_prove _ _ _ _ _ _ _ _ _ _ _ _ _ g hW.fewT.1 hW.fewT.2 π τ hτ⟩

theorem link_hashed (i : I) (c : DrawC lam L Bd aT aL h.KT h.KL) (j : ℕ)
    (e : DrawCopy lam L Bd aT aL h.KL) (hj : c.copies[j]? = some e)
    (l : Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL)))
    (hl : ((commitAt W S cA h i c).det g).1.links[j]? = some l) (π : OneProtocolProof lam (batLC L aL))
    (hπ : l.2.2 = some π) :
    ∃ τ : Tr (batLC L aL).loc.shape,
      (proveLA W cA
        (fun k => if k = 0 then (tabG W S h g i c.r c.s).tree else (tabG W S h g i e.r e.s).tree)
        (h.dressL (h.rvL e.κ) e.co) h.capL (tabG W S h g i c.r c.s).tree.root
        (tabG W S h g i e.r e.s).tree.root (L.recOf i c.r (tabG W S h g i c.r c.s).seed)
        (L.recOf i e.r (tabG W S h g i e.r e.s).seed) (L.encodeIndex i c.r, L.encodeIndex i e.r)
        (h.st.Lk i (c.r, (tabG W S h g i c.r c.s).seed) (e.r, (tabG W S h g i e.r e.s).seed)
          e.κ)).det g = .ok (π, τ) ∧
      PlainAt (batLC L aL) (wLC W)
        (h.st.Lk i (c.r, (tabG W S h g i c.r c.s).seed) (e.r, (tabG W S h g i e.r e.s).seed) e.κ)
        h.capL π τ ∧
      h.st.stopL i (c.r, (tabG W S h g i c.r c.s).seed) (e.r, (tabG W S h g i e.r e.s).seed)
        τ.rho = false ∧
      ∃ Rt ph, chainF g Tag.link
        (cmsLA cA (tabG W S h g i c.r c.s).tree.root (tabG W S h g i e.r e.s).tree.root
          (L.recOf i c.r (tabG W S h g i c.r c.s).seed).2
          (L.recOf i e.r (tabG W S h g i e.r e.s).seed).2) none π.salt π.rtreq
        (batLC L aL).loc.shape (batLC L aL).ann (wLC W).sh id 0 .first π.roots π.plains =
          some (τ.rho, Rt, ph) := by
  rw [det_commitAt] at hl
  have hl' : (c.copies.map fun e => (linkO W cA h i (tabG W S h g i c.r c.s)
      (tabG W S h g i e.r e.s) e).det g)[j]? = some l := hl
  rw [List.getElem?_map, hj, Option.map_some, det_linkO] at hl'
  obtain rfl := Option.some.inj hl'
  obtain ⟨τ, hτ, hs⟩ := shown_go hπ
  exact ⟨τ, hτ, plains_of_prove _ _ _ _ _ _ _ _ _ _ _ _ _ g π τ hτ, hs,
    hashed_of_prove _ _ _ _ _ _ _ _ _ _ _ _ _ g hW.fewL.1 hW.fewL.2 π τ hτ⟩

theorem session_hashed (i : I) (x : X) (c : DrawC lam L Bd aT aL h.KT h.KL)
    (e : DrawCopy lam L Bd aT aL h.KL) (dP : DrawP lam L Bd aT aL h.KB)
    (hj : c.copies[dP.j]? = some e) (π : OneProtocolProof lam L.onlineBatch)
    (hπ : ((proveAt W cA r₀ h ((commitAt W S cA h i c).det g).2 x dP).det g).piB = some π) :
    ∃ τ : Tr L.onlineBatch.loc.shape,
      (proveBA W cA r₀ (fun _ => (tabG W S h g i e.r e.s).tree) (h.dressB (h.rvB dP.κ) dP.co)
        h.capB (tabG W S h g i e.r e.s).tree.root x (L.recOf i e.r (tabG W S h g i e.r e.s).seed)
        (L.encodeIndex i e.r)
        (h.st.B i e.r (tabG W S h g i e.r e.s).seed x (h.nm dP.j) dP.κ)).det g = .ok (π, τ) ∧
      PlainAt L.onlineBatch (wBC W) (h.st.B i e.r (tabG W S h g i e.r e.s).seed x (h.nm dP.j) dP.κ) h.capB
        π τ ∧
      h.st.stopB i e.r (tabG W S h g i e.r e.s).seed x (h.nm dP.j) τ.rho = false ∧
      ∃ Rt ph, chainF g Tag.onl
        (cmsBA cA (tabG W S h g i e.r e.s).tree.root
          (L.recOf i e.r (tabG W S h g i e.r e.s).seed).2)
        (xinBA r₀ (x, L.recOf i e.r (tabG W S h g i e.r e.s).seed)) π.salt π.rtreq
        L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh id 0 .first π.roots π.plains =
          some (τ.rho, Rt, ph) := by
  have ht : ((commitAt W S cA h i c).det g).2.copies[dP.j]? = some (tabG W S h g i e.r e.s) := by
    rw [det_commitAt]
    show (c.copies.map fun e => tabG W S h g i e.r e.s)[dP.j]? = _
    rw [List.getElem?_map, hj]
    rfl
  rw [det_proveAt W cA r₀ h g _ x dP _ ht] at hπ
  obtain ⟨τ, hτ, hs⟩ := shown_go hπ
  have hi : ((commitAt W S cA h i c).det g).2.i = i := by rw [det_commitAt]
  rw [hi] at hτ hs
  exact ⟨τ, hτ, plains_of_prove _ _ _ _ _ _ _ _ _ _ _ _ _ g π τ hτ, hs,
    hashed_of_prove _ _ _ _ _ _ _ _ _ _ _ _ _ g hW.fewB.1 hW.fewB.2 π τ hτ⟩

end Whole

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.chain_pass
#print axioms AtPublicFiles.Shown.treesO_len
#print axioms AtPublicFiles.Shown.chain_hashed
#print axioms AtPublicFiles.Shown.puts_plain
#print axioms AtPublicFiles.Shown.PlainAt.puts
#print axioms AtPublicFiles.Shown.plains_of_prove
#print axioms AtPublicFiles.Shown.hashed_of_prove
#print axioms AtPublicFiles.Shown.accepts_at
#print axioms AtPublicFiles.Shown.key_plains
#print axioms AtPublicFiles.Shown.link_plains
#print axioms AtPublicFiles.Shown.session_plains
#print axioms AtPublicFiles.Shown.shown_go
#print axioms AtPublicFiles.Shown.key_hashed
#print axioms AtPublicFiles.Shown.link_hashed
#print axioms AtPublicFiles.Shown.session_hashed
