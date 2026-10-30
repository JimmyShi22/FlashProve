-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WrapLaws/AtKit.lean: the premises of the game's theorem at the reduction's own letters, from
the premises of the statement of index privacy; and the game's bound there.

Lemmas, one statement (Spec.gameAtW) and its proof. This file states no goal of the release.

The reduction wrapW (Johnson/WholeKey/Wrap.lean) plays against the game of Hiop/Seeded/Game.lean at
the kit kitW: the auxiliary value of a run is (the outcome, the log of answers) of a dry first pass
of the compiled prover's chain, and the verifier's randomness is read off the outcome. The game's
theorem at one index (Spec.lifeSeededAt, Hiop/Seeded/AtIndex.lean) has premises at that kit. Here
they are had from PremW (Johnson/WholeKey/Premises.lean), AT AN INDEX i WITH ok i: PremW asks that
the runs can be simulated at the indices of its letter ok alone.
  the simulators are good at the kit, at i (good_kitW). PremW says it under UNIFORM verifier's
    randomness with the test bits set to 0, apart for the stops that hang on the private input: the
    measure of "no such stop, and output and simulator differ" (Sims.Good) and the measure of "such
    a stop" (StopsSmall). The law of a dry pass (chainLawDry_rhoO, OnBytes/Dry/ChainLaw.lean)
    carries both to the kit: "no search ran out and the verifier's randomness lies in B" has at most
    the uniform measure of B with the test bits set to 0. So the error of a run at the kit is the
    sum of the two;
  the honest sides speak of the encodings (ext_recsG), from ExtEnc;
  the reads and the hiding of the encoding: PremW's own clause (ReadsG);
  the budget, from PremW's two inequalities (fits_boundsW, Johnson/WrapLaws/Bounds.lean).
A lemma beside them, used by nothing here: cntO_of_cntB. ReadsG counts the reads of a session of ONE
slot. Whoever has the count for a batch of N slots (BatchInteractiveOracleProof.ReadsAtMost, Iop/Batch.lean) has that
one from it if 0 < N; at N = 0 the count for a batch says nothing.

Main names (namespace OnBytes.WrapLaws).
  recsG a          the game's honest sides: Johnson/WrapLaws/Recs.lean.
  pr_pass1_le      the law of a dry pass, in the kit's letters.
  Spec.gameAtW, gameAtW   the real game and the simulated game at the reduction's letters are within
                   (zT + (M + 1) · zL + n · zO) + (hT + (M + 1) · hL + n · hO): the two summands of
                   zetaW (Johnson/WholeKey/Zeta.lean) for the simulators' errors and for the stops,
                   in its letters. The shape of the premise "game" of the frame
                   (Compile/PrivFrame/Spec.lean).
Limits: those of Hiop/Seeded/Game.lean. NOTHING HERE BOUNDS FROM ABOVE THE CHANCE THAT THE KIT's
VERIFIER's RANDOMNESS IS "none" (a search of the dry pass has run out), not even at a toy: where it
is none both games show the same and the bound is idle. (For the SCHEME at the second toy's letters,
at an index in range, the proof of one request holds a string but for probability 1/16:
string_often_pad2, Johnson/WholeKey/FoeScheme.lean. That is a statement on the real prover's run,
not on the kit's dry pass.) The premises are asked at every number of a copy. Whether an index lies
in the range ok is not hidden by anything here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WrapLaws.Bounds
import Johnson.WrapLaws.Recs
import Johnson.WholeKey.Zeta
import OnBytes.Dry.ChainLaw
import Hiop.Seeded.AtIndex

set_option autoImplicit false

noncomputable section

namespace OnBytes.WrapLaws
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey Hiop Hiop.Seeded
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

namespace Spec

/-- Under the premises of the statement of index privacy: the real game on an index i with ok i and
the simulated game (at ANY fixed index i₀), at the reduction's kit, bounds, honest sides and
simulators, for an adversary with at most n calls for a session, all at instances in the relation
with i. -/
def gameAtW : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params) (a : AtRecs lam L Bd aT aL)
    (Sm : Sims L) (ok : I → Prop) (Gs : L.OutOfDomainSeed → Prop) (Ryes : I → X → Prop) (c : CoinNums Bd)
    (u : NumsW),
    PremW W S cA p a Sm ok Gs Ryes c u →
    ∀ i : I, ok i → ∀ (i₀ : I) (n : ℕ) (α : Type)
      (E : Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GOut L (kitW W r₀ a.side).form)
        (GIn L (kitW W r₀ a.side).form) α),
      E.CallsOK (okCall (Ryes i)) → SessLe E n →
        tv ((interact (gameReal L (kitW W r₀ a.side) (recsG a) i (boundsW a.side u.s1) Gs _) E
              (none, Table.empty _)).map Prod.fst)
            ((interact (gameSim L (kitW W r₀ a.side) (simsG a.side Sm) i₀ (boundsW a.side u.s1) Gs
              _) E (none, Table.empty _)).map Prod.fst) ≤
          (u.zT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.zL + (n : ℝ≥0∞) * u.zO) +
            (u.hT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.hL + (n : ℝ≥0∞) * u.hO)

end Spec

/-! ## One slot reads at most what a batch reads -/

section Slot
variable {N : ℕ}

/-- the verifier's randomness of a batch in which every slot sees ρ -/
def repRho : (s : Shape) → (A : RoundSplits s) → Rho s → BRho N s A
  | [], _, _ => ()
  | _ :: s, (a, A), (c, ρ) =>
      ((match a.kind with
        | .sh => c
        | .lo => fun _ => c : a.kind.All N _), repRho s A ρ)

theorem slot_repRho (j : Fin N) : ∀ (s : Shape) (A : RoundSplits s) (ρ : Rho s),
    BRho.slot j (repRho (N := N) s A ρ) = ρ
  | [], _, _ => rfl
  | _ :: s, (a, A), (c, ρ) => by
    show (a.kind.slot _ j, BRho.slot j (repRho s A ρ)) = (c, ρ)
    rw [slot_repRho j s A ρ]
    cases a.kind <;> rfl

theorem cntO_of_cntB {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} {q : ℕ}
    (h : Q.ReadsAtMost N q) (hN : 0 < N) (y : Y) (ρ : Rho Q.loc.shape) :
    (Q.loc.extReads y ρ).card ≤ q := by
  classical
  refine (Finset.card_le_card fun p hp => ?_).trans
    (h (fun _ => some y) (repRho Q.loc.shape Q.ann ρ))
  unfold BatchInteractiveOracleProof.allReads
  refine Finset.mem_biUnion.2 ⟨⟨0, hN⟩, Finset.mem_univ _, ?_⟩
  show p ∈ Q.loc.extReads y (BRho.slot ⟨0, hN⟩ (repRho Q.loc.shape Q.ann ρ))
  rw [slot_repRho]
  exact hp

end Slot

theorem ext_recsG {a : AtRecs lam L Bd aT aL} (h : ExtEnc a.Hs) : (recsG a).Ext :=
  ⟨fun _ i r s => h.T i r s, fun _ i r s r' s' => h.Lk i r s r' s',
    fun e i r s => h.B i r s (a.nm (e - 1))⟩

/-! ## The law of a dry pass, in the kit's letters -/

theorem pr_pass1_le {I' X' : Type} {K : ℕ} {L' : BatchProtocolWithLeafBody I' X'} (t : Tag) {Y : Type} {E : ExtSpec}
    (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L')
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L' t) (annOf L' t)) (xin : Y → Option X')
    (cms : List (Dig lam)) (x : Y) (cap : ℕ → ℕ) (co : Coins lam L')
    (hW : RoundsQueryLayout.OKG Q.loc.shape Q.ann wq.sh) (B : Set (Rho Q.loc.shape)) :
    pr (pass1 t Q wq embS embP xin cms x cap co) {z | ∃ ρ, z.1.toOption = some ρ ∧ ρ ∈ B} ≤
      pr (unif (Rho Q.loc.shape)) {ρ | RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh ρ ∈ B} := by
  refine (pr_mono _ fun z hz => ?_).trans
    (OnBytes.Dry.chainLawDry_rhoO lateRun t rfl cms (xin x) co cap Q.loc.shape Q.ann wq.sh embS embP
      0 .first (Strat.dflt _ ()) hW B)
  obtain ⟨ρ, e, hρ⟩ := hz
  obtain ⟨v, R⟩ := z
  cases v with
  | ok w => exact ⟨ρ, congrArg Res.ok (Option.some.inj e), hρ⟩
  | noFormat => exact absurd e (by simp [Res.toOption])
  | ranOut j => exact absurd e (by simp [Res.toOption])

/-- From the two measures under uniform verifier's randomness to the measure under a dry pass. Hid:
the stops that hang on the private input; D: output and simulator differ. -/
theorem pr_pass1_split {I' X' : Type} {K : ℕ} {L' : BatchProtocolWithLeafBody I' X'} (t : Tag) {Y : Type} {E : ExtSpec}
    (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L')
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L' t) (annOf L' t)) (xin : Y → Option X')
    (cms : List (Dig lam)) (x : Y) (cap : ℕ → ℕ) (co : Coins lam L')
    (hW : RoundsQueryLayout.OKG Q.loc.shape Q.ann wq.sh) (Hid D : Set (Rho Q.loc.shape)) {z hz : ℝ≥0∞}
    (h1 : pr (unif (Rho Q.loc.shape))
      {ρ | RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh ρ ∉ Hid ∧
        RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh ρ ∈ D} ≤ z)
    (h2 : pr (unif (Rho Q.loc.shape)) {ρ | RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh ρ ∈ Hid} ≤ hz) :
    pr (pass1 t Q wq embS embP xin cms x cap co) {v | ∃ ρ, v.1.toOption = some ρ ∧ ρ ∈ D} ≤
      z + hz := by
  classical
  refine (pr_pass1_le t Q wq embS embP xin cms x cap co hW D).trans
    ((pr_le_add _ fun ρ hρ => ?_).trans (add_le_add h1 h2))
  by_cases hh : RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh ρ ∈ Hid
  · exact Or.inr hh
  · exact Or.inl ⟨hh, hρ⟩

/-! ## The simulators are good at the kit -/

theorem good_kitW {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {cA : L.OutOfDomainAnswer → List (Dig lam)} (r₀ : L.Rec)
    {a : AtRecs lam L Bd aT aL} {Sm : Sims L} {ok : I → Prop} {Gs : L.OutOfDomainSeed → Prop}
    {Ryes : I → X → Prop} {zT zL zO hT hL hO : ℝ≥0∞} (hW : OKA W cA)
    (hG : Sm.Good a.Hs W ok Gs Ryes zT zL zO) (hS : StopsSmall a.Hs W ok Gs Ryes hT hL hO) {i : I}
    (hi : ok i) :
    (simsG a.side Sm).GoodAt (kitW W r₀ a.side) (recsG a) Gs Ryes i (zT + hT) (zL + hL)
      (zO + hO) where
  goodT := fun _ r s hs =>
    pr_pass1_split Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none) [] (L.recOf i r s)
      a.capT (blank a.b₀ W.depthReqT) hW.T.sh (a.Hs.T.Hid (i, r, s) (L.recOf i r s))
      {ρ | a.Hs.T.output (i, r, s) (L.recOf i r s) ρ ≠
        Sm.T (L.recOf i r s) ρ (L.offline.extAns (L.recOf i r s) ρ (L.encodeIndex i r))}
      (hG.T i r s hi hs) (hS.T i r s hi hs)
  goodL := fun _ r s r' s' hs hs' =>
    pr_pass1_split Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none) []
      (L.recOf i r s, L.recOf i r' s') a.capL (blank a.b₀ W.depthReqL) hW.Lk.sh
      (a.Hs.Lk.Hid (i, (r, s), (r', s')) (L.recOf i r s, L.recOf i r' s'))
      {ρ | a.Hs.Lk.output (i, (r, s), (r', s')) (L.recOf i r s, L.recOf i r' s') ρ ≠
        Sm.Lk (L.recOf i r s, L.recOf i r' s') ρ
          (L.link.extAns (L.recOf i r s, L.recOf i r' s') ρ (L.encodeIndex i r, L.encodeIndex i r'))}
      (hG.Lk i r s r' s' hi hs hs') (hS.Lk i r s r' s' hi hs hs')
  goodB := fun e r s x hs hx =>
    pr_pass1_split Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) [] (x, L.recOf i r s) a.capB
      (blank a.b₀ W.depthReq) hW.B.sh
      ((sessionAt a.Hs (a.nm (e - 1))).Hid (i, r, s) (x, L.recOf i r s))
      {ρ | (sessionAt a.Hs (a.nm (e - 1))).output (i, r, s) (x, L.recOf i r s) ρ ≠
        Sm.B (a.nm (e - 1)) (x, L.recOf i r s) ρ
          (L.onlineBatch.loc.extAns (x, L.recOf i r s) ρ (L.encodeIndex i r))}
      (hG.B (a.nm (e - 1)) i r s x hi hs hx) (hS.B (a.nm (e - 1)) i r s x hi hs hx)

/-! ## The bound -/

theorem gameAtW : Spec.gameAtW := by
  intro I X lam L Bd aT aL W S cA r₀ p a Sm ok Gs Ryes c u hP i hi i₀ n α E hE hn
  have h := lifeSeededAt _ I X L (kitW W r₀ a.side) Gs Ryes u.b u.qT u.qpar u.qch u.qon
    (u.zT + u.hT) (u.zL + u.hL) (u.zO + u.hO) hP.reads (recsG a)
    (ext_recsG hP.ext) (simsG a.side Sm) (boundsW a.side u.s1)
    (fits_boundsW a.side u.s1 hP.budget₀ hP.budget₁) i
    (good_kitW r₀ hP.wires hP.good hP.stops hi) i₀ n α E hE hn
  refine h.trans (le_of_eq ?_)
  rw [errN_boundsW]
  show u.zT + u.hT + ((a.M + 1 : ℕ) : ℝ≥0∞) * (u.zL + u.hL) + (n : ℝ≥0∞) * (u.zO + u.hO) = _
  ring

end OnBytes.WrapLaws

#print axioms OnBytes.WrapLaws.good_kitW
#print axioms OnBytes.WrapLaws.gameAtW
