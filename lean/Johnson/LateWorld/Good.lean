-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/Good.lean: THE REDUCTION's SETUP BEHIND THE TABLES, AGAINST THE REAL GAME: the
key's test and the links (restA, Johnson/LateWorld/SpecSetupA.lean) are the honest test and links
laid late (testM, linksM, Johnson/LateWorld/SpecSetup.lean), with the reduction's and the game's
states beside them.

This file states no goal of the release: one step of the proof of Spec.lateToWrap
(Johnson/LateWorld/SpecWrap.lean). The statements on the game's tables and on the links
(Johnson/LateWorld/SpecSetupW.lean) and on the key's test (Johnson/LateWorld/SpecBranches.lean) are
taken as hypotheses here; Johnson/LateWorld/Whole.lean puts their proofs in.

Main names (namespace OnBytes.LateWorld).
  game_start, game_test   the game's reply to the call for the first table; for the key's test.
  usedT        the game's counts after the key's test.
  drawU_len, mkTs_len, linksUsed_sess, coVT_eq   small facts.
  restA_good   THE STEP: the setup behind the tables, against the game.

Limits. It speaks of a state of the game in which no table was refused and nothing has been asked
yet. It says nothing where a seed lies outside Gs.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateWorld.Batch
import Johnson.LateWorld.SpecBranches
import Johnson.LateWorld.SpecSetupA

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.LateWorld
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.Dry OnBytes.WrapLaws
open _root_.Compile.GlueB (GCall GIn GAdm asW)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
  {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
  {cA : L.OutOfDomainAnswer → List (Dig lam)} (r₀ : L.Rec) {a : AtRecs lam L Bd aT aL} {Gs : L.OutOfDomainSeed → Prop}
  (s1 : ℕ) (i : I)

/-! ## Two replies of the game -/

theorem game_start (Tg : Tb W) (s : L.OutOfDomainSeed) (hs : Gs s) :
    repG W r₀ a Gs s1 i (none, Tg) (.table s) =
      (unif L.EncodingRandomness).map fun r =>
        (.ood (L.recOf i r s), (some (0, Hiop.UsedR.zero, (0, fun _ => (r, s))), Tg)) := by
  show (Hiop.Seeded.gameReply (Hiop.Seeded.realLawsG L (kitW W r₀ a.side) (recsG a) i).host
    (boundsW a.side s1) Gs none (.table s)).map (fun p => (p.1, (p.2, Tg))) = _
  simp only [Hiop.Seeded.gameReply]
  rw [if_pos hs]
  have e1 : (Hiop.Seeded.realLawsG L (kitW W r₀ a.side) (recsG a) i).host.start s =
      (unif L.EncodingRandomness).map fun r => (L.recOf i r s, ((0, fun _ => (r, s)) : StH L)) := rfl
  rw [e1]
  exact (PMF.map_comp _ _ _).trans ((PMF.map_comp _ _ _).trans rfl)

theorem game_test (c : ℕ) (u : Hiop.UsedR) (st : StH L) (Tg : Tb W) (e : ℕ) (he : e ≤ c)
    (hu : u.tests e < (boundsW a.side s1).tests e) :
    repG W r₀ a Gs s1 i (some (c, u, st), Tg) (.test e) =
      (Hiop.Seeded.runAt ((recsG a).T e)
        ((kitW W r₀ a.side).μT e (L.recOf i (st.2 e).1 (st.2 e).2)) (kitW W r₀ a.side).ρT
        (i, (st.2 e).1, (st.2 e).2) (L.recOf i (st.2 e).1 (st.2 e).2)).map fun v =>
        (.test v, (some (c, { u with tests := Hiop.bump u.tests e }, st), Tg)) := by
  show (Hiop.Seeded.gameReply (Hiop.Seeded.realLawsG L (kitW W r₀ a.side) (recsG a) i).host
    (boundsW a.side s1) Gs (some (c, u, st)) (.test e)).map (fun p => (p.1, (p.2, Tg))) = _
  simp only [Hiop.Seeded.gameReply]
  rw [if_pos ⟨he, hu⟩]
  have e1 : (Hiop.Seeded.realLawsG L (kitW W r₀ a.side) (recsG a) i).host.test st e =
      (Hiop.Seeded.runAt ((recsG a).T e)
        ((kitW W r₀ a.side).μT e (L.recOf i (st.2 e).1 (st.2 e).2)) (kitW W r₀ a.side).ρT
        (i, (st.2 e).1, (st.2 e).2) (L.recOf i (st.2 e).1 (st.2 e).2)).map fun v => (v, st) :=
    rfl
  rw [e1]
  exact (PMF.map_comp _ _ _).trans ((PMF.map_comp _ _ _).trans rfl)

/-! ## Small facts -/

/-- The game's counts after the key's test, and nothing else. -/
def usedT : Hiop.UsedR :=
  { Hiop.UsedR.zero with tests := Hiop.bump Hiop.UsedR.zero.tests 0 }

theorem linksUsed_sess : ∀ (n : ℕ) (u : Hiop.UsedR) (e : ℕ), (linksUsed u e n).sess = u.sess
  | 0, _, _ => rfl
  | n + 1, u, e => linksUsed_sess n { u with links := Hiop.bump u.links e } (e + 1)

theorem drawU_len : ∀ (n : ℕ), ∀ rs ∈ (drawU L n).support, rs.length = n
  | 0, rs, h => by
    rw [drawU, PMF.support_pure, Set.mem_singleton_iff] at h
    rw [h]
    rfl
  | n + 1, rs, h => by
    rw [drawU] at h
    obtain ⟨r, -, h⟩ := (PMF.mem_support_bind_iff _ _ _).1 h
    obtain ⟨rs', h', h⟩ := (PMF.mem_support_bind_iff _ _ _).1 h
    rw [PMF.support_pure, Set.mem_singleton_iff] at h
    rw [h, List.length_cons, drawU_len n rs' h']

theorem mkTs_len : ∀ (rs : List L.EncodingRandomness) (os : List (TreeK lam (typedOracleCarrier L Bd aT aL) × L.OutOfDomainSeed)),
    rs.length = os.length → (mkTs i rs os).length = os.length
  | [], [], _ => rfl
  | r :: rs, o :: os, h => by
    rw [mkTs, List.length_cons, List.length_cons, mkTs_len rs os (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- the coins of the second pass, in the reduction's text and in coVT -/
theorem coVT_eq (co : Coins lam (typedOracleCarrier L Bd aT aL)) (v : Option (DView L.offline)) :
    (match v with
      | some d => a.side.dressT (a.side.pvT d.plains) co
      | none => co) = coVT a co (v.map DView.plains) := by
  cases v <;> rfl

/-! ## The setup behind the tables -/

/-- **The setup behind the tables, against the game**: the honest test and links, laid late. tr₁:
the first table's tree over fillings; (r₁, sd₁): its randomness and seed, which the game keeps at
the number 0. -/
theorem restA_good (hT : Spec.testBranch) (hLk : Spec.linksW) {ok : I → Prop} {δ : ℝ≥0∞}
    (hP : PremLate W S cA a ok Gs δ) (hi : ok i) (d : DrawC lam L Bd aT aL a.side.KT a.side.KL)
    (T : Tb W) (tr₁ : TreeK lam (typedOracleCarrier L Bd aT aL)) (r₁ : L.EncodingRandomness) (sd₁ : L.OutOfDomainSeed)
    (ts : List (TabW lam L Bd aT aL)) (c : ℕ) (st : StH L) (Tg : Tb W)
    (hst : st.2 0 = (r₁, sd₁)) (hco : d.co.path.length = W.depthReqT)
    (hc : 1 + (d.copies.zip ts).length ≤ c + 1)
    (hl : ∀ k x, (d.copies.zip ts)[k]? = some x →
      x.2.ood = L.recOf i (st.2 (1 + k)).1 (st.2 (1 + k)).2 ∧ x.1.co.path.length = W.depthReqL) :
    runG W r₀ a Gs s1 i
        (restA W cA r₀ a.side d T (some ⟨tr₁, L.recOf i r₁ sd₁⟩) (some ts))
        (some (c, Hiop.UsedR.zero, st), Tg) =
      (testM W cA a.side i ⟨r₁, realTree W a.b₀ (L.encodeIndex i r₁) tr₁, sd₁⟩ d.co T).bind fun o₃ =>
        (linksM W cA a.side i ⟨r₁, realTree W a.b₀ (L.encodeIndex i r₁) tr₁, sd₁⟩
          (((d.copies.zip ts).map fun x => x.1.co).zip
            (realCopies W a i st.2 1 ((d.copies.zip ts).map fun x => x.2))) o₃.2).map fun o₄ =>
          ((.inl ⟨tr₁.root, L.recOf i r₁ sd₁, o₃.1, o₄.1⟩, (o₄.2, some ts)),
            (some (c, linksUsed usedT 1 (d.copies.zip ts).length, st), Tg)) := by
  have hlk := fun T' => hLk I X lam L Bd aT aL W S cA r₀ a ok Gs δ s1 i hP hi
    ⟨tr₁, L.recOf i r₁ sd₁⟩ c st Tg (d.copies.zip ts) 1 usedT T' le_rfl hc (fun _ _ => rfl)
    (by rw [hst]) hl
  simp only [hst] at hlk
  have ht := hT I X lam L Bd aT aL W S cA r₀ a ok Gs δ i hP hi 0 ⟨tr₁, L.recOf i r₁ sd₁⟩ r₁ sd₁ d.co
    hco T
  rw [restA, runG_call, game_test r₀ s1 i c Hiop.UsedR.zero st Tg 0 (Nat.zero_le c)
    (Nat.zero_lt_one), PMF.bind_map]
  simp only [hst]
  have hstep : ∀ v : (kitW W r₀ a.side).AT × Option (DView L.offline),
      runG W r₀ a Gs s1 i
        ((pass2A Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none)
          (cmsTA cA tr₁.root (L.recOf i r₁ sd₁).2) (L.recOf i r₁ sd₁) (fun _ => tr₁) a.side.capT
          W.embE v.2
          (match v.2 with
            | some d' => a.side.dressT (a.side.pvT d'.plains) d.co
            | none => d.co) v.1.2 T).bind fun o₃ =>
          (linksA W cA r₀ a.side ⟨tr₁, L.recOf i r₁ sd₁⟩ 1 (d.copies.zip ts) o₃.2).bind fun o₄ =>
            .halt ((Sum.inl ⟨tr₁.root, L.recOf i r₁ sd₁, o₃.1, o₄.1⟩ :
              GIn (FullKey lam L aT aL) (RequestProof lam L)), ((o₄.2, some ts) : StG W)))
        (some (c, usedT, st), Tg) =
      (pass2 Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none)
        (cmsTA cA tr₁.root (L.recOf i r₁ sd₁).2) (L.recOf i r₁ sd₁) (fun _ => tr₁) a.side.capT
        W.embE v.2 (coVT a d.co (v.2.map DView.plains)) v.1.2 T).bind fun o₃ =>
        (linksM W cA a.side i ⟨r₁, realTree W a.b₀ (L.encodeIndex i r₁) tr₁, sd₁⟩
          (((d.copies.zip ts).map fun x => x.1.co).zip
            (realCopies W a i st.2 1 ((d.copies.zip ts).map fun x => x.2))) o₃.2).map fun o₄ =>
          ((.inl ⟨tr₁.root, L.recOf i r₁ sd₁, o₃.1, o₄.1⟩, (o₄.2, some ts)),
            (some (c, linksUsed usedT 1 (d.copies.zip ts).length, st), Tg)) := by
    intro v
    rw [runG_bind, runG_pass2A, PMF.bind_map, coVT_eq]
    refine congrArg _ (funext fun o₃ => ?_)
    show runG W r₀ a Gs s1 i ((linksA W cA r₀ a.side ⟨tr₁, L.recOf i r₁ sd₁⟩ 1 (d.copies.zip ts)
      o₃.2).bind _) (some (c, usedT, st), Tg) = _
    rw [runG_bind, hlk o₃.2, PMF.bind_map]
    rfl
  refine (congrArg _ (funext fun v => hstep v)).trans ?_
  rw [← PMF.bind_bind, ht]
  refine congrArg (fun p => PMF.bind p _) ?_
  exact (bind_enum (β := a.Hs.T.Coin) a.kT hP.kT fun κ =>
    lateTA W cA (fun _ => realTree W a.b₀ (L.encodeIndex i r₁) tr₁) (a.side.dressT (a.side.rvT κ) d.co)
      a.side.capT tr₁.root (L.recOf i r₁ sd₁) (L.encodeIndex i r₁) (a.side.st.stopT i r₁ sd₁)
      (a.side.st.T i r₁ sd₁ κ) T).symm

end OnBytes.LateWorld

#print axioms OnBytes.LateWorld.restA_good
