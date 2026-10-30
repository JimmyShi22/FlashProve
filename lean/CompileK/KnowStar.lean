-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/KnowStar.lean: what an accepting run of the compiled verifier of a slot says about the
extracted local transcript τ∗, and how the named witness extractor reads the oracles of τ∗.

This file is about soundness of an interactive oracle proof compiled with Merkle trees and
Fiat-Shamir queries: the step without probabilities, under the hypotheses of its statements, from an
accepting run of the compiled verifier to a transcript that the IOP verifier accepts.
τ∗ (`trStar`, Compile/Batch/Runs.lean): the local transcript with the oracles that the trace
determines under the roots of the argument string, its plain parts, and the chain's verifier
messages. `RunsIn tr c a` (Compile/Spec.lean): c, without coins, runs to a with all its queries and
answers taken from tr.

Main names, each under the hypotheses of its statement:
  Part 1
  `rtsPure_of_chainB`: the roots that the verifier's chain deals out to the rounds are those that
    `rtsPure` deals out without any query (CompileK/KnowExt.lean).
  `trStar_read`: the oracles of τ∗ are `readStar`: they do not depend on the verifier messages.
  `readStar_congr`: `readStar` depends on the trace only through what stands under the roots of the
    rounds.
  Part 2
  `star_of_accepted`: outside the hash events (`hM`, `hF`) and the protocol's state event (`hS`), if
    the compiled verifier of a slot accepts and all its queries are in the trace, then its chain
    yields verifier messages ρ and roots rts such that (1) the state function is 0 at the full τ∗
    and (2) the IOP verifier accepts τ∗ with the extracted external oracles. The laws of the state
    function are asked along the instances that the chain takes in, at the extracted external
    oracles only, and without a language: state 0 at the start (`hst1`); a prover message keeps 0
    (`hst2`).
  `rtsB_of_chainQB`, `readB_of_chainQB`: for a slot of Batch: what the named extractor reads
    (`rtsB`, `readB`) are the roots of the verifier's chain and the oracles of τ∗.
  A check: the conclusion of `Compile.Batch.mem_of_accepted` follows from `star_of_accepted`.

Why: `star_of_accepted` is the analogue of `Compile.Batch.mem_of_accepted`
(Compile/Batch/Sound.lean), which proves both facts on its way to a contradiction and exports
neither; the one-round lemma of Part 1 (`runsIn_chainB_cons_rts`) is the analogue of
`runsIn_chainB_cons_flags` (Compile/Batch/Runs.lean), which hides how the list of roots goes on.

Limits: this file says nothing about probabilities, and nothing about a witness: that is
CompileK/KnowSound.lean.

Terms: lean/GLOSSARY.md.
-/
import CompileK.KnowStarDefs

set_option autoImplicit false

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

/-! ## Part 1. The roots and the oracles of τ∗ -/

section Part1
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-- The chain, one round, with the list of roots: how `rtsPure` goes through the same round. -/
theorem runsIn_chainB_cons_rts {tr : Trace (spec lam K L)} {t : Tag} {cms : List (Dig lam)}
    {x : Option X} {salt : Bits} {rtreq : Dig lam} {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s}
    {w : WireRB lam K r a} {ws : RoundsQueryLayout lam K s A}
    {embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)} {i : ℕ} {ph ph' : Phase lam}
    {rts : List (Dig lam)} {pl : r.Plain} {pls : Plains s} {c : r.Chal} {ρ : Rho s}
    {rt : RtC lam × RtC lam} {RTs : RootsOfChain lam s}
    (h : RunsIn tr
      (recomputeChain (K := K) t cms x salt rtreq (r :: s) (a, A) (w, ws) embP i ph rts (pl, pls))
      (some ((c, ρ), (rt, RTs), ph'))) :
    ∃ (ph₁ : Phase lam) (rts' : List (Dig lam)),
      RunsIn tr
        (recomputeChain (K := K) t cms x salt rtreq s A ws (fun z => embP (.inr z)) (i + 1) ph₁ rts' pls)
        (some (ρ, RTs, ph')) ∧
      ∀ R : RootsOfChain lam s, rtsPure s A ws ph₁.k rts' = some R →
        rtsPure (r :: s) (a, A) (w, ws) ph.k rts = some (rt, R) := by
  -- one query, with the slot's component or with the shared one
  have one : ∀ (hd : Head lam X) (next : Bits → Phase lam) (root : Option (Dig lam))
        (rts' : List (Dig lam)) (α : PlainPart (shapeOf L t) (annOf L t)) (rt' : RtC lam × RtC lam),
      RunsIn tr ((askTypedOracle (L := L) (K := K) (OracleName.fb t)
          (⟨i, hd, root, α⟩ : FbIn lam L t)).bind fun ans =>
            (recomputeChain (K := K) t cms x salt rtreq s A ws (fun z => embP (.inr z)) (i + 1)
              (next (List.ofFn ans.2)) rts' pls).bind fun r' =>
                OComp.pure
                  (r'.map fun z =>
                    (((w.chal ans.1, z.1), (rt', z.2.1), z.2.2) :
                      Rho (r :: s) × RootsOfChain lam (r :: s) × Phase lam)))
        (some ((c, ρ), (rt, RTs), ph')) →
      ∃ ans : FsAns lam K,
        fbE t (⟨i, hd, root, α⟩ : FbIn lam L t) ans ∈ tr ∧ c = w.chal ans.1 ∧ rt = rt' ∧
        RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A ws (fun z => embP (.inr z)) (i + 1)
            (next (link ans)) rts' pls)
          (some (ρ, RTs, ph')) := by
    intro hd next root rts' α rt' h'
    obtain ⟨ans, ha, h2⟩ := (runsIn_bind_iff _ _ _).1 h'
    obtain ⟨r', hr', h3⟩ := (runsIn_bind_iff _ _ _).1 h2
    have h4 := runsIn_pure_iff.1 h3
    cases r' with
    | none => cases h4
    | some z =>
      obtain ⟨ρ', RTs', ph''⟩ := z
      have h5 : (((w.chal ans.1, ρ'), (rt', RTs'), ph'') :
            (r.Chal × Rho s) × ((RtC lam × RtC lam) × RootsOfChain lam s) × Phase lam) =
          ((c, ρ), (rt, RTs), ph') :=
        Option.some.inj h4
      simp only [Prod.mk.injEq] at h5
      obtain ⟨⟨h6, rfl⟩, ⟨h7, rfl⟩, rfl⟩ := h5
      exact ⟨ans, runsIn_ask_iff.1 ha, h6.symm, h7.symm, hr'⟩
  unfold recomputeChain at h
  cases hk : a.kind with
  | lo =>
    cases ph with
    | first =>
      simp only [hk, actOf] at h
      cases hrt : takeRt w.hasJ rts with
      | none => simp only [hrt] at h; cases runsIn_pure_iff.1 h
      | some z =>
        obtain ⟨root, rts'⟩ := z
        simp only [hrt] at h
        obtain ⟨ans, h1, h2, rfl, h4⟩ := one _ _ _ _ _ _ h
        exact ⟨_, rts', h4, fun R hR => by
          simp only [Phase.k] at hR ⊢
          simp [rtsPure, hk, hrt, hR]
          rfl⟩
    | loc ρ' =>
      simp only [hk, actOf] at h
      cases hrt : takeRt w.hasJ rts with
      | none => simp only [hrt] at h; cases runsIn_pure_iff.1 h
      | some z =>
        obtain ⟨root, rts'⟩ := z
        simp only [hrt] at h
        obtain ⟨ans, h1, h2, rfl, h4⟩ := one _ _ _ _ _ _ h
        exact ⟨_, rts', h4, fun R hR => by
          simp only [Phase.k] at hR ⊢
          simp [rtsPure, hk, hrt, hR]
          rfl⟩
    | shr ρ0 cv =>
      simp only [hk, actOf] at h
      cases hrt : takeRt w.hasJ rts with
      | none => simp only [hrt] at h; cases runsIn_pure_iff.1 h
      | some z =>
        obtain ⟨root, rts'⟩ := z
        simp only [hrt] at h
        obtain ⟨ans, h1, h2, rfl, h4⟩ := one _ (fun v => Phase.aft v cv) _ _ _ _ h
        exact ⟨_, rts', h4, fun R hR => by
          simp only [Phase.k] at hR ⊢
          simp [rtsPure, hk, hrt, hR]
          rfl⟩
    | aft ρ' cv =>
      simp only [hk, actOf] at h
      cases hrt : takeRt w.hasJ rts with
      | none => simp only [hrt] at h; cases runsIn_pure_iff.1 h
      | some z =>
        obtain ⟨root, rts'⟩ := z
        simp only [hrt] at h
        obtain ⟨ans, h1, h2, rfl, h4⟩ := one _ (fun v => Phase.aft v cv) _ _ _ _ h
        exact ⟨_, rts', h4, fun R hR => by
          simp only [Phase.k] at hR ⊢
          simp [rtsPure, hk, hrt, hR]
          rfl⟩
  | sh =>
    cases ph with
    | first => simp only [hk, actOf] at h; cases runsIn_pure_iff.1 h
    | aft ρ' cv => simp only [hk, actOf] at h; cases runsIn_pure_iff.1 h
    | shr ρ0 cv =>
      simp only [hk, actOf] at h
      cases hrt : takeRt w.has0 rts with
      | none => simp only [hrt] at h; cases runsIn_pure_iff.1 h
      | some z =>
        obtain ⟨root, rts'⟩ := z
        simp only [hrt] at h
        obtain ⟨ans, h1, h2, rfl, h4⟩ := one _ (fun v => Phase.shr v cv) _ _ _ _ h
        exact ⟨_, rts', h4, fun R hR => by
          simp only [Phase.k] at hR ⊢
          simp [rtsPure, hk, hrt, hR]
          rfl⟩
    | loc ρ' =>
      simp only [hk, actOf] at h
      cases hrt : takeRt w.hasJ rts with
      | none => simp only [hrt] at h; cases runsIn_pure_iff.1 h
      | some z =>
        obtain ⟨rtj, rts1⟩ := z
        simp only [hrt] at h
        cases hrt0 : takeRt w.has0 rts1 with
        | none => simp only [hrt0] at h; cases runsIn_pure_iff.1 h
        | some z0 =>
          obtain ⟨rt0, rts'⟩ := z0
          simp only [hrt0] at h
          rw [bind_eq] at h
          obtain ⟨cv, hc, h2⟩ := (runsIn_bind_iff _ _ _).1 h
          obtain ⟨ans, h1, h3, rfl, h4⟩ := one _ (fun v => Phase.shr v cv) _ _ _ _ h2
          exact ⟨_, rts', h4, fun R hR => by
            simp only [Phase.k] at hR ⊢
            simp [rtsPure, hk, hrt, hrt0, hR]
            rfl⟩

/-- The roots that the verifier's chain yields, round by round, are a function of the list of roots,
the kinds of the rounds, the flags of the wire and the kind of the phase at the start (`ph.k`): no
answer of the oracle enters. -/
theorem rtsPure_of_chainB {tr : Trace (spec lam K L)} {t : Tag} {cms : List (Dig lam)}
    {x : Option X} {salt : Bits} {rtreq : Dig lam} :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph ph' : Phase lam)
        (rts : List (Dig lam)) (pls : Plains s) (ρ : Rho s) (RTs : RootsOfChain lam s),
      RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A ws embP i ph rts pls) (some (ρ, RTs, ph')) →
      rtsPure s A ws ph.k rts = some RTs
  | [], _, _, _, _, _, _, _, _, _, (), _ => rfl
  | _ :: s, (_, A), (_, ws), _, i, _, ph', _, (_, pls), (_, ρ), (_, RTs), h => by
      obtain ⟨ph₁, rts', hr, hR⟩ := runsIn_chainB_cons_rts h
      exact hR RTs (rtsPure_of_chainB s A ws _ (i + 1) ph₁ ph' rts' pls ρ RTs hr)

/-- The oracles of τ∗ do not depend on its verifier messages. -/
theorem trStar_read (tr : Trace (spec lam K L)) :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A)
        (prjS : (p : OPos s) → Body L → Option (OSym s p)) (rts : RootsOfChain lam s)
        (pls : Plains s) (ρ : Rho s),
      (trStar tr s A ws prjS rts pls ρ).read = readStar tr s A ws prjS rts pls
  | [], _, _, _, _, _, _ => funext fun p => nomatch p
  | _ :: s, (_, A), (_, ws), prjS, (_, rts), (_, pls), (_, ρ) => funext fun p =>
      match p with
      | .inl _ => rfl
      | .inr p => congrFun (trStar_read tr s A ws (fun p => prjS (.inr p)) rts pls ρ) p

/-- What is read depends on the trace only through what stands under the roots of the rounds. -/
theorem readStar_congr {tr tr' : Trace (spec lam K L)} :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A)
        (prjS : (p : OPos s) → Body L → Option (OSym s p)) (rts : RootsOfChain lam s) (pls : Plains s),
      (∀ c ∈ RootsOfChain.list s rts, ∀ d j, extLeaf tr d c j = extLeaf tr' d c j) →
      readStar tr s A ws prjS rts pls = readStar tr' s A ws prjS rts pls
  | [], _, _, _, _, _, _ => funext fun p => nomatch p
  | _ :: s, (_, A), (w, ws), prjS, (rt, rts), (pl, pls), h => funext fun p =>
      match p with
      | .inl p => by
          show Round.rd _ (msgStar tr w (fun p => prjS (.inl p)) rt pl).1 p =
            Round.rd _ (msgStar tr' w (fun p => prjS (.inl p)) rt pl).1 p
          rw [msgStar_congr w (fun p => prjS (.inl p)) pl fun c hc => h c (by
            rcases hc with hc | hc <;> simp [RootsOfChain.list, hc])]
      | .inr p => congrFun (readStar_congr s A ws (fun p => prjS (.inr p)) rts pls fun c hc => h c (by
          simp only [RootsOfChain.list, List.mem_append]; exact Or.inr hc)) p

end Part1

/-! ## Part 2. The invariant, exported -/

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {W : QueryLayout lam L}

/-- Under the hypotheses below: state 0 at the full τ∗, and the IOP verifier accepts τ∗. inst i is
the instance that the chain has taken in with the query of round i (`hx`; `instX`,
Compile/Batch/LateX.lean). -/
theorem star_of_accepted (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam W.K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (hOK : wq.OKG) (hloc : Q.loc.IsLocal) (hco : Q.ann.Coherent)
    (State : E.Str → Y → PTr Q.loc.shape → Bool)
    (prjS : (p : OPos Q.loc.shape) → Body L → Option (OSym Q.loc.shape p))
    (hprjS : ∀ p a, prjS p (embS p a) = some a)
    (prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.loc.shape Q.ann))
    (hprjP : ∀ z, prjP (embP z) = some z) (xout : Option X → Option Y)
    (extY : Tc W → List (Dig lam) → E.Str) (ε : Err Q.loc.shape) {tr : Tc W} (hM : ¬ EM tr)
    (hF : ¬ EF tr) (hS : ¬ StepEvent (laneOf W t Q wq.sh prjS prjP ε State xout extY).step tr)
    (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (inst : ℕ → Y)
    (hx : ∀ i, xout (instX L (xin x) i) = some (inst i))
    (hlate : ∀ n, L.late = some n → xin x ≠ none → 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann)
    (hst1 : State (extY tr cms) (inst 0) (PTr.empty Q.loc.shape) = false)
    (hst2 : ∀ (τ : AtP Q.loc.shape) (m : τ.round.Msg),
      State (extY tr cms) (inst (τ.idx - 1)) (.atP τ) = false →
      State (extY tr cms) (inst τ.idx) (.atV (τ.snoc m)) = false)
    (hrun : RunsIn tr (verifyB t Q wq embS embP xin embE W.depthReq cms x π) true)
    (hstab : ∀ pre (q : FbIn lam L t) (a : FsAns lam W.K) post, tr = pre ++ fbE t q a :: post →
      (∀ c ∈ cms.take 2, (evM lam W.K L).OccursIn (pre ++ [fbE t q a]) c) →
      extY pre cms = extY tr cms)
    (hagree : ∀ p a sl,
      extLeaf tr wq.ext.depth (cms.getD (wq.ext.which p) default) (wq.ext.leaf p) =
        some ⟨embE a, sl⟩ →
      E.rd (extY tr cms) p = a) :
    ∃ (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam),
      RunsIn tr (recomputeChainOfProof t Q wq embP xin cms x π) (some (ρ, rts, ph)) ∧
      State (extY tr cms) (inst (Q.loc.shape.length - 1))
          (.full (trStar tr Q.loc.shape Q.ann wq.sh prjS rts π.plains ρ)) = false ∧
      Q.loc.accept x (extY tr cms) (trStar tr Q.loc.shape Q.ann wq.sh prjS rts π.plains ρ) =
        true := by
  letI := wq.decO
  letI := wq.ext.dec
  unfold verifyB recomputeChainOfProof afterB at hrun
  obtain ⟨r, hr, h2⟩ := (runsIn_bind_iff _ _ _).1 hrun
  cases r with
  | none => cases runsIn_pure_iff.1 h2
  | some z =>
    obtain ⟨ρ, rts, ph⟩ := z
    dsimp only at h2
    split at h2
    · rename_i a b ha hb
      split at h2
      · rename_i hcond
        rw [bind_eq] at h2
        obtain ⟨ok, hok, h3⟩ := (runsIn_bind_iff _ _ _).1 h2
        have hkey : (∀ c, ph.slotVal = some c →
              RunsIn tr (reqCheck (K := W.K) (L := L) W.depthReq π.rtreq π.slot π.path c) true) ∧
            ok = true ∧
            Q.loc.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
                (mkTr Q.loc.shape Q.ann wq.sh rts π.plains ρ π.opens) = true := by
          cases hsv : ph.slotVal with
          | none =>
            simp only [hsv] at h3
            obtain ⟨y, hy, h4⟩ := (runsIn_bind_iff _ _ _).1 h3
            have h5 := Bool.and_eq_true_iff.1 (runsIn_pure_iff.1 h4)
            exact ⟨fun c hc => (by cases hc), (Bool.and_eq_true_iff.1 h5.1).1, h5.2⟩
          | some c =>
            simp only [hsv] at h3
            rw [bind_eq] at h3
            obtain ⟨y, hy, h4⟩ := (runsIn_bind_iff _ _ _).1 h3
            have h5 := Bool.and_eq_true_iff.1 (runsIn_pure_iff.1 h4)
            obtain ⟨h6, rfl⟩ := Bool.and_eq_true_iff.1 h5.1
            exact ⟨fun c' hc' => (by cases hc'; exact hy), h6, h5.2⟩
        obtain ⟨hreq, rfl, hacc⟩ := hkey
        -- the slot value stands under the request root
        have hfin : ∀ c,
            ph.slotVal = some c → extReq tr W.depthReq π.rtreq π.slot = some (List.ofFn c) :=
          fun c hc => (extReq_of_check hM (hreq c hc)).2
        -- the state stays 0 along the chain
        let C : Ctx W := ⟨tr, t, cms, xin x, π.salt, π.rtreq, π.slot⟩
        have hbad : State (extY tr cms) (inst (Q.loc.shape.length - 1))
              (.full (trStar tr Q.loc.shape Q.ann wq.sh prjS rts π.plains ρ)) = false :=
          stays0 C hM hF Q.loc.shape Q.ann wq.sh prjS prjP embP
            hprjP (swSt (State (extY tr cms)) inst)
            (fun τ m h => by
              show State (extY tr cms) (inst (τ.snoc m).idx) _ = false
              rw [AtP.idx_snoc]
              exact hst2 τ m h) 0 .first ph π.roots π.plains ρ rts []
            hr ⟨rfl, rfl⟩
            (fun n hl hxn _ => ⟨(hlate n hl hxn).1, Or.inl ⟨rfl, rfl⟩, (hlate n hl hxn).2⟩) hfin
            (fun pre q a post rest cur τ htr hnew hours hlt hτ hl => by
              by_contra hn
              have hidx : τ.idx = rest.length := idx_trOf pre _ _ _ _ _ rest cur τ hτ
              have hn' : State (extY tr cms) (inst rest.length) (τ.snoc (chalAt wq.sh τ a.1)) =
                  true := by
                rw [swSt_snoc, hidx] at hn
                simpa using hn
              have hl' : State (extY tr cms) (inst rest.length) (.atV τ) = false := by
                rw [← hidx]; exact hl
              have hy : extY pre cms = extY tr cms := hstab pre q a post htr (ours_cms C a hours)
              have hfl : (laneOf W t Q wq.sh prjS prjP ε State xout extY).flips
                  pre cms (lastX C.xo rest cur) rest cur a :=
                ⟨State (extY tr cms) (inst rest.length), τ, by
                  show (xout (lastX ((xin x).map L.early) rest cur)).map (State (extY pre cms)) = _
                  rw [lastX_of_lateIs (xin x) rest cur hlt, hx, hy]; rfl, hτ, hl', hn'⟩
              rw [List.nil_append] at hours
              rcases hours with ⟨h1 | h1, rfl⟩ | ⟨slot, sh, c, sd, h1, h7, h8, h9, h10⟩
              · exact hS ⟨pre, fbE t q a, post, htr, hnew, q, a, _, rfl, h1, hfl⟩
              · exact hS ⟨pre, fbE t q a, post, htr, hnew, q, a, _, rfl, h1, hfl⟩
              · obtain rfl : rest = (slotTr sd sh q).1 := (congrArg Prod.fst h10).symm
                obtain rfl : cur = (slotTr sd sh q).2 := (congrArg Prod.snd h10).symm
                have e3 : sd.x = C.xo := h9
                refine hS ⟨pre, fbE t q a, post, htr, hnew, q, a, _, rfl, h1,
                    π.slot % 2 ^ W.depthReq, Nat.mod_lt _ (Nat.pow_pos (by decide)), π.rtreq, c, sd,
                    digOf_ofFn _, by rw [extReq_mod]; exact h7, h8, ?_⟩
                rw [e3]
                exact hfl)
            (by rw [swSt_empty]; exact hst1)
        have hall : ∀ c ∈ a ++ b,
            c.wellFormed = true ∧ RunsIn tr (runCheck (K := W.K) c) true := fun c hc =>
          ⟨(Bool.and_eq_true_iff.1 (List.all_eq_true.1 hcond.2 c hc)).1,
            runsIn_runCheck_of_runChecks _ hok c hc⟩
        -- the oracle-level verifier accepts
        have heq := hloc x (wq.ext.build fun p => (π.ext p).map Opening.sym) (extY tr cms)
          (mkTr Q.loc.shape Q.ann wq.sh rts π.plains ρ π.opens)
          (trStar tr Q.loc.shape Q.ann wq.sh prjS rts π.plains ρ)
          (by rw [mkTr_rho, trStar_rho]) (by rw [mkTr_plains, trStar_plains tr _ _ hco])
          (fun p hp => by
            rw [mkTr_rho] at hp
            obtain ⟨op, hop, hmem⟩ := mem_checksExt
              wq.ext embE cms _ π.ext wq.ext.all b hb p (hOK.ext.complete p) (decide_eq_true hp)
            obtain ⟨hwf, hrc⟩ := hall _ (List.mem_append_right _ hmem)
            rw [hOK.ext.build_rd _ p op.sym (by rw [hop]; rfl)]
            exact (hagree p op.sym op.salt (extLeaf_of_check _ hM hwf hrc)).symm)
          (fun p hp => by
            rw [mkTr_rho, mkTr_plains] at hp
            exact read_mkTr_eq hM Q.loc.shape Q.ann hco wq.sh hOK.sh embS prjS
              hprjS rts _ π.opens a ha
              (fun c hc => hall c (List.mem_append_left _ hc)) π.plains ρ p (decide_eq_true hp))
        exact ⟨ρ, rts, ph, hr, hbad, heq ▸ hacc⟩
      · cases runsIn_pure_iff.1 h2
    · cases runsIn_pure_iff.1 h2

/-- Under `h`: the roots that the named extractor reads off the argument string of a slot of Batch
are those that the verifier's chain yields. -/
theorem rtsB_of_chainQB {tr : Tc W}
    {embP : PlainPart L.onlineBatch.loc.shape L.onlineBatch.ann → PlainPart (shapeOf L Tag.onl) (annOf L Tag.onl)}
    {xin : X → Option X} {cms : List (Dig lam)} {x : X} {π : OneProtocolProof lam L.onlineBatch}
    {ρ : Rho L.onlineBatch.loc.shape} {rts : RootsOfChain lam L.onlineBatch.loc.shape} {ph : Phase lam}
    (h : RunsIn tr (recomputeChainOfProof Tag.onl L.onlineBatch W.B embP xin cms x π) (some (ρ, rts, ph))) :
    rtsB W π = rts := by
  unfold rtsB
  rw [show rtsPure L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh .first π.roots = some rts from
    rtsPure_of_chainB L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh embP 0 .first ph π.roots π.plains ρ rts h]
  rfl

/-- Under `h`: what the named extractor reads are the oracles of τ∗. -/
theorem readB_of_chainQB {tr tr' : Tc W}
    {embP : PlainPart L.onlineBatch.loc.shape L.onlineBatch.ann → PlainPart (shapeOf L Tag.onl) (annOf L Tag.onl)}
    {xin : X → Option X} {cms : List (Dig lam)} {x : X} {π : OneProtocolProof lam L.onlineBatch}
    {ρ : Rho L.onlineBatch.loc.shape} {rts : RootsOfChain lam L.onlineBatch.loc.shape} {ph : Phase lam}
    (h : RunsIn tr' (recomputeChainOfProof Tag.onl L.onlineBatch W.B embP xin cms x π) (some (ρ, rts, ph))) :
    readB W tr π =
      (trStar tr L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh (prjSym Tag.onl) rts π.plains ρ).read := by
  unfold readB
  rw [rtsB_of_chainQB h, trStar_read]

/-- A check: the conclusion of `Compile.Batch.mem_of_accepted`, from its hypotheses, by
`star_of_accepted`. -/
example (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam W.K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (hOK : wq.OKG) (hloc : Q.loc.IsLocal) (hco : Q.ann.Coherent)
    {Lg : Y → E.Str → Prop} (State : E.Str → Y → PTr Q.loc.shape → Bool)
    (prjS : (p : OPos Q.loc.shape) → Body L → Option (OSym Q.loc.shape p))
    (hprjS : ∀ p a, prjS p (embS p a) = some a)
    (prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.loc.shape Q.ann))
    (hprjP : ∀ z, prjP (embP z) = some z) (xout : Option X → Option Y)
    (extY : Tc W → List (Dig lam) → E.Str) (ε : Err Q.loc.shape) {tr : Tc W} (hM : ¬ EM tr)
    (hF : ¬ EF tr) (hS : ¬ StepEvent (laneOf W t Q wq.sh prjS prjP ε State xout extY).step tr)
    (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (inst : ℕ → Y)
    (hx : ∀ i, xout (instX L (xin x) i) = some (inst i))
    (hlate : ∀ n, L.late = some n → xin x ≠ none → 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann)
    (hst1 : ∀ y, ¬ Lg x y → State y (inst 0) (PTr.empty Q.loc.shape) = false)
    (hst2 : ∀ y (τ : AtP Q.loc.shape) (m : τ.round.Msg), ¬ Lg x y →
      State y (inst (τ.idx - 1)) (.atP τ) = false → State y (inst τ.idx) (.atV (τ.snoc m)) = false)
    (hst3 : ∀ y τ, ¬ Lg x y → State y (inst (Q.loc.shape.length - 1)) (.full τ) = false →
      Q.loc.accept x y τ = false)
    (hrun : RunsIn tr (verifyB t Q wq embS embP xin embE W.depthReq cms x π) true)
    (hstab : ∀ pre (q : FbIn lam L t) (a : FsAns lam W.K) post, tr = pre ++ fbE t q a :: post →
      (∀ c ∈ cms.take 2, (evM lam W.K L).OccursIn (pre ++ [fbE t q a]) c) →
      extY pre cms = extY tr cms)
    (hagree : ∀ p a sl,
      extLeaf tr wq.ext.depth (cms.getD (wq.ext.which p) default) (wq.ext.leaf p) =
        some ⟨embE a, sl⟩ →
      E.rd (extY tr cms) p = a) : Lg x (extY tr cms) := by
  by_contra hL
  obtain ⟨ρ, rts, ph, -, h0, hacc⟩ :=
    star_of_accepted t Q wq embS embP xin embE hOK hloc hco State prjS hprjS prjP hprjP xout extY ε
      hM hF hS cms x π inst hx hlate (hst1 _ hL) (fun τ m => hst2 _ τ m hL) hrun hstab hagree
  rw [hst3 _ _ hL h0] at hacc
  cases hacc

end Compile.Batch
