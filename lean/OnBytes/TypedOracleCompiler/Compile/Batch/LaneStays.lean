-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/LaneStays.lean: outside the two hash events and a lane's step event, the
lane's state is 0 at the end of a chain that runs in the trace. No decision of a local verifier is
used.

This file belongs to the second form of the verifier's side of the library's compiler under
OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`). What that form is, and in which five respects it differs
from the library's own, is told in the head of OnBytes/TypedOracleCompiler/Iop/BatchWire.lean. The folder has the
verifier's side alone: no prover and no completeness. Nothing here is on hiding. The library has no
file of this name.

Why. `mem_of_accepted` (Sound.lean) goes from an accepting run to membership in a language, and it
needs `IsLocal` to pass from the string that the openings build to the string that the trace
determines. A state function that hangs on the whole external string (for example: at the seed s two
members of a list in the string y have the same answers) is decided by no local verifier, so such an
event cannot be had through that lemma. But the first half of its proof needs no decision of a
verifier at all. It is a lemma of its own here.

  `chain_stays0`
      The first half of `mem_of_accepted_ours` (SoundOurs.lean): no accept, no `IsLocal`, no
      openings, no language. Outside `EM`, `EF` and the lane's step event: if the chain of a
      protocol (`recomputeChain`: its Fiat-Shamir queries alone) runs in the trace and yields the verifier
      messages ρ, and the state function is 0 at the start and no prover message raises it, then the
      state is 0 at the full transcript (the oracles that the trace determines under the roots; the
      plain parts; ρ), at the string that the whole trace determines under the external roots. The
      hypotheses `hx` and `hlate` on an instance that enters the chain late are those of
      `mem_of_accepted`. One more, `hfin`, which the whole lemma derives from the check in the
      request tree, is asked here: if the chain has joined, its slot value stands under the request
      root, as the beginning of a leaf's input. For a chain of local rounds alone it is empty (not
      proved in this folder).
  `no_coll`
      The use: a state function that looks at the verifier messages alone, `bad y ρ`, and is 0
      before the last of them: then `bad (extY tr cms) ρ = false`.

The stability of `extY` is asked at the queries of the verifier's own chain alone (SoundOurs.lean).

Limits. Not said: any protocol, any `bad`, any `extY`; that the step event is rare (`laneOf_ok`,
from the joint law; for `bad` it is a count of verifier messages); a statement with two lanes
(TwoLanes.lean).

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.SoundOurs

noncomputable section

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol
open Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L}

/-- The state stays 0 along a chain that runs in the trace: no decision, no locality, no opening. -/
theorem chain_stays0 (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam W.K Q)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (State : E.Str → Y → PTr Q.loc.shape → Bool)
    (prjS : (p : OPos Q.loc.shape) → Body L → Option (OSym Q.loc.shape p))
    (prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.loc.shape Q.ann))
    (hprjP : ∀ z, prjP (embP z) = some z) (xout : Option X → Option Y)
    (extY : Tc W → List (Dig lam) → E.Str) (ε : Err Q.loc.shape) {tr : Tc W} (hM : ¬ EM tr)
    (hF : ¬ EF tr) (hS : ¬ StepEvent (laneOf W t Q wq.sh prjS prjP ε State xout extY).step tr)
    (cms : List (Dig lam)) (x : Y) (salt : Bits) (rtreq : Dig lam) (jS : ℕ)
    (roots : List (Dig lam)) (plains : Plains Q.loc.shape) (inst : ℕ → Y)
    (hx : ∀ i, xout (instX L (xin x) i) = some (inst i))
    (hlate : ∀ n, L.late = some n → xin x ≠ none → 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann)
    (hst1 : State (extY tr cms) (inst 0) (PTr.empty Q.loc.shape) = false)
    (hst2 : ∀ (τ : AtP Q.loc.shape) (m : τ.round.Msg),
      State (extY tr cms) (inst (τ.idx - 1)) (.atP τ) = false →
      State (extY tr cms) (inst τ.idx) (.atV (τ.snoc m)) = false)
    {ρ : Rho Q.loc.shape} {rts : RootsOfChain lam Q.loc.shape} {ph : Phase lam}
    (hr : RunsIn tr (recomputeChain (K := W.K) t cms (xin x) salt rtreq Q.loc.shape Q.ann wq.sh embP 0
        .first roots plains)
      (some (ρ, rts, ph)))
    (hfin : ∀ c, ph.slotVal = some c → extReq tr (W.dReq t) rtreq jS = some (List.ofFn c))
    (hstab : ∀ pre (q : FbIn lam L t) (a : FsAns lam W.K) post l cur,
        tr = pre ++ fbE t q a :: post →
      Ours (⟨tr, t, cms, xin x, salt, rtreq, jS⟩ : Ctx W) pre q l cur →
      extY pre cms = extY tr cms) :
    State (extY tr cms) (inst (Q.loc.shape.length - 1))
      (.full (trStar tr Q.loc.shape Q.ann wq.sh prjS rts plains ρ)) = false := by
  let C : Ctx W := ⟨tr, t, cms, xin x, salt, rtreq, jS⟩
  have hbad : State (extY tr cms) (inst (Q.loc.shape.length - 1))
        (.full (trStar tr Q.loc.shape Q.ann wq.sh prjS rts plains ρ)) = false :=
    stays0 C hM hF Q.loc.shape Q.ann wq.sh prjS prjP embP
      hprjP (swSt (State (extY tr cms)) inst)
      (fun τ m h => by
        show State (extY tr cms) (inst (τ.snoc m).idx) _ = false
        rw [AtP.idx_snoc]
        exact hst2 τ m h) 0 .first ph roots plains ρ rts []
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
        have hy : extY pre cms = extY tr cms := hstab pre q a post _ cur htr hours
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
              jS % 2 ^ (W.dReq t), Nat.mod_lt _ (Nat.pow_pos (by decide)), rtreq, c, sd,
              digOf_ofFn _, (extReq_mod pre (W.dReq t) _ _).trans h7, h8, ?_⟩
          rw [e3]
          exact hfl)
      (by rw [swSt_empty]; exact hst1)
  exact hbad

/-- a state function that looks at the verifier messages alone, and only when all are there -/
def stBad {s : Shape} {Str Y : Type} (bad : Str → Rho s → Bool) : Str → Y → PTr s → Bool :=
  fun y _ τ => match τ with
    | .full τ => bad y τ.rho
    | _ => false

theorem stBad_empty {Str Y : Type} : ∀ {s : Shape} (bad : Str → Rho s → Bool) (y : Str)
    (x : Y), s ≠ [] →
    stBad bad y x (PTr.empty s) = false
  | [], _, _, _, h => absurd rfl h
  | _ :: _, _, _, _, _ => rfl

/-- Outside `EM`, `EF` and the step event of the lane whose state is `bad y ρ`: if the chain runs in
the trace and yields ρ, then bad (the string that the whole trace determines under the external
roots) ρ = false. -/
theorem no_coll (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (hne : Q.loc.shape ≠ [])
    (wq : ProtocolQueryLayout lam W.K Q)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (bad : E.Str → Rho Q.loc.shape → Bool)
    (prjS : (p : OPos Q.loc.shape) → Body L → Option (OSym Q.loc.shape p))
    (prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.loc.shape Q.ann))
    (hprjP : ∀ z, prjP (embP z) = some z) (xout : Option X → Option Y)
    (extY : Tc W → List (Dig lam) → E.Str) (ε : Err Q.loc.shape) {tr : Tc W} (hM : ¬ EM tr)
    (hF : ¬ EF tr) (hS : ¬ StepEvent (laneOf W t Q wq.sh prjS prjP ε (stBad bad) xout extY).step tr)
    (cms : List (Dig lam)) (x : Y) (salt : Bits) (rtreq : Dig lam) (jS : ℕ)
    (roots : List (Dig lam)) (plains : Plains Q.loc.shape) (inst : ℕ → Y)
    (hx : ∀ i, xout (instX L (xin x) i) = some (inst i))
    (hlate : ∀ n, L.late = some n → xin x ≠ none → 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann)
    {ρ : Rho Q.loc.shape} {rts : RootsOfChain lam Q.loc.shape} {ph : Phase lam}
    (hr : RunsIn tr (recomputeChain (K := W.K) t cms (xin x) salt rtreq Q.loc.shape Q.ann wq.sh embP 0
        .first roots plains)
      (some (ρ, rts, ph)))
    (hfin : ∀ c, ph.slotVal = some c → extReq tr (W.dReq t) rtreq jS = some (List.ofFn c))
    (hstab : ∀ pre (q : FbIn lam L t) (a : FsAns lam W.K) post l cur,
        tr = pre ++ fbE t q a :: post →
      Ours (⟨tr, t, cms, xin x, salt, rtreq, jS⟩ : Ctx W) pre q l cur →
      extY pre cms = extY tr cms) :
    bad (extY tr cms) ρ = false := by
  have h := chain_stays0 t Q wq embP xin (stBad bad) prjS prjP hprjP xout extY ε hM hF hS cms
      x salt rtreq jS
    roots plains inst hx hlate (stBad_empty bad _ _ hne) (fun _ _ _ => rfl) hr hfin hstab
  have h' : bad (extY tr cms) (trStar tr Q.loc.shape Q.ann wq.sh prjS rts plains ρ).rho = false := h
  rwa [trStar_rho] at h'

end TypedOracleCompiler.Compile.Batch
