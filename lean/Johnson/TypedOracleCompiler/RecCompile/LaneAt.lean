-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/LaneAt.lean: one protocol's clause of soundness, for a lane whose state is
any function of the trace so far, the first query's list and the request.

`laneOf` (OnBytes/TypedOracleCompiler/Compile/Batch/Sound.lean) makes a lane from a state function, a reading of the
external string off the trace and a reading of the instance off the request. Here the lane's state
is a free function `st`. So a lane may take a part of its instance from the trace: for a table with
a record, the seed that the root's own queries have given.

Main names:
  `laneAt`: the lane.
  `laneAt_ok`: its laws, from the joint law at every trace and list.
  `mem_of_accepted_at`: outside E_M, E_F and the lane's event: an accepted proof string has its
    instance in the language with the string y. Asked, in the place of the two readings' laws: at
    each query of our own chain, `st` of the trace before it is the state function that F gives at
    the number of the chain's earlier records (`hstab`).

The proof of `mem_of_accepted_at` is the text of `mem_of_accepted_ours`
(OnBytes/TypedOracleCompiler/Compile/Batch/SoundOurs.lean), copied by a program, with F in the place of the state
function at the two readings.

Limits: soundness alone; typed oracles.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.SoundOurs

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L}

/-- A lane whose state is any function of the trace so far, the list and the request. -/
def laneAt (W : QueryLayout lam L) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (ws : RoundsQueryLayout lam W.K Q.loc.shape Q.ann)
    (prjS : (p : OPos Q.loc.shape) → Body L → Option (OSym Q.loc.shape p))
    (prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.loc.shape Q.ann)) (ε : Err Q.loc.shape)
    (st : Tc W → List (Dig lam) → Option X → Option (PTr Q.loc.shape → Bool)) : Lane W where
  t := t
  s := Q.loc.shape
  A := Q.ann
  ws := ws
  prjS := prjS
  prjP := prjP
  ε := ε
  state := st

/-- The lane's laws, from the laws of the wires and the joint law at every trace and list. -/
theorem laneAt_ok {t : Tag} {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}
    {ws : RoundsQueryLayout lam W.K Q.loc.shape Q.ann}
    {prjS : (p : OPos Q.loc.shape) → Body L → Option (OSym Q.loc.shape p)}
    {prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.loc.shape Q.ann)} {ε : Err Q.loc.shape}
    {st : Tc W → List (Dig lam) → Option X → Option (PTr Q.loc.shape → Bool)} {N : ℕ}
    (hws : RoundsQueryLayout.OKG Q.loc.shape Q.ann ws)
    (hj : ∀ pre cms (xs : Fin N → Option (Option X)),
      JointLaw N Q.loc.shape Q.ann ε fun j => (xs j).bind (st pre cms)) :
    (laneAt W t Q ws prjS prjP ε st).OK N :=
  ⟨hws, hj⟩

/-- Outside E_M, E_F and the lane's event, a proof string that the lax verifier accepts (hrun) has
its instance in the language with the string y, if `st` is stable along our own chain (`hstab`).
Further premises: the wire's laws (hOK); the verifier is local (hloc) and the annotation coherent
(hco); the two projections read back what is written (hprjS, hprjP); a late round stands behind
local rounds alone (hlate); F is a state function for the language at x and y (hst1 to hst3); y
agrees with the leaves that the trace fixes (hagree). -/
theorem mem_of_accepted_at (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam W.K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (hOK : wq.OKG) (hloc : Q.loc.IsLocal) (hco : Q.ann.Coherent)
    {Lg : Y → E.Str → Prop}
    (st : Tc W → List (Dig lam) → Option X → Option (PTr Q.loc.shape → Bool))
    (prjS : (p : OPos Q.loc.shape) → Body L → Option (OSym Q.loc.shape p))
    (hprjS : ∀ p a, prjS p (embS p a) = some a)
    (prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.loc.shape Q.ann))
    (hprjP : ∀ z, prjP (embP z) = some z)
    (ε : Err Q.loc.shape) {tr : Tc W} (hM : ¬ EM tr)
    (hF : ¬ EF tr) (hS : ¬ StepEvent (laneAt W t Q wq.sh prjS prjP ε st).step tr)
    (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (y : E.Str)
    (F : ℕ → PTr Q.loc.shape → Bool)
    (hlate : ∀ n, L.late = some n → xin x ≠ none → 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann)
    (hst1 : ¬ Lg x y → F 0 (PTr.empty Q.loc.shape) = false)
    (hst2 : ∀ (τ : AtP Q.loc.shape) (m : τ.round.Msg), ¬ Lg x y →
      F (τ.idx - 1) (.atP τ) = false → F τ.idx (.atV (τ.snoc m)) = false)
    (hst3 : ∀ τ, ¬ Lg x y → F (Q.loc.shape.length - 1) (.full τ) = false →
      Q.loc.accept x y τ = false)
    (hrun : RunsIn tr (verifyB t Q wq embS embP xin embE (W.dReq t) cms x π) true)
    (hstab : ∀ pre (q : FbIn lam L t) (a : FsAns lam W.K) post l cur,
        tr = pre ++ fbE t q a :: post →
      Ours (⟨tr, t, cms, xin x, π.salt, π.rtreq, π.slot⟩ : Ctx W) pre q l cur →
      st pre cms (instX L (xin x) l.length) = some (F l.length))
    (hagree : ∀ p a sl,
      extLeaf tr wq.ext.depth (cms.getD (wq.ext.which p) default) (wq.ext.leaf p) =
        some ⟨embE a, sl⟩ →
      E.rd y p = a) : Lg x y := by
  by_contra hL
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
              RunsIn tr (reqCheck (K := W.K) (L := L) (W.dReq t) π.rtreq π.slot π.path c π.rsalt)
                  true) ∧
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
            ph.slotVal = some c → extReq tr (W.dReq t) π.rtreq π.slot = some (List.ofFn c) :=
          fun c hc => (extReq_of_check hM (hreq c hc)).2
        -- the state stays 0 along the chain
        let C : Ctx W := ⟨tr, t, cms, xin x, π.salt, π.rtreq, π.slot⟩
        have hbad : F (Q.loc.shape.length - 1)
              (.full (trStar tr Q.loc.shape Q.ann wq.sh prjS rts π.plains ρ)) = false :=
          stays0 C hM hF Q.loc.shape Q.ann wq.sh prjS prjP embP
            hprjP (swSt F id)
            (fun τ m h => by
              show F (τ.snoc m).idx _ = false
              rw [AtP.idx_snoc]
              exact hst2 τ m hL h) 0 .first ph π.roots π.plains ρ rts []
            hr ⟨rfl, rfl⟩
            (fun n hl hxn _ => ⟨(hlate n hl hxn).1, Or.inl ⟨rfl, rfl⟩, (hlate n hl hxn).2⟩) hfin
            (fun pre q a post rest cur τ htr hnew hours hlt hτ hl => by
              by_contra hn
              have hidx : τ.idx = rest.length := idx_trOf pre _ _ _ _ _ rest cur τ hτ
              have hn' : F rest.length (τ.snoc (chalAt wq.sh τ a.1)) =
                  true := by
                rw [swSt_snoc, hidx] at hn
                simpa using hn
              have hl' : F rest.length (.atV τ) = false := by
                rw [← hidx]; exact hl
              have hy := hstab pre q a post _ cur htr hours
              have hfl : (laneAt W t Q wq.sh prjS prjP ε st).flips
                  pre cms (lastX C.xo rest cur) rest cur a :=
                ⟨F rest.length, τ, by
                  show st pre cms (lastX ((xin x).map L.early) rest cur) = _
                  rw [lastX_of_lateIs (xin x) rest cur hlt]
                  simpa using hy, hτ, hl', hn'⟩
              rw [List.nil_append] at hours
              rcases hours with ⟨h1 | h1, rfl⟩ | ⟨slot, sh, c, sd, h1, h7, h8, h9, h10⟩
              · exact hS ⟨pre, fbE t q a, post, htr, hnew, q, a, _, rfl, h1, hfl⟩
              · exact hS ⟨pre, fbE t q a, post, htr, hnew, q, a, _, rfl, h1, hfl⟩
              · obtain rfl : rest = (slotTr sd sh q).1 := (congrArg Prod.fst h10).symm
                obtain rfl : cur = (slotTr sd sh q).2 := (congrArg Prod.snd h10).symm
                have e3 : sd.x = C.xo := h9
                refine hS ⟨pre, fbE t q a, post, htr, hnew, q, a, _, rfl, h1,
                    π.slot % 2 ^ (W.dReq t), Nat.mod_lt _ (Nat.pow_pos (by decide)), π.rtreq, c, sd,
                    digOf_ofFn _, (extReq_mod pre (W.dReq t) _ _).trans h7, h8, ?_⟩
                rw [e3]
                exact hfl)
            (by rw [swSt_empty]; exact hst1 hL)
        have hall : ∀ c ∈ a ++ b,
            c.wellFormed = true ∧ RunsIn tr (runCheck (K := W.K) c) true := fun c hc =>
          ⟨(Bool.and_eq_true_iff.1 (List.all_eq_true.1 hcond.2 c hc)).1,
            runsIn_runCheck_of_runChecks _ hok c hc⟩
        -- the oracle-level verifier accepts
        have heq := hloc x (wq.ext.build fun p => (π.ext p).map Opening.sym) y
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
        rw [heq, hst3 _ hL hbad] at hacc
        cases hacc
      · cases runsIn_pure_iff.1 h2
    · cases runsIn_pure_iff.1 h2

end TypedOracleCompiler.Compile.Batch
