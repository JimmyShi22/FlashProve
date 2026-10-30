-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/SoundOurs.lean: `mem_of_accepted` with its hypothesis of stability
narrowed to what its proof uses.

This file belongs to the second form of the verifier's side of the library's compiler under
OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`). What that form is, and in which five respects it differs
from the library's own, is told in the head of OnBytes/TypedOracleCompiler/Iop/BatchWire.lean. The folder has the
verifier's side alone: no prover and no completeness. Nothing here is on hiding. The library has no
file of this name.

Why. `mem_of_accepted` (Sound.lean) asks that the reading of the external string be stable at every
Fiat-Shamir query of the tag such that the external roots occur in the prefix with that query. A
Merkle answer is an occurrence: so once the tree is hashed the hypothesis speaks of every later
query at the tag, those of other chains under other roots among them. For a string under a root `EM`
gives that. For a value that is read off a chain apart (SeedOff.lean) it is more than a rule on
makers of queries can give (a trace against it: the tree is hashed; a first query with another root;
then our root's chain apart). The proof calls the hypothesis once, at a query that is ours.

  `mem_of_accepted_ours`
      The text of `mem_of_accepted`, changed in two places: the hypothesis is asked at the queries q
      with `Ours C pre q l cur` alone (C: the trace, the tag, our external roots, our instance,
      salt, request root and slot: Chain.lean): q is rooted in a chain that starts at a first query
      with our roots and our instance (or, shared, our slot's value stands under our request root);
      and the one call of the hypothesis hands that fact on.
  `mem_of_accepted_of_ours`
      The hypothesis of stability of `mem_of_accepted` gives this one (`ours_cms`): so that
      statement follows, and nothing is lost.
  `mem_off_ours`
      `mem_off` (SeedOff.lean) over it: the value read off the trace need be stable at our own
      chain's queries alone; the first of them is a first query (F1) with our roots and our early
      instance.

Limits. What is then still asked of a value read off a chain apart (by `ours_first`, OursFirst.lean,
and `extSOf`, `extSOf_stable`, ReadRun.lean; no one statement of this folder joins them): that the
chain's queries stand in the trace before the first query (F1) with our roots and our early
instance, be it a maker's or the checker's own. At the checker's own first query this asks the order
"the chain apart, then the first chain", which the programs' verifier, as it is written again in
Lean under OnBytes/, does not have. `Ours` fixes our external roots (the whole list) and our early
instance, not the salt: a first query with our roots, our early instance and another salt is ours.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.SeedOff

noncomputable section

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol
open Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L}

/-- One protocol, with the reading's stability asked at our own chain's queries alone. -/
theorem mem_of_accepted_ours (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam W.K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
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
    (hrun : RunsIn tr (verifyB t Q wq embS embP xin embE (W.dReq t) cms x π) true)
    (hstab : ∀ pre (q : FbIn lam L t) (a : FsAns lam W.K) post l cur,
        tr = pre ++ fbE t q a :: post →
      Ours (⟨tr, t, cms, xin x, π.salt, π.rtreq, π.slot⟩ : Ctx W) pre q l cur →
      extY pre cms = extY tr cms)
    (hagree : ∀ p a sl,
      extLeaf tr wq.ext.depth (cms.getD (wq.ext.which p) default) (wq.ext.leaf p) =
        some ⟨embE a, sl⟩ →
      E.rd (extY tr cms) p = a) : Lg x (extY tr cms) := by
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
        have hbad : State (extY tr cms) (inst (Q.loc.shape.length - 1))
              (.full (trStar tr Q.loc.shape Q.ann wq.sh prjS rts π.plains ρ)) = false :=
          stays0 C hM hF Q.loc.shape Q.ann wq.sh prjS prjP embP
            hprjP (swSt (State (extY tr cms)) inst)
            (fun τ m h => by
              show State (extY tr cms) (inst (τ.snoc m).idx) _ = false
              rw [AtP.idx_snoc]
              exact hst2 _ τ m hL h) 0 .first ph π.roots π.plains ρ rts []
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
                    π.slot % 2 ^ (W.dReq t), Nat.mod_lt _ (Nat.pow_pos (by decide)), π.rtreq, c, sd,
                    digOf_ofFn _, (extReq_mod pre (W.dReq t) _ _).trans h7, h8, ?_⟩
                rw [e3]
                exact hfl)
            (by rw [swSt_empty]; exact hst1 _ hL)
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
        rw [heq, hst3 _ _ hL hbad] at hacc
        cases hacc
      · cases runsIn_pure_iff.1 h2
    · cases runsIn_pure_iff.1 h2

/-- The hypothesis of stability of `mem_of_accepted` gives this one; so that statement follows from
`mem_of_accepted_ours`. -/
theorem mem_of_accepted_of_ours (t : Tag) {E : ExtSpec}
    (extY : Tc W → List (Dig lam) → E.Str) {tr : Tc W} (cms : List (Dig lam)) (xo : Option X)
        (salt : Bits) (rtreq : Dig lam) (j : ℕ)
    (hstab : ∀ pre (q : FbIn lam L t) (a : FsAns lam W.K) post, tr = pre ++ fbE t q a :: post →
      (∀ c ∈ cms.take 2, (evM lam W.K L).OccursIn (pre ++ [fbE t q a]) c) →
      extY pre cms = extY tr cms) :
    ∀ pre (q : FbIn lam L t) (a : FsAns lam W.K) post l cur, tr = pre ++ fbE t q a :: post →
      Ours (⟨tr, t, cms, xo, salt, rtreq, j⟩ : Ctx W) pre q l cur → extY pre cms = extY tr cms :=
  fun pre q a post _ _ htr hours => hstab pre q a post htr
      (ours_cms (⟨tr, t, cms, xo, salt, rtreq, j⟩ : Ctx W) a hours)

/-- A part of the instance that stands in no query, read off the trace: stable at our own chain's
queries alone. -/
theorem mem_off_ours (t : Tag) {Y0 Sd : Type} {E : ExtSpec}
    (Q : BatchInteractiveOracleProof (Y0 × Sd) (ExtSpec.withS E Sd))
    (wq : ProtocolQueryLayout lam W.K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y0 × Sd → Option X)
    (embE : E.Sym → Body L) (hOK : wq.OKG) (hloc : Q.loc.IsLocal) (hco : Q.ann.Coherent)
    {Lg : Y0 × Sd → E.Str → Prop} (State : E.Str → Y0 × Sd → PTr Q.loc.shape → Bool)
    (prjS : (p : OPos Q.loc.shape) → Body L → Option (OSym Q.loc.shape p))
    (hprjS : ∀ p a, prjS p (embS p a) = some a)
    (prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.loc.shape Q.ann))
    (hprjP : ∀ z, prjP (embP z) = some z) (xout : Option X → Option Y0) (d : Sd)
    (extY : Tc W → List (Dig lam) → E.Str) (extS : Tc W → List (Dig lam) → Sd)
    (ε : Err Q.loc.shape) {tr : Tc W} (hM : ¬ EM tr) (hF : ¬ EF tr)
    (hS : ¬ StepEvent (laneOf W t Q wq.sh prjS prjP ε
      (fun (y : E.Str × Sd) x τ => State y.1 (x.1, y.2) τ) (fun o => (xout o).map fun a => (a, d))
      (fun tr cms => (extY tr cms, extS tr cms))).step tr)
    (cms : List (Dig lam)) (x : Y0 × Sd) (π : OneProtocolProof lam Q) (inst : ℕ → Y0)
    (hx : ∀ i, xout (instX L (xin x) i) = some (inst i))
    (hlate : ∀ n, L.late = some n → xin x ≠ none → 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann)
    (hst1 : ∀ y, ¬ Lg x y → State y (inst 0, x.2) (PTr.empty Q.loc.shape) = false)
    (hst2 : ∀ y (τ : AtP Q.loc.shape) (m : τ.round.Msg), ¬ Lg x y →
      State y (inst (τ.idx - 1), x.2) (.atP τ) = false →
          State y (inst τ.idx, x.2) (.atV (τ.snoc m)) = false)
    (hst3 : ∀ y s τ, ¬ Lg x y → State y (inst (Q.loc.shape.length - 1), x.2) (.full τ) = false →
      Q.loc.accept x (y, s) τ = false)
    (hrun : RunsIn tr (verifyB t Q wq embS embP xin embE (W.dReq t) cms x π) true)
    (hstab : ∀ pre (q : FbIn lam L t) (a : FsAns lam W.K) post l cur,
        tr = pre ++ fbE t q a :: post →
      Ours (⟨tr, t, cms, xin x, π.salt, π.rtreq, π.slot⟩ : Ctx W) pre q l cur →
      extY pre cms = extY tr cms ∧ extS pre cms = extS tr cms)
    (hagree : ∀ p a sl,
      extLeaf tr wq.ext.depth (cms.getD (wq.ext.which p) default) (wq.ext.leaf p) =
        some ⟨embE a, sl⟩ →
      E.rd (extY tr cms) p = a) : extS tr cms ≠ x.2 ∨ Lg x (extY tr cms) :=
  mem_of_accepted_ours t Q wq embS embP xin embE hOK hloc hco
    (Lg := fun x (y : E.Str × Sd) => y.2 ≠ x.2 ∨ Lg x y.1)
    (fun (y : E.Str × Sd) x τ => State y.1 (x.1, y.2) τ) prjS hprjS prjP hprjP
    (fun o => (xout o).map fun a => (a, d)) (fun tr cms => (extY tr cms, extS tr cms)) ε
        hM hF hS cms x π
    (fun i => (inst i, d)) (fun i => by
      show (xout (instX L (xin x) i)).map (fun a => (a, d)) = some (inst i, d)
      rw [hx i]
      rfl) hlate
    (fun y hL => by
      obtain ⟨h1, h2⟩ := not_or.1 hL
      show State y.1 (inst 0, y.2) _ = false
      rw [not_not.1 h1]
      exact hst1 y.1 h2)
    (fun y τ m hL h => by
      obtain ⟨h1, h2⟩ := not_or.1 hL
      have e : y.2 = x.2 := not_not.1 h1
      show State y.1 (inst τ.idx, y.2) _ = false
      have h' : State y.1 (inst (τ.idx - 1), y.2) (.atP τ) = false := h
      rw [e] at h' ⊢
      exact hst2 y.1 τ m h2 h')
    (fun y τ hL h => by
      obtain ⟨h1, h2⟩ := not_or.1 hL
      have e : y.2 = x.2 := not_not.1 h1
      have h' : State y.1 (inst (Q.loc.shape.length - 1), y.2) (.full τ) = false := h
      rw [e] at h'
      exact hst3 y.1 y.2 τ h2 h')
    hrun
    (fun pre q a post l cur htr hours => Prod.ext (hstab pre q a post l cur htr hours).1
        (hstab pre q a post l cur htr hours).2)
    hagree

end TypedOracleCompiler.Compile.Batch
