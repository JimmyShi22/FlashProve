-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RecCompile/CmsBcs.lean: the proof of Spec.cms_bcs (Cms.lean).
Part 1: laneOfC, laneOfC_ok, mem_of_acceptedC: laneOf, laneOf_ok, mem_of_accepted of
Compile/Batch/Sound.lean with ONE turn: the map xout, which reads the chain's request back as an
instance, is also handed the list cms of the first query. mem_of_acceptedC's proof is the library's
text, copied by a program, with that argument written in at four places. Part 2: the seed's event.
Part 3: the theorem.

-/
import Johnson.RecCompile.Cms

set_option autoImplicit false

noncomputable section

namespace Compile.Batch.Cms
open Iop Rom Prob
open Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

section Gen
variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {W : QueryLayout lam L}

def laneOfC (W : QueryLayout lam L) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (ws : RoundsQueryLayout lam W.K Q.loc.shape Q.ann)
    (prjS : (p : OPos Q.loc.shape) → Body L → Option (OSym Q.loc.shape p))
    (prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.loc.shape Q.ann)) (ε : Err Q.loc.shape)
    (State : E.Str → Y → PTr Q.loc.shape → Bool) (xout : List (Dig lam) → Option X → Option Y)
    (extY : Tc W → List (Dig lam) → E.Str) : Lane W where
  t := t
  s := Q.loc.shape
  A := Q.ann
  ws := ws
  prjS := prjS
  prjP := prjP
  ε := ε
  state := fun tr cms xo => (xout cms xo).map (State (extY tr cms))

theorem laneOfC_ok {t : Tag} {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}
    {ws : RoundsQueryLayout lam W.K Q.loc.shape Q.ann}
    {prjS : (p : OPos Q.loc.shape) → Body L → Option (OSym Q.loc.shape p)}
    {prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.loc.shape Q.ann)} {ε : Err Q.loc.shape}
    {State : E.Str → Y → PTr Q.loc.shape → Bool} {xout : List (Dig lam) → Option X → Option Y}
    {extY : Tc W → List (Dig lam) → E.Str} {N : ℕ} (hws : RoundsQueryLayout.OKG Q.loc.shape Q.ann ws)
    (hj : ∀ y cms (xs : Fin N → Option (Option X)),
      JointLaw N Q.loc.shape Q.ann ε fun j => ((xs j).bind (xout cms)).map (State y)) :
    (laneOfC W t Q ws prjS prjP ε State xout extY).OK N :=
  ⟨hws, fun pre cms xs => by
    have h := hj (extY pre cms) cms xs
    have e : (fun j => ((xs j).bind (xout cms)).map (State (extY pre cms))) =
        fun j =>
          (xs j).bind
              ((laneOfC W t Q ws prjS prjP ε State xout extY).state pre cms) := funext fun j => by
      cases xs j <;> rfl
    rw [e] at h
    exact h⟩

theorem mem_of_acceptedC (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam W.K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (hOK : wq.OKG) (hloc : Q.loc.IsLocal) (hco : Q.ann.Coherent)
    {Lg : Y → E.Str → Prop} (State : E.Str → Y → PTr Q.loc.shape → Bool)
    (prjS : (p : OPos Q.loc.shape) → Body L → Option (OSym Q.loc.shape p))
    (hprjS : ∀ p a, prjS p (embS p a) = some a)
    (prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.loc.shape Q.ann))
    (hprjP : ∀ z, prjP (embP z) = some z) (xout : List (Dig lam) → Option X → Option Y)
    (extY : Tc W → List (Dig lam) → E.Str) (ε : Err Q.loc.shape) {tr : Tc W} (hM : ¬ EM tr)
    (hF : ¬ EF tr) (hS : ¬ StepEvent (laneOfC W t Q wq.sh prjS prjP ε State xout extY).step tr)
    (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (inst : ℕ → Y)
    (hx : ∀ i, xout cms (instX L (xin x) i) = some (inst i))
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
        -- the slot value is under the request root
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
              have hy : extY pre cms = extY tr cms := hstab pre q a post htr (ours_cms C a hours)
              have hfl : (laneOfC W t Q wq.sh prjS prjP ε State xout extY).flips
                  pre cms (lastX C.xo rest cur) rest cur a :=
                ⟨State (extY tr cms) (inst rest.length), τ, by
                  show (xout cms (lastX ((xin x).map L.early) rest cur)).map (State (extY pre cms)) = _
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

end Gen

end Compile.Batch.Cms

namespace Compile.Batch.Cms
open Iop Rom Prob
open Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

variable {I X Wn : Type} {lam : ℕ} {L : HolographicProtocol I X} (W : QueryLayout lam L.carrierC) (S : OutOfDomainSampleQueryLayout lam W.K L)

/-! ## Part 2. The seed's event -/

/-- The entry e, after the trace pre, is a new seed's query at a root cm, and its seed is a
collision seed of the word that pre determines under cm. -/
def stepSeed (pre : Tc W) (e : QA (spec lam W.K L.carrierC)) : Prop :=
  e ∉ pre ∧ ∃ (t : Tag) (cm : Dig lam) (a : FsAns lam W.K),
    e = fbE t (seedQ W S t cm) a ∧ L.hasCollisionAt (extEnc W pre cm) (S.seed a.1)

/-- A seed's query is no rooted query: it causes no lane's event. -/
theorem not_step_seed (ℓ : Lane W) (pre : Tc W) (t : Tag) (cm : Dig lam) (a : FsAns lam W.K) :
    ¬ ℓ.step pre (fbE t (seedQ W S t cm) a) := by
  obtain ⟨t', s, A, ws, pS, pP, ε, st⟩ := ℓ
  rintro ⟨-, q', a', D, he, hr, -⟩
  have ht : OracleName.fb t = OracleName.fb t' := congrArg Sigma.fst he
  cases ht
  obtain ⟨rfl, -⟩ := fbE_inj he
  cases (show (none : Option (Data lam W.K L.carrierC t)) = some D from hr)

/-- An exactly uniform map from digests to seeds has the law, by the record clause. -/
theorem seedLaw_of_unif {K : ℕ} {S : OutOfDomainSampleQueryLayout lam K L}
    (hu : (unif (Fin K → Dig lam)).map S.seed = unif L.OutOfDomainSeed) {eR : ℕ} {εs : ℝ≥0∞}
    (hrcd : ∀ y, cnt (fun s => L.hasCollisionAt y s) ≤ eR)
    (heR : (eR : ℝ≥0∞) ≤ εs * (Fintype.card L.OutOfDomainSeed : ℝ≥0∞)) : S.Law εs := by
  intro y
  have h1 : pr (unif (Fin K → Dig lam)) {a | L.hasCollisionAt y (S.seed a)}
      = pr ((unif (Fin K → Dig lam)).map S.seed) {s | L.hasCollisionAt y s} := by
    rw [pr_map]; rfl
  rw [h1, hu]
  exact (pr_unif_le_iff _ _).2 (le_trans (Nat.cast_le.2 (hrcd y)) heR)

theorem pr_seed_le {S : OutOfDomainSampleQueryLayout lam W.K L} {εs : ℝ≥0∞} (hS : S.Law εs) (y : Fin L.wordLength → L.Symbol) :
    pr (unif (FsAns lam W.K)) {a | L.hasCollisionAt y (S.seed a.1)} ≤ εs := by
  have h1 : pr (unif (FsAns lam W.K)) {a | L.hasCollisionAt y (S.seed a.1)}
      = pr ((unif (FsAns lam W.K)).map Prod.fst) {b | L.hasCollisionAt y (S.seed b)} := by
    rw [pr_map]; rfl
  rw [h1, map_fst_unif]
  exact hS y

/-- The answer to one query causes one of the four events with probability at most εs: a query
belongs to one of them only. -/
theorem pr_step4_le {ℓT ℓL ℓB : Lane W} (hT : ℓT.t = Tag.test) (hL : ℓL.t = Tag.link)
    (hB : ℓB.t = Tag.onl) {N : ℕ} (hN : N = 2 ^ W.depthReq) (oT : ℓT.OK N) (oL : ℓL.OK N)
    (oB : ℓB.OK N) {εs : ℝ≥0∞} (bT : Err.Below ℓT.ε εs) (bL : Err.Below ℓL.ε εs)
    (bB : Err.Below ℓB.ε εs) (hS : S.Law εs)
    (pre : Tc W) (o : OracleName) (q : domOf lam L.carrierC o) :
    pr (unif ((spec lam W.K L.carrierC).Rng o))
        {r | stepS W ℓT ℓL ℓB pre (⟨o, q, r⟩ : QA (spec lam W.K L.carrierC)) ∨
          stepSeed W S pre (⟨o, q, r⟩ : QA (spec lam W.K L.carrierC))} ≤ εs := by
  by_cases h : ∃ t cm, (⟨o, q⟩ : Σ o, domOf lam L.carrierC o) = ⟨OracleName.fb t, seedQ W S t cm⟩
  · obtain ⟨t, cm, h⟩ := h
    cases h
    refine le_trans (pr_mono _ ?_) (pr_seed_le W hS (extEnc W pre cm))
    rintro r ((h | h | h) | ⟨-, t', cm', a, he, hc⟩)
    · exact absurd h (not_step_seed W S _ pre t cm r)
    · exact absurd h (not_step_seed W S _ pre t cm r)
    · exact absurd h (not_step_seed W S _ pre t cm r)
    · have ht : OracleName.fb t = OracleName.fb t' := congrArg Sigma.fst he
      cases ht
      obtain ⟨hq, rfl⟩ := fbE_inj he
      have hcm : cm = cm' := by
        have h2 := congrArg (fun z : FbIn lam L.carrierC t => z.head) hq
        simpa [seedQ] using h2
      subst hcm
      exact hc
  · refine le_trans (pr_mono _ ?_) (pr_stepS_le hT hL hB hN oT oL oB bT bL bB pre o q)
    rintro r (h1 | ⟨-, t, cm, a, he, -⟩)
    · exact h1
    · refine absurd ⟨t, cm, ?_⟩ h
      have he' : (⟨o, q, r⟩ : QA (spec lam W.K L.carrierC)) = ⟨OracleName.fb t, seedQ W S t cm, a⟩ := he
      cases he'
      rfl

/-! ## Part 3. The lanes and the theorem -/

open Classical in
/-- the instance of a slot of a session, read back from the chain's request and the list cms: none
unless the list holds the request's record behind its two first places -/
def xoutBC (cms : List (Dig lam)) (xo : Option L.XC) : Option (X × L.Rec) :=
  xo.bind fun a => a.1.bind fun x => if cms.drop 2 = S.code a.2.1 then some (x, a.2.1) else none

theorem xoutBC_code {cms : List (Dig lam)} {xo : Option (Option L.XC)} {a : X × L.Rec}
    (h : xo.bind (xoutBC W S cms) = some a) : cms.drop 2 = S.code a.2 := by
  obtain ⟨x1, -, h1⟩ := Option.bind_eq_some_iff.1 h
  unfold xoutBC at h1
  obtain ⟨b, -, h2⟩ := Option.bind_eq_some_iff.1 h1
  obtain ⟨x, -, h3⟩ := Option.bind_eq_some_iff.1 h2
  split_ifs at h3 with hc
  cases h3
  exact hc

def xoutTC (xo : Option L.XC) : Option L.Rec := xo.map fun a => a.2.1
def xoutLC (xo : Option L.XC) : Option (L.Rec × L.Rec) := xo.map fun a => a.2

def laneTC (εT : Err L.offline.shape) : Lane W :=
  laneOf W Tag.test (BatchInteractiveOracleProof.ofProto L.offline) (wTC W).sh (prjSym (L := L.carrierC) Tag.test) some
    εT (stOf L.offline εT) xoutTC
    fun tr cms => extEnc W tr (cms.getD 0 default)

def laneLC (εL : Err L.link.shape) : Lane W :=
  laneOf W Tag.link (BatchInteractiveOracleProof.ofProto L.link) (wLC W).sh (prjSym (L := L.carrierC) Tag.link) some
    εL (stOf L.link εL) xoutLC
    fun tr cms => (extEnc W tr (cms.getD 0 default), extEnc W tr (cms.getD 1 default))

def laneBC (εB : Err L.onlineBatch.loc.shape)
    (State : (oneExternalString L.wordLength L.Symbol).Str → X × L.Rec → PTr L.onlineBatch.loc.shape → Bool) : Lane W :=
  laneOfC W Tag.onl L.onlineBatch (wBC W).sh (prjSym (L := L.carrierC) Tag.onl) some εB State (xoutBC W S)
    fun tr cms => extEnc W tr (cms.getD 0 default)

theorem cms_bcs : Spec.cms_bcs := by
  intro I X Wn lam L W S Rno wit eR εT εL εB εs hS hSd hbT hbL hbB hl hlT hlL hlB hco hW
  choose h0 St h1 h2 h3 h4 h5 using fun rec =>
    (Iop.sndBKT_laws X Wn _ (L.batAt rec) L.maxBatchSize L.early L.late (L.relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) εB).1 (hS.sndB rec)
  let State : (oneExternalString L.wordLength L.Symbol).Str → X × L.Rec → PTr L.onlineBatch.loc.shape → Bool :=
    fun y a => St a.2 y a.1
  have hl' : L.carrierC.late = none := hl
  have oT : (laneTC W εT).OK L.maxBatchSize := laneOf_ok hW.T.sh (stOf_joint L.offline εT L.maxBatchSize)
  have oL : (laneLC W εL).OK L.maxBatchSize := laneOf_ok hW.Lk.sh (stOf_joint L.link εL L.maxBatchSize)
  have oB : (laneBC W S εB State).OK L.maxBatchSize := by
    refine laneOfC_ok hW.B.sh fun y cms xs => ?_
    by_cases hex : ∃ j a, (xs j).bind (xoutBC W S cms) = some a
    · obtain ⟨j0, a0, hj0⟩ := hex
      have key : ∀ j a, (xs j).bind (xoutBC W S cms) = some a → a.2 = a0.2 := fun j a ha =>
        hW.seed.inj ((xoutBC_code W S ha).symm.trans (xoutBC_code W S hj0))
      refine cast (congrArg (JointLaw L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann εB) ?_)
        (h5 a0.2 y fun j => ((xs j).bind (xoutBC W S cms)).map Prod.fst)
      funext j
      show Option.map (St a0.2 y) (Option.map Prod.fst ((xs j).bind (xoutBC W S cms))) =
        Option.map (State y) ((xs j).bind (xoutBC W S cms))
      cases hj : (xs j).bind (xoutBC W S cms) with
      | none => rfl
      | some a =>
        show some (St a0.2 y a.1) = some (St a.2 y a.1)
        rw [key j a hj]
    · refine cast (congrArg (JointLaw L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann εB) ?_)
        (Iop.BatchOne.jointLaw_none L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann εB)
      funext j
      show none = Option.map (State y) ((xs j).bind (xoutBC W S cms))
      cases hj : (xs j).bind (xoutBC W S cms) with
      | none => rfl
      | some a => exact absurd ⟨j, a, hj⟩ hex
  refine ⟨fun tr => (EM tr ∨ EF tr) ∨ StepEvent (fun pre e =>
      stepS W (laneTC W εT) (laneLC W εL) (laneBC W S εB State) pre e ∨ stepSeed W S pre e) tr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro β A t hA
    have h := pr_stepEvent_le (S := spec lam W.K L.carrierC)
      (fun pre e =>
        stepS W (laneTC W εT) (laneLC W εL) (laneBC W S εB State) pre e ∨ stepSeed W S pre e)
      (fun _ => εs)
      (fun pre e he hs => hs.elim
        (fun hs => hs.elim (fun h1 => h1.1 he) fun h1 =>
          h1.elim (fun h2 => h2.1 he) fun h2 => h2.1 he)
        fun h1 => h1.1 he)
      (fun pre o q _ => pr_step4_le W S rfl rfl rfl hW.base.slots oT oL oB hbT hbL hbB hSd
        pre o q) A t hA
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    calc
      pr A.withTrace.law
            {o | (EM o.2 ∨ EF o.2) ∨ StepEvent (fun pre e =>
              stepS W (laneTC W εT) (laneLC W εL) (laneBC W S εB State) pre e ∨
                stepSeed W S pre e) o.2} ≤
          pr A.withTrace.law {o | EM o.2 ∨ EF o.2} +
            pr A.withTrace.law
              {o | StepEvent (fun pre e =>
                stepS W (laneTC W εT) (laneLC W εL) (laneBC W S εB State) pre e ∨
                  stepSeed W S pre e) o.2} :=
        pr_union_le _ _ _
      _ ≤ 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam + (t : ℝ≥0∞) * εs := add_le_add (hashEvents A t hA) h
      _ ≤ (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
          rw [add_comm]
          gcongr
          exact Nat.le_succ t
  · rintro tr tr' ((h | h) | h)
    · exact Or.inl (Or.inl (h.append tr'))
    · exact Or.inl (Or.inr (h.append tr'))
    · exact Or.inr (StepEvent.append h tr')
  · intro tr t cm a hB hmem hc
    have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
    obtain ⟨pre, post, htr, hnew⟩ := List.eq_append_cons_of_mem hmem
    refine hB (Or.inr ⟨pre, _, post, htr, Or.inr ⟨hnew, t, cm, a, rfl, ?_⟩⟩)
    rw [extEnc_before htr hM ⟨fbE t (seedQ W S t cm) a, by simp,
      evM_occurs_cms (q := seedQ W S t cm) a (cms := [cm]) (x := none) (sl := []) rfl (by simp)⟩]
    exact hc
  · intro tr tr' t cm a hB hmem
    exact extEnc_stable (fun h => hB (Or.inl (Or.inl h))) (List.prefix_append _ _)
      ⟨fbE t (seedQ W S t cm) a, hmem,
        evM_occurs_cms (q := seedQ W S t cm) a (cms := [cm]) (x := none) (sl := []) rfl (by simp)⟩
  · intro tr cm rec π hB hrun
    have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
    exact mem_of_accepted Tag.test (BatchInteractiveOracleProof.ofProto L.offline) (wTC W) _ id xinT
      (fun s => some (.inl s)) hW.T hlT
      (Iop.BatchOne.BAnn.allLocal_coherent _)
      (Lg := fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) (stOf L.offline εT)
      (prjSym (L := L.carrierC) Tag.test) (fun p a => prjSym_emb (L := L.carrierC) Tag.test p a)
      some (fun _ => rfl) xoutTC
      (fun tr cms => extEnc W tr (cms.getD 0 default)) εT hM (fun h => hB (Or.inl (Or.inr h)))
      (fun ⟨pre, e, post, h1, h2⟩ => hB (Or.inr ⟨pre, e, post, h1, Or.inl (Or.inl h2)⟩)) [cm] rec π
      (fun _ => rec) (fun i => by rw [instX_of_late_none hl']; rfl)
      (fun n hn _ => by cases hl'.symm.trans hn)
      (fun y hL => stOf_start hS.sndT y rec hL)
      (fun y τ m _ h => stOf_prover y rec τ m h) (fun y τ _ h => stOf_full y rec τ h) hrun
      (fun pre q a post htr hocc => extEnc_before htr hM (hocc _ (by simp)))
      (fun p a sl h => by
        change extLeaf tr W.T.ext.depth ([cm].getD (W.T.ext.which p) default) (W.T.ext.leaf p) = _
          at h
        rw [hW.base.extDepth.1, (hW.base.extT p).1, (hW.base.extT p).2] at h
        exact extEnc_apply hW.base h)
  · intro tr cm cm' rec rec' π hB hrun
    have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
    exact mem_of_accepted Tag.link (BatchInteractiveOracleProof.ofProto L.link) (wLC W) _ id xinL
      (fun s => some (.inl s)) hW.Lk hlL
      (Iop.BatchOne.BAnn.allLocal_coherent _)
      (Lg := fun rr y =>
        L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1)
      (stOf L.link εL)
      (prjSym (L := L.carrierC) Tag.link) (fun p a => prjSym_emb (L := L.carrierC) Tag.link p a)
      some (fun _ => rfl) xoutLC
      (fun tr cms => (extEnc W tr (cms.getD 0 default), extEnc W tr (cms.getD 1 default)))
      εL hM (fun h => hB (Or.inl (Or.inr h)))
      (fun ⟨pre, e, post, h1, h2⟩ =>
        hB (Or.inr ⟨pre, e, post, h1, Or.inl (Or.inr (Or.inl h2))⟩))
      [cm, cm'] (rec, rec') π
      (fun _ => (rec, rec')) (fun i => by rw [instX_of_late_none hl']; rfl)
      (fun n hn _ => by cases hl'.symm.trans hn)
      (fun y hL => stOf_start hS.sndL y (rec, rec') hL)
      (fun y τ m _ h => stOf_prover y (rec, rec') τ m h)
      (fun y τ _ h => stOf_full y (rec, rec') τ h) hrun
      (fun pre q a post htr hocc =>
        Prod.ext (extEnc_before htr hM (hocc _ (by simp)))
          (extEnc_before htr hM (hocc _ (by simp))))
      (fun p a sl h => agreeLk hW.base p a sl h)
  · intro tr cm x rec π hB hrun
    have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
    exact mem_of_acceptedC Tag.onl L.onlineBatch (wBC W) _ id xinB (fun s => some (.inl s)) hW.B hlB hco
      (Lg := fun a y => L.decodeIndex y a.2 = none ∨ ∃ i, L.decodeIndex y a.2 = some i ∧ ∃ w, Rno i a.1 w) State
      (prjSym (L := L.carrierC) Tag.onl) (fun p a => prjSym_emb (L := L.carrierC) Tag.onl p a)
      some (fun _ => rfl) (xoutBC W S)
      (fun tr cms => extEnc W tr (cms.getD 0 default)) εB hM (fun h => hB (Or.inl (Or.inr h)))
      (fun ⟨pre, e, post, h1, h2⟩ =>
        hB (Or.inr ⟨pre, e, post, h1, Or.inl (Or.inr (Or.inr h2))⟩))
      (cmsB W S cm rec) (x, rec) π
      (fun _ => (L.early x, rec))
      (fun i => by
        rw [instX_of_late_none hl']
        show (if (cmsB W S cm rec).drop 2 = S.code rec then some (L.early x, rec) else none) = _
        exact if_pos rfl)
      (fun n hn _ => by cases hl'.symm.trans hn)
      (fun y _ => h1 rec y x)
      (fun y τ m _ h => h2 rec y _ τ m h)
      (fun y τ hL h => Bool.eq_false_iff.2 fun hacc => hL (by
        have h6 := h4 rec y x τ
        rw [hl] at h6
        rcases h6 h hacc with h7 | ⟨i, hi, hr⟩
        · exact Or.inl h7
        · exact Or.inr ⟨i, hi, _, hr⟩)) hrun
      (fun pre q a post htr hocc => extEnc_before htr hM (hocc _ (by simp [cmsB])))
      (fun p a sl h => by
        change extLeaf tr W.B.ext.depth ((cmsB W S cm rec).getD (W.B.ext.which p) default)
          (W.B.ext.leaf p) = _ at h
        rw [hW.base.extDepth.2.2, (hW.base.extB p).1, (hW.base.extB p).2] at h
        exact extEnc_apply hW.base h)
  · intro tr tr' cm hB hann
    exact extEnc_stable (fun h => hB (Or.inl (Or.inl h)))
      (List.prefix_append _ _) (occursIn_of_announced hann)

end Compile.Batch.Cms

#print axioms Compile.Batch.Cms.cms_bcs
