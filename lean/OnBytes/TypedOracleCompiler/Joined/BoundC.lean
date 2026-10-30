-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/BoundC.lean: OnBytes/TypedOracleCompiler/Joined/Bound.lean and BoundFiles.lean once more, for a
protocol whose instances are read back from a chain's queries AND from the list of outer roots.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

Why. A compiled verifier with a record hands a session's chain the list "the root, the root, then
the record, written as digests". All slots under one request root have that list in common, so they
have one record; and round-by-round soundness of the session's protocol is known record by record.
The law on the verifier's messages of shared rounds is then needed only for vectors of instances
with one record. For that the map that reads a chain's instance back is also handed the list of
outer roots, and gives nothing where list and instance do not fit.

Part 1, in a namespace below that of OnBytes/TypedOracleCompiler/Compile/Batch: `laneOfC`, `laneOfC_ok`,
`mem_of_accepted_oursC`: `laneOf`, `laneOf_ok` (Sound.lean there) and `mem_of_accepted_ours`
(SoundOurs.lean there) with that one turn. The proof of the third is that file's text, copied by a
program, with the further argument written in at four places and three lines broken.
`mem_of_accepted_ours` is the new lemma at `fun _ => xout` (by the two texts; no theorem here says
so): the two texts stand side by side.
Part 2: the form that a statement on several verifiers calls:
  `ReadBackC Z early okX`: the read-back, with `xout` handed the list; its law on instances is asked
    where `okX cms x` holds; `ReadBackC.restrict`: it serves every narrower predicate;
  `SndLaws Q early late Lg State`: all clauses of `BatchInteractiveOracleProof.SndBL` (Iop/Batch.lean) but the law on
    verifier messages, for a given state function;
  `mem_of_sndC`: outside the three events a yes means "in the language";
  `LaneForC`: `LaneFor` (BoundFiles.lean) with a predicate on the list AND the instance;
  `laneForC_of_laws`: from `SndLaws` and the law on verifier messages for the vectors that `xout`
    gives at one list; `LaneForC.of_yes`, `LaneForC.mem`, `LaneFor.toC`.

Limits: as in OnBytes/TypedOracleCompiler/Joined/Bound.lean. At an `xout` that never gives an instance the law on
verifier messages is empty; but then `xout_in` can be met only if `okX` holds of nothing, and the
statement says nothing. The two pull against each other, and whoever states a theorem pins `okX` to
the calls of the verifier that runs.
No other file of the library uses `mem_of_sndC`, `laneForC_of_laws` or `ReadBackC.restrict` yet.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.BoundFiles

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Joined
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol
open Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L}

/-! ## Part 1. The lemma on one protocol, with the list of outer roots handed to the read-back -/

/-- `laneOf`, with `xout` also handed the list of outer roots of the first query. -/
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

/-- The lane is well formed if the law on verifier messages holds for the vectors of instances that
`xout` gives at one list. -/
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

/-- `mem_of_accepted_ours`, with `xout` also handed the list of outer roots. -/
theorem mem_of_accepted_oursC (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
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
              RunsIn tr
                (reqCheck (K := W.K) (L := L) (W.dReq t) π.rtreq π.slot π.path c π.rsalt) true) ∧
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
              have hfl : (laneOfC W t Q wq.sh prjS prjP ε State xout extY).flips
                  pre cms (lastX C.xo rest cur) rest cur a :=
                ⟨State (extY tr cms) (inst rest.length), τ, by
                  show (xout cms (lastX ((xin x).map L.early) rest cur)).map
                    (State (extY pre cms)) = _
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

end TypedOracleCompiler.Compile.Batch.Joined

namespace TypedOracleCompiler.Joined
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Joined Rom
  Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L}

/-! ## Part 2. The form that a statement on several verifiers calls -/

/-- `ReadBack` (OnBytes/TypedOracleCompiler/Joined/Bound.lean), with `xout` also handed the list of outer roots; the
law on instances is asked where `okX cms x` holds. -/
structure ReadBackC {Y : Type} {E : ExtSpec} (Z : Written W Y E) (early : Y → Y)
    (okX : List (Dig lam) → Y → Prop) where
  prjS : (p : OPos Z.Q.loc.shape) → Body L → Option (OSym Z.Q.loc.shape p)
  prjP : PlainPart (shapeOf L Z.t) (annOf L Z.t) → Option (PlainPart Z.Q.loc.shape Z.Q.ann)
  xout : List (Dig lam) → Option X → Option Y
  /-- a symbol that was written is read back -/
  prjS_emb : ∀ p a, prjS p (Z.embS p a) = some a
  /-- a plain part that was written is read back -/
  prjP_emb : ∀ z, prjP (Z.embP z) = some z
  /-- what a chain's queries hold of an instance up to round i is read back as `instAt`, at a list
  that fits the instance -/
  xout_in : ∀ cms x i, okX cms x → xout cms (instX L (Z.xin x) i) = some (instAt early L.late x i)

/-- A read-back serves every narrower predicate on list and instance. -/
def ReadBackC.restrict {Y : Type} {E : ExtSpec} {Z : Written W Y E} {early : Y → Y}
    {okX okX' : List (Dig lam) → Y → Prop} (R : ReadBackC Z early okX)
    (h : ∀ cms x, okX' cms x → okX cms x) : ReadBackC Z early okX' where
  prjS := R.prjS
  prjP := R.prjP
  xout := R.xout
  prjS_emb := R.prjS_emb
  prjP_emb := R.prjP_emb
  xout_in := fun cms x i hC => R.xout_in cms x i (h cms x hC)

/-- All clauses of (Snd-B) in the late form (`BatchInteractiveOracleProof.SndBL`, Iop/Batch.lean) but the law on
verifier messages, for a given state function. -/
structure SndLaws {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (early : Y → Y) (late : Option ℕ)
    (Lg : Y → E.Str → Prop) (State : E.Str → Y → PTr Q.loc.shape → Bool) : Prop where
  /-- the round `late` is not the first, and it and all rounds before it are local -/
  local_to : ∀ n, late = some n → 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann
  /-- a false statement starts in state 0 of its early part -/
  start : ∀ y x, ¬ Lg x y → State y (early x) (PTr.empty Q.loc.shape) = false
  /-- a prover message never changes 0 to 1 -/
  prover : ∀ y x (τ : AtP Q.loc.shape) (m : τ.round.Msg),
    State y x (.atP τ) = false → State y x (.atV (τ.snoc m)) = false
  /-- at the round `late` state 0 of the early part gives state 0 of a false statement -/
  switch : ∀ y x (τ : AtP Q.loc.shape), ¬ Lg x y → late = some τ.idx →
    State y (early x) (.atP τ) = false → State y x (.atP τ) = false
  /-- at the end state 0 means that a false statement is rejected -/
  full : ∀ y x (τ : Tr Q.loc.shape), ¬ Lg x y →
    State y (if late.isSome then x else early x) (.full τ) = false → Q.loc.accept x y τ = false

section Lane
variable {Y : Type} {E : ExtSpec} {early : Y → Y} {okX : List (Dig lam) → Y → Prop}

/-- the protocol as a lane of the analysis -/
def laneJC (Z : Written W Y E) (R : ReadBackC Z early okX) (ε : Err Z.Q.loc.shape)
    (State : E.Str → Y → PTr Z.Q.loc.shape → Bool) (extY : Tc W → List (Dig lam) → E.Str) :
    Lane W :=
  laneOfC W Z.t Z.Q Z.wq.sh R.prjS R.prjP ε State R.xout extY

/-- `mem_of_snd` (OnBytes/TypedOracleCompiler/Joined/Bound.lean) at a list of outer roots that fits the instance. -/
theorem mem_of_sndC (Z : Written W Y E) (R : ReadBackC Z early okX) (hOK : Z.wq.OKG)
    (hloc : Z.Q.loc.IsLocal) (hco : Z.Q.ann.Coherent) {Lg : Y → E.Str → Prop}
    (ε : Err Z.Q.loc.shape) (State : E.Str → Y → PTr Z.Q.loc.shape → Bool)
    (hl : SndLaws Z.Q early L.late Lg State) (extY : Tc W → List (Dig lam) → E.Str) {tr : Tc W}
    (hM : ¬ EM tr) (hF : ¬ EF tr) (hS : ¬ StepEvent (laneJC Z R ε State extY).step tr)
    (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Z.Q) (hC : okX cms x)
    (hrun : RunsIn tr (Z.verifyLax cms x π) true)
    (hext : ExtReads (⟨tr, Z.t, cms, Z.xin x, π.salt, π.rtreq, π.slot⟩ : Ctx W) Z.wq.ext Z.embE
      extY) :
    Lg x (extY tr cms) :=
  mem_of_accepted_oursC Z.t Z.Q Z.wq Z.embS Z.embP Z.xin Z.embE hOK hloc hco (Lg := Lg) State
    R.prjS R.prjS_emb R.prjP R.prjP_emb R.xout extY ε hM hF hS cms x π
    (instAt early L.late x) (fun i => R.xout_in cms x i hC) (fun n hn _ => hl.local_to n hn)
    (fun y hL => by rw [instAt_zero hl.local_to]; exact hl.start y x hL)
    (fun y τ m hL h => by
      rcases instAt_step (early := early) hl.local_to x τ.idx with e | ⟨e1, e2, e3⟩
      · rw [e] at h; exact hl.prover y _ τ m h
      · rw [e2] at h; rw [e3]; exact hl.prover y x τ m (hl.switch y x τ hL e1 h))
    (fun y τ hL h =>
      hl.full y x τ hL (by rw [← instAt_last (early := early) hl.local_to]; exact h))
    hrun hext.stable hext.agrees

end Lane

/-- The lane ℓ serves the verifier V, at the calls with `okX cms x`. -/
structure LaneForC (W : QueryLayout lam L) (t : Tag) (N : ℕ) {Y P : Type} {E : ExtSpec}
    (V : List (Dig lam) → Y → P → TypedOracleComputation lam W.K L Bool) (okX : List (Dig lam) → Y → Prop)
    (Lg : Y → E.Str → Prop) (extY : Tc W → List (Dig lam) → E.Str) (εs : ℝ≥0∞) (ℓ : Lane W) :
    Prop where
  /-- its queries have the tag t -/
  tag : ℓ.t = t
  /-- it is well formed -/
  ok : ℓ.OK N
  /-- its round errors, as probabilities, are at most εs -/
  below : Err.Below ℓ.ε εs
  /-- outside the two hash events and the lane's state event, a yes means "in the language" -/
  yes : ∀ (tr : Tc W) cms x π, okX cms x → ¬ EM tr → ¬ EF tr → ¬ StepEvent ℓ.step tr →
    RunsIn tr (V cms x π) true → Lg x (extY tr cms)

/-- From the laws of a state function, and the law on verifier messages for the vectors of
instances that the read-back gives at one list of outer roots. -/
theorem laneForC_of_laws {Y : Type} {E : ExtSpec} {early : Y → Y}
    {okX : List (Dig lam) → Y → Prop} (Z : Written W Y E) (R : ReadBackC Z early okX) {N : ℕ}
    {Lg : Y → E.Str → Prop} {ε : Err Z.Q.loc.shape} {εs : ℝ≥0∞}
    (State : E.Str → Y → PTr Z.Q.loc.shape → Bool) (hl : SndLaws Z.Q early L.late Lg State)
    (hj : ∀ y cms (xs : Fin N → Option (Option X)),
      JointLaw N Z.Q.loc.shape Z.Q.ann ε fun j => ((xs j).bind (R.xout cms)).map (State y))
    (hε : Err.Below ε εs) (hOK : Z.wq.OKG) (hloc : Z.Q.loc.IsLocal) (hco : Z.Q.ann.Coherent)
    (extY : Tc W → List (Dig lam) → E.Str)
    (hext : ∀ (tr : Tc W) cms x (π : OneProtocolProof lam Z.Q), okX cms x → ¬ EM tr →
      ExtReads (⟨tr, Z.t, cms, Z.xin x, π.salt, π.rtreq, π.slot⟩ : Ctx W) Z.wq.ext Z.embE extY) :
    LaneForC W Z.t N Z.verifyLax okX Lg extY εs (laneJC Z R ε State extY) :=
  ⟨rfl, laneOfC_ok hOK.sh hj, hε, fun tr cms x π hC hM hF hS hrun =>
    mem_of_sndC Z R hOK hloc hco ε State hl extY hM hF hS cms x π hC hrun
      (hext tr cms x π hC hM)⟩

section Rules
variable {t : Tag} {N : ℕ} {Y P P' : Type} {E : ExtSpec}
  {V : List (Dig lam) → Y → P → TypedOracleComputation lam W.K L Bool} {Lg : Y → E.Str → Prop}
  {extY : Tc W → List (Dig lam) → E.Str} {εs : ℝ≥0∞} {ℓ : Lane W}

/-- `LaneFor` is `LaneForC` at a predicate that does not look at the instance. -/
theorem LaneFor.toC {okC : List (Dig lam) → Prop} (h : LaneFor W t N V okC Lg extY εs ℓ) :
    LaneForC W t N V (fun cms _ => okC cms) Lg extY εs ℓ :=
  ⟨h.tag, h.ok, h.below, h.yes⟩

/-- A verifier that says yes only where V does is served by the same lane. -/
theorem LaneForC.of_yes {okX : List (Dig lam) → Y → Prop}
    {V' : List (Dig lam) → Y → P' → TypedOracleComputation lam W.K L Bool} (h : LaneForC W t N V okX Lg extY εs ℓ)
    (hV : ∀ (tr : Tc W) cms x π', RunsIn tr (V' cms x π') true → ∃ π, RunsIn tr (V cms x π) true) :
    LaneForC W t N V' okX Lg extY εs ℓ :=
  ⟨h.tag, h.ok, h.below, fun tr cms x π' hC hM hF hS hrun => by
    obtain ⟨π, hπ⟩ := hV tr cms x π' hrun
    exact h.yes tr cms x π hC hM hF hS hπ⟩

/-- Outside the bad event of a list that holds the lane, a yes means "in the language". -/
theorem LaneForC.mem {okX : List (Dig lam) → Y → Prop} (h : LaneForC W t N V okX Lg extY εs ℓ)
    {ℓs : List (Lane W)} (hm : ℓ ∈ ℓs) {tr : Tc W} (hB : ¬ BadL ℓs tr) {cms : List (Dig lam)}
    {x : Y} {π : P} (hC : okX cms x) (hrun : RunsIn tr (V cms x π) true) : Lg x (extY tr cms) := by
  obtain ⟨hM, hF, hS, -⟩ := not_badL hB
  exact h.yes tr cms x π hC hM hF (hS ℓ hm) hrun

end Rules

end TypedOracleCompiler.Joined
