-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBatchBlocks.lean: round-by-round knowledge soundness of one proximity test on a group of
oracle messages, when at most N instances are proved together (a batch).

A group (`Grp`, Cb/Ld/LdBatSig.lean) is some whole oracle messages of a signature, read at common
long positions, with one joint radius.
Definitions, statements (each a `Prop` in `Cb.Spec`) and proofs (an assembly).

The protocol is `ldRunE` of Cb/Ld/LdLinCloseRun.lean, unchanged, and so are its extractor and its
errors. A statement carries oracle messages with their samples; it claims rows on the messages of a
group G of them, and something more, A₀, of the oracle messages that are kept. The three parts:
  1. The bridge (one round: the seed of a zero-evader): the rows of the claim and all sample rows of
    all members become one form on the message of the group's complex; the members that are not kept
    leave the statement.
  2. A whole test: a whole proximity test T on the complex, run beside the kept oracle messages,
    their samples, the further oracles and A₀, none of which it touches.
  3. A step without rounds: the trivial statement that the test leaves is dropped.
Here: who speaks (an annotation of its shape, `RoundSplits`, Iop/Batch.lean: a local round has a verifier
message for each slot, a shared round one for all), and for which vectors of statements the errors
hold (`KnowB`).

In standard terms: `R.KnowB A N adm on RA RB ext ε` (Ior/BatchSeq.lean) is round-by-round knowledge
soundness by sets of bad verifier messages, for a batch. On a statement with the condition `on` and
a transcript of R without a bad value, if the verifier outputs a statement, the extractor turns a
witness of it into one of the input statement. For every admissible vector (adm) of at most N
statements (one to a slot; a slot may be empty) the bad sets are within the errors ε, which are
counts: in a local round the bad set of each slot that has had no bad value so far, in a shared
round the union over these slots.

Main names: there are two ways to run the test.
  In every slot, in the slot's local rounds (a group that holds oracle messages of one instance, and
    perhaps shared ones beside them). `Spec.ldRunB_local`: if the evader evades (`Z.OK`), the
    complex has lists of at most L members at the joint radius (`G.C.ListAt G.e L`), the joint
    radius implies each member's own (`G.Fits`), T is a tail that needs at most t long positions of
    the complex (`T.OK t`), every oracle message is a member of G or kept (`hc`), and G.P is not
    empty: states `KnowB` of `ldRunE`, from `S.over` (rows on G, beside A₀ of the kept messages) to
    `(S.sub kp).over A₀`, both ends relaxed by decoding with a sample, with the one-instance errors
    (in a row: L · (the evader's number) (`L * Z.err`), then T's), for every vector of statements.
    d, d': values for the extractor where nothing was output.
  Once, by the shared part of the prover (`RAnn.ofShared`, Iop/Batch.lean), under shared verifier
    messages (a group of shared oracle messages alone). `Spec.ldRunB_shared`: under the hypotheses
    of its statement (those of `Spec.ldRunB_local`): states `KnowB` of `ldRunE` with the same
    errors, paid once, not N times, for the vectors whose members have one acting part.
  `ldRunAct a`: the acting part of a statement. What a slot carries beside it (kept oracle messages
    that are no members, their samples, further oracles, the explicit part of the base joint A₀) is
    free, and may differ from slot to slot.
  Both at the joints whose condition ("collision-free", and the base joint's own condition) is moved
    into the relaxed relation (`Rels.cf`), as chains are made (`D.link`,
    Cb/Ld/LdLinCloseChain.lean).
  As links of a chain in a batch (`LinkA`, `KB`, Cb/Ld/LdLinChainB.lean): `D.linkLo`, `D.linkSh`,
    with `Spec.ldRunB_link_local`, `Spec.ldRunB_link_shared`. A key (`JKey`, same file) is a
    function of the statement at a joint.

Limits: this file says nothing on the honest side of a batch. Which groups a protocol forms, and
that a shared group's rows are the same for all slots, is the protocol's matter: here it is the
hypothesis on the key (`Spec.ldRunB_link_shared`). All of `KnowB`'s content hangs on which vectors
are admissible (the head of Ior/BatchSeq.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinCloseChain
import Cb.Ld.LdLinChainB
import Ior.KnowBRulesStep
import Iop.SplitUnderJoin
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood

section
variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} (G : Grp S) (Sb : B → Type)
  (St₀ : Type) (E₀ : ExtSpec)

/-- The acting part of a statement: all rows that the test takes in (the rows of the claim on the
group, and the sample rows of all members: seeds and answers), with targets and states, and the
members' words. -/
def ldRunAct (a : ((((B → E) × (∀ b, Sb b)) × St₀) × S.Smp) × (E₀.prod S.ext).Str) :
    ((G.Row B → E) × (∀ ν, G.RowSt Sb ν)) × G.C.ext.Str :=
  (G.claims a.1.1.1 a.1.2, G.word a.2.2)

end

namespace Spec

/-- In every slot, in local rounds. -/
def ldRunB_local : Prop :=
  ∀ (E B St₀ Wp : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P]
      (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
      (Z : Evader E (G.Row B)) (L : ℕ) (E₀ : ExtSpec) (A₀ : Rels Unit St₀ E₀ ((S.sub kp).Msg × Wp))
      (hc : ∀ o, G.mem o ∨ kp o) (d : S.Wit × Wp) (d' : LdBrW G kp Wp)
      (T : LdEnd (G.joint Sb sl Z)) (t N : ℕ),
    Z.OK → G.C.ListAt G.e L → G.Fits → T.OK t →
    (ldRunE G kp Sb sl Z St₀ E₀ T).KnowB (RoundSplits.allLocal _) N (fun _ => True) (fun _ => True)
      (S.over (claimRels (fun x m => Slf.All sl x (G.msg m))
          (onMsgRels (S.res (T := OMsg.Msg) kp) A₀))).cf.relR
      ((S.sub kp).over A₀).cf.relR (ldRunEX G kp Sb sl Z St₀ Wp E₀ T hc d d')
      (ldRunEN G kp Sb sl Z St₀ E₀ T Unit (L * Z.err)).err

/-- Once, by the shared part. -/
def ldRunB_shared : Prop :=
  ∀ (E B St₀ Wp : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P]
      (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
      (Z : Evader E (G.Row B)) (L : ℕ) (E₀ : ExtSpec) (A₀ : Rels Unit St₀ E₀ ((S.sub kp).Msg × Wp))
      (hc : ∀ o, G.mem o ∨ kp o) (d : S.Wit × Wp) (d' : LdBrW G kp Wp)
      (T : LdEnd (G.joint Sb sl Z)) (t N : ℕ),
    Z.OK → G.C.ListAt G.e L → G.Fits → T.OK t →
    (ldRunE G kp Sb sl Z St₀ E₀ T).KnowB (RoundSplits.const (RAnn.ofShared .sh) _) N
      (SameKey (ldRunAct G Sb St₀ E₀)) (fun _ => True)
      (S.over (claimRels (fun x m => Slf.All sl x (G.msg m))
          (onMsgRels (S.res (T := OMsg.Msg) kp) A₀))).cf.relR
      ((S.sub kp).over A₀).cf.relR (ldRunEX G kp Sb sl Z St₀ Wp E₀ T hc d d')
      (ldRunEN G kp Sb sl Z St₀ E₀ T Unit (L * Z.err)).err

end Spec

theorem ldRunB_local : Spec.ldRunB_local := by
  classical
  intro E B St₀ Wp _ _ _ S G _ kp _ Sb sl Z L E₀ A₀ hc d d' T t N hZ hL hF hT
  have h := closedTr_cf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (ldClose_run E B Unit St₀ Wp S G kp Sb sl Z L E₀ A₀ hc d d' T t (fun _ => True) (fun _ => True)
      hZ hL hF hT fun _ _ => trivial)
  exact knowB_local _ _ _ _ _ _ _ RAnn.allLocal (fun _ => rfl) N _ _ _ _ _ h.good.know

theorem ldRunB_shared : Spec.ldRunB_shared := by
  classical
  intro E B St₀ Wp _ _ _ S G _ kp _ Sb sl Z L E₀ A₀ hc d d' T t N hZ hL hF hT
  -- the whole, for one instance: only "the condition is carried" is used of it
  have hW := ldClose_run E B Unit St₀ Wp S G kp Sb sl Z L E₀ A₀ hc d d' T t (fun _ => True)
    (fun _ => True) hZ hL hF hT fun _ _ => trivial
  -- 1. the seed of the bridge, on the acting part, beside the carried part
  have k1 := knowB_shared_beside _ _ (LdCarX kp St₀) _ _ (LdCarE kp E₀) _ _ (LdCarW kp Wp)
    (ldBatEx G.C (G.RowSt Sb) Z) N _ _ _ _ _ ((S.sub kp).over A₀).on ((S.sub kp).over A₀).relR
    (ldBat_ex E G.P (G.Row B) Unit G.C (G.RowSt Sb) (G.rows sl) Z G.e L (fun _ => ())
      (fun _ => True) hZ hL).good.know
  have k1' : (IOR.draw Z.D (ldBrNx G kp Sb Z St₀) (LdBrE G kp E₀)).KnowB
      (RoundSplits.const (RAnn.ofShared .sh) _) N (SameKey fun a => (a.1.1, a.2.1))
      (IOR.Rels.beside (G.C.relsAll (G.rows sl) G.e fun _ => ()) ((S.sub kp).over A₀)).on
      (IOR.Rels.beside (G.C.relsAll (G.rows sl) G.e fun _ => ()) ((S.sub kp).over A₀)).relR
      (IOR.Rels.beside (G.C.rels (Slf.bat Z.ze (G.rows sl)) G.e fun _ => ())
        ((S.sub kp).over A₀)).relR
      (fun _ _ w => w) ((L * Z.err, ()) : ℕ × Unit) := by
    obtain ⟨bad, c, J⟩ := k1
    exact ⟨bad, c, J⟩
  -- 2. the step without rounds in front of it
  have st := ldBat_step E B Unit St₀ Wp S G kp Sb sl E₀ A₀ hc hF
  have k2 := knowB_pre _ _ _ _ _ _ _ _ _ _ _ N _ _ _ _ _ _
    (fun x => some (ldBrF G kp Sb St₀ x)) (ldBrG G kp E₀)
    (S.over
      (claimRels (fun x m => Slf.All sl x (G.msg m)) (onMsgRels (S.res (T := OMsg.Msg) kp) A₀))).on
    (S.over (claimRels (fun x m => Slf.All sl x (G.msg m))
        (onMsgRels (S.res (T := OMsg.Msg) kp) A₀))).relR
    (fun _ w => ldBrBack G kp Wp hc w) (fun _ _ w => ldBrBack G kp Wp hc w)
    k1' st.onOut st.know (fun _ _ _ _ _ => rfl)
  -- 3. the test, beside the carried part; 4. the trivial statement is dropped
  have k3 := knowB_shared_beside _ _ (LdCarX kp St₀) _ _ (LdCarE kp E₀) _ _ (LdCarW kp Wp)
    T.R N _ _ _ _ _ ((S.sub kp).over A₀).on ((S.sub kp).over A₀).relR hT.good.know
  have k4 := knowB_pure (Unit × LdCarX kp St₀) (LdCarX kp St₀) (extNone.prod (LdCarE kp E₀))
    (LdCarE kp E₀) (Unit × LdCarW kp Wp) (LdCarW kp Wp) (fun x => some x.2)
    (ExtMap.snd extNone (LdCarE kp E₀)) N
    (IOR.Rels.beside trivRels ((S.sub kp).over A₀)).on
    (IOR.Rels.beside trivRels ((S.sub kp).over A₀)).relR
    ((S.sub kp).over A₀).relR (fun _ w => ((), w))
    (fun x y x' w _ hx h => by
      obtain rfl := Option.some.inj hx
      exact ⟨trivial, h⟩)
  have g3 := (closedTr_beside Unit _ _ (LdCarX kp St₀) _ (LdCarE kp E₀) T.R _ _ (LdCarW kp Wp)
    T.H _ _ T.ext T.N ((S.sub kp).over A₀) _ (fun _ => True) hT).1
  have k34 := knowB_seq _ _ _ _ _ _ _ _ _ (T.R.keep (LdCarX kp St₀) (LdCarE kp E₀))
    (ldDropT kp St₀ E₀) _ _ N _ _ _ _ _ _ _ _ _ _ _ d' k3 k4 g3.good.onOut (fun _ _ _ => trivial)
  have g2 := ldBat_bridge E B Unit St₀ Wp S G kp Sb sl Z L E₀ A₀ hc (fun _ => True) (fun _ => True)
    hZ hL hF fun _ _ => trivial
  have k := knowB_seq _ _ _ _ _ _ _ _ _ (ldBridge G kp Sb Z St₀ E₀) ((T.R.keep (LdCarX kp St₀) (LdCarE kp E₀)).seq (ldDropT kp St₀ E₀)) _ _ N _ _ _ _ _ _ _ _ _ _ _ d k2 k34 g2.good.onOut (by
    intro a ha τ
    have h1 := sameKey_shared _ _ _ _ _ _ (IOR.draw Z.D (ldBrNx G kp Sb Z St₀) (LdBrE G kp E₀)) N
      (fun a => (a.1.1, a.2.1)) (fun b => (b.1.1, b.2.1))
      (fun k τ => (batNx Z.ze k.1 (drawn τ), k.2)) (fun a τ b hb => by
        obtain rfl := Option.some.inj hb
        rfl) _ ha τ
    refine cast (congrArg (SameKey _) ?_) h1
    funext j
    cases a j <;> rfl)
  have k' := knowB_conseq _ _ _ _ _ _ _ _ N _ (SameKey (ldRunAct G Sb St₀ E₀)) _ _ _ _ _ _ _ _ k (by
    intro a ha j j' b b' hb hb'
    obtain ⟨aj, haj, h2⟩ := Option.bind_eq_some_iff.mp hb
    obtain ⟨aj', haj', h2'⟩ := Option.bind_eq_some_iff.mp hb'
    obtain rfl := Option.some.inj h2
    obtain rfl := Option.some.inj h2'
    exact ha j j' aj aj' haj haj') (fun _ h => h) (fun _ _ _ h => h) (fun _ _ h => h)
  have e : RoundSplits.const (RAnn.ofShared .sh) (ldRunE G kp Sb sl Z St₀ E₀ T).shape =
      RoundSplits.app (s := (ldBridge G kp Sb Z St₀ E₀).shape) (RoundSplits.const (RAnn.ofShared .sh) _)
        (RoundSplits.app (s := T.R.shape) (t := []) (RoundSplits.const (RAnn.ofShared .sh) _) PUnit.unit) :=
    (RoundSplits.const_app _ (ldBridge G kp Sb Z St₀ E₀).shape (T.R.shape ++ [])).trans
      (congrArg _ (RoundSplits.const_app _ T.R.shape []))
  rw [e]
  exact knowB_cf _ _ _ _ _ _ _ _ N _ _ _ _ _ _ _ hW.good.onOut k'

/-! ## As links of a chain in a batch -/

section
variable {E : Type} [Field E] [Fintype E] {S : Sig E}

/-- the test D in every slot, in local rounds -/
def LdRunD.linkLo (D : LdRunD S) {St₀ Wp : Type} {E₀ : ExtSpec}
    (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) :
    LinkA Unit (S.jointCf (D.pre A₀)) ((S.sub D.kp).jointCf A₀) :=
  ⟨D.link A₀ d d', RoundSplits.allLocal _, (D.link A₀ d d').P.err⟩

/-- the test D once, by the shared part -/
def LdRunD.linkSh (D : LdRunD S) {St₀ Wp : Type} {E₀ : ExtSpec}
    (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) :
    LinkA Unit (S.jointCf (D.pre A₀)) ((S.sub D.kp).jointCf A₀) :=
  ⟨D.link A₀ d d', RoundSplits.const (RAnn.ofShared .sh) _, (D.link A₀ d d').P.err⟩

end

namespace Spec

/-- The slot's own test as a link. States, if `D.OK` (Cb/Ld/LdLinCloseRuns.lean): `KB` between any
two keys such that the new key is a function of the old one. -/
def ldRunB_link_local : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (St₀ Wp : Type) (E₀ : ExtSpec)
      (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp)
      (d' : LdBrW D.G D.kp Wp) (N : ℕ) (kA : JKey (S.jointCf (D.pre A₀)))
      (kB : JKey ((S.sub D.kp).jointCf A₀)) (F : kA.κ → kB.κ),
    D.OK → (∀ a τ b, (D.link A₀ d d').R.red.out a τ = some b → kB.key b = F (kA.key a)) →
    (D.linkLo A₀ d d').KB N kA kB

/-- The shared test as a link. States `KB`, if `D.OK`, the acting part is a function of the old key,
and the new key is a function of the old key and the transcript. -/
def ldRunB_link_shared : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (St₀ Wp : Type) (E₀ : ExtSpec)
      (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp)
      (N : ℕ) (kA : JKey (S.jointCf (D.pre A₀))) (kB : JKey ((S.sub D.kp).jointCf A₀))
      (act : kA.κ → ((D.G.Row D.B → E) × (∀ ν, D.G.RowSt D.Sb ν)) × D.G.C.ext.Str)
      (F : kA.κ → Tr (D.link A₀ d d').R.shape → kB.κ),
    D.OK → (∀ a, ldRunAct D.G D.Sb St₀ E₀ a = act (kA.key a)) →
    (∀ a τ b, (D.link A₀ d d').R.red.out a τ = some b → kB.key b = F (kA.key a) τ) →
    (D.linkSh A₀ d d').KB N kA kB

end Spec

theorem ldRunB_link_local : Spec.ldRunB_link_local := by
  intro E _ _ S D St₀ Wp E₀ A₀ d d' N kA kB F hD hF
  exact ⟨knowB_conseq _ _ _ _ _ _ _ _ N _ _ _ _ _ _ _ _ _ _
      (ldRunB_local E D.B St₀ Wp S D.G D.kp D.Sb D.sl D.Z D.L E₀ A₀ D.hc d d' D.T D.t N hD.ev
        hD.list hD.fits hD.tail)
      (fun _ _ => trivial) (fun _ h => h) (fun _ _ _ h => h) (fun _ _ h => h),
    sameKey_any _ _ _ _ _ _ (D.link A₀ d d').R _ N kA.key kB.key F hF⟩

theorem ldRunB_link_shared : Spec.ldRunB_link_shared := by
  intro E _ _ S D St₀ Wp E₀ A₀ d d' N kA kB act F hD hact hF
  refine ⟨knowB_conseq _ _ _ _ _ _ _ _ N _ _ _ _ _ _ _ _ _ _
      (ldRunB_shared E D.B St₀ Wp S D.G D.kp D.Sb D.sl D.Z D.L E₀ A₀ D.hc d d' D.T D.t N hD.ev
        hD.list hD.fits hD.tail)
      (fun a ha j j' aj aj' hj hj' => ?_) (fun _ h => h) (fun _ _ _ h => h) (fun _ _ h => h),
    sameKey_shared _ _ _ _ _ _ (D.link A₀ d d').R N kA.key kB.key F hF⟩
  rw [hact aj, hact aj', ha j j' aj aj' hj hj']

end Cb
