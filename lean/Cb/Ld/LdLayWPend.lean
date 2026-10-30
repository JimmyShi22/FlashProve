-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLayWPend.lean: masks that are pending across the range check's draw:
  (1) under the hypotheses of `Spec.ldLayW_pend`, in every first reference segment that meets the
    clause "lay", the own masks of the digits' lookup stand in messages that are open at the
    segment's entry and, for some reading RdL, are still fresh after the whole chain up to that
    lookup, the draw included;
  (2) under the hypotheses of `Spec.ldLayW_pend_last`, a fact that the clause "layB" names is fresh
    after the whole chain up to the last three moves: all draws and all closings included.

Definitions, statements (in `Cb.Spec`) and proofs: assemblies (`Link.GivesAt`, `Link.RoomAt`:
Cb/Ld/LdLayWGive.lean). For all data: no toy occurs here.
A fact: A `MaskFact W` is a reading `kc` of witnesses of type W into a type `Kc`, a finite,
non-empty type `Mk`, and a map `put : Mk → Kc → Kc`.

Why: the clauses lay, layT, layB of the request's record (Cb/Req1/LdReqRefStd.lean) are recursions
on lists. A reader who asks "is a mask really pending across a step at which the honest prover can
give up?" wants the property itself, of a chain as one link (`c.FreshS`: Cb/Req1/LdSegFreshS.lean:
given all that the chain shows, the masks are still uniform, and independent of the rest of what is
read) (exactly: `Honest.Fresh`, Ior/KnowCollRulesMask.lean), for a chain that visibly holds the
draw.

Main names:
  `S.upTo c₀`: the chain up to the digits' lookup of the segment S, after c₀.
  `Spec.ldLayW_pend`: E of characteristic pp, `first.Hyp`, `S.OK pp`, and the clause "lay" at the
    first segment S ⇒ for some reading RdL: the digits' lookup is a masked block; its own masks are
    entries of oracle messages that are open at the segment's entry; they are `FreshS` after
    `S.upTo` (the first sending).
  `Spec.ldLayW_pend_gives`: under E of characteristic pp, `first.Hyp`, `S.OK pp`: that chain, as
    one link, gives up at the core k with at least the probability of the window event (`rngEv`,
    Cb/Ld/LdRng.lean) of k's matrix.
  `Spec.ldLayW_pend_cut`.
  `ldReqUpToLast`: the chain up to the last three moves of the reference request r with one first
    sending (`ldReqRef1`): first sending; all segments with their closings; the last segment.
  `Spec.ldLayW_pend_last`: `r.Hyp`, `r.ZkS`, `T.tail.Hyp` ⇒ every fact f that the last segment
    hands on from a fact that is laid before it (the form of the clause "layB") is `FreshS` after
    that chain.
  `Spec.ldLayW_pend_last_gives`: under `r.Hyp`, `T.tail.Hyp`: that chain gives up at k with at
    least the probability of the last segment's window event.

Limits: (1) is for a first segment (behind one sending); "open at the entry" is shown, not "free
entries of the first sending's layout" (before the entry step the first sending is the only sending:
by the form of the term). (2) is for the fact as layB has it: the wide fact of the final batching's
own masks; the step from the wide fact to the block's own fact is inside `r.ZkS` and not repeated
here. This file does not say that a chain here has room (does not always give up):
Cb/Ld/LdLayWRoom.lean for the whole request; for the two chains here `Spec.ldLayW_upTo_room`,
`Spec.ldLayW_upToLast_room` (Cb/Ld/LdLayWRoomZk.lean), with `RoomD` among their hypotheses. It says
nothing on splittings.
The proof of (1) repeats, for its middle part, a step of the proof of `Cb.ldSegRefAll_zk`
(Cb/Req1/LdSegRefAllZkProofs.lean), where it is not stated by itself.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLayWRoom
import Cb.Req1.LdReqRefLayJ
import Cb.Req1.LdSegRefAllZkProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp
open scoped ENNReal

/-- The chain up to the digits' lookup of the segment S, after a chain c₀: entry step; front
(`S.A.V.prog`); read, range check (with the draw); the shift before the lookup. -/
def LdRefS.upTo {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {a : LdStage E Kc}
    (S : LdRefS E Kc I a) {A₀ : Joint Kc} (c₀ : Chain Kc A₀ a.J) :
    Chain Kc A₀ (S.A.Xa.Q.lkS S.A.Xa.mult).J :=
  (S.A.Xa.Q.pre S.A.Xa.mult).onto (S.A.Xa.Q.D.prog.onto (S.A.V.prog.onto (c₀.append S.entry.chain)))

/-- The chain up to the last three moves of the request: first sending; the segments; the last
segment. -/
def ldReqUpToLast {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] (R : LdORE F E Kc) {a : LdStage E Kc} (first : LdSendD a) (b : LdStage E Kc)
    (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b) : Chain Kc a.J R.X.src.J :=
  T.tail.onto (L.segs.onto (.one first.link))

namespace Spec

/-- Pending across the draw. The hypothesis on zero knowledge is the clause "lay" of the request's
record at its first segment, beside its hypotheses (`first.Hyp`, `S.OK pp`). (not all hypotheses are
named here: see the statement below) -/
def ldLayW_pend : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (I : LdRefIx E) (a : LdStage E Kc)
    (first : LdSendD a) (S : LdRefS E Kc I first.tgt),
    first.Hyp → S.OK pp →
    S.A.ZkAt pp (fun f =>
      ∃ g,
        MaskFact.JCl (fun f => first.link.H.Fresh a.J.rels.rel first.link.P.bud f.kc f.Mk f.put) g ∧
        S.Enters g f) →
    ∃ RdL : S.A.Xa.Q.T.Ent → Prop,
      -- the digits' lookup is a masked block: its messages are hidden by masks that stand in its
      -- input witness in this sense: `Link.GoodM` (Ior/KnowCollRulesChain.lean; `GoodM`,
      -- Ior/Masked.lean)
      S.A.Xa.link.GoodM (S.A.Xa.dm RdL) ∧
      -- its own masks are entries of oracle messages that are open at the segment's entry
      (∀ j, S.A.Xa.A.swAll j → ∃ n, S.A.up n = j) ∧
      -- given all that the chain up to the lookup shows, they are still uniform, and independent
      -- of the rest of what the lookup reads in this sense: `Chain.FreshS`
      -- (Cb/Req1/LdSegFreshS.lean: `Honest.Fresh`, Ior/KnowCollRulesMask.lean, of the chain as one
      -- link)
      (S.upTo (.one first.link)).FreshS (S.A.Xa.dm RdL).kc (S.A.Xa.dm RdL).Mk (S.A.Xa.dm RdL).put

/-- under the hypotheses below: that chain gives up with at least the probability of the window
event -/
def ldLayW_pend_gives : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (I : LdRefIx E) (a : LdStage E Kc)
      (first : LdSendD a) (S : LdRefS E Kc I first.tgt) (d : a.J.W) (k : Kc),
    first.Hyp → S.OK pp →
    ((S.upTo (.one first.link)).link d).GivesAt k (prRho (rngEv S.A.Xa.Q.D.p (S.A.Xa.Q.D.c.yz k)))

/-- The segment's body after c₀ is: that chain; the lookup's link; the rest. -/
def ldLayW_pend_cut : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E) (a : LdStage E Kc) (S : LdRefS E Kc I a)
      (A₀ : Joint Kc) (c₀ : Chain Kc A₀ a.J),
    S.seg.body.onto c₀ = S.K.tensor.onto (((S.upTo c₀).snoc S.A.Xa.link).append S.A.Y.step.chain)

/-- Pending across all draws and closings. The premise on f is the form of the clause "layB". (not
all hypotheses are named here: see the statement below) -/
def ldLayW_pend_last : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R : LdORE F E Kc)
      (a : LdStage E Kc) (first : LdSendD a) (b : LdStage E Kc) (L : LdRefL E Kc R.ix first.tgt b)
      (T : LdRefT R b) (f : MaskFact R.X.src.J.W),
    (ldReqRef1 R first b L T).Hyp → (ldReqRef1 R first b L T).ZkS → T.tail.Hyp →
    (∃ g,
      L.LaidJ (ldReqRef1 R first b L T).base₀ g ∧
      ∀ Y : MaskFact b.J.W → Prop, Y g → T.tail.After Y f) →
    (ldReqUpToLast R first b L T).FreshS f.kc f.Mk f.put

def ldLayW_pend_last_gives : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R : LdORE F E Kc)
      (a : LdStage E Kc) (first : LdSendD a) (b : LdStage E Kc) (L : LdRefL E Kc R.ix first.tgt b)
      (T : LdRefT R b) (d : a.J.W) (k : Kc),
    (ldReqRef1 R first b L T).Hyp → T.tail.Hyp →
    ((ldReqUpToLast R first b L T).link d).GivesAt
      k (prRho (rngEv T.A.Xa.Q.D.p (T.A.Xa.Q.D.c.yz k)))

end Spec

section
variable {E Kc : Type} [Field E] [Fintype E]

/-- two lists in a row, after a chain -/
theorem LdProg.onto_app {A₀ : Joint Kc} {a b c : LdStage E Kc} (c₀ : Chain Kc A₀ a.J)
    (p : LdProg a b) (q : LdProg b c) :
    (p.app q).onto c₀ = q.onto (p.onto c₀) := by
  induction q with
  | nil => rw [LdProg.app_nil, LdProg.onto_nil]
  | snoc q m ih => rw [LdProg.app_snoc, LdProg.onto_snoc, LdProg.onto_snoc, ih]

/-- the hypotheses of the parts of a segment's body -/
theorem LdRefS.parts_hyp {I : LdRefIx E} {a : LdStage E Kc} (S : LdRefS E Kc I a) (h : S.seg.Hyp) :
    S.entry.Hyp ∧ S.A.V.prog.Hyp ∧ S.A.Xa.Q.D.prog.Hyp ∧ (S.A.Xa.Q.pre S.A.Xa.mult).Hyp := by
  have hb : (((LdProg.nil a).snoc S.entry).app
      (S.A.Y.body _ (S.A.X.prog S.K.St₁ S.K.fz S.K.Az))).Hyp := h.body
  unfold LdBodyD.body at hb
  rw [ldProg_app_hyp, LdProg.hyp_snoc, ldProg_app_hyp, LdProg.hyp_snoc,
    ldProg_app_hyp, ldProg_app_hyp] at hb
  have hd := hb.2.1.1.2
  unfold LdDgP.prog at hd
  rw [LdProg.hyp_snoc] at hd
  exact ⟨hb.1.2, hb.2.1.1.1.1, hb.2.1.1.1.2, hd.1⟩

theorem LdRefS.upTo_allB {I : LdRefIx E} {a : LdStage E Kc} (S : LdRefS E Kc I a) (h : S.seg.Hyp)
    {A₀ : Joint Kc} (c₀ : Chain Kc A₀ a.J) (h0 : c₀.AllB) : (S.upTo c₀).AllB := by
  obtain ⟨h1, h2, h3, h4⟩ := S.parts_hyp h
  exact LdProg.onto_allB _ _
    (LdProg.onto_allB _ _
      (LdProg.onto_allB _ _
        (((all_append Kc _ _ _ c₀ S.entry.chain).1).2 ⟨h0, ldSeg_mv E Kc _ _ _ h1⟩) h2) h3) h4

end

open Classical in
theorem ldLayW_pend : Spec.ldLayW_pend := by
  intro E Kc _ _ pp _ I a first S hF hS hZ
  obtain ⟨hne, W, F, κ, RdL, hG, hFo, hFF, hL⟩ := hZ
  haveI := hne
  have h := hS.body
  obtain ⟨h1, h2, h3, h4⟩ := S.parts_hyp (ldReqRef_seg E Kc pp I _ S hS)
  refine ⟨RdL, ldSegRef_asm_goodM E Kc _ _ pp S.A.Xa RdL h.inj h.named h.adm hL.maskL hL.rdL,
    hL.inL, ?_⟩
  -- the lookup's fact after front, range check and shift, given the facts at the entry
  have pOK : (S.A.plL RdL).OK :=
    (ldLkpPl2_asm E S.A.Xa.A I.C.E0 S.A.Xa.Q.T.Msg (I.C.PIdx × (S.A.W₁ × S.A.Gh))
      Kc S.A.Xa.Q.T.ents RdL S.A.Xa.Dt hL.maskL).1.1
  have pAt : ∀ j, (S.A.plL RdL).At j ↔ S.A.Xa.A.swAll j :=
    (ldLkpPl2_asm E S.A.Xa.A I.C.E0 S.A.Xa.Q.T.Msg (I.C.PIdx × (S.A.W₁ × S.A.Gh))
      Kc S.A.Xa.Q.T.ents RdL S.A.Xa.Dt hL.maskL).1.2
  have wL :=
    ldSegRefX_lk E Kc pp _ S.A W F κ _ S.A.ownL (S.A.Xa.dm RdL).Mk (S.A.valL RdL) h hG hFo hL.passL
  have fL : (S.A.Xa.Q.pre S.A.Xa.mult).After
      (S.A.Xa.Q.D.prog.After
        (S.A.V.prog.After (fun f =>
          ∃ g,
            MaskFact.JCl
              (fun f => first.link.H.Fresh a.J.rels.rel first.link.P.bud f.kc f.Mk f.put) g ∧
            S.Enters g f)))
      (S.A.Xa.dm RdL).fact := by
    unfold LdDgP.pre at wL ⊢
    rw [LdProg.after_snoc] at wL ⊢
    refine segWide_read E Kc _ (S.A.Xa.Q.lkS S.A.Xa.mult) _ _ W.Rd2 W.Rr2 (S.A.own2 S.A.ownL)
      (S.A.Xa.dm RdL).Mk (S.A.val2 (S.A.valL RdL)) S.A.Xa.Q.T.Ent (S.A.plL RdL).I id
      (S.A.plL RdL).pl (fun M => (S.A.plL RdL).ve M) RdL (fun w => S.A.Xa.Q.T.ents w.1)
      (S.A.Xa.dm RdL).kc (S.A.Xa.dm RdL).put Function.injective_id pOK.inj (fun _ _ _ => rfl)
      (fun _ _ _ j hj => absurd rfl (hj j)) ?_ ?_ (fun M k => pOK.put M k) ?_ ?_ hL.wideL ?_ wL
    · intro w j hj
      exact if_pos hj
    · intro w j hj
      exact if_neg hj
    · intro n
      exact (S.A.own2_iff S.A.Xa.A.swAll hL.inL n).trans (pAt n).symm
    · intro M i
      obtain ⟨n, hn⟩ := hL.inL ((S.A.plL RdL).pl i) ((pAt _).1 ⟨i, rfl⟩)
      rw [← hn, S.A.val2_up]
      show Function.extend (S.A.plL RdL).pl ((S.A.plL RdL).ve M) (fun _ => 0) (S.A.up n) = _
      rw [hn]
      exact pOK.inj.extend_apply _ _ i
    · intro i
      exact hL.rdL _ (Or.inr ((pAt _).1 ⟨i, rfl⟩))
  -- after the first sending
  have b0 : (Chain.one first.link).AllB := (allB_one _).2 (goodB_of_goodT' (first.goodT hF))
  have f0 : ∀ g,
      MaskFact.JCl (fun f => first.link.H.Fresh a.J.rels.rel first.link.P.bud f.kc f.Mk f.put) g →
      (Chain.one first.link).FreshS g.kc g.Mk g.put :=
    freshS_jcl Kc _ _ _ _ fun g hg =>
      freshS_of_for Kc _ _ _ _ g.kc g.Mk g.put b0 ((freshFor_one _ _ _ _).2 hg)
  -- through the entry step
  have e1 : ((LdProg.nil first.tgt).snoc S.entry).onto (.one first.link) =
      (Chain.one first.link).append S.entry.chain := by
    rw [LdProg.onto_snoc, LdProg.onto_nil]
  have hp1 : ((LdProg.nil first.tgt).snoc S.entry).Hyp :=
    (LdProg.hyp_snoc _ _).2 ⟨LdProg.hyp_nilK _, h1⟩
  have f1 :=
    ldReqS_prog_fresh E Kc _ _ _ (.one first.link) ((LdProg.nil first.tgt).snoc S.entry) _ b0 hp1 f0
  rw [e1] at f1
  have b1 : ((Chain.one first.link).append S.entry.chain).AllB := e1 ▸ LdProg.onto_allB _ _ b0 hp1
  have f2 := ldReqS_prog_fresh E Kc _ _ _ _ S.A.V.prog _ b1 h2 f1
  have b2 := LdProg.onto_allB S.A.V.prog _ b1 h2
  have f3 := ldReqS_prog_fresh E Kc _ _ _ _ S.A.Xa.Q.D.prog _ b2 h3 f2
  have b3 := LdProg.onto_allB S.A.Xa.Q.D.prog _ b2 h3
  have f4 := ldReqS_prog_fresh E Kc _ _ _ _ (S.A.Xa.Q.pre S.A.Xa.mult) _ b3 h4 f3
  refine f4 (S.A.Xa.dm RdL).fact ?_
  -- the facts at the entry are among those that the entry step hands on
  have m0 : ∀ f,
      (∃ g,
        MaskFact.JCl (fun f => first.link.H.Fresh a.J.rels.rel first.link.P.bud f.kc f.Mk f.put) g ∧
        S.Enters g f) →
      ((LdProg.nil first.tgt).snoc S.entry).After
        (MaskFact.JCl fun f => first.link.H.Fresh a.J.rels.rel first.link.P.bud f.kc f.Mk f.put)
        f := by
    rintro f ⟨g, hg, he⟩
    rw [LdProg.after_snoc, LdProg.after_nil]
    exact he _ hg
  exact (LdProg.mono E Kc _ _ _
      ((LdProg.mono E Kc _ _ _ ((LdProg.mono E Kc S.A.V.prog _ _ m0).1)).1)).1
    _ fL

theorem ldLayW_pend_gives : Spec.ldLayW_pend_gives := by
  intro E Kc _ _ pp _ I a first S d k hF hS
  have hs := ldReqRef_seg E Kc pp I _ S hS
  refine ldLayW_gives Kc _ _ _ d k _
    (S.upTo_allB hs _ ((allB_one _).2 (goodB_of_goodT' (first.goodT hF)))) fun h => ?_
  unfold LdRefS.upTo at h
  rw [ldLayW_onto, ldLayW_onto] at h
  exact ldLayW_rr_at E Kc _ _ _ S.A.Xa.Q.D h.1.2 (ldLayW_draw_gives E Kc _ _ S.A.Xa.Q.D k)

theorem ldLayW_pend_cut : Spec.ldLayW_pend_cut := by
  intro E Kc _ _ I a S A₀ c₀
  show (((LdProg.nil a).snoc S.entry).app
      (S.A.Y.body _ (S.A.X.prog S.K.St₁ S.K.fz S.K.Az))).onto c₀ = _
  unfold LdBodyD.body LdRefS.upTo LdDgP.prog
  rw [LdProg.onto_app, LdProg.onto_app, LdProg.onto_snoc, LdProg.onto_app, LdProg.onto_app,
    LdProg.onto_snoc, LdProg.onto_snoc, LdProg.onto_nil]
  have c4 : (LdMv.sub (S.A.Y.G.Q.lkS S.A.Y.mult)
        (S.A.Y.G.Q.lkT S.A.Y.G.ent S.A.Y.G.n) S.A.Y.lk).chain =
      .one S.A.Xa.link := by
    rw [LdMv.chain]; rfl
  rw [c4, append_one]
  rfl

theorem ldLayW_pend_last : Spec.ldLayW_pend_last := by
  intro F E Kc _ _ _ _ _ R a first b L T f hH hZ hT hf
  obtain ⟨g, hg, hY⟩ := hf
  have h0 : (Chain.one first.link).Ok := (ok_one _).2 (first.goodT hH.first)
  have eb : ∀ g, (ldReqRef1 R first b L T).base₀ g →
      first.link.H.Fresh a.J.rels.rel first.link.P.bud g.kc g.Mk g.put := fun g hg => by
    have h' : (LdProg.nil first.tgt).After
        (fun f => first.link.H.Fresh a.J.rels.rel first.link.P.bud f.kc f.Mk f.put) g := hg
    rwa [LdProg.after_nil] at h'
  have hb : ∀ g, (ldReqRef1 R first b L T).base₀ g →
      (Chain.one first.link).FreshS g.kc g.Mk g.put := fun g hg =>
    freshS_of_for Kc _ _ _ _ g.kc g.Mk g.put
      ((ok_of_allT Kc _ _ _).2 h0) ((freshFor_one _ _ _ _).2 (eb g hg))
  obtain ⟨o, fr⟩ := LdSegs.ontoS E Kc L.segs _ _ (okS_of_ok Kc _ _ _ h0) hb hH.segs hZ.segs
  exact ldReqS_prog_fresh E Kc _ _ _ _ T.tail _ (allB_of_okS Kc _ _ _ o) hT fr f
    (hY _ (ldReqRefLayJ_after E Kc _ _ _ L _ g hg))

theorem ldLayW_pend_last_gives : Spec.ldLayW_pend_last_gives := by
  intro F E Kc _ _ _ _ _ R a first b L T d k hH hT
  have b0 : (Chain.one first.link).AllB := (allB_one _).2 (goodB_of_goodT' (first.goodT hH.first))
  refine ldLayW_gives Kc _ _ _ d k _
    (LdProg.onto_allB _ _ (LdSegs.onto_allB _ _ b0 hH.segs) hT) fun h => ?_
  unfold ldReqUpToLast at h
  rw [ldLayW_onto] at h
  exact ldLayW_tail_at F E Kc _ R b T h.2 (ldLayW_draw_gives E Kc _ _ T.A.Xa.Q.D k)

end Cb
