-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/RecutProofs.lean: properties of a protocol whose rounds are split and merged.

A plan (`XPlan`, Iop/Recut.lean) goes through a protocol's rounds and keeps a round, splits off a
first part of it, or merges it with the next. `InteractiveOracleProof.recut` is the protocol after a plan P (words of
this library: lean/GLOSSARY.md).
  `recutLength`: `Spec.recutLength`: one round more for each split, one less for each merge
  `InteractiveOracleProof.Sound.recut`: round-by-round soundness, with the errors `Err.recut P ε` (statement and
      hypotheses: below; the errors: Iop/Recut.lean)
  under `XPlan.OK` (every split satisfies `RCut.OK`; between two merged prover messages the
      challenge has one value; between two merged challenges the prover message has one value):
      locality, acceptance, the probability of the abort set (`Honest.withheld`), honest-verifier
      zero knowledge with the same bound, and string oracles are preserved
It also has the simulator as a term (`simRecut`, `simRecut_good`).
The proofs treat a split as in Iop/SplitProofs.lean, the two merges as in Iop/JoinProofs.lean.
Limits: what the head of Iop/Recut.lean lists as not said is not said here either.
-/
import Iop.Recut
import Iop.SplitProofs
import Iop.JoinProofs
noncomputable section -- Lean tags what it cannot compile

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. The maps to the old rounds -/

theorem recutLength : Spec.recutLength := by
  intro s P
  induction P with
  | nil => rfl
  | keep r P ih =>
      show P.shape.length + 1 + P.joins = _ + 1 + P.cuts
      omega
  | cut c P ih =>
      have ih' : P.shape.length + P.joins = _ + 1 + P.cuts := ih
      show P.shape.length + 1 + P.joins = _ + 1 + (P.cuts + 1)
      omega
  | msg r1 r2 u P ih =>
      have ih' : P.shape.length + P.joins = _ + 1 + P.cuts := ih
      show P.shape.length + (P.joins + 1) = _ + 1 + 1 + P.cuts
      omega
  | chal r1 r2 np P ih =>
      have ih' : P.shape.length + P.joins = _ + 1 + P.cuts := ih
      show P.shape.length + (P.joins + 1) = _ + 1 + 1 + P.cuts
      omega

theorem Tr.rho_old {s : Shape} (P : XPlan s) :
    ∀ τ : Tr P.shape, (Tr.old P τ).rho = Rho.old P τ.rho := by
  induction P with
  | nil => intro _; rfl
  | keep r P ih =>
      rintro ⟨m, c, τ⟩
      show (c, (Tr.old P τ).rho) = (c, Rho.old P τ.rho)
      rw [ih]
  | cut c P ih =>
      rintro ⟨a, u, τ⟩
      exact (RCut.rho_glue a (Tr.old P τ)).trans (ih τ)
  | msg r1 r2 u P ih =>
      intro τ
      refine (Tr.rho_unMsg u (Tr.old P τ)).trans ?_
      rw [ih]
      rfl
  | chal r1 r2 np P ih =>
      intro τ
      refine (Tr.rho_unChal (Tr.old P τ)).trans ?_
      rw [ih]
      rfl

theorem Tr.plains_old {s : Shape} (P : XPlan s) :
    ∀ τ : Tr P.shape, (Tr.old P τ).plains = Plains.old P τ.plains := by
  induction P with
  | nil => intro _; rfl
  | keep r P ih =>
      rintro ⟨m, c, τ⟩
      show (m.2, (Tr.old P τ).plains) = (m.2, Plains.old P τ.plains)
      rw [ih]
  | cut c P ih =>
      rintro ⟨a, u, τ⟩
      refine (RCut.plains_glue a (Tr.old P τ)).trans ?_
      rw [ih]
      rfl
  | msg r1 r2 u P ih =>
      intro τ
      refine (Tr.plains_unMsg u (Tr.old P τ)).trans ?_
      rw [ih]
      rfl
  | chal r1 r2 np P ih =>
      intro τ
      refine (Tr.plains_unChal (Tr.old P τ)).trans ?_
      rw [ih]
      rfl

theorem Plains.new_old {s : Shape} (P : XPlan s) :
    ∀ pl : Plains P.shape, Plains.new P (Plains.old P pl) = pl := by
  induction P with
  | nil => intro _; rfl
  | keep r P ih =>
      rintro ⟨a, pl⟩
      show (a, Plains.new P (Plains.old P pl)) = (a, pl)
      rw [ih]
  | cut c P ih =>
      rintro ⟨a, pl⟩
      show ((c.plain (c.plain.symm (a, (Plains.old P pl).1))).1,
          Plains.new P ((c.plain (c.plain.symm (a, (Plains.old P pl).1))).2, (Plains.old P pl).2)) =
        (a, pl)
      rw [Equiv.apply_symm_apply]
      exact congrArg (Prod.mk a) (ih pl)
  | msg r1 r2 u P ih => exact fun pl => ih pl
  | chal r1 r2 np P ih => exact fun pl => ih pl

theorem OSym.new_old {s : Shape} (P : XPlan s) :
    ∀ (p : OPos P.shape) (a : OSym P.shape p), OSym.new P p (OSym.old P p a) = a := by
  induction P with
  | nil => intro p; exact Empty.elim p
  | keep r P ih =>
      rintro (p | q) a
      · rfl
      · exact ih q a
  | cut c P ih =>
      rintro (p | q) a
      · rfl
      · show OSym.new P q (c.symDown _ (c.symUp _ (OSym.old P q a))) = a
        rw [RCut.symDown_symUp, ih]
  | msg r1 r2 u P ih =>
      intro p a
      show OSym.new P p (OSym.reMsg _ (OSym.unMsg _ (OSym.old P p a))) = a
      rw [OSym.reMsg_unMsg, ih]
  | chal r1 r2 np P ih =>
      intro p a
      show OSym.new P p (OSym.reChal np _ (OSym.unChal np _ (OSym.old P p a))) = a
      rw [OSym.reChal_unChal, ih]

/-- Under `P.OK`, the answers of the prover's oracles do not change. -/
theorem Tr.read_old {s : Shape} (P : XPlan s) (hP : P.OK) :
    ∀ (τ : Tr P.shape) (p : OPos P.shape),
      (Tr.old P τ).read (OPos.oldEquiv P p) = OSym.old P p (τ.read p) := by
  induction P with
  | nil => intro _ p; exact Empty.elim p
  | keep r P ih =>
      rintro ⟨m, c, τ⟩ (p | q)
      · rfl
      · exact ih hP τ q
  | cut c P ih =>
      rintro ⟨a, u, τ⟩ (p | q)
      · exact RCut.read_glue_inl hP.1 a (Tr.old P τ) p
      · refine (RCut.read_glue_inr hP.1 a (Tr.old P τ) (OPos.oldEquiv P q)).trans ?_
        rw [ih hP.2]
        rfl
  | msg r1 r2 u P ih =>
      intro τ p
      refine (Tr.read_unMsg u (Tr.old P τ) (OPos.oldEquiv P p)).trans ?_
      rw [ih hP.2]
      rfl
  | chal r1 r2 np P ih =>
      intro τ p
      refine (Tr.read_unChal np (Tr.old P τ) (OPos.oldEquiv P p)).trans ?_
      rw [ih hP.2]
      rfl

/-- Under `P.OK`, the transcript of a run of the new strategy, mapped to the old rounds, is that of
the run of the old strategy at the old randomness. -/
theorem Strat.run_recut {s : Shape} {β : Type} (P : XPlan s) (hP : P.OK) :
    ∀ (S : Strat s β) (ρ : Rho P.shape),
      Tr.old P ((Strat.recut P S).run ρ).1 = (S.run (Rho.old P ρ)).1 := by
  induction P with
  | nil => intro _ _; rfl
  | keep r P ih =>
      rintro ⟨m, k⟩ ⟨c, ρ⟩
      show (m, c, Tr.old P ((Strat.recut P (k c)).run ρ).1) = (m, c, ((k c).run (Rho.old P ρ)).1)
      rw [ih hP]
  | @cut r s c P ih =>
      rintro ⟨m, k⟩ ⟨u, ρ⟩
      show c.glue (c.left m) (Tr.old P ((Strat.recut P (c.right m, k)).run ρ).1) =
        (Strat.run (s := r :: s) (m, k) (Rho.old (s := c.snd :: s) P ρ)).1
      rw [ih hP.2]
      generalize Rho.old P ρ = ρ'
      obtain ⟨ch, ρ''⟩ := ρ'
      show (c.join (c.left m) (c.right m), ch, ((k ch).run ρ'').1) = (m, ch, ((k ch).run ρ'').1)
      rw [RCut.join_left_right]
  | @msg r1 r2 s u P ih =>
      rintro ⟨m, k⟩ ρ
      show Tr.unMsg u
          (Tr.old P ((Strat.recut P
              (show Strat (r1.joinMsg r2 :: s) β
                from (Round.msgPair m (k u).1, (k u).2))).run ρ).1) =
        (Strat.run (s := r1 :: r2 :: s) (m, k) (u, (Rho.old P ρ : Rho (r1.joinMsg r2 :: s)))).1
      rw [ih hP.2]
      generalize Rho.old P ρ = ρ'
      obtain ⟨c2, ρ''⟩ := ρ'
      rcases hk : k u with ⟨m2, k2⟩
      show _ = (m, u, (Strat.run (s := r2 :: s) (k u) (c2, ρ'')).1)
      rw [hk]
      rfl
  | @chal r1 r2 s np P ih =>
      rintro ⟨m, k⟩ ρ
      show Tr.unChal
          (Tr.old P ((Strat.recut P
              (show Strat (r1.joinChal r2 :: s) β from (m, fun c => (k c.1).2 c.2))).run ρ).1) =
        (Strat.run (s := r1 :: r2 :: s) (m, k)
          ((Rho.old P ρ : Rho (r1.joinChal r2 :: s)).1.1,
            (Rho.old P ρ : Rho (r1.joinChal r2 :: s)).1.2,
            (Rho.old P ρ : Rho (r1.joinChal r2 :: s)).2)).1
      rw [ih hP.2]
      generalize Rho.old P ρ = ρ'
      obtain ⟨⟨c1, c2⟩, ρ''⟩ := ρ'
      show _ = (m, c1, (Strat.run (s := r2 :: s) (k c1) (c2, ρ'')).1)
      rcases hk : k c1 with ⟨m2, k2⟩
      obtain rfl : m2 = r2.dMsg := hP.1 m2
      show (m, c1, r2.dMsg, c2, (((k c1).2 c2).run ρ'').1) = _
      rw [hk]
      rfl

/-! ## 2. The verifier randomness: a bijection, under `P.OK` -/

theorem Rho.new_old {s : Shape} (P : XPlan s) : ∀ ρ : Rho P.shape, Rho.new P (Rho.old P ρ) = ρ := by
  induction P with
  | nil => intro _; rfl
  | keep r P ih =>
      rintro ⟨c, ρ⟩
      show (c, Rho.new P (Rho.old P ρ)) = (c, ρ)
      rw [ih]
  | cut c P ih =>
      rintro ⟨u, ρ⟩
      show ((), Rho.new P (Rho.old P ρ)) = (u, ρ)
      rw [ih]
  | msg r1 r2 u P ih => exact fun ρ => ih ρ
  | chal r1 r2 np P ih => exact fun ρ => ih ρ

theorem Rho.old_new {s : Shape} (P : XPlan s) (hP : P.OK) :
    ∀ ρ : Rho s, Rho.old P (Rho.new P ρ) = ρ := by
  induction P with
  | nil => intro _; rfl
  | keep r P ih =>
      rintro ⟨c, ρ⟩
      show (c, Rho.old P (Rho.new P ρ)) = (c, ρ)
      rw [ih hP]
  | cut c P ih => exact fun ρ => ih hP.2 ρ
  | @msg r1 r2 s u P ih =>
      rintro ⟨c1, ρ⟩
      show (u, (Rho.old P
            (Rho.new P (show Rho (r1.joinMsg r2 :: s) from ρ)) : Rho (r1.joinMsg r2 :: s))) =
        (c1, ρ)
      rw [ih hP.2, hP.1 c1]
      rfl
  | @chal r1 r2 s np P ih =>
      rintro ⟨c1, c2, ρ⟩
      have e := ih hP.2 (show Rho (r1.joinChal r2 :: s) from ((c1, c2), ρ))
      show ((Rho.old P
            (Rho.new P
              (show Rho (r1.joinChal r2 :: s) from ((c1, c2), ρ))) : Rho (r1.joinChal r2 :: s)).1.1,
          (Rho.old P
            (Rho.new P
              (show Rho (r1.joinChal r2 :: s) from ((c1, c2), ρ))) : Rho (r1.joinChal r2 :: s)).1.2,
          (Rho.old P
            (Rho.new P
              (show Rho (r1.joinChal r2 :: s) from ((c1, c2), ρ))) : Rho (r1.joinChal r2 :: s)).2) =
        (c1, c2, ρ)
      rw [e]

def Rho.oldEquiv {s : Shape} (P : XPlan s) (hP : P.OK) : Rho P.shape ≃ Rho s :=
  ⟨Rho.old P, Rho.new P, Rho.new_old P, Rho.old_new P hP⟩

/-- Under `P.OK`, the preimage of a set of values of the verifier randomness has the same
probability. -/
theorem prRho_old {s : Shape} (P : XPlan s) (hP : P.OK) (S : Set (Rho s)) :
    prRho {ρ : Rho P.shape | Rho.old P ρ ∈ S} = prRho S := by
  unfold prRho
  rw [← map_unif_equiv (Rho.oldEquiv P hP), pr_map]
  rfl

/-! ## 3. Soundness -/

theorem Doomed.recutS {s : Shape} (P : XPlan s) :
    ∀ (ε : Err s) (bad : Tr s → Prop),
      Doomed s ε bad → Doomed P.shape (Err.recut P ε) (fun τ => bad (Tr.old P τ)) := by
  induction P with
  | nil => intro _ _ h; exact h
  | keep r P ih =>
      rintro ⟨e, ε⟩ bad h
      exact fun m => le_trans (cnt_mono fun c hc hd => hc (ih ε (fun τ => bad (m, c, τ)) hd)) (h m)
  | cut c P ih =>
      intro ε bad h
      refine fun a => le_of_eq (cnt_false fun _ hn => hn (ih ε (fun z => bad (c.glue a z)) ?_))
      obtain ⟨e, ε⟩ := ε
      exact fun b => h (c.join a b)
  | @msg r1 r2 s u P ih =>
      rintro ⟨e1, e2, ε⟩ bad h
      refine ih (e1 * Fintype.card r2.Chal + Fintype.card r1.Chal * e2, ε)
        (fun z => bad (Tr.unMsg u z)) fun m => ?_
      exact le_trans
        (cnt_slice_le
          (fun x : r1.Chal × r2.Chal =>
            ¬ Doomed s ε (fun τ => bad (Round.msgFst m, x.1, Round.msgSnd m, x.2, τ))) u)
        (h.two (Round.msgFst m) (Round.msgSnd m))
  | @chal r1 r2 s np P ih =>
      rintro ⟨e1, e2, ε⟩ bad h
      exact ih (e1 * Fintype.card r2.Chal + Fintype.card r1.Chal * e2, ε)
        (fun z => bad (Tr.unChal z)) fun m => h.two m r2.dMsg

theorem InteractiveOracleProof.Sound.recut {X : Type} {E : ExtSpec} {Q : InteractiveOracleProof X E} (P : XPlan Q.shape)
    {L : X → E.Str → Prop} {ε : Err Q.shape} (h : Q.Sound L ε) :
    (Q.recut P).Sound L (Err.recut P ε) :=
  fun x y hL => Doomed.recutS P ε _ (h x y hL)

/-! ## 5. Locality, acceptance, abort sets -/

section OneProtocol

variable {X : Type} {E : ExtSpec} {Q : InteractiveOracleProof X E} {Wt : Type}

theorem InteractiveOracleProof.mem_reads_recut
    (P : XPlan Q.shape) (x : X) (ρ : Rho P.shape) (pl : Plains P.shape) (p : OPos P.shape) :
    p ∈ (Q.recut P).reads x ρ pl ↔
    OPos.oldEquiv P p ∈ Q.reads x (Rho.old P ρ) (Plains.old P pl) := by
  show p ∈ (Q.reads x (Rho.old P ρ) (Plains.old P pl)).map (OPos.oldEquiv P).symm.toEmbedding ↔ _
  rw [Finset.mem_map_equiv, Equiv.symm_symm]

/-- The verifier reads as many positions as before. -/
theorem InteractiveOracleProof.card_reads_recut (P : XPlan Q.shape) (x : X) (ρ : Rho P.shape) (pl : Plains P.shape) :
    ((Q.recut P).reads x ρ pl).card = (Q.reads x (Rho.old P ρ) (Plains.old P pl)).card :=
  Finset.card_map _

theorem InteractiveOracleProof.IsLocal.recut (h : Q.IsLocal) {P : XPlan Q.shape} (hP : P.OK) :
    (Q.recut P).IsLocal := by
  intro x y y' τ τ' hρ hpl hext hrd
  refine h x y y' (Tr.old P τ) (Tr.old P τ') ?_ ?_ ?_ ?_
  · rw [Tr.rho_old, Tr.rho_old]
    exact congrArg (Rho.old P) hρ
  · rw [Tr.plains_old, Tr.plains_old]
    exact congrArg (Plains.old P) hpl
  · intro p hp
    rw [Tr.rho_old] at hp
    exact hext p hp
  · intro p hp
    rw [Tr.rho_old, Tr.plains_old] at hp
    obtain ⟨p', rfl⟩ := (OPos.oldEquiv P).surjective p
    rw [Tr.read_old P hP, Tr.read_old P hP]
    exact congrArg (OSym.old P p') (hrd p' ((InteractiveOracleProof.mem_reads_recut P x _ _ p').2 hp))

theorem Honest.mem_withheld_recut
    (H : Honest Q Wt) (P : XPlan Q.shape) (w : Wt) (x : X) (ρ : Rho P.shape) :
    ρ ∈ (H.recut P).withheld w x ↔ Rho.old P ρ ∈ H.withheld w x := Iff.rfl

theorem Honest.Acc.recut {H : Honest Q Wt} {valid : Wt → X → Prop} (h : H.Acc valid)
    {P : XPlan Q.shape} (hP : P.OK) : (H.recut P).Acc valid := by
  intro w x c ρ hv hρ
  show Q.accept x (H.ext w) (Tr.old P ((Strat.recut P (H.strat w x c)).run ρ).1) = true
  rw [Strat.run_recut P hP]
  exact h w x c (Rho.old P ρ) hv hρ

theorem Honest.prRho_withheld_recut
    (H : Honest Q Wt) {P : XPlan Q.shape} (hP : P.OK) (w : Wt) (x : X) :
    prRho ((H.recut P).withheld w x) = prRho (H.withheld w x) :=
  prRho_old P hP (H.withheld w x)

/-! ## 6. Honest-verifier zero knowledge -/

/-- A disclosed view (`DView`) of the protocol, read as a disclosed view of the new protocol. -/
def DView.recut (P : XPlan Q.shape) (v : DView Q) : DView (Q.recut P) where
  plains := Plains.new P v.plains
  ext := v.ext
  orc := fun p => (v.orc (OPos.oldEquiv P p)).map (OSym.new P p)

theorem InteractiveOracleProof.extAns_recut (P : XPlan Q.shape) (x : X) (ρ : Rho P.shape) (y : E.Str) :
    (Q.recut P).extAns x ρ y = Q.extAns x (Rho.old P ρ) y := rfl

theorem InteractiveOracleProof.dview_recut {P : XPlan Q.shape} (hP : P.OK) (x : X) (y : E.Str) (τ : Tr P.shape) :
    (Q.recut P).dview x y τ = DView.recut P (Q.dview x y (Tr.old P τ)) := by
  have h1 : τ.plains = Plains.new P (Tr.old P τ).plains := by rw [Tr.plains_old, Plains.new_old]
  have h2 : (Q.recut P).extAns x τ.rho y = Q.extAns x (Tr.old P τ).rho y := by
    rw [Tr.rho_old, InteractiveOracleProof.extAns_recut]
  have h3 : ((Q.recut P).dview x y τ).orc = (DView.recut P (Q.dview x y (Tr.old P τ))).orc := by
    funext p
    have hiff : (p ∈ (Q.recut P).reads x τ.rho τ.plains ∨ (Q.recut P).blinded p = false) ↔
        (OPos.oldEquiv P p ∈ Q.reads x (Tr.old P τ).rho (Tr.old P τ).plains ∨
          Q.blinded (OPos.oldEquiv P p) = false) := by
      refine or_congr ?_ Iff.rfl
      rw [Tr.rho_old, Tr.plains_old]
      exact InteractiveOracleProof.mem_reads_recut P x τ.rho τ.plains p
    dsimp only [InteractiveOracleProof.dview, DView.recut]
    split_ifs with ha hb hb
    · exact congrArg some
        ((OSym.new_old P p (τ.read p)).symm.trans
          (congrArg (OSym.new P p) (Tr.read_old P hP τ p).symm))
    · exact absurd (hiff.1 ha) hb
    · exact absurd (hiff.2 hb) ha
    · rfl
  show DView.mk τ.plains ((Q.recut P).extAns x τ.rho y) ((Q.recut P).dview x y τ).orc =
    DView.mk (Plains.new P (Tr.old P τ).plains) (Q.extAns x (Tr.old P τ).rho y)
      (DView.recut P (Q.dview x y (Tr.old P τ))).orc
  rw [← h1, ← h2, ← h3]

theorem Honest.output_recut (H : Honest Q Wt) {P : XPlan Q.shape} (hP : P.OK) (w : Wt)
    (x : X) (ρ : Rho P.shape) :
    (H.recut P).output w x ρ = (H.output w x (Rho.old P ρ)).map (Option.map (DView.recut P)) := by
  by_cases h : Rho.old P ρ ∈ H.withheld w x
  · have e1 : (H.recut P).output w x ρ = PMF.pure none := if_pos h
    have e2 : H.output w x (Rho.old P ρ) = PMF.pure none := if_pos h
    rw [e1, e2, PMF.pure_map]
    rfl
  · have e1 : (H.recut P).output w x ρ =
        (unif H.Coin).map fun c =>
          some ((Q.recut P).dview x (H.ext w) ((Strat.recut P (H.strat w x c)).run ρ).1) := if_neg h
    have e2 : H.output w x (Rho.old P ρ) =
        (unif H.Coin).map fun c =>
          some (Q.dview x (H.ext w) ((H.strat w x c).run (Rho.old P ρ)).1) := if_neg h
    rw [e1, e2, PMF.map_comp]
    congr 1
    funext c
    show some ((Q.recut P).dview x (H.ext w) ((Strat.recut P (H.strat w x c)).run ρ).1) =
      some (DView.recut P (Q.dview x (H.ext w) ((H.strat w x c).run (Rho.old P ρ)).1))
    rw [InteractiveOracleProof.dview_recut hP, Strat.run_recut P hP]

/-- The simulator of the new protocol, as an explicit term: run the old simulator at the old
challenges and map its output. -/
def simRecut (P : XPlan Q.shape)
    (Sim : X → (ρ : Rho Q.shape) → (E.Pos → Option E.Sym) → PMF (Option (DView Q))) :
    X → (ρ : Rho (Q.recut P).shape) → (E.Pos → Option E.Sym) → PMF (Option (DView (Q.recut P))) :=
  fun x ρ a => (Sim x (Rho.old P ρ) a).map (Option.map (DView.recut P))

/-- Under `P.OK`, at one w and x: if `Sim` differs from the honest output with probability at most
z, so does `simRecut P Sim`. (`prRho`, `Honest.HVZK`: Iop/InteractiveOracleProof.lean) -/
theorem simRecut_good {H : Honest Q Wt} {P : XPlan Q.shape} (hP : P.OK)
    (Sim : X → (ρ : Rho Q.shape) → (E.Pos → Option E.Sym) → PMF (Option (DView Q))) (w : Wt) (x : X)
    {z : ℝ≥0∞} (h : prRho {ρ | H.output w x ρ ≠ Sim x ρ (Q.extAns x ρ (H.ext w))} ≤ z) :
    prRho {ρ | (H.recut P).output w x ρ ≠
          simRecut P Sim x ρ ((Q.recut P).extAns x ρ ((H.recut P).ext w))} ≤ z := by
  refine le_trans (pr_mono _ ?_) ((le_of_eq (prRho_old P hP _)).trans h)
  intro ρ hρ heq
  apply hρ
  rw [Honest.output_recut H hP, heq]
  rfl

/-- Under `P.OK`, honest-verifier zero knowledge in the exact form is preserved, with the same bound
z. -/
theorem Honest.HVZK.recut {H : Honest Q Wt} {valid : Wt → X → Prop} {z : ℝ≥0∞} (h : H.HVZK valid z)
    {P : XPlan Q.shape} (hP : P.OK) : (H.recut P).HVZK valid z :=
  let ⟨Sim, hS⟩ := h
  ⟨simRecut P Sim, fun w x hv => simRecut_good hP Sim w x (hS w x hv)⟩

end OneProtocol

/-! ## 7. String oracles -/

/-- Under `P.OK`, the new rounds' oracles are strings if the old ones are. (The data of a scheme:
Iop/RecutData.lean.) -/
def Shape.IsPoint.recut : {s : Shape} → (P : XPlan s) → P.OK → s.IsPoint → P.shape.IsPoint
  | _, .nil => fun _ _ => ()
  | _, .keep _ P => fun hP h => (h.1, Shape.IsPoint.recut P hP h.2)
  | _, .cut _ P => fun hP h => (RCut.pointFst hP.1 h.1, Shape.IsPoint.recut P hP.2 (RCut.pointSnd hP.1 h.1, h.2))
  | _, .msg r1 r2 (s := s) _ P => fun hP (h : r1.IsPoint × r2.IsPoint × s.IsPoint) =>
      Shape.IsPoint.recut P hP.2
        (show Shape.IsPoint (r1.joinMsg r2 :: s) from (h.1.joinMsg h.2.1, h.2.2))
  | _, .chal r1 r2 (s := s) _ P => fun hP (h : r1.IsPoint × r2.IsPoint × s.IsPoint) =>
      Shape.IsPoint.recut P hP.2
        (show Shape.IsPoint (r1.joinChal r2 :: s) from (h.1.joinChal r2, h.2.2))

end Iop
