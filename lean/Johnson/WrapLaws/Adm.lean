-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WrapLaws/Adm.lean: the reduction wrapW (Johnson/WholeKey/Wrap.lean) makes admissible
adversaries of the game.

One statement (Spec.admW) and its proof. This file states no goal of the release.

An outer adversary with the reduction inside is an adversary against the game of
Hiop/Seeded/Game.lean. The game's theorems (Spec.lifeSeededN, Hiop/Seeded/Total.lean; at one index:
Spec.lifeSeededAt, Hiop/Seeded/AtIndex.lean) ask two things of an adversary: the instance of every
session that it calls for is in the relation with the index, and it calls for at most n sessions.
Here: both hold, if the outer adversary is admissible in the library's sense (GAdm,
Compile/Batch/SpecGlue.lean: one setup, first; then at most n batches, each valid for the index).
Why: the setup calls for tables, one test and links, and for no session. A batch calls for one
session, at the batch's one own instance, or for none. Answering a query makes no call.
All other bounds (which table exists, one test, one link a copy, s1 sessions a copy, the seeds) are
kept by the game itself, which refuses; nothing is owed on them here.

Main names (namespace OnBytes.WrapLaws).
  tame_…           Tame (Johnson/WrapLaws/Calc.lean), program by program.
  Spec.admW, admW  the statement, in the shape of the premise "adm" of the frame
                   (Compile/PrivFrame/Spec.lean).
Limits. Nothing is said on the order of the reduction's calls, nor on how often the game refuses
one. That the real scheme does not run into the game's refusals, or at what price, is not said here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WrapLaws.Calc
import Johnson.WholeKey.Wrap
import Compile.PrivFrame.Spec

set_option autoImplicit false

noncomputable section

namespace OnBytes.WrapLaws
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey Hiop.Seeded
open _root_.Compile.GlueB (GCall SCall GAdm forget)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

namespace Spec

/-- An admissible outer adversary with the reduction inside, from any state of the reduction: every
session that it calls for is at an instance in the relation with the index, and there are at most n
such calls. -/
def admW : Prop :=
  ∀ (I X Wn PP : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
      (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
      (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)
      (R : ZKCP.Gen.RelPair I X Wn PP) (Ryes : I → X → Prop) (B : ℕ),
    (∀ i x w, R.yes i x w → Ryes i x) →
    ∀ (i : I) (α : Type)
      (D : Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Wn)
        (Compile.GlueB.GIn (FullKey lam L aT aL) (RequestProof lam L)) α) (b : Bool) (n : ℕ) (w : StG W),
      GAdm (fun c => ZKCP.Gen.ValidBatch R B i c.pairs) D b n →
        (((wrapW W S cA r₀ h).pre forget).adv D w).CallsOK (okCall (Ryes i)) ∧
          SessLe (((wrapW W S cA r₀ h).pre forget).adv D w) n

end Spec

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL) (ok : X → Prop)

/-- Pass 2 makes neither a query nor a call. -/
theorem quiet_pass2A {I' X' : Type} {K : ℕ} {L' : BatchProtocolWithLeafBody I' X'} (t : Tag) {Y : Type} {E : ExtSpec}
    (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L')
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L' t) (annOf L' t)) (xin : Y → Option X')
    (cms : List (Dig lam)) (x : Y) (xt : ℕ → TreeK lam L') (cap : ℕ → ℕ) {Out In : Type}
    (embE : E.Sym → Body L') (v : Option (DView Q.loc)) (co : Coins lam L')
    (Rc : Record (typedOracleFamily lam K L')) (T : Table (typedOracleFamily lam K L')) :
    (pass2A (Out := Out) (In := In) t Q wq embS embP xin cms x xt cap embE v co Rc T).Quiet :=
  (quiet_runReplayA _ _ _ _ _).bind fun _ => trivial

theorem tame_tableA (s : ℕ → Bits) (T : Tb W) : Tame ok (tableA W S r₀ h s T) 0 :=
  (Tame.of_quiet (quiet_runDeferA _ _ _ _) 0).bind0 fun o => Tame.table _ fun a => by
    cases a <;> exact Tame.halt _ 0

theorem tame_tablesA : ∀ (ss : List (ℕ → Bits)) (T : Tb W), Tame ok (tablesA W S r₀ h ss T) 0
  | [], _ => Tame.halt _ 0
  | s :: ss, T => (tame_tableA W S r₀ h ok s T).bind0 fun o =>
      (tame_tablesA ss o.2).bind0 fun _ => Tame.halt _ 0

theorem tame_linksA (t₁ : TabW lam L Bd aT aL) :
    ∀ (l : List (DrawCopy lam L Bd aT aL h.KL × TabW lam L Bd aT aL)) (e : ℕ) (T : Tb W),
      Tame ok (linksA W cA r₀ h t₁ e l T) 0
  | [], _, _ => Tame.halt _ 0
  | a :: l, e, T => Tame.link e fun rp => by
      refine Tame.bind0 ?_ fun o => (tame_linksA t₁ l (e + 1) o.2).bind0 fun _ => Tame.halt _ 0
      cases rp with
      | link u => exact Tame.of_quiet (quiet_pass2A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) 0
      | ood _ => exact Tame.halt _ 0
      | test _ => exact Tame.halt _ 0
      | sess _ _ => exact Tame.halt _ 0
      | sym _ => exact Tame.halt _ 0
      | none => exact Tame.halt _ 0

theorem tame_setupA (T : Tb W) : Tame ok (setupA W S cA r₀ h T) 0 :=
  (Tame.of_quiet (quiet_runLazyA _ _) 0).bind0 fun o₀ =>
  (tame_tableA W S r₀ h ok _ _).bind0 fun o₁ =>
  (tame_tablesA W S r₀ h ok _ _).bind0 fun o₂ => by
    cases h1 : o₁.1 with
    | none => exact Tame.halt _ 0
    | some t₁ =>
      cases h2 : o₂.1 with
      | none => exact Tame.halt _ 0
      | some ts =>
        refine Tame.test 0 fun rp => Tame.bind0 ?_ fun o₃ =>
          (tame_linksA W cA r₀ h ok t₁ _ 1 o₃.2).bind0 fun _ => Tame.halt _ 0
        cases rp with
        | test u => exact Tame.of_quiet (quiet_pass2A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) 0
        | ood _ => exact Tame.halt _ 0
        | link _ => exact Tame.halt _ 0
        | sess _ _ => exact Tame.halt _ 0
        | sym _ => exact Tame.halt _ 0
        | none => exact Tame.halt _ 0

theorem tame_proveStepA (w : StG W) :
    ∀ xs : List X, (∀ x ∈ xs, ok x) → Tame ok (proveStepA W cA r₀ h w xs) 1
  | [], _ => Tame.halt _ 1
  | [x], hx => (Tame.of_quiet (quiet_runLazyA _ _) 0).bind0 fun o => by
      cases h1 : (w.2.bind fun ts => ts[o.1.j]?) with
      | none =>
        simp only [h1]
        exact Tame.halt _ 1
      | some t =>
        simp only [h1]
        refine Tame.sess (n := 0) _ (hx x (List.mem_singleton.2 rfl)) fun rp =>
          Tame.bind0 ?_ fun _ => Tame.halt _ 0
        cases rp with
        | sess _ u => exact Tame.of_quiet (quiet_pass2A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) 0
        | ood _ => exact Tame.halt _ 0
        | test _ => exact Tame.halt _ 0
        | link _ => exact Tame.halt _ 0
        | sym _ => exact Tame.halt _ 0
        | none => exact Tame.halt _ 0
  | _ :: _ :: _, _ => Tame.halt _ 1

theorem tame_ans (w : StG W) (o : TypedOracleCompiler.Compile.Batch.OracleName)
    (q : domOf lam (typedOracleCarrier L Bd aT aL) o) : Tame ok ((wrapW W S cA r₀ h).ans w o q) 0 := by
  have hq : ((wrapW W S cA r₀ h).ans w o q).Quiet := by
    show ((HandlerA.lazy w.1 o q).bind fun p => Adv.halt (p.1, (p.2, w.2))).Quiet
    exact (quietA_lazy w.1 o q).bind fun _ => trivial
  exact Tame.of_quiet hq 0

/-- The own instances of a valid batch are in the relation. -/
theorem ownX_ok {Wn PP : Type} {R : ZKCP.Gen.RelPair I X Wn PP} {Ryes : I → X → Prop}
    (hR : ∀ i x w, R.yes i x w → Ryes i x) {B : ℕ} {i : I} {c : ZKCP.Gen.Batch X Wn}
    (hc : ZKCP.Gen.ValidBatch R B i c.pairs) : ∀ x ∈ c.ownX, Ryes i x := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
  exact hR i s.1 s.2.1 (hc.2 (s.1, s.2.1) (List.mem_map.2 ⟨s, (List.mem_filter.1 hs).1, rfl⟩))

theorem tame_subst {Wn PP : Type} {R : ZKCP.Gen.RelPair I X Wn PP} {Ryes : I → X → Prop}
    (hR : ∀ i x w, R.yes i x w → Ryes i x) {B : ℕ} {i : I} {α : Type}
    (D : Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Wn)
      (Compile.GlueB.GIn (FullKey lam L aT aL) (RequestProof lam L)) α) :
    ∀ (b : Bool) (n : ℕ) (w : StG W), GAdm (fun c => ZKCP.Gen.ValidBatch R B i c.pairs) D b n →
      Tame (Ryes i) (((wrapW W S cA r₀ h).pre forget).subst D w) n := by
  induction D with
  | halt a => intro _ n _ _; exact Tame.halt _ n
  | sample m k ih =>
    intro b n w hD
    exact ⟨fun r => (ih r b n w (hD r)).1, fun r => (ih r b n w (hD r)).2⟩
  | query o q k ih =>
    intro b n w hD
    exact (tame_ans W S cA r₀ h (Ryes i) w o q).bind0 fun x => ih x.1 b n x.2 (hD x.1)
  | call c k ih =>
    intro b n w hD
    cases c with
    | setup =>
      exact (tame_setupA W S cA r₀ h (Ryes i) w.1).bind0 fun x => ih x.1 true n x.2 (hD.2 x.1)
    | batch c =>
      cases n with
      | zero => exact hD.elim
      | succ j =>
        have h0 := Tame.bind (fun x => ih x.1 b j x.2 (hD.2.2 x.1))
          (tame_proveStepA W cA r₀ h (Ryes i) w c.ownX (ownX_ok hR hD.2.1))
        rw [Nat.add_comm] at h0
        exact h0

theorem admW : Spec.admW := by
  intro I X Wn PP lam L Bd aT aL W S cA r₀ h R Ryes B hR i α D b n w hD
  exact Tame.bind (n := 0) (fun _ => Tame.halt _ 0) (tame_subst W S cA r₀ h hR D b n w hD)

end OnBytes.WrapLaws

#print axioms OnBytes.WrapLaws.admW
