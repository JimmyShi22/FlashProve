-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WrapLaws/Cons.lean: the reduction wrapW (Johnson/WholeKey/Wrap.lean) around ANY game never
answers a repeated query differently.

One statement (Spec.consW) and its proof. This file states no goal of the release.

World.Consistent (Rom/World.lean) asks for a table of the answers given, from which repeated queries
are answered and of which no move ever changes an entry. The reduction keeps the oracle's table in
its own state and never asks the game's oracles, so that table serves, whatever the game is:
  a query is answered by lazy sampling from it (answer_wrapW);
  a call only adds to it: its programs sample lazily, or write a log each entry only where there is
  none (Table.lay), and a call to the game does not touch it (keeps_…).
The proof follows consistent_wrapBP (Compile/Batch/PubWr.lean), which has the like for the first
form's reduction.

Main names (namespace OnBytes.WrapLaws).
  handOut_sub      what a simulated run leaves holds every entry of the table after its chain.
  keeps_…          KeepsBy (Johnson/WrapLaws/Calc.lean), program by program.
  Spec.consW, consW   the statement, in the shape of the premise "cons" of the frame
                   (Compile/PrivFrame/Spec.lean), for every game.
Limits. Consistency alone: nothing is said on the law of an answer.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WrapLaws.Calc
import Johnson.WholeKey.Wrap

set_option autoImplicit false

noncomputable section

namespace OnBytes.WrapLaws
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey Hiop.Seeded
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

namespace Spec

/-- The reduction around any game is consistent. -/
def consW : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
      (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
      (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)
      (G : World (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GOut L (kitW W r₀ h).form)
        (GIn L (kitW W r₀ h).form)),
    ((wrapW W S cA r₀ h).world G).Consistent

end Spec

section Generic
variable {I' X' : Type} {lam K : ℕ} {L' : BatchProtocolWithLeafBody I' X'} (t : Tag) {Y : Type} {E : ExtSpec}
  (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L')
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L' t) (annOf L' t)) (xin : Y → Option X')
  (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeK lam L') (cap : ℕ → ℕ)

/-- What a simulated run leaves holds every entry of the table after its chain. -/
theorem handOut_sub (go : Bool) (co : Coins lam L')
    (o : Res (OutP lam L' Q.loc.shape) × RSt (typedOracleFamily lam K L') (Table (typedOracleFamily lam K L'))) :
    o.2.base.Sub (handOut Q wq x y xt go co o).2 := by
  unfold handOut
  split
  · exact ((Table.sub_lay _ _).trans (Table.sub_lay _ _)).trans (Table.sub_lay _ _)
  · exact Table.Sub.refl _

theorem keeps_pass2A {Out In : Type} (embE : E.Sym → Body L') (v : Option (DView Q.loc))
    (co : Coins lam L') (Rc : Record (typedOracleFamily lam K L')) (T : Table (typedOracleFamily lam K L')) :
    KeepsBy Prod.snd T
      (pass2A (Out := Out) (In := In) t Q wq embS embP xin cms x xt cap embE v co Rc T) :=
  (KeepsBy.runReplayA _ _ T [] Rc).bind fun o => KeepsBy.halt (handOut_sub Q wq x _ _ _ co o)

end Generic

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)

theorem keeps_tableA (s : ℕ → Bits) (T : Tb W) : KeepsBy Prod.snd T (tableA W S r₀ h s T) :=
  (KeepsBy.runDeferA _ _ T []).bind fun o => KeepsBy.call _ fun a => by
    cases a <;> exact KeepsBy.halt (Table.Sub.refl _)

theorem keeps_tablesA : ∀ (ss : List (ℕ → Bits)) (T : Tb W),
    KeepsBy Prod.snd T (tablesA W S r₀ h ss T)
  | [], T => KeepsBy.halt (Table.Sub.refl T)
  | s :: ss, T => (keeps_tableA W S r₀ h s T).bind fun o =>
      (keeps_tablesA ss o.2).bind fun _ => KeepsBy.halt (Table.Sub.refl _)

theorem keeps_linksA (t₁ : TabW lam L Bd aT aL) :
    ∀ (l : List (DrawCopy lam L Bd aT aL h.KL × TabW lam L Bd aT aL)) (e : ℕ) (T : Tb W),
      KeepsBy Prod.snd T (linksA W cA r₀ h t₁ e l T)
  | [], _, T => KeepsBy.halt (Table.Sub.refl T)
  | a :: l, e, T => KeepsBy.call _ fun rp => by
      refine KeepsBy.bind (π₁ := Prod.snd) ?_ fun o =>
        (keeps_linksA t₁ l (e + 1) o.2).bind fun _ => KeepsBy.halt (Table.Sub.refl _)
      cases rp with
      | link u => exact keeps_pass2A _ _ _ _ _ _ _ _ _ _ _ _ _ _ T
      | ood _ => exact KeepsBy.halt (Table.Sub.refl T)
      | test _ => exact KeepsBy.halt (Table.Sub.refl T)
      | sess _ _ => exact KeepsBy.halt (Table.Sub.refl T)
      | sym _ => exact KeepsBy.halt (Table.Sub.refl T)
      | none => exact KeepsBy.halt (Table.Sub.refl T)

/-- the table in the reduction's state, read off what a call returns -/
abbrev tabOf {γ : Type} (x : γ × StG W) : Tb W := x.2.1

theorem keeps_setupA (T : Tb W) : KeepsBy (tabOf W) T (setupA W S cA r₀ h T) :=
  (KeepsBy.runLazyA _ T).bind fun o₀ =>
  (keeps_tableA W S r₀ h _ o₀.2).bind fun o₁ =>
  (keeps_tablesA W S r₀ h _ o₁.2).bind fun o₂ => by
    cases h1 : o₁.1 with
    | none => exact KeepsBy.halt (Table.Sub.refl _)
    | some t₁ =>
      cases h2 : o₂.1 with
      | none => exact KeepsBy.halt (Table.Sub.refl _)
      | some ts =>
        refine KeepsBy.call _ fun rp => KeepsBy.bind (π₁ := Prod.snd) ?_ fun o₃ =>
          (keeps_linksA W cA r₀ h t₁ _ 1 o₃.2).bind fun _ => KeepsBy.halt (Table.Sub.refl _)
        cases rp with
        | test u => exact keeps_pass2A _ _ _ _ _ _ _ _ _ _ _ _ _ _ o₂.2
        | ood _ => exact KeepsBy.halt (Table.Sub.refl _)
        | link _ => exact KeepsBy.halt (Table.Sub.refl _)
        | sess _ _ => exact KeepsBy.halt (Table.Sub.refl _)
        | sym _ => exact KeepsBy.halt (Table.Sub.refl _)
        | none => exact KeepsBy.halt (Table.Sub.refl _)

theorem keeps_proveStepA (w : StG W) :
    ∀ xs : List X, KeepsBy (tabOf W) w.1 (proveStepA W cA r₀ h w xs)
  | [] => KeepsBy.halt (Table.Sub.refl _)
  | [x] => (KeepsBy.runLazyA _ w.1).bind fun o => by
      cases h1 : (w.2.bind fun ts => ts[o.1.j]?) with
      | none =>
        simp only [h1]
        exact KeepsBy.halt (Table.Sub.refl _)
      | some t =>
        simp only [h1]
        refine KeepsBy.call _ fun rp => KeepsBy.bind (π₁ := Prod.snd) ?_ fun _ =>
          KeepsBy.halt (Table.Sub.refl _)
        cases rp with
        | sess _ u => exact keeps_pass2A _ _ _ _ _ _ _ _ _ _ _ _ _ _ o.2
        | ood _ => exact KeepsBy.halt (Table.Sub.refl _)
        | test _ => exact KeepsBy.halt (Table.Sub.refl _)
        | link _ => exact KeepsBy.halt (Table.Sub.refl _)
        | sym _ => exact KeepsBy.halt (Table.Sub.refl _)
        | none => exact KeepsBy.halt (Table.Sub.refl _)
  | _ :: _ :: _ => KeepsBy.halt (Table.Sub.refl _)

theorem keeps_rep (w : StG W) (c : Compile.GlueB.SCall X) :
    KeepsBy (tabOf W) w.1 ((wrapW W S cA r₀ h).rep w c) := by
  cases c with
  | setup => exact keeps_setupA W S cA r₀ h w.1
  | prove xs => exact keeps_proveStepA W cA r₀ h w xs

variable (G : World (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GOut L (kitW W r₀ h).form)
  (GIn L (kitW W r₀ h).form))

/-- A query is answered by lazy sampling from the reduction's own table. -/
theorem answer_wrapW (w : StG W) (g : G.σ) (o : TypedOracleCompiler.Compile.Batch.OracleName)
    (q : domOf lam (typedOracleCarrier L Bd aT aL) o) :
    ((wrapW W S cA r₀ h).world G).answer (w, g) o q =
      (lazyAnswer (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) w.1 o q).map fun a =>
        (a.1, ((a.2, w.2), g)) := by
  show (interact G ((HandlerA.lazy w.1 o q).bind fun p => .halt (p.1, (p.2, w.2))) g).map _ = _
  rw [interact_bind, realises_lazy G g w.1 o q, PMF.bind_map, PMF.map_bind]
  simp only [Function.comp_def, interact, PMF.pure_map]
  rfl

theorem consW : Spec.consW := by
  intro I X lam L Bd aT aL W S cA r₀ h G
  refine ⟨fun s => s.1.1, ?_, ?_, ?_⟩
  · rintro ⟨w, g⟩ o q r hr x hx
    rw [answer_wrapW, lazyAnswer_of_some hr, PMF.pure_map] at hx
    rw [(PMF.mem_support_pure_iff _ _).1 hx]
  · rintro ⟨w, g⟩ o q x hx
    rw [answer_wrapW] at hx
    cases hT : w.1 o q with
    | some r =>
      rw [lazyAnswer_of_some hT, PMF.pure_map] at hx
      rw [(PMF.mem_support_pure_iff _ _).1 hx]
      exact ⟨hT, fun _ _ _ h => h⟩
    | none =>
      rw [lazyAnswer_of_none hT, PMF.map_comp] at hx
      obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
      exact ⟨Table.set_apply_same _ _ _ _, Table.sub_set hT r⟩
  · rintro ⟨w, g⟩ m x hx
    obtain ⟨z, hz, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
    exact keeps_rep W S cA r₀ h w m G g z hz

end OnBytes.WrapLaws

#print axioms OnBytes.WrapLaws.consW
