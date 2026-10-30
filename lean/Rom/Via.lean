-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Via.lean: a family of random oracles does not change if its points are permuted. The proofs of
the statements of Rom/SpecVia.lean, whose head says what they are for and what they do not say.

Which hypotheses are used. `OComp.runLazy_via` and `OComp.law_via` use only that ψ undoes φ
(`QMap.Inv φ ψ`); `viaWorld` uses both halves of `QMap.Perm`; `viaConsistent` uses neither: it holds
for every translation (`Via.consistent_pre`). `Via.via_set` is the one place where injectivity on
points is used.

Stronger than the statements: `Via.interact_via` (`viaWorld` with the tables at the end related: for
a challenger that is run in two phases); `OComp.law_via` (the distribution of the output from the
empty table does not change: the title of Rom/SpecVia.lean, for one algorithm).
-/
import Rom.SpecVia
import Prob.Count

open scoped ENNReal
open Prob
namespace Rom

variable {S : OSpec} {Out In α : Type}

namespace Via

/-! ## 1. Points -/

/-- a point: an oracle and a query to it -/
abbrev Pnt (S : OSpec) : Type := Σ o : S.ι, S.Dom o

/-- the point that is queried in place of p -/
def img (φ : QMap S) (p : Pnt S) : Pnt S := ⟨(φ p.1 p.2).1, (φ p.1 p.2).2.1⟩

theorem img_img {φ ψ : QMap S} (h : QMap.Inv φ ψ) (p : Pnt S) : img ψ (img φ p) = p := by
  obtain ⟨o, q⟩ := p
  obtain ⟨b, hb, -, -⟩ := h o q
  show (⟨(ψ (φ o q).1 (φ o q).2.1).1, (ψ (φ o q).1 (φ o q).2.1).2.1⟩ : Pnt S) = ⟨o, q⟩
  rw [hb]

theorem img_injective {φ ψ : QMap S} (h : QMap.Inv φ ψ) : Function.Injective (img φ) :=
  Function.LeftInverse.injective (img_img h)

/-- If ψ undoes φ, a uniform answer at the image, translated, is a uniform answer at the point: the
map between the ranges is a bijection. -/
theorem map_unif_rng {φ ψ : QMap S} (h : QMap.Inv φ ψ) (o : S.ι) (q : S.Dom o) :
    (PMF.uniformOfFintype (S.Rng (φ o q).1)).map (φ o q).2.2 = PMF.uniformOfFintype (S.Rng o) := by
  obtain ⟨b, -, h1, h2⟩ := h o q
  exact map_unif_equiv (⟨(φ o q).2.2, b, h2, h1⟩ : S.Rng (φ o q).1 ≃ S.Rng o)

theorem bind_unif_via {φ ψ : QMap S} (h : QMap.Inv φ ψ) (o : S.ι) (q : S.Dom o)
    {β : Type} (F : S.Rng o → PMF β) :
    ((PMF.uniformOfFintype (S.Rng (φ o q).1)).bind fun r => F ((φ o q).2.2 r)) =
      (PMF.uniformOfFintype (S.Rng o)).bind F := by
  rw [← map_unif_rng h o q, PMF.bind_map]
  rfl

/-! ## 2. Tables -/

theorem set_same (T : Table S) (o : S.ι) (q : S.Dom o) (r : S.Rng o) :
    (T.set o q r) o q = some r := by
  unfold Table.set
  rw [Function.update_self, Function.update_self]

theorem set_other (T : Table S) (o : S.ι) (q : S.Dom o) (r : S.Rng o) (o' : S.ι)
    (q' : S.Dom o') (h : (⟨o', q'⟩ : Pnt S) ≠ ⟨o, q⟩) :
    (T.set o q r) o' q' = T o' q' := by
  unfold Table.set
  by_cases ho : o' = o
  · subst ho
    have hq : q' ≠ q := fun e => h (by rw [e])
    rw [Function.update_self, Function.update_of_ne hq]
  · rw [Function.update_of_ne ho]

/-- If ψ undoes φ, to write at the image of a point and then translate is to translate and then
write at the point. -/
theorem via_set {φ ψ : QMap S} (h : QMap.Inv φ ψ) (T : Table S) (o : S.ι)
    (q : S.Dom o) (r : S.Rng (φ o q).1) :
    Table.via φ (T.set (φ o q).1 (φ o q).2.1 r) = (Table.via φ T).set o q ((φ o q).2.2 r) := by
  funext o₁ q₁
  by_cases hp : (⟨o₁, q₁⟩ : Pnt S) = ⟨o, q⟩
  · cases hp
    rw [set_same]
    show ((T.set (φ o q).1 (φ o q).2.1 r) (φ o q).1 (φ o q).2.1).map (φ o q).2.2 = _
    rw [set_same]
    rfl
  · rw [set_other _ _ _ _ _ _ hp]
    show ((T.set (φ o q).1 (φ o q).2.1 r) (φ o₁ q₁).1 (φ o₁ q₁).2.1).map (φ o₁ q₁).2.2 =
      (T (φ o₁ q₁).1 (φ o₁ q₁).2.1).map (φ o₁ q₁).2.2
    rw [set_other _ _ _ _ _ _ fun e => hp (img_injective h (a₁ := ⟨o₁, q₁⟩) (a₂ := ⟨o, q⟩) e)]

end Via

open Via

/-! ## 3. Algorithms -/


theorem Via.runLazy_some {T : Table S} {o : S.ι} {q : S.Dom o} {r : S.Rng o}
    (k : S.Rng o → OComp S α) (h : T o q = some r) :
    (OComp.query o q k).runLazy T = (k r).runLazy T := by
  simp only [OComp.runLazy, h]

theorem Via.runLazy_none {T : Table S} {o : S.ι} {q : S.Dom o}
    (k : S.Rng o → OComp S α) (h : T o q = none) :
    (OComp.query o q k).runLazy T =
      (PMF.uniformOfFintype (S.Rng o)).bind fun r => (k r).runLazy (T.set o q r) := by
  simp only [OComp.runLazy, h]

theorem OComp.runLazy_via {φ ψ : QMap S} (h : QMap.Inv φ ψ) : ∀ (c : OComp S α) (T : Table S),
    ((c.via φ).runLazy T).map (fun x => (x.1, Table.via φ x.2)) = c.runLazy (Table.via φ T)
  | .pure a, T => PMF.pure_map _ _
  | .query o q k, T => by
      show ((OComp.query (φ o q).1 (φ o q).2.1 fun r =>
          (k ((φ o q).2.2 r)).via φ).runLazy T).map _ = _
      cases hT : T (φ o q).1 (φ o q).2.1 with
      | some r =>
        have hV : Table.via φ T o q = some ((φ o q).2.2 r) := by
          show (T (φ o q).1 (φ o q).2.1).map (φ o q).2.2 = _
          rw [hT]
          rfl
        rw [Via.runLazy_some _ hT, Via.runLazy_some _ hV]
        exact OComp.runLazy_via h (k ((φ o q).2.2 r)) T
      | none =>
        have hV : Table.via φ T o q = none := by
          show (T (φ o q).1 (φ o q).2.1).map (φ o q).2.2 = _
          rw [hT]
          rfl
        rw [Via.runLazy_none _ hT, Via.runLazy_none _ hV, PMF.map_bind, ← bind_unif_via h o q]
        refine congrArg (PMF.uniformOfFintype (S.Rng (φ o q).1)).bind (funext fun r => ?_)
        rw [OComp.runLazy_via h (k ((φ o q).2.2 r)) (T.set (φ o q).1 (φ o q).2.1 r), via_set h]
  | .sample n k, T => by
      show ((PMF.uniformOfFintype (Fin (n + 1))).bind fun r => ((k r).via φ).runLazy T).map _ =
        (PMF.uniformOfFintype (Fin (n + 1))).bind fun r => (k r).runLazy (Table.via φ T)
      rw [PMF.map_bind]
      exact congrArg (PMF.uniformOfFintype (Fin (n + 1))).bind
        (funext fun r => OComp.runLazy_via h (k r) T)

/-- If ψ undoes φ, the law of the output under lazily sampled oracles does not change. -/
theorem OComp.law_via {φ ψ : QMap S} (h : QMap.Inv φ ψ) (c : OComp S α) :
    (c.via φ).law = c.law := by
  have e := congrArg (PMF.map Prod.fst) (OComp.runLazy_via h c (Table.empty S))
  exact Eq.trans
    (PMF.map_comp (fun x : α × Table S => (x.1, Table.via φ x.2))
      ((c.via φ).runLazy (Table.empty S)) Prod.fst).symm e

/-! ## 4. Any challenger after a translation -/

theorem Via.interact_pre (ψ : QMap S) (W : World S Out In) :
    ∀ (A : Adv S Out In α) (s : W.σ), interact (W.pre ψ) A s = interact W (A.via ψ) s
  | .halt _, _ => rfl
  | .sample n k, s =>
    congrArg (PMF.uniformOfFintype (Fin (n + 1))).bind
      (funext fun r => Via.interact_pre ψ W (k r) s)
  | .query o q k, s => by
      show ((W.answer s (ψ o q).1 (ψ o q).2.1).map fun x => ((ψ o q).2.2 x.1, x.2)).bind
          (fun p => interact (W.pre ψ) (k p.1) p.2) =
        (W.answer s (ψ o q).1 (ψ o q).2.1).bind fun p =>
          interact W ((k ((ψ o q).2.2 p.1)).via ψ) p.2
      rw [PMF.bind_map]
      exact congrArg (W.answer s (ψ o q).1 (ψ o q).2.1).bind
        (funext fun p => Via.interact_pre ψ W (k ((ψ o q).2.2 p.1)) p.2)
  | .call m k, s => congrArg (W.reply s m).bind (funext fun p => Via.interact_pre ψ W (k p.1) p.2)

theorem viaPre : Spec.viaPre := fun _ _ _ _ ψ W A s => Via.interact_pre ψ W A s

theorem Adv.TotalBound.via (ψ : QMap S) :
    ∀ (A : Adv S Out In α) (t N : ℕ), A.TotalBound t N → (A.via ψ).TotalBound t N
  | .halt _, _, _, _ => trivial
  | .sample _ k, t, N, h => fun r => Adv.TotalBound.via ψ (k r) t N (h r)
  | .query _ _ _, 0, _, h => h
  | .query o q k, t + 1, N, h => fun r => Adv.TotalBound.via ψ (k ((ψ o q).2.2 r)) t N (h _)
  | .call _ _, _, 0, h => h
  | .call _ k, t, N + 1, h => fun a => Adv.TotalBound.via ψ (k a) t N (h a)

theorem Adv.CallsOK.via (ψ : QMap S) (ok : Out → Prop) :
    ∀ A : Adv S Out In α, A.CallsOK ok → (A.via ψ).CallsOK ok
  | .halt _, _ => trivial
  | .sample _ k, h => fun r => Adv.CallsOK.via ψ ok (k r) (h r)
  | .query o q k, h => fun r => Adv.CallsOK.via ψ ok (k ((ψ o q).2.2 r)) (h _)
  | .call _ k, h => ⟨h.1, fun a => Adv.CallsOK.via ψ ok (k a) (h.2 a)⟩

theorem viaBounds : Spec.viaBounds := fun _ _ _ _ ψ A =>
  ⟨Adv.TotalBound.via ψ A, fun ok => Adv.CallsOK.via ψ ok A⟩

/-- Consistency is kept, for every translation: the table of the answers given is the translated
table. -/
theorem Via.consistent_pre (ψ : QMap S) (W : World S Out In) (h : W.Consistent) :
    (W.pre ψ).Consistent := by
  obtain ⟨seen, h1, h2, h3⟩ := h
  have up : ∀ (s s' : W.σ), (∀ o q r, seen s o q = some r → seen s' o q = some r) →
      ∀ o q r, Table.via ψ (seen s) o q = some r → Table.via ψ (seen s') o q = some r := by
    intro s s' hs o q r hr
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 hr
    show (seen s' (ψ o q).1 (ψ o q).2.1).map (ψ o q).2.2 = _
    rw [hs _ _ _ hr']
    rfl
  refine ⟨fun s => Table.via ψ (seen s), ?_, ?_, fun s m x hx => up s x.2 (h3 s m x hx)⟩
  · intro s o q r hr x hx
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 hr
    obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
    exact congrArg (ψ o q).2.2 (h1 s _ _ r' hr' y hy)
  · intro s o q x hx
    obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
    refine ⟨?_, up s y.2 (h2 s _ _ y hy).2⟩
    show (seen y.2 (ψ o q).1 (ψ o q).2.1).map (ψ o q).2.2 = _
    rw [(h2 s _ _ y hy).1]
    rfl

theorem viaConsistent : Spec.viaConsistent := fun _ _ _ _ ψ _ W h => Via.consistent_pre ψ W h

/-! ## 5. A challenger of oracle algorithms, all translated -/

namespace Via

theorem lazy_some {T : Table S} {o : S.ι} {q : S.Dom o} {r : S.Rng o} (h : T o q = some r) :
    lazyAnswer T o q = PMF.pure (r, T) := by
  unfold lazyAnswer
  rw [h]

theorem lazy_none {T : Table S} {o : S.ι} {q : S.Dom o} (h : T o q = none) :
    lazyAnswer T o q = (PMF.uniformOfFintype (S.Rng o)).map fun r => (r, T.set o q r) := by
  unfold lazyAnswer
  rw [h]

/-- If ψ undoes φ, for any point (o', q') and any z with φ o' q' = z: the entry of the translated
table at (o', q'), and the translated table after a write at z's point, in terms of z. (A form of
via_set that can be used after `QMap.Inv ψ φ` has rewritten φ (ψ p).) -/
theorem at_back {φ ψ : QMap S} (h : QMap.Inv φ ψ) (T : Table S) (o' : S.ι) (q' : S.Dom o')
    (z : Σ o : S.ι, S.Dom o × (S.Rng o → S.Rng o')) (hz : φ o' q' = z) :
    Table.via φ T o' q' = (T z.1 z.2.1).map z.2.2 ∧
    ∀ r : S.Rng z.1, Table.via φ (T.set z.1 z.2.1 r) = (Table.via φ T).set o' q' (z.2.2 r) := by
  subst hz
  exact ⟨rfl, fun r => via_set h T o' q' r⟩

/-- If φ and ψ undo each other (`QMap.Perm`), a lazy answer of the translated table at the point
that ψ queries, translated back, is a lazy answer of the table at the point itself. -/
theorem lazyAnswer_via {φ ψ : QMap S} (h : QMap.Perm φ ψ) (T : Table S) (o : S.ι) (q : S.Dom o) :
    (lazyAnswer (Table.via φ T) (ψ o q).1 (ψ o q).2.1).map (fun p => ((ψ o q).2.2 p.1, p.2)) =
      (lazyAnswer T o q).map fun p => (p.1, Table.via φ p.2) := by
  obtain ⟨b, hb, hb1, hb2⟩ := h.right o q
  obtain ⟨hat, hset⟩ := at_back h.left T (ψ o q).1 (ψ o q).2.1 ⟨o, q, b⟩ hb
  cases hT : T o q with
  | some r =>
    have hV : Table.via φ T (ψ o q).1 (ψ o q).2.1 = some (b r) := by
      rw [hat]
      show (T o q).map b = _
      rw [hT]
      rfl
    rw [lazy_some hT, lazy_some hV, PMF.pure_map, PMF.pure_map, hb1]
  | none =>
    have hV : Table.via φ T (ψ o q).1 (ψ o q).2.1 = none := by
      rw [hat]
      show (T o q).map b = _
      rw [hT]
      rfl
    rw [lazy_none hT, lazy_none hV, PMF.map_comp, PMF.map_comp]
    rw [← map_unif_rng h.right o q, PMF.map_comp]
    refine congrArg (fun f => PMF.map f (PMF.uniformOfFintype (S.Rng (ψ o q).1)))
      (funext fun r => ?_)
    show ((ψ o q).2.2 r, (Table.via φ T).set (ψ o q).1 (ψ o q).2.1 r) =
      ((ψ o q).2.2 r, Table.via φ (T.set o q ((ψ o q).2.2 r)))
    rw [hset ((ψ o q).2.2 r)]
    show _ = ((ψ o q).2.2 r, (Table.via φ T).set (ψ o q).1 (ψ o q).2.1 (b ((ψ o q).2.2 r)))
    rw [hb2]

/-- The two runs, with the tables at the end related. -/
theorem interact_via {τ : Type} {φ ψ : QMap S}
    (h : QMap.Perm φ ψ) (step : τ → Out → OComp S (In × τ)) :
    ∀ (A : Adv S Out In α) (s : τ) (T : Table S),
      (interact (World.ofOComp fun s m => (step s m).via φ) A (s, T)).map
          (fun x => (x.1, (x.2.1, Table.via φ x.2.2))) =
        interact (World.ofOComp step) (A.via ψ) (s, Table.via φ T)
  | .halt a, s, T => PMF.pure_map _ _
  | .sample n k, s, T => by
      show ((PMF.uniformOfFintype (Fin (n + 1))).bind fun r =>
          interact (World.ofOComp fun s m => (step s m).via φ) (k r) (s, T)).map _ =
        (PMF.uniformOfFintype (Fin (n + 1))).bind fun r =>
          interact (World.ofOComp step) ((k r).via ψ) (s, Table.via φ T)
      rw [PMF.map_bind]
      exact congrArg (PMF.uniformOfFintype (Fin (n + 1))).bind
        (funext fun r => interact_via h step (k r) s T)
  | .query o q k, s, T => by
      show (((lazyAnswer T o q).map fun p => (p.1, (s, p.2))).bind fun p =>
          interact (World.ofOComp fun s m => (step s m).via φ) (k p.1) p.2).map _ =
        ((lazyAnswer (Table.via φ T) (ψ o q).1 (ψ o q).2.1).map fun p => (p.1, (s, p.2))).bind
          fun p => interact (World.ofOComp step) ((k ((ψ o q).2.2 p.1)).via ψ) p.2
      rw [PMF.bind_map, PMF.bind_map, PMF.map_bind]
      have e := lazyAnswer_via h T o q
      have e' : ((lazyAnswer (Table.via φ T) (ψ o q).1 (ψ o q).2.1).bind fun p =>
            interact (World.ofOComp step) ((k ((ψ o q).2.2 p.1)).via ψ) (s, p.2)) =
          ((lazyAnswer (Table.via φ T) (ψ o q).1 (ψ o q).2.1).map fun p =>
              ((ψ o q).2.2 p.1, p.2)).bind
            fun p => interact (World.ofOComp step) ((k p.1).via ψ) (s, p.2) := by
        rw [PMF.bind_map]
        rfl
      refine Eq.trans ?_ e'.symm
      rw [e, PMF.bind_map]
      exact congrArg (lazyAnswer T o q).bind (funext fun p => interact_via h step (k p.1) s p.2)
  | .call m k, s, T => by
      show PMF.map _
          (((((step s m).via φ).runLazy T).map (fun p => (p.1.1, (p.1.2, p.2)))).bind
            (fun p => interact (World.ofOComp fun s m => (step s m).via φ) (k p.1) p.2)) =
        (((step s m).runLazy (Table.via φ T)).map fun p => (p.1.1, (p.1.2, p.2))).bind
          fun p => interact (World.ofOComp step) ((k p.1).via ψ) p.2
      rw [← OComp.runLazy_via h.left (step s m) T, PMF.bind_map, PMF.bind_map,
        PMF.bind_map, PMF.map_bind]
      exact congrArg (((step s m).via φ).runLazy T).bind
        (funext fun p => interact_via h step (k p.1.1) p.1.2 p.2)

end Via

theorem viaWorld : Spec.viaWorld := fun S _ _ τ α φ _ h step A s T =>
  Eq.trans (PMF.map_comp (fun x : α × (τ × Table S) => (x.1, (x.2.1, Table.via φ x.2.2)))
      (interact (World.ofOComp fun s m => (step s m).via φ) A (s, T)) Prod.fst).symm
    (congrArg (PMF.map Prod.fst) (Via.interact_via h step A s T))

end Rom
