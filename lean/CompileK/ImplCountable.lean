-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/ImplCountable.lean: the points of the compiler's typed oracles are countable if the
interface's instances, positions, alphabets and plain parts are.

Definitions, statements (`Compile.Batch.Spec.countable_pts`, `Spec.countable_door`) and proofs. A
tool for guards against empty theorems: it discharges the two hypotheses of
CompileK/ImplExists.lean. A point is an oracle, a query to it and the number of a block of the
answer (`Pts`, Compile/Batch/ImplOf.lean); the statements are on `RealPts` and `GhostPts` there.

Main names:
  `Spec.countable_pts`: instances, the alphabet of an encoded index, and the three protocols'
    rounds countable (`CtbSh`, `CtbS`) ⇒ the points of the real oracles and of the ghost names are
    countable.
  `ctbS_allLocal`, `ctbSh_pull`, `ctbS_pull`, `ctbSh_grind`, `ctbS_grind`: the conditions are kept
    by "local rounds only", by "verifier messages are made from blocks" and by "tests are added"
    (nonces countable, their type inhabited).
  `Spec.countable_door`: so at the interface that is compiled (`D.LO o`, CompileK/GrindOpt.lean:
    the work an option), for an inhabited and countable type Nn of nonces: from the conditions on
    the interface L itself.

Limits: this file says nothing on sizes. Verifier messages are not asked to be countable here (they
are finite by type, and no query holds one).

Terms: lean/GLOSSARY.md.
-/
import CompileK.ImplExists
import CompileK.GrindOpt

set_option autoImplicit false

namespace Iop

/-- positions, symbols and plain parts of every round are countable -/
def CtbSh : Shape → Prop
  | [] => True
  | r :: s => (Countable r.Pos ∧ (∀ p, Countable (r.Sym p)) ∧ Countable r.Plain) ∧ CtbSh s

/-- positions, symbols, and the plain parts of the two components of every round are countable -/
def CtbS : (s : Shape) → RoundSplits s → Prop
  | [], _ => True
  | r :: s, (a, A) =>
    (Countable r.Pos ∧ (∀ p, Countable (r.Sym p)) ∧ Countable a.P0 ∧ Countable a.Pj) ∧ CtbS s A

theorem ctbS_allLocal : ∀ {s : Shape}, CtbSh s → CtbS s (RoundSplits.allLocal s)
  | [], _ => trivial
  | _ :: _, h => ⟨⟨h.1.1, h.1.2.1, inferInstanceAs (Countable Unit), h.1.2.2⟩, ctbS_allLocal h.2⟩

theorem ctbSh_pull : ∀ {s : Shape} (σ : Samplers s), CtbSh s → CtbSh (s.pull σ)
  | [], _, _ => trivial
  | _ :: _, (_, σs), h => ⟨h.1, ctbSh_pull σs h.2⟩

theorem ctbS_pull :
    ∀ {s : Shape} (σ : Samplers s) {A : RoundSplits s}, CtbS s A → CtbS (s.pull σ) (A.pull σ)
  | [], _, _, _ => trivial
  | _ :: _, (_, σs), (_, _), h => ⟨h.1, ctbS_pull σs h.2⟩

theorem countable_gplain (W : Type) [Countable W] :
    ∀ (b : ℕ) (P : Type), Countable P → Countable (GPlain W b P)
  | 0, _, h => h
  | _ + 1, P, h => by
      haveI := h
      exact inferInstanceAs (Countable (P × W))

theorem ctbSh_grind (W : Type) [Inhabited W] [Countable W] :
    ∀ {s : Shape} (g : GBits s), CtbSh s → CtbSh (s.grind W g)
  | [], _, _ => trivial
  | _ :: _, (b, g), h => ⟨⟨h.1.1, h.1.2.1, countable_gplain W b _ h.1.2.2⟩, ctbSh_grind W g h.2⟩

theorem ctbS_grind (W : Type) [Inhabited W] [Countable W] :
    ∀ {s : Shape} (g : GBits s) {A : RoundSplits s}, CtbS s A → CtbS (s.grind W g) (A.grind W g)
  | [], _, _, _ => trivial
  | _ :: _, (b, g), (a, _), h =>
    ⟨⟨h.1.1, h.1.2.1, countable_gplain W (a.kind.b0 b) _ h.1.2.2.1,
        countable_gplain W (a.kind.bJ b) _ h.1.2.2.2⟩,
      ctbS_grind W g h.2⟩

end Iop

namespace Compile.Batch
open Iop Rom

theorem countable_PB : ∀ (s : Shape) (A : RoundSplits s), CtbS s A → Countable (PlainPart s A)
  | [], _, _ => inferInstanceAs (Countable Empty)
  | _ :: s, (a, A), h => by
      haveI := h.1.2.2.1
      haveI := h.1.2.2.2
      haveI := countable_PB s A h.2
      exact inferInstanceAs (Countable ((a.P0 ⊕ a.Pj) ⊕ PlainPart s A))

theorem countable_symAny : ∀ (s : Shape) (A : RoundSplits s), CtbS s A → Countable (SymAny s)
  | [], _, _ => ⟨⟨fun x => x.1.elim, fun x => x.1.elim⟩⟩
  | r :: s, (_, A), h => by
      haveI := h.1.1
      haveI := h.1.2.1
      haveI := countable_symAny s A h.2
      let f : SymAny (r :: s) → (Σ p : r.Pos, r.Sym p) ⊕ SymAny s := fun x => match x with
        | ⟨.inl p, a⟩ => .inl ⟨p, a⟩
        | ⟨.inr p, a⟩ => .inr ⟨p, a⟩
      refine Function.Injective.countable (f := f) ?_
      rintro ⟨p | p, a⟩ ⟨q | q, b⟩ hab
      · cases hab; rfl
      · cases hab
      · cases hab
      · cases hab; rfl

theorem countable_head (lam : ℕ) (X : Type) [Countable X] : Countable (Head lam X) := by
  let f : Head lam X →
      (List (Dig lam) × Option X × Bits) ⊕ (Option X × Bits) ⊕ (Bits × Bits) ⊕
        (List (Dig lam) × Bits) ⊕ Bits := fun h => match h with
    | .f1 a b c => .inl (a, b, c)
    | .f2 a b => .inr (.inl (a, b))
    | .f3 a b => .inr (.inr (.inl (a, b)))
    | .f4 a b => .inr (.inr (.inr (.inl (a, b))))
    | .f5 a => .inr (.inr (.inr (.inr a)))
  refine Function.Injective.countable (f := f) ?_
  intro a b hab
  cases a <;> cases b
    <;> simp only [f, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, reduceCtorEq] at hab
    <;> simp [hab]

section
variable {I X : Type}

namespace Spec

/-- Under the hypotheses below, the points of the real oracles and of the ghost names are
countable. -/
def countable_pts : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X), Countable X → Countable L.Symbol → CtbSh L.offline.shape →
    CtbSh L.link.shape → CtbS L.onlineBatch.loc.shape L.onlineBatch.ann →
    Countable (RealPts lam K L) ∧ Countable (GhostPts lam K L)

/-- The same at the interface that is compiled, `D.LO o`, from the conditions on L itself, for an
inhabited and countable type Nn of nonces. -/
def countable_door : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] [Countable Nn] (I X : Type) (L : BatchProtocol I X) (lam : ℕ)
      (D : DataK L lam) (o : Option (Work Nn L)),
    Countable X → Countable L.Symbol → CtbSh L.offline.shape → CtbSh L.link.shape →
    CtbS L.onlineBatch.loc.shape L.onlineBatch.ann →
    Countable (RealPts lam (D.WO o).K (D.LO o)) ∧ Countable (GhostPts lam (D.WO o).K (D.LO o))

end Spec

theorem countable_pts : Spec.countable_pts := by
  intro I X lam K L hX hSg hT hL hB
  haveI := hX
  haveI := hSg
  haveI := countable_head lam X
  have hA : ∀ t : Tag, CtbS (shapeOf L t) (annOf L t) := fun t => by
    cases t
    · exact ctbS_allLocal hT
    · exact ctbS_allLocal hL
    · exact hB
  haveI : ∀ t : Tag, Countable (PlainPart (shapeOf L t) (annOf L t)) := fun t => countable_PB _ _ (hA t)
  haveI : ∀ t : Tag, Countable (SymAny (shapeOf L t)) := fun t => countable_symAny _ _ (hA t)
  haveI : Countable Tag := ⟨⟨fun t => match t with | .test => 0 | .link => 1 | .onl => 2, fun a b h => by cases a <;> cases b <;> first | rfl | cases h⟩⟩
  haveI : Countable
      (LeafIn L) := Function.Injective.countable (f := fun x : LeafIn L => (x.body,
          x.salt)) fun a b h => by
    cases a; cases b; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  haveI : ∀ t : Tag, Countable (FbIn lam L t) := fun t =>
    Function.Injective.countable
        (f := fun x : FbIn lam L t => (x.round, x.head, x.rt, x.plain)) fun a b h => by
    cases a; cases b; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl
  haveI : ∀ t : Tag, Countable (JoiningRoundQuery lam L t) := fun t =>
    Function.Injective.countable
        (f := fun x : JoiningRoundQuery lam L t => (x.round, x.ρ, x.rt, x.plain)) fun a b h => by
    cases a; cases b; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl
  exact ⟨inferInstance, inferInstance⟩

theorem countable_door : Spec.countable_door := by
  intro Nn _ _ I X L lam D o hX hSg hT hL hB
  cases o with
  | none =>
    exact countable_pts I X lam _ D.L hX hSg (ctbSh_pull _ hT) (ctbSh_pull _ hL) (ctbS_pull _ hB)
  | some w =>
    exact countable_pts I X lam _ (D.LWk w) hX hSg (ctbSh_grind Nn _ (ctbSh_pull _ hT))
      (ctbSh_grind Nn _ (ctbSh_pull _ hL)) (ctbS_grind Nn _ (ctbS_pull _ hB))

end
end Compile.Batch
