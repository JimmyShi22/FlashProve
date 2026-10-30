-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/KnowJoin.lean: every marked round joins the next prover message (a marked last round is
kept).

This file is about the interactive oracle proofs that the compiler takes: it takes a marking of
rounds, makes the plan that merges each marked round, but a last one, into the round after it, and
shows that, under the hypotheses of the statements, the properties with a witness and the format of
the rounds are kept.
The plan of the join from a marking, and the interface after the join. Definitions, statements and
proofs.
A marking of a shape (`Marks`, Ior/Hoist.lean) names rounds whose verifier message has one value u
(`μ.OK`): in the constructions the rounds in which a block sends its mask oracle, the first message
after a hoist, the round of the oracle of cells.

Main names:
  `XPlan.ofMarks μ`: the plan (Iop/Recut.lean) that joins every marked round with the round after
    it, by the step "msg": (m1 . u) (m2 . c2) becomes ((m1, m2) . c2). Runs of marked rounds all
    join the first unmarked round after them. A marked last round is kept (nothing stands behind
    it). The plan cuts nothing and joins no two verifier messages; its laws follow from `μ.OK`
    (`XPlan.ofMarks_ok`).
  `L.join μT μL μB`: the interface after the join, for markings of the offline IOP, the link and the
    session (`BatchProtocol.recut` along these plans; nothing is to be annotated, since nothing is cut).
  `Spec.propsK_join`: for markings with `Marks.OK`, at least one slot, `L.late = none` and M.εs < 1,
    all properties of the interface with a witness (`BatchProtocol.PropsK`) are kept, with the same numbers;
    the extractor reads the same symbols (CompileK/KnowRecut.lean).
  `Marks.SameKind μ A`: every marked round of a session has the kind (local, shared) of the round
    after it: a mask round of the shared part stands before a shared round, one of a slot before a
    local round.
  `Spec.fmt_join`: then the format of a session's rounds (`RoundSplits.Fmt`: local, shared, local; which
    component is sent where) is kept.
So the compiler (CompileK/Main.lean) takes `L.join` as it takes L.

Limits: the compiler's other side conditions (`FitK`: samplers, numbers of opened positions) are
conditions on the joined interface, to be discharged there. Zero knowledge of the whole object
(Hiop/Whole.lean: HVZKWhole) after a join is not treated here. As in CompileK/KnowRecut.lean: two
oracles of a joined message stay two oracles.

Terms: lean/GLOSSARY.md.
-/
import CompileK.KnowRecut
import Ior.Hoist

set_option autoImplicit false

namespace Iop
open Prob BatchSplit BatchJoin BatchRecut
open scoped ENNReal

/-- The plan, with the first round (kept so far, or already a join) and its mark as arguments. -/
def XPlan.from (r : Round) (o : Option r.Chal) : (s : Shape) → Marks s → XPlan (r :: s)
  | [], _ => .keep r .nil
  | r2 :: s, (o2, μ) => match o with
      | none => .keep r (XPlan.from r2 o2 s μ)
      | some u => .msg r r2 u (XPlan.from (r.joinMsg r2) o2 s μ)

/-- The plan of a marking: every marked round joins the round after it. (A marked last round is
kept.) -/
def XPlan.ofMarks : {s : Shape} → Marks s → XPlan s
  | [], _ => .nil
  | r :: s, (o, μ) => XPlan.from r o s μ

theorem Marks.ok_cons {r : Round} {s : Shape} (o : Option r.Chal) (μ : Marks s) :
    Marks.OK (s := r :: s) (o, μ) ↔ (∀ u, o = some u → ∀ c, c = u) ∧ μ.OK := by
  cases o with
  | none => exact ⟨fun h => ⟨fun _ h' => (by cases h'), h⟩, fun h => h.2⟩
  | some u =>
    exact ⟨fun h => ⟨fun _ h' => Option.some.inj h' ▸ h.1, h.2⟩, fun h => ⟨h.1 u rfl, h.2⟩⟩

theorem XPlan.from_ok :
    ∀ (s : Shape) (r : Round) (o : Option r.Chal) (μ : Marks s),
      (∀ u, o = some u → ∀ c, c = u) → μ.OK → (XPlan.from r o s μ).OK
  | [], _, _, _, _, _ => trivial
  | r2 :: s, _, none, (o2, μ), _, h =>
    XPlan.from_ok s r2 o2 μ ((Marks.ok_cons o2 μ).1 h).1 ((Marks.ok_cons o2 μ).1 h).2
  | r2 :: s, r, some u, (o2, μ), hu, h =>
    ⟨hu u rfl,
      XPlan.from_ok s (r.joinMsg r2) o2 μ ((Marks.ok_cons o2 μ).1 h).1 ((Marks.ok_cons o2 μ).1 h).2⟩

theorem XPlan.from_noCut :
    ∀ (s : Shape) (r : Round) (o : Option r.Chal) (μ : Marks s), (XPlan.from r o s μ).NoCut
  | [], _, _, _ => trivial
  | r2 :: s, _, none, (o2, μ) => XPlan.from_noCut s r2 o2 μ
  | r2 :: s, r, some _, (o2, μ) => XPlan.from_noCut s (r.joinMsg r2) o2 μ

theorem XPlan.from_noChal :
    ∀ (s : Shape) (r : Round) (o : Option r.Chal) (μ : Marks s), (XPlan.from r o s μ).NoChal
  | [], _, _, _ => trivial
  | r2 :: s, _, none, (o2, μ) => XPlan.from_noChal s r2 o2 μ
  | r2 :: s, r, some _, (o2, μ) => XPlan.from_noChal s (r.joinMsg r2) o2 μ

theorem XPlan.ofMarks_ok : ∀ {s : Shape} (μ : Marks s), μ.OK → (XPlan.ofMarks μ).OK
  | [], _, _ => trivial
  | _ :: s, (o, μ), h =>
    XPlan.from_ok s _ o μ ((Marks.ok_cons o μ).1 h).1 ((Marks.ok_cons o μ).1 h).2

theorem XPlan.ofMarks_noCut : ∀ {s : Shape} (μ : Marks s), (XPlan.ofMarks μ).NoCut
  | [], _ => trivial
  | _ :: s, (o, μ) => XPlan.from_noCut s _ o μ

theorem XPlan.ofMarks_noChal : ∀ {s : Shape} (μ : Marks s), (XPlan.ofMarks μ).NoChal
  | [], _ => trivial
  | _ :: s, (o, μ) => XPlan.from_noChal s _ o μ

/-- Where no two verifier messages are joined, the law on their kinds is empty. -/
theorem AXPlan.kinds_of_noChal {s : Shape} (P : XPlan s) (h : P.NoChal) :
    ∀ (A : RoundSplits s) (Z : AXPlan P A), AXPlan.Kinds P A Z := by
  induction P with
  | nil => intro _ _; trivial
  | keep r P ih => exact fun A Z => ih h A.2 Z
  | cut c P ih => exact fun A Z => ih h (Z.1.ann2, A.2) Z.2
  | msg r1 r2 u P ih => exact fun A Z => ih h (A.1.joinMsg A.2.1, A.2.2) Z
  | chal r1 r2 np P ih => exact h.elim

/-! ## The format -/

/-- Every marked round has the kind of the round after it; k, b: kind and mark of the round before.
-/
def Marks.sameFrom (k : Kind) (b : Bool) : (s : Shape) → Marks s → RoundSplits s → Prop
  | [], _, _ => True
  | _ :: s, (o2, μ), (a2, A) => (b = true → k = a2.kind) ∧ Marks.sameFrom a2.kind o2.isSome s μ A

/-- Every marked round has the kind of the round after it. -/
def Marks.SameKind : {s : Shape} → Marks s → RoundSplits s → Prop
  | [], _, _ => True
  | _ :: s, (o, μ), (a, A) => Marks.sameFrom a.kind o.isSome s μ A

theorem fitMsg_same (k : Kind) (ph : FPhase) {S L : Prop} (h : fmtAt k ph S L) :
    FPhase.fitMsg k k ph := by
  cases k <;> cases ph <;> simp_all [fmtAt, FPhase.fitMsg]

theorem XPlan.fit_from :
    ∀ (s : Shape) (r : Round) (a : RAnn r) (o : Option r.Chal) (μ : Marks s) (A : RoundSplits s)
        (ph : FPhase) (Z : AXPlan (XPlan.from r o s μ) (show RoundSplits (r :: s) from (a, A))),
      RoundSplits.FmtFrom (r :: s) (a, A) ph → Marks.sameFrom a.kind o.isSome s μ A →
      AXPlan.Fit (XPlan.from r o s μ) (show RoundSplits (r :: s) from (a, A)) Z ph
  | [], _, _, _, _, _, _, _, _, _ => trivial
  | r2 :: s, r, a, none, (o2, μ), (a2, A), ph, Z, h, hs =>
      XPlan.fit_from s r2 a2 o2 μ A (FPhase.after a.kind ph) Z
        ((fmtFrom_cons a (show RoundSplits (r2 :: s) from (a2, A)) ph).1 h).2 hs.2
  | r2 :: s, r, a, some u, (o2, μ), (a2, A), ph, Z, h, hs => by
      obtain ⟨h1, h'⟩ := (fmtFrom_cons a (show RoundSplits (r2 :: s) from (a2, A)) ph).1 h
      obtain ⟨h2, h3⟩ := (fmtFrom_cons a2 A _).1 h'
      have hk : a.kind = a2.kind := hs.1 rfl
      have hF : FPhase.fitMsg a.kind a2.kind ph := hk ▸ fitMsg_same a.kind ph h1
      obtain ⟨t1, t2⟩ := fitMsg_table a.kind a2.kind ph noShared_msg noSlot_msg h1 h2 hF
      exact ⟨hF, XPlan.fit_from s (r.joinMsg r2) (a.joinMsg a2) o2 μ A ph Z
        ((fmtFrom_cons (a.joinMsg a2) A ph).2 ⟨t1, by rw [show FPhase.after (a.joinMsg a2).kind ph = FPhase.after a2.kind ph from rfl, ← t2]; exact h3⟩) hs.2⟩

theorem XPlan.fit_ofMarks :
    ∀ {s : Shape} (μ : Marks s) (A : RoundSplits s) (ph : FPhase) (Z : AXPlan (XPlan.ofMarks μ) A),
      RoundSplits.FmtFrom s A ph → μ.SameKind A → AXPlan.Fit (XPlan.ofMarks μ) A Z ph
  | [], _, _, _, _, _, _ => trivial
  | r :: s, (o, μ), (a, A), ph, Z, h, hs => XPlan.fit_from s r a o μ A ph Z h hs

/-! ## The interface -/

/-- The interface after the join. -/
def BatchProtocol.join {I X : Type} (L : BatchProtocol I X) (μT : Marks L.offline.shape)
    (μL : Marks L.link.shape) (μB : Marks L.onlineBatch.loc.shape) : BatchProtocol I X :=
  L.recut (XPlan.ofMarks μT) (XPlan.ofMarks μL) (XPlan.ofMarks μB)
    (AXPlan.noCut _ (XPlan.ofMarks_noCut μB) L.onlineBatch.ann)
    (AXPlan.kinds_of_noChal _ (XPlan.ofMarks_noChal μB) _ _)

namespace Spec

/-- States, under the hypotheses below: all properties with a witness are kept by the join, with the
same numbers. -/
def propsK_join : Prop :=
  ∀ (I X W : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → W → Prop)
      (wit : X → Orcs L.onlineBatch.loc.shape → W) (M : LH.Nums) (μT : Marks L.offline.shape)
      (μL : Marks L.link.shape) (μB : Marks L.onlineBatch.loc.shape),
    μT.OK → μL.OK → μB.OK → 0 < L.maxBatchSize → L.late = none → M.εs < 1 → L.PropsK Ryes Rno wit M →
    (L.join μT μL μB).PropsK Ryes Rno (fun x o => wit x (Orcs.old (XPlan.ofMarks μB) o)) M

/-- States: the format of a session's rounds is kept, if `μB.SameKind L.onlineBatch.ann`. -/
def fmt_join : Prop :=
  ∀ (I X : Type) (L : BatchProtocol I X) (μT : Marks L.offline.shape)
      (μL : Marks L.link.shape) (μB : Marks L.onlineBatch.loc.shape),
    μB.SameKind L.onlineBatch.ann → L.onlineBatch.ann.Fmt → (L.join μT μL μB).onlineBatch.ann.Fmt

end Spec

theorem propsK_join : Spec.propsK_join := by
  intro I X W L Ryes Rno wit M μT μL μB hT hL hB hN hl h1 h
  exact propsK_recut I X W L Ryes Rno wit M _ _ _ _ _ (XPlan.ofMarks_ok μT hT)
    (XPlan.ofMarks_ok μL hL) (XPlan.ofMarks_ok μB hB) (XPlan.ofMarks_noChal μT)
    (XPlan.ofMarks_noChal μL) (XPlan.ofMarks_noChal μB) (AXPlan.noCut_ok _ _ _) hN
    (fun n hn => by rw [hl] at hn; cases hn) h1 h

theorem fmt_join : Spec.fmt_join := by
  intro I X L μT μL μB hs hF
  exact (recutFmtB X _ L.onlineBatch (XPlan.ofMarks μB)
      (AXPlan.noCut _ (XPlan.ofMarks_noCut μB) L.onlineBatch.ann)).1
    (AXPlan.noCut_ok _ _ _) (AXPlan.kinds_of_noChal _ (XPlan.ofMarks_noChal μB) _ _) hF
    (XPlan.fit_ofMarks μB L.onlineBatch.ann .first _ hF hs)

end Iop
