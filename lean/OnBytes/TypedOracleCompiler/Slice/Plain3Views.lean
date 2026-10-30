-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Plain3Views.lean.
TWO: CUT OVER THE SIBLING's RD (a list of trees a round) after a file of this project that is not in
this library; the head below is that file's, to the letter but for the paths of files that are not
in this library; a wiring IS given: Plain3Wire.lean.

A file of this project that is not in this library: how a transcript of the protocol in three
stretches comes apart, and
what a yes of its verifier gives.

OnBytes/TypedOracleCompiler/Slice/Plain3.lean defines the protocol `Plain3 G dec` (the head's own file, which
defined its like, is not in this library). Its shape is a seam, the first
stretch, two seams, the second stretch, a seam, the third stretch. This file has the small facts
with which a proof about the protocol takes a transcript apart and puts it together.

Main theorems.
 `shape_eq`       the shape, written out; by definition.
 `exists_whole`   every transcript is made of four seams' messages and three stretches'
                 transcripts.
 `tr₁_whole`, `tr₂_whole`, `tr₃_whole`   the stretches of a transcript that is put together.
 `accept_eq`, `accept_whole`   the verifier's decision is `accOn` on the three stretches.
 `accept_seams`   the decision does not depend on what is sent or drawn in the four seams.
 `accOn_iff`, `accOn_true`   a yes is: each stretch passes its three tests, and the decision says
                 yes to the three views.
 `rho_tr₁`, `rho_tr₂`, `rho_tr₃`, `dr_tr₁`, `dr_tr₂`, `dr_tr₃`   the verifier messages of a stretch,
                 and what was drawn in it, are functions of the verifier messages of the whole.
 `plains_tr₁`, `plains_tr₂`, `plains_tr₃`   the same for the plain parts, as a congruence.
 `read_in₁`, `read_in₂`, `read_in₃`   two transcripts agree at a position of a stretch if and only
                 if their stretches agree there.
Not claimed. Nothing on soundness. That some transcript is accepted is not shown.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Plain3
import Run.PlanQSLaws
import OnBytes.TypedOracleCompiler.Run.PlanQSLaws

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open _root_.Iop TypedOracleCompiler.Run

namespace Stretches
variable (G : Stretches)

/-- The shape of the protocol, written out. -/
theorem shape_eq (dec : PQ.View → PQ.View → PQ.View → Bool) :
    (Plain3 G dec).shape =
      G.s0.r :: (PQ.uL G.C G.ds₁ ++ (G.s1.r :: G.s2.r ::
        (PQ.uL G.C G.ds₂ ++ (G.s3.r :: PQ.uL G.C G.ds₃)))) :=
  rfl

section
variable (m0 : G.s0.r.Msg) (c0 : G.s0.r.Chal)
  (τ₁ : Tr (PQ.uL G.C G.ds₁))
  (m1 : G.s1.r.Msg) (c1 : G.s1.r.Chal)
  (m2 : G.s2.r.Msg) (c2 : G.s2.r.Chal)
  (τ₂ : Tr (PQ.uL G.C G.ds₂))
  (m3 : G.s3.r.Msg) (c3 : G.s3.r.Chal)
  (τ₃ : Tr (PQ.uL G.C G.ds₃))

/-- A transcript, put together from the four seams and the three stretches. -/
@[reducible] def whole : Tr G.sh :=
  (m0, c0, Tr.app (t := G.sh₂) τ₁ (m1, c1, m2, c2, Tr.app (t := G.sh₃) τ₂ (m3, c3, τ₃)))

theorem tr₁_whole : G.tr₁ (G.whole m0 c0 τ₁ m1 c1 m2 c2 τ₂ m3 c3 τ₃) = τ₁ :=
  Tr.fst_app τ₁ _

theorem trRest_whole :
    G.trRest (G.whole m0 c0 τ₁ m1 c1 m2 c2 τ₂ m3 c3 τ₃) = Tr.app (t := G.sh₃) τ₂ (m3, c3, τ₃) := by
  show (Tr.snd (s := PQ.uL G.C G.ds₁) (Tr.app (t := G.sh₂) τ₁ _)).2.2.2.2 = _
  rw [Tr.snd_app]

theorem tr₂_whole : G.tr₂ (G.whole m0 c0 τ₁ m1 c1 m2 c2 τ₂ m3 c3 τ₃) = τ₂ := by
  unfold tr₂
  rw [trRest_whole]
  exact Tr.fst_app τ₂ _

theorem tr₃_whole : G.tr₃ (G.whole m0 c0 τ₁ m1 c1 m2 c2 τ₂ m3 c3 τ₃) = τ₃ := by
  unfold tr₃
  rw [trRest_whole, Tr.snd_app]

end

/-- Every transcript is made of four seams' messages and three stretches' transcripts. -/
theorem exists_whole (τ : Tr G.sh) :
    ∃ m0 c0 τ₁ m1 c1 m2 c2 τ₂ m3 c3 τ₃, τ = G.whole m0 c0 τ₁ m1 c1 m2 c2 τ₂ m3 c3 τ₃ := by
  obtain ⟨m0, c0, r⟩ := τ
  obtain ⟨τ₁, r2, rfl⟩ : ∃ a b, r = Tr.app (s := PQ.uL G.C G.ds₁) (t := G.sh₂) a b :=
    ⟨Tr.fst r, Tr.snd (s := PQ.uL G.C G.ds₁) r, (Tr.app_fst_snd r).symm⟩
  obtain ⟨m1, c1, m2, c2, r3⟩ := r2
  obtain ⟨τ₂, r4, rfl⟩ : ∃ a b, r3 = Tr.app (s := PQ.uL G.C G.ds₂) (t := G.sh₃) a b :=
    ⟨Tr.fst r3, Tr.snd (s := PQ.uL G.C G.ds₂) r3, (Tr.app_fst_snd r3).symm⟩
  obtain ⟨m3, c3, τ₃⟩ := r4
  exact ⟨m0, c0, τ₁, m1, c1, m2, c2, τ₂, m3, c3, τ₃, rfl⟩

/-! ## The decision -/

section
variable (dec : PQ.View → PQ.View → PQ.View → Bool) (y : Fin (2 ^ G.a) → PQ.SgX)

/-- The verifier's decision is `accOn` on the three stretches of the transcript. -/
theorem accept_eq (τ : Tr G.sh) :
    (Plain3 G dec).accept () y τ = G.accOn y (G.tr₁ τ) (G.tr₂ τ) (G.tr₃ τ) dec :=
  rfl

/-- The verifier's decision on a transcript that is put together. -/
theorem accept_whole (m0 : G.s0.r.Msg) (c0 : G.s0.r.Chal)
    (τ₁ : Tr (PQ.uL G.C G.ds₁)) (m1 : G.s1.r.Msg) (c1 : G.s1.r.Chal)
    (m2 : G.s2.r.Msg) (c2 : G.s2.r.Chal) (τ₂ : Tr (PQ.uL G.C G.ds₂))
    (m3 : G.s3.r.Msg) (c3 : G.s3.r.Chal) (τ₃ : Tr (PQ.uL G.C G.ds₃)) :
    (Plain3 G dec).accept () y
        (m0, c0, Tr.app (t := G.sh₂) τ₁ (m1, c1, m2, c2, Tr.app (t := G.sh₃) τ₂ (m3, c3, τ₃))) =
      G.accOn y τ₁ τ₂ τ₃ dec := by
  have e := G.accept_eq dec y (G.whole m0 c0 τ₁ m1 c1 m2 c2 τ₂ m3 c3 τ₃)
  rw [tr₁_whole, tr₂_whole, tr₃_whole] at e
  exact e

/-- The decision does not depend on the seams: two transcripts with the same three stretches get
the same decision, whatever is sent and drawn in the four seams. -/
theorem accept_seams (τ τ' : Tr G.sh) (h₁ : G.tr₁ τ = G.tr₁ τ') (h₂ : G.tr₂ τ = G.tr₂ τ')
    (h₃ : G.tr₃ τ = G.tr₃ τ') : (Plain3 G dec).accept () y τ = (Plain3 G dec).accept () y τ' := by
  rw [accept_eq, accept_eq, h₁, h₂, h₃]

variable (τ₁ : Tr (PQ.uL G.C G.ds₁)) (τ₂ : Tr (PQ.uL G.C G.ds₂)) (τ₃ : Tr (PQ.uL G.C G.ds₃))

/-- What a yes is: the three tests in each stretch, and the decision's yes to the three views. -/
theorem accOn_iff :
    G.accOn y τ₁ τ₂ τ₃ dec = true ↔
      (PQ.passSL G.C G.ds₁ (PQ.rhoSL G.C G.ds₁ τ₁) = true ∧
        PQ.everyOpeningHasItsDraws G.xs₁ (drOn G.C G.ds₁ τ₁) = true ∧
        carries1 G.a G.all G.ds₁ G.xs₁ (drOn G.C G.ds₁ τ₁) y = true) ∧
      (PQ.passSL G.C G.ds₂ (PQ.rhoSL G.C G.ds₂ τ₂) = true ∧
        PQ.everyOpeningHasItsDraws G.xs₂ (drOn G.C G.ds₂ τ₂) = true ∧
        carries1 G.a G.all G.ds₂ G.xs₂ (drOn G.C G.ds₂ τ₂) y = true) ∧
      (PQ.passSL G.C G.ds₃ (PQ.rhoSL G.C G.ds₃ τ₃) = true ∧
        PQ.everyOpeningHasItsDraws G.xs₃ (drOn G.C G.ds₃ τ₃) = true ∧
        carries1 G.a G.all G.ds₃ G.xs₃ (drOn G.C G.ds₃ τ₃) y = true) ∧
      dec (G.view₁ y τ₁ τ₂ τ₃) (G.view₂ y τ₁ τ₂ τ₃) (G.view₃ y τ₁ τ₂ τ₃) = true := by
  unfold accOn okOn
  simp only [Bool.and_eq_true, and_assoc]

/-- A yes gives the three stretches' tests of work and the decision's yes to the three views. -/
theorem accOn_true (h : G.accOn y τ₁ τ₂ τ₃ dec = true) :
    PQ.passSL G.C G.ds₁ (PQ.rhoSL G.C G.ds₁ τ₁) = true ∧
      PQ.passSL G.C G.ds₂ (PQ.rhoSL G.C G.ds₂ τ₂) = true ∧
      PQ.passSL G.C G.ds₃ (PQ.rhoSL G.C G.ds₃ τ₃) = true ∧
      dec (G.view₁ y τ₁ τ₂ τ₃) (G.view₂ y τ₁ τ₂ τ₃) (G.view₃ y τ₁ τ₂ τ₃) = true :=
  have h' := (G.accOn_iff dec y τ₁ τ₂ τ₃).1 h
  ⟨h'.1.1, h'.2.1.1, h'.2.2.1.1, h'.2.2.2⟩

end

/-! ## Verifier messages, plain parts and oracles of a stretch -/

theorem rho_tr₁ (τ : Tr G.sh) : (G.tr₁ τ).rho = G.rho₁ τ.rho := by
  obtain ⟨m0, c0, r⟩ := τ
  exact Tr.rho_fst r

theorem rho_trRest (τ : Tr G.sh) : (G.trRest τ).rho = G.rhoRest τ.rho := by
  obtain ⟨m0, c0, r⟩ := τ
  show (Tr.snd (s := PQ.uL G.C G.ds₁) r).2.2.2.2.rho =
    (Rho.snd (s := PQ.uL G.C G.ds₁) (Tr.rho r)).2.2
  rw [← Tr.rho_snd]
  generalize Tr.snd (s := PQ.uL G.C G.ds₁) r = z
  obtain ⟨m1, c1, m2, c2, z⟩ := z
  rfl

theorem rho_tr₂ (τ : Tr G.sh) : (G.tr₂ τ).rho = G.rho₂ τ.rho := by
  unfold tr₂ rho₂
  rw [Tr.rho_fst, rho_trRest]

theorem rho_tr₃ (τ : Tr G.sh) : (G.tr₃ τ).rho = G.rho₃ τ.rho := by
  unfold tr₃ rho₃
  rw [← rho_trRest, ← Tr.rho_snd]
  generalize Tr.snd (s := PQ.uL G.C G.ds₂) (G.trRest τ) = z
  obtain ⟨m3, c3, z⟩ := z
  rfl

/-- What was drawn in a stretch is a function of the verifier messages of the whole. -/
theorem dr_tr₁ (τ : Tr G.sh) :
    drOn G.C G.ds₁ (G.tr₁ τ) = PQ.drawnSL G.C G.ds₁ (G.rho₁ τ.rho) := by
  unfold drOn
  rw [PQ.rhoS_eq, rho_tr₁]

theorem dr_tr₂ (τ : Tr G.sh) :
    drOn G.C G.ds₂ (G.tr₂ τ) = PQ.drawnSL G.C G.ds₂ (G.rho₂ τ.rho) := by
  unfold drOn
  rw [PQ.rhoS_eq, rho_tr₂]

theorem dr_tr₃ (τ : Tr G.sh) :
    drOn G.C G.ds₃ (G.tr₃ τ) = PQ.drawnSL G.C G.ds₃ (G.rho₃ τ.rho) := by
  unfold drOn
  rw [PQ.rhoS_eq, rho_tr₃]

theorem plains_tr₁ (τ τ' : Tr G.sh) (h : τ.plains = τ'.plains) :
    (G.tr₁ τ).plains = (G.tr₁ τ').plains := by
  obtain ⟨m0, c0, r⟩ := τ
  obtain ⟨m0', c0', r'⟩ := τ'
  have e : r.plains = r'.plains := congrArg Prod.snd h
  show (Tr.fst r).plains = (Tr.fst r').plains
  rw [Tr.plains_fst, Tr.plains_fst, e]

theorem plains_trRest (τ τ' : Tr G.sh) (h : τ.plains = τ'.plains) :
    (G.trRest τ).plains = (G.trRest τ').plains := by
  obtain ⟨m0, c0, r⟩ := τ
  obtain ⟨m0', c0', r'⟩ := τ'
  have e : r.plains = r'.plains := congrArg Prod.snd h
  have e2 : (Tr.snd (s := PQ.uL G.C G.ds₁) r).plains =
      (Tr.snd (s := PQ.uL G.C G.ds₁) r').plains := by
    rw [Tr.plains_snd, Tr.plains_snd, e]
  show (Tr.snd (s := PQ.uL G.C G.ds₁) r).2.2.2.2.plains =
    (Tr.snd (s := PQ.uL G.C G.ds₁) r').2.2.2.2.plains
  generalize Tr.snd (s := PQ.uL G.C G.ds₁) r = z at e2 ⊢
  generalize Tr.snd (s := PQ.uL G.C G.ds₁) r' = z' at e2 ⊢
  obtain ⟨m1, c1, m2, c2, z⟩ := z
  obtain ⟨m1', c1', m2', c2', z'⟩ := z'
  exact congrArg (fun p => p.2.2) e2

theorem plains_tr₂ (τ τ' : Tr G.sh) (h : τ.plains = τ'.plains) :
    (G.tr₂ τ).plains = (G.tr₂ τ').plains := by
  unfold tr₂
  rw [Tr.plains_fst, Tr.plains_fst, G.plains_trRest τ τ' h]

theorem plains_tr₃ (τ τ' : Tr G.sh) (h : τ.plains = τ'.plains) :
    (G.tr₃ τ).plains = (G.tr₃ τ').plains := by
  have e2 : (Tr.snd (s := PQ.uL G.C G.ds₂) (G.trRest τ)).plains =
      (Tr.snd (s := PQ.uL G.C G.ds₂) (G.trRest τ')).plains := by
    rw [Tr.plains_snd, Tr.plains_snd, G.plains_trRest τ τ' h]
  unfold tr₃
  generalize Tr.snd (s := PQ.uL G.C G.ds₂) (G.trRest τ) = z at e2 ⊢
  generalize Tr.snd (s := PQ.uL G.C G.ds₂) (G.trRest τ') = z' at e2 ⊢
  obtain ⟨m3, c3, z⟩ := z
  obtain ⟨m3', c3', z'⟩ := z'
  exact congrArg Prod.snd e2

/-- Two transcripts agree at a position of the first stretch if and only if their first stretches
agree there. -/
theorem read_in₁ (τ τ' : Tr G.sh) (p : OPos (PQ.uL G.C G.ds₁)) :
    τ.read (G.in₁ p) = τ'.read (G.in₁ p) ↔ (G.tr₁ τ).read p = (G.tr₁ τ').read p := by
  obtain ⟨m0, c0, r⟩ := τ
  obtain ⟨m0', c0', r'⟩ := τ'
  exact Tr.read_left_eq_iff r r' p

/-- Two transcripts agree at a position behind the third seam if and only if their parts behind that
seam agree there. -/
theorem read_inRest (τ τ' : Tr G.sh) (p : OPos (PQ.uL G.C G.ds₂ ++ G.sh₃)) :
    τ.read (.inr (OPos.right (s := PQ.uL G.C G.ds₁) (t := G.sh₂) (.inr (.inr p)))) =
        τ'.read (.inr (OPos.right (s := PQ.uL G.C G.ds₁) (t := G.sh₂) (.inr (.inr p)))) ↔
      (G.trRest τ).read p = (G.trRest τ').read p := by
  obtain ⟨m0, c0, r⟩ := τ
  obtain ⟨m0', c0', r'⟩ := τ'
  refine (Tr.read_right_eq_iff (s := PQ.uL G.C G.ds₁) (t := G.sh₂) r r' (.inr (.inr p))).trans ?_
  show _ ↔ (Tr.snd (s := PQ.uL G.C G.ds₁) r).2.2.2.2.read p =
    (Tr.snd (s := PQ.uL G.C G.ds₁) r').2.2.2.2.read p
  generalize Tr.snd (s := PQ.uL G.C G.ds₁) r = z
  generalize Tr.snd (s := PQ.uL G.C G.ds₁) r' = z'
  obtain ⟨m1, c1, m2, c2, z⟩ := z
  obtain ⟨m1', c1', m2', c2', z'⟩ := z'
  exact Iff.rfl

/-- The same for the second stretch. -/
theorem read_in₂ (τ τ' : Tr G.sh) (p : OPos (PQ.uL G.C G.ds₂)) :
    τ.read (G.in₂ p) = τ'.read (G.in₂ p) ↔ (G.tr₂ τ).read p = (G.tr₂ τ').read p :=
  (G.read_inRest τ τ' (OPos.left p)).trans (Tr.read_left_eq_iff _ _ p)

/-- The same for the third stretch. -/
theorem read_in₃ (τ τ' : Tr G.sh) (p : OPos (PQ.uL G.C G.ds₃)) :
    τ.read (G.in₃ p) = τ'.read (G.in₃ p) ↔ (G.tr₃ τ).read p = (G.tr₃ τ').read p := by
  refine (G.read_inRest τ τ' (OPos.right (s := PQ.uL G.C G.ds₂) (t := G.sh₃) (.inr p))).trans ?_
  refine (Tr.read_right_eq_iff (s := PQ.uL G.C G.ds₂) (t := G.sh₃) _ _ (.inr p)).trans ?_
  unfold tr₃
  generalize Tr.snd (s := PQ.uL G.C G.ds₂) (G.trRest τ) = z
  generalize Tr.snd (s := PQ.uL G.C G.ds₂) (G.trRest τ') = z'
  obtain ⟨m3, c3, z⟩ := z
  obtain ⟨m3', c3', z'⟩ := z'
  exact Iff.rfl

end Stretches

end TypedOracleCompiler.Slice
