-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/ExactSeq.lean: under the hypotheses of its statement, exact honest-verifier zero knowledge with
further reads composes.
The file is about the sequential composition of two interactive oracle reductions (IORs).

Proof of `Iop.Spec.exact_seq` (stated in Ior/Honest.lean), with the simulator of the composition
named (`IOR.simSeq`, `exactWith_seq`).
An IOR (`IOR`, Ior/Ior.lean) is an interactive oracle reduction: a protocol after whose rounds the
verifier rejects or outputs a new statement. A statement has an explicit part, held by the verifier,
and an implicit part: oracles that it queries. Below, x is the explicit part of the input statement,
y its implicit part, ρ the verifier's randomness.

The simulator of "R₁; then R₂" (`simSeq S₁ S₂`). It is given x, ρ = (ρ₁, ρ₂), a set T of further
positions, and the symbols of y at the positions `(R₁.seq R₂).given ρ T`. T₁, T₂ are the parts of T
in the two protocols.
 1. It runs S₁ on x, ρ₁ and the set `firstT` = T₁ together with every position of the first prover's
    oracles from which a symbol of the middle implicit instance at `R₂.given ρ₂ T₂` is computed. The
    symbols of y that S₁ is to be given are among those that the simulator has
    (`given_first_subset`). If S₁ gives the notice (`none`: `Honest.output`, Ior/Honest.lean), so
    does the simulator.
 2. From the view V₁ that S₁ wrote it takes some oracles y' and some transcript τ' that agree with
    all that it has been given and with all that V₁ shows (a choice; a simulator need not be
    efficient here), and computes from them the middle explicit instance x₂ and the symbols of the
    middle implicit instance at `R₂.given ρ₂ T₂`. Because R₁ is local, these are the true ones
    (exactly: `simCont_view`).
 3. It runs S₂ on x₂, ρ₂, T₂ and these symbols. If S₂ gives the notice, so does the simulator. Else
    it takes some transcript that agrees with what S₂ wrote, and outputs what the joined transcript
    shows at the verifier's positions of the composition and at T (exactly: `simCont`, `glue`;
    `view`, Ior/Honest.lean). (So what V₁ shows beyond that is dropped.)
The simulator reads nothing of the honest sides: not their bad sets, not their strategies.

Why it is exact: outside the withheld set of the first, for fixed coins of the first prover, the
statement handed on is in the middle relation (completeness of the first), so (with `hρ₂`, `hb₂` in
the proof of `exactWith_seq`) the law of the second part is that of S₂; and S₂'s arguments depend on
the first prover's coins only through the view at `firstT`. So the joint law is a bind over the law
of that view, which is S₁'s.

Limits: this file says nothing about the probability of the withheld set of the composition:
`(H₁.seq H₂).Hid` holds every ρ whose first part is not publicly bad (`H₁.Bad`) and whose second
part is hidden-withheld (`H₂.Hid`) for some coins of the first prover. Rules for bounds are stated
in Ior/Chain.lean (`Spec.hid_seq_le`, `Spec.withheld_seq_le`).
Terms: lean/GLOSSARY.md.
-/
import Ior.SeqProofs
import Prob.LawKit
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. Taking some element with a property -/

namespace IOR

open Classical in
/-- Some element with the property P, if there is one. -/
def pick {α : Type} (P : α → Prop) : Option α :=
  if h : ∃ a, P a then some (Classical.choose h) else none

theorem pick_spec {α : Type} {P : α → Prop} (h : ∃ a, P a) : ∃ a, pick P = some a ∧ P a :=
  ⟨Classical.choose h, dif_pos h, Classical.choose_spec h⟩

theorem pick_map_congr {α β : Type} {P : α → Prop} {f g : α → β} (h : ∀ a, P a → f a = g a) :
    (pick P).map f = (pick P).map g := by
  by_cases hP : ∃ a, P a
  · obtain ⟨a, ha, hPa⟩ := pick_spec hP
    rw [ha, Option.map_some, Option.map_some, h a hPa]
  · have : pick P = none := dif_neg hP
    rw [this, Option.map_none, Option.map_none]

end IOR

/-! ## 2. Answers of external oracles on a set of positions -/

/-- The oracles y agree with all the answers given. -/
def ExtSpec.Fits (E : ExtSpec) (a : E.Pos → Option E.Sym) (y : E.Str) : Prop :=
  ∀ p s, a p = some s → E.rd y p = s

theorem ExtSpec.ans_of_mem (E : ExtSpec) {U : Finset E.Pos} (y : E.Str) {p : E.Pos} (h : p ∈ U) :
    E.ans U y p = some (E.rd y p) := if_pos h

theorem ExtSpec.ans_of_not_mem
    (E : ExtSpec) {U : Finset E.Pos} (y : E.Str) {p : E.Pos} (h : p ∉ U) : E.ans U y p = none :=
  if_neg h

theorem ExtSpec.fits_ans (E : ExtSpec) (U : Finset E.Pos) (y : E.Str) :
    E.Fits (E.ans U y) y := fun p s h => by
  by_cases hp : p ∈ U
  · rw [E.ans_of_mem y hp] at h
    exact Option.some.inj h
  · rw [E.ans_of_not_mem y hp] at h
    cases h

theorem ExtSpec.Fits.rd_eq {E : ExtSpec} {U : Finset E.Pos} {y y' : E.Str}
    (h : E.Fits (E.ans U y) y') {p : E.Pos} (hp : p ∈ U) : E.rd y' p = E.rd y p :=
  h p _ (E.ans_of_mem y hp)

theorem ExtSpec.ans_congr (E : ExtSpec) {U : Finset E.Pos}
    {y y' : E.Str} (h : ∀ p ∈ U, E.rd y p = E.rd y' p) : E.ans U y = E.ans U y' := by
  funext p
  by_cases hp : p ∈ U
  · rw [E.ans_of_mem y hp, E.ans_of_mem y' hp, h p hp]
  · rw [E.ans_of_not_mem y hp, E.ans_of_not_mem y' hp]

open Classical in
/-- The answers on a larger set, cut down to a smaller one. -/
theorem ExtSpec.cut_ans (E : ExtSpec) {U V : Finset E.Pos} (h : U ⊆ V) (y : E.Str) :
    (fun p => if p ∈ U then E.ans V y p else none) = E.ans U y := by
  funext p
  by_cases hp : p ∈ U
  · rw [if_pos hp, E.ans_of_mem y hp, E.ans_of_mem y (h hp)]
  · rw [if_neg hp, E.ans_of_not_mem y hp]

namespace IOR
variable {X₁ X₂ X₃ Xi Xo : Type} {E₁ E₂ E₃ Ei Eo : ExtSpec}

/-! ## 3. Views -/

section View
variable {R : IOR Xi Ei Xo Eo}

/-- The position p is shown at ρ with the further positions T. -/
def Shown (R : IOR Xi Ei Xo Eo) (ρ : Rho R.shape) (T : Finset (OPos R.shape)) (p : OPos R.shape) :
    Prop :=
  p ∈ R.reads ρ ∨ p ∈ T ∨ R.blinded p = false

/-- The transcript τ has the verifier's randomness ρ and agrees with all that the view shows. -/
def View.Fits (V : View R) (ρ : Rho R.shape) (τ : Tr R.shape) : Prop :=
  τ.rho = ρ ∧ τ.plains = V.plains ∧ ∀ p s, V.orc p = some s → τ.read p = s

theorem View.ext' {V V' : View R} (h1 : V.plains = V'.plains) (h2 : V.orc = V'.orc) : V = V' := by
  obtain ⟨a, b⟩ := V
  obtain ⟨a', b'⟩ := V'
  dsimp only at h1 h2
  subst h1
  subst h2
  rfl

theorem view_orc_of_shown (T : Finset (OPos R.shape)) (τ : Tr R.shape)
    {p : OPos R.shape} (h : R.Shown τ.rho T p) :
    (R.view T τ).orc p = some (τ.read p) := if_pos h

theorem view_orc_of_not_shown
    (T : Finset (OPos R.shape)) (τ : Tr R.shape) {p : OPos R.shape} (h : ¬ R.Shown τ.rho T p) :
    (R.view T τ).orc p = none := if_neg h

theorem view_fits (T : Finset (OPos R.shape)) (τ : Tr R.shape) : (R.view T τ).Fits τ.rho τ := ⟨rfl, rfl, fun p s h => by
  by_cases hp : R.Shown τ.rho T p
  · rw [view_orc_of_shown T τ hp] at h
    exact Option.some.inj h
  · rw [view_orc_of_not_shown T τ hp] at h
    cases h⟩

theorem View.Fits.read_eq {T : Finset (OPos R.shape)} {τ τ' : Tr R.shape} {ρ : Rho R.shape}
    (h : (R.view T τ).Fits ρ τ') {p : OPos R.shape} (hp : R.Shown τ.rho T p) :
    τ'.read p = τ.read p :=
  h.2.2 p _ (view_orc_of_shown T τ hp)

/-- A view depends on the transcript only through ρ, the plain parts and the symbols shown. -/
theorem view_congr (T : Finset (OPos R.shape)) {τ τ' : Tr R.shape} (h1 : τ.rho = τ'.rho)
    (h2 : τ.plains = τ'.plains) (h3 : ∀ p, R.Shown τ.rho T p → τ.read p = τ'.read p) :
    R.view T τ = R.view T τ' := by
  refine View.ext' h2 (funext fun p => ?_)
  by_cases hp : R.Shown τ.rho T p
  · rw [view_orc_of_shown T τ hp, view_orc_of_shown T τ' (h1 ▸ hp), h3 p hp]
  · rw [view_orc_of_not_shown T τ hp, view_orc_of_not_shown T τ' (h1 ▸ hp)]

theorem mem_given {ρ : Rho R.shape} {T : Finset (OPos R.shape)} {q : Ei.Pos} :
    q ∈ R.given ρ T ↔ q ∈ R.extReads ρ ∨ ∃ p, (p ∈ R.reads ρ ∨ p ∈ T) ∧ q ∈ R.tie ρ p := by
  unfold given
  simp only [Finset.mem_union, Finset.mem_biUnion]

variable {Wi Wo : Type}

theorem Honest.output_of_mem (H : R.Honest Wi Wo) {w : Wi} {x : Xi} {ρ : Rho R.shape}
    (T : Finset (OPos R.shape)) (h : ρ ∈ H.withheld w x) :
    H.output w x ρ T = PMF.pure none := if_pos h

theorem Honest.output_of_not_mem (H : R.Honest Wi Wo) {w : Wi} {x : Xi} {ρ : Rho R.shape}
    (T : Finset (OPos R.shape)) (h : ρ ∉ H.withheld w x) :
    H.output w x ρ T = (unif H.Coin).map fun c => some (R.view T ((H.strat w x c).run ρ).1) :=
  if_neg h

end View

/-! ## 4. The two parts of a set of positions -/

/-- The part of T in the first protocol. -/
def partL {s t : Shape} (T : Finset (OPos (s ++ t))) : Finset (OPos s) :=
  T.preimage OPos.left OPos.left_injective.injOn

/-- The part of T in the second protocol. -/
def partR (s : Shape) {t : Shape} (T : Finset (OPos (s ++ t))) : Finset (OPos t) :=
  T.preimage (OPos.right (s := s)) OPos.right_injective.injOn

theorem mem_partL {s t : Shape} {T : Finset (OPos (s ++ t))} {p : OPos s} :
    p ∈ partL T ↔ OPos.left p ∈ T :=
  Finset.mem_preimage

theorem mem_partR {s t : Shape} {T : Finset (OPos (s ++ t))} {p : OPos t} :
    p ∈ partR s T ↔ OPos.right (s := s) p ∈ T :=
  Finset.mem_preimage

/-- A position of s ++ t is a position of s or a position of t. -/
theorem left_or_right {s t : Shape} (p : OPos (s ++ t)) :
    (∃ q, p = OPos.left q) ∨ ∃ q, p = OPos.right (s := s) q := by
  have h := OPos.elim_split (s := s) p
  cases hp : OPos.split (s := s) p with
  | inl q => rw [hp] at h; exact Or.inl ⟨q, h.symm⟩
  | inr q => rw [hp] at h; exact Or.inr ⟨q, h.symm⟩

/-! ## 5. What the composition shows, and what its simulator is given

What the composition reads and ties is unfolded in Ior/SeqProofs.lean. -/

section Seq
variable (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)

open Classical in
/-- The further positions for the first simulator: the part of T in the first protocol, and every
position of the first prover's oracles from which a symbol that the second simulator is given is
computed. -/
def firstT (ρ : Rho (R₁.shape ++ R₂.shape))
    (T : Finset (OPos (R₁.shape ++ R₂.shape))) : Finset (OPos R₁.shape) :=
  partL T ∪ (R₂.given (Rho.snd (s := R₁.shape) ρ) (partR R₁.shape T)).biUnion (R₁.srcO (Rho.fst ρ))

variable {R₁ R₂}

theorem mem_firstT {ρ : Rho (R₁.shape ++ R₂.shape)}
    {T : Finset (OPos (R₁.shape ++ R₂.shape))} {p : OPos R₁.shape} :
    p ∈ firstT R₁ R₂ ρ T ↔
    OPos.left p ∈ T ∨
    ∃ e ∈ R₂.given (Rho.snd (s := R₁.shape) ρ) (partR R₁.shape T), p ∈ R₁.srcO (Rho.fst ρ) e := by
  unfold firstT
  simp only [Finset.mem_union, Finset.mem_biUnion, mem_partL]

/-- What the composition shows of the first prover's oracles, the first view at firstT shows. -/
theorem shown_left {ρ : Rho (R₁.shape ++ R₂.shape)} {T : Finset (OPos (R₁.shape ++ R₂.shape))}
    {p : OPos R₁.shape} (h : (R₁.seq R₂).Shown ρ T (OPos.left p)) :
    R₁.Shown (Rho.fst ρ) (firstT R₁ R₂ ρ T) p := by
  rcases h with h | h | h
  · rcases (left_mem_seq_reads R₁ R₂ _ _).1 h with h | ⟨e, he, hp⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl (mem_firstT.2 (Or.inr ⟨e, mem_given.2 (Or.inl he), hp⟩)))
  · exact Or.inr (Or.inl (mem_firstT.2 (Or.inl h)))
  · rw [seq_blinded_left] at h
    exact Or.inr (Or.inr h)

/-- What the composition shows of the second prover's oracles, the second view at the second part of
T shows. -/
theorem shown_right {ρ : Rho (R₁.shape ++ R₂.shape)} {T : Finset (OPos (R₁.shape ++ R₂.shape))}
    {p : OPos R₂.shape} (h : (R₁.seq R₂).Shown ρ T (OPos.right (s := R₁.shape) p)) :
    R₂.Shown (Rho.snd (s := R₁.shape) ρ) (partR R₁.shape T) p := by
  rcases h with h | h | h
  · exact Or.inl ((right_mem_seq_reads R₁ R₂ _ _).1 h)
  · exact Or.inr (Or.inl (mem_partR.2 h))
  · rw [seq_blinded_right] at h
    exact Or.inr (Or.inr h)

/-- The symbols of y from which the symbols for the second simulator are computed are among those
given. -/
theorem srcE_subset_given {ρ : Rho (R₁.shape ++ R₂.shape)}
    {T : Finset (OPos (R₁.shape ++ R₂.shape))} {e : E₂.Pos}
    (he : e ∈ R₂.given (Rho.snd (s := R₁.shape) ρ) (partR R₁.shape T))
    {q : E₁.Pos} (hq : q ∈ R₁.srcE (Rho.fst ρ) e) : q ∈ (R₁.seq R₂).given ρ T := by
  rcases mem_given.1 he with he | ⟨r, hr, he⟩
  · exact mem_given.2 (Or.inl ((mem_seq_extReads R₁ R₂ _ _).2 (Or.inr ⟨e, he, hq⟩)))
  · refine mem_given.2
      (Or.inr
        ⟨OPos.right (s := R₁.shape) r, ?_, (mem_seq_tie_right R₁ R₂ _ _ _).2 ⟨e, he, Or.inl hq⟩⟩)
    exact hr.imp (right_mem_seq_reads R₁ R₂ _ _).2 mem_partR.1

/-- The symbols of y for the first simulator are among those given. -/
theorem given_first_subset (ρ : Rho (R₁.shape ++ R₂.shape))
    (T : Finset (OPos (R₁.shape ++ R₂.shape))) :
    R₁.given (Rho.fst ρ) (firstT R₁ R₂ ρ T) ⊆ (R₁.seq R₂).given ρ T := by
  intro q hq
  rcases mem_given.1 hq with hq | ⟨p, hp, hq⟩
  · exact mem_given.2 (Or.inl ((mem_seq_extReads R₁ R₂ _ _).2 (Or.inl hq)))
  · have viaLeft : (OPos.left p ∈ (R₁.seq R₂).reads ρ ∨ OPos.left p ∈ T) →
        q ∈ (R₁.seq R₂).given ρ T := fun h =>
      mem_given.2 (Or.inr ⟨OPos.left p, h, by rw [seq_tie_left]; exact hq⟩)
    rcases hp with hp | hp
    · exact viaLeft (Or.inl ((left_mem_seq_reads R₁ R₂ _ _).2 (Or.inl hp)))
    · rcases mem_firstT.1 hp with hp | ⟨e, he, hp⟩
      · exact viaLeft (Or.inr hp)
      · rcases mem_given.1 he with he | ⟨r, hr, he⟩
        · exact viaLeft (Or.inl ((left_mem_seq_reads R₁ R₂ _ _).2 (Or.inr ⟨e, he, hp⟩)))
        · refine mem_given.2
            (Or.inr ⟨OPos.right (s := R₁.shape) r,
                ?_,
                (mem_seq_tie_right R₁ R₂ _ _ _).2 ⟨e, he, Or.inr ⟨p, hp, hq⟩⟩⟩)
          exact hr.imp (right_mem_seq_reads R₁ R₂ _ _).2 mem_partR.1

/-- Under `a1`, `a1'`, `a2`, `a2'`: the view of the composition depends on the two transcripts only
through what the two views show. -/
theorem view_app_congr (ρ : Rho (R₁.shape ++ R₂.shape)) (T : Finset (OPos (R₁.shape ++ R₂.shape)))
    {τ₁ τ₁' : Tr R₁.shape} {τ₂ τ₂' : Tr R₂.shape} (a1 : τ₁.rho = Rho.fst ρ)
    (a1' : τ₁'.rho = Rho.fst ρ) (a2 : τ₂.rho = Rho.snd (s := R₁.shape) ρ)
    (a2' : τ₂'.rho = Rho.snd (s := R₁.shape) ρ) (b1 : τ₁.plains = τ₁'.plains)
    (b2 : τ₂.plains = τ₂'.plains)
    (c1 : ∀ p, R₁.Shown (Rho.fst ρ) (firstT R₁ R₂ ρ T) p → τ₁.read p = τ₁'.read p)
    (c2 : ∀ p, R₂.Shown (Rho.snd (s := R₁.shape) ρ) (partR R₁.shape T) p → τ₂.read p = τ₂'.read p) :
    (R₁.seq R₂).view T (Tr.app τ₁ τ₂) = (R₁.seq R₂).view T (Tr.app τ₁' τ₂') := by
  have hρ : (Tr.app τ₁ τ₂).rho = ρ := by rw [Tr.rho_app, a1, a2, Rho.app_fst_snd]
  have hρ' : (Tr.app τ₁' τ₂').rho = ρ := by rw [Tr.rho_app, a1', a2', Rho.app_fst_snd]
  refine view_congr (R := R₁.seq R₂) T (hρ.trans hρ'.symm) ?_ ?_
  · exact (Tr.plains_app τ₁ τ₂).trans (by rw [b1, b2]; exact (Tr.plains_app τ₁' τ₂').symm)
  · intro p hp
    have hp' : (R₁.seq R₂).Shown ρ T p := hρ ▸ hp
    rcases left_or_right p with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · refine (Tr.read_left_eq_iff (Tr.app τ₁ τ₂) (Tr.app τ₁' τ₂') q).2 ?_
      rw [Tr.fst_app, Tr.fst_app]
      exact c1 q (shown_left hp')
    · refine (Tr.read_right_eq_iff (Tr.app τ₁ τ₂) (Tr.app τ₁' τ₂') q).2 ?_
      rw [Tr.snd_app, Tr.snd_app]
      exact c2 q (shown_right hp')

/-! ## 6. The simulator -/

variable (R₁ R₂)

/-- From the first transcript and what the second simulator wrote: what the composition shows. -/
def glue (ρ₂ : Rho R₂.shape) (T : Finset (OPos (R₁.shape ++ R₂.shape)))
    (τ₁ : Tr R₁.shape) (o₂ : Option (View R₂)) : Option (View (R₁.seq R₂)) :=
  o₂.bind fun V₂ => (pick (V₂.Fits ρ₂)).map fun τ₂ => (R₁.seq R₂).view T (Tr.app τ₁ τ₂)

variable {R₁ R₂}

/-- Steps 2 and 3 of the simulator: from the view that the first simulator wrote. -/
def simCont (S₂ : Honest.Sim R₂) (x : X₁) (ρ : Rho (R₁.shape ++ R₂.shape))
    (T : Finset (OPos (R₁.shape ++ R₂.shape))) (a : E₁.Pos → Option E₁.Sym) (V₁ : View R₁) :
    PMF (Option (View (R₁.seq R₂))) :=
  (pick fun z : E₁.Str × Tr R₁.shape => E₁.Fits a z.1 ∧ V₁.Fits (Rho.fst ρ) z.2).elim
      (PMF.pure none) fun z =>
    (R₁.out x z.1 z.2).elim (PMF.pure none) fun x₂ =>
      (S₂ x₂ (Rho.snd (s := R₁.shape) ρ) (partR R₁.shape T)
          (E₂.ans (R₂.given (Rho.snd (s := R₁.shape) ρ) (partR R₁.shape T)) (R₁.imp z.1 z.2))).map
        (glue R₁ R₂ (Rho.snd (s := R₁.shape) ρ) T z.2)

open Classical in
/-- The simulator of the composition. -/
def simSeq (S₁ : Honest.Sim R₁) (S₂ : Honest.Sim R₂) :
    Honest.Sim (R₁.seq R₂) := fun x ρ T a =>
  (S₁ x (Rho.fst (s := R₁.shape) (t := R₂.shape) ρ) (firstT R₁ R₂ ρ T) fun p =>
      if p ∈ R₁.given (Rho.fst (s := R₁.shape) (t := R₂.shape) ρ) (firstT R₁ R₂ ρ T) then a p
      else none).bind fun o₁ =>
    o₁.elim (PMF.pure none) (simCont S₂ x ρ T a)

/-- Under `a1`, `a2`: what is glued from a true second view is the true view of the composition. -/
theorem glue_view (ρ : Rho (R₁.shape ++ R₂.shape)) (T : Finset (OPos (R₁.shape ++ R₂.shape)))
    {τ₁ : Tr R₁.shape} {τ₂ : Tr R₂.shape} (a1 : τ₁.rho = Rho.fst ρ)
    (a2 : τ₂.rho = Rho.snd (s := R₁.shape) ρ) :
    glue R₁ R₂ (Rho.snd (s := R₁.shape) ρ) T τ₁ (some (R₂.view (partR R₁.shape T) τ₂)) =
      some ((R₁.seq R₂).view T (Tr.app τ₁ τ₂)) := by
  obtain ⟨τ, hτ, hF⟩ := pick_spec
    (P := (R₂.view (partR R₁.shape T) τ₂).Fits (Rho.snd (s := R₁.shape) ρ))
    ⟨τ₂, a2 ▸ view_fits _ τ₂⟩
  show (pick _).map _ = _
  rw [hτ, Option.map_some]
  exact congrArg some
    (view_app_congr ρ T a1 a1 hF.1 a2 rfl hF.2.1 (fun _ _ => rfl) fun p hp => hF.read_eq (a2 ▸ hp))

/-- Steps 2 and 3 on a true first view: the second simulator on the true middle statement, glued to
the true first transcript. (not all hypotheses are named here: see the statement below) -/
theorem simCont_view (hL : R₁.IsLocal) (S₂ : Honest.Sim R₂) (x : X₁) (y : E₁.Str)
    (ρ : Rho (R₁.shape ++ R₂.shape)) (T : Finset (OPos (R₁.shape ++ R₂.shape))) (τ₁ : Tr R₁.shape)
    (a1 : τ₁.rho = Rho.fst ρ) (x₂ : X₂) (hout : R₁.out x y τ₁ = some x₂) :
    simCont S₂ x ρ T (E₁.ans ((R₁.seq R₂).given ρ T) y) (R₁.view (firstT R₁ R₂ ρ T) τ₁) =
      (S₂ x₂ (Rho.snd (s := R₁.shape) ρ) (partR R₁.shape T)
          (E₂.ans (R₂.given (Rho.snd (s := R₁.shape) ρ) (partR R₁.shape T)) (R₁.imp y τ₁))).map
        (glue R₁ R₂ (Rho.snd (s := R₁.shape) ρ) T τ₁) := by
  obtain ⟨z, hz, hE, hV⟩ := pick_spec
    (P := fun z : E₁.Str × Tr R₁.shape =>
        E₁.Fits (E₁.ans ((R₁.seq R₂).given ρ T) y) z.1 ∧
        (R₁.view (firstT R₁ R₂ ρ T) τ₁).Fits (Rho.fst ρ) z.2)
    ⟨(y, τ₁), E₁.fits_ans _ y, a1 ▸ view_fits _ τ₁⟩
  have hr : z.2.rho = τ₁.rho := hV.1.trans a1.symm
  have h1 : R₁.out x z.1 z.2 = some x₂ := by
    rw [← hout]
    refine hL.out x z.1 y z.2 τ₁ hr hV.2.1 (fun p hp => hE.rd_eq ?_)
      (fun p hp => hV.read_eq (Or.inl (hr ▸ hp)))
    exact given_first_subset ρ T (mem_given.2 (Or.inl (hV.1 ▸ hp)))
  have h2 : E₂.ans (R₂.given (Rho.snd (s := R₁.shape) ρ) (partR R₁.shape T)) (R₁.imp z.1 z.2) =
      E₂.ans (R₂.given (Rho.snd (s := R₁.shape) ρ) (partR R₁.shape T)) (R₁.imp y τ₁) := by
    refine E₂.ans_congr fun e he =>
      hL.imp z.1 y z.2 τ₁ e hr hV.2.1
        (fun p hp => hE.rd_eq (srcE_subset_given he (hV.1 ▸ hp))) fun p hp => hV.read_eq ?_
    exact Or.inr (Or.inl (mem_firstT.2 (Or.inr ⟨e, he, hV.1 ▸ hp⟩)))
  have h3 : glue R₁ R₂ (Rho.snd (s := R₁.shape) ρ) T z.2 =
      glue R₁ R₂ (Rho.snd (s := R₁.shape) ρ) T τ₁ := by
    funext o₂
    cases o₂ with
    | none => rfl
    | some V₂ =>
        exact pick_map_congr fun τ₂ hτ₂ =>
          view_app_congr ρ T hV.1 a1 hτ₂.1 hτ₂.1 hV.2.1 rfl
            (fun p hp => hV.read_eq (a1 ▸ hp)) fun _ _ => rfl
  unfold simCont
  rw [hz, Option.elim_some, h1, Option.elim_some, h2, h3]

end Seq

/-! ## 7. The theorem -/

/-- Under `hL`, `hA`, `h₁`, `h₂`: honest-verifier exact zero knowledge (`Honest.ExactWith`,
Ior/Honest.lean) composes, at the composed budget, with the simulator named. -/
theorem exactWith_seq {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃} {W₁ W₂ W₃ : Type}
    {H₁ : R₁.Honest W₁ W₂} {H₂ : R₂.Honest W₂ W₃} {Ra : X₁ → E₁.Str → W₁ → Prop}
    {Rb : X₂ → E₂.Str → W₂ → Prop} {b₁ : Rho R₁.shape → Finset (OPos R₁.shape) → Prop}
    {b₂ : Rho R₂.shape → Finset (OPos R₂.shape) → Prop} {S₁ : Honest.Sim R₁}
    {S₂ : Honest.Sim R₂} (hL : R₁.IsLocal) (hA : H₁.Acc Ra Rb)
    (h₁ : H₁.ExactWith Ra b₁ S₁) (h₂ : H₂.ExactWith Rb b₂ S₂) :
    (H₁.seq H₂).ExactWith Ra (budSeq R₁ R₂ b₁ b₂) (simSeq S₁ S₂) := by
  intro x y w hR ρ hρ T hT
  obtain ⟨hb₂, hb₁⟩ := hT (partL T) (partR R₁.shape T) (fun _ => mem_partL) (fun _ => mem_partR)
  have hρ₁ : Rho.fst (s := R₁.shape) (t := R₂.shape) ρ ∉ H₁.Hid w x := fun h => hρ (Or.inl h)
  have hρ₂ : Rho.fst (s := R₁.shape) (t := R₂.shape) ρ ∉ H₁.Bad →
      ∀ c, Rho.snd (s := R₁.shape) (t := R₂.shape) ρ ∉
        H₂.Hid ((H₁.strat w x c).run (Rho.fst (s := R₁.shape) (t := R₂.shape) ρ)).2.2
          ((H₁.strat w x c).run (Rho.fst (s := R₁.shape) (t := R₂.shape) ρ)).2.1 :=
    fun hB c h => hρ (Or.inr ⟨hB, c, h⟩)
  have e₁ := h₁ x y w hR (Rho.fst (s := R₁.shape) (t := R₂.shape) ρ) hρ₁ (firstT R₁ R₂ ρ T) hb₁
  unfold simSeq
  rw [E₁.cut_ans (given_first_subset ρ T) y, ← e₁]
  by_cases hw₁ : Rho.fst (s := R₁.shape) (t := R₂.shape) ρ ∈ H₁.withheld w x
  · have hw : ρ ∈ (H₁.seq H₂).withheld w x :=
      hw₁.elim (fun h => Or.inl (Or.inl h)) fun h => absurd h hρ₁
    rw [H₁.output_of_mem _ hw₁, PMF.pure_bind, (H₁.seq H₂).output_of_mem T hw]
    rfl
  · replace hρ₂ := hρ₂ fun h => hw₁ (Or.inl h)
    rw [H₁.output_of_not_mem _ hw₁, PMF.bind_map]
    have key : ∀ c₁ : H₁.Coin,
        simCont S₂ x ρ T (E₁.ans ((R₁.seq R₂).given ρ T) y)
            (R₁.view (firstT R₁ R₂ ρ T)
              ((H₁.strat w x c₁).run (Rho.fst (s := R₁.shape) (t := R₂.shape) ρ)).1) =
          (H₂.output ((H₁.strat w x c₁).run (Rho.fst (s := R₁.shape) (t := R₂.shape) ρ)).2.2
              ((H₁.strat w x c₁).run (Rho.fst (s := R₁.shape) (t := R₂.shape) ρ)).2.1
              (Rho.snd (s := R₁.shape) (t := R₂.shape) ρ) (partR R₁.shape T)).map
            (glue R₁ R₂ (Rho.snd (s := R₁.shape) (t := R₂.shape) ρ) T
              ((H₁.strat w x c₁).run (Rho.fst (s := R₁.shape) (t := R₂.shape) ρ)).1) := fun c₁ => by
      obtain ⟨ho, hRb⟩ := hA x y w c₁ _ hR hw₁
      rw [simCont_view hL S₂ x y ρ T _ (Strat.rho_run _ _) _ ho, h₂ _ _ _ hRb _ (hρ₂ c₁) _ hb₂]
    have step : ((fun o₁ : Option (View R₁) =>
            o₁.elim (PMF.pure none) (simCont S₂ x ρ T (E₁.ans ((R₁.seq R₂).given ρ T) y))) ∘
          fun c =>
            some (R₁.view (firstT R₁ R₂ ρ T)
                ((H₁.strat w x c).run (Rho.fst (s := R₁.shape) (t := R₂.shape) ρ)).1)) =
        fun c₁ => _ := funext key
    rw [step]
    by_cases hB₂ : Rho.snd (s := R₁.shape) (t := R₂.shape) ρ ∈ H₂.Bad
    · have hw : ρ ∈ (H₁.seq H₂).withheld w x := Or.inl (Or.inr hB₂)
      rw [(H₁.seq H₂).output_of_mem T hw]
      have : ∀ c₁ : H₁.Coin,
          (H₂.output ((H₁.strat w x c₁).run (Rho.fst (s := R₁.shape) (t := R₂.shape) ρ)).2.2
                ((H₁.strat w x c₁).run (Rho.fst (s := R₁.shape) (t := R₂.shape) ρ)).2.1
                (Rho.snd (s := R₁.shape) (t := R₂.shape) ρ) (partR R₁.shape T)).map
              (glue R₁ R₂ (Rho.snd (s := R₁.shape) (t := R₂.shape) ρ) T
                ((H₁.strat w x c₁).run (Rho.fst (s := R₁.shape) (t := R₂.shape) ρ)).1) =
            PMF.pure none := fun c₁ => by
        rw [H₂.output_of_mem _ (Or.inl hB₂), PMF.pure_map]
        rfl
      rw [funext this, PMF.bind_const]
    · have hw : ρ ∉ (H₁.seq H₂).withheld w x := by
        rintro ((h | h) | h)
        · exact hw₁ (Or.inl h)
        · exact hB₂ h
        · exact hρ h
      rw [(H₁.seq H₂).output_of_not_mem T hw]
      refine (map_unif_prod (α := H₁.Coin) (β := H₂.Coin) _).trans
        (congrArg _ (funext fun c₁ => ?_))
      rw [H₂.output_of_not_mem _ (fun h => h.elim hB₂ (hρ₂ c₁)), PMF.map_comp]
      refine congrArg (fun f => PMF.map f (unif H₂.Coin)) (funext fun c₂ => ?_)
      show some ((R₁.seq R₂).view T
            ((Strat.bind (H₁.strat w x c₁) fun o => H₂.strat o.2 o.1 c₂).run ρ).1) =
        glue R₁ R₂ _ T _ (some _)
      rw [glue_view ρ T (Strat.rho_run _ _) (Strat.rho_run _ _), Strat.run_bind]

end IOR

theorem exact_seq : Spec.exact_seq := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ Ra Rb b₁ b₂ hL hA ⟨S₁, h₁⟩ ⟨S₂, h₂⟩
  exact ⟨IOR.simSeq S₁ S₂, IOR.exactWith_seq hL hA h₁ h₂⟩

end Iop
