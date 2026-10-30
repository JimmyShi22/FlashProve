-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/OnlineHonView.lean: what one slot of "an IOR F in every slot, then a batch IOP Q" shows, put
together from what F's run shows, what Q's run shows and given answers of the shared oracle
(`ans`).

Definitions and lemmas for Ior/OnlineHon.lean, on the honest prover's side of a composition: an
interactive oracle reduction (IOR) run for each instance of a batch, then an interactive oracle
proof for the whole batch. What a slot is: the head of Ior/OnlineHon.lean.

Notions of other files, for an IOR R (here F, `Q.ior`, `F.seq Q.ior`):
  In `furth`, `glue`, `info` and the lemmas on them, T is a set of further positions in the
    oracles of the composition `F.seq Q.ior`; in `rep`, `read_eq_of_view`, in F's; in `mem_given`
    and in the rows below, in R's (further positions: `IOR.view`, Ior/Honest.lean).
  `R.tie ρ p` is a finite set of positions of the implicit instance, for each ρ and each position
    p of the prover's oracles; it enters `R.given`. (Ior/Ior.lean.)
  `R.given ρ T` is the set of positions of the implicit instance that the verifier reads at ρ,
    together with `R.tie ρ p` for every p that the verifier reads in the prover's oracles or that
    is in T. (Ior/Honest.lean.)
  `R.srcO ρ q`, `R.srcE ρ q` (Ior/Ior.lean), the sources of q: the positions of the prover's
    oracles, and of the old implicit instance, from whose symbols the symbol at q of the new
    implicit instance is computed (data; the condition: `IOR.IsLocal`, Ior/Ior.lean).
  `R.blinded p` is a Boolean mark at each position p of the prover's oracles; `R.view` has the
    symbol at every position whose mark is false. (Ior/Ior.lean; Ior/Honest.lean.)

Main names:
  `orcApp`: the shown symbols of two shapes in a row.
    `orcApp_read`: under the hypotheses of its statement, for a joined transcript they are the
      shown symbols of the two parts.
  `furth`: the positions at which F is simulated, namely the part of T in F's shape and the
    sources of all that Q's simulator is given.
  `glue`: the disclosed view of the composition with the further positions T, from F's view at
    `furth`, Q's disclosed view at its part of T, and given answers of the shared oracle.
    `dviewT_app`: under the hypotheses of its statement, it is that view.
  `rep`: some implicit instance and transcript, the transcript showing a given view (taken by
    choice: a simulator need not be computable here).
  `info`: from F's view and given answers of the shared oracle, the explicit part that F's
    verifier outputs and the symbols of (shared oracle, slot's own oracles) that Q's simulator is
    given.
    `info_view`: under the hypotheses of its statement, on the view of a run it returns the true
      ones. Under the hypotheses of its statement, this rests on `F.IsLocal`: both are functions
      of x, ρ and T, of the plain parts, of symbols that the view shows and of given answers of
      the shared oracle.

Limits: probability is not here. No declaration of this file has a `PMF`, an honest side or a
simulator's type. ("The simulator of the composition": `OnlineHon.sim`, Ior/OnlineHon.lean.)

Terms: lean/GLOSSARY.md.
-/
import Ior.Batch
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
namespace OnlineHon

/-! ## 1. Shown symbols of two shapes in a row -/

def orcApp :
    {s t : Shape} → ((p : OPos s) → Option (OSym s p)) → ((p : OPos t) → Option (OSym t p)) →
    (p : OPos (s ++ t)) → Option (OSym (s ++ t) p)
  | [], _, _, g => g
  | _ :: _, _, f, g => fun p => match p with
    | .inl p => f (.inl p)
    | .inr p => orcApp (fun q => f (.inr q)) g p

theorem orcApp_read :
    ∀ {s t : Shape} (τ₁ : Tr s) (τ₂ : Tr t) (P : OPos (s ++ t) → Prop) (P₁ : OPos s → Prop)
        (P₂ : OPos t → Prop) [DecidablePred P] [DecidablePred P₁] [DecidablePred P₂],
      (∀ p, P (OPos.left p) ↔ P₁ p) → (∀ p, P (OPos.right (s := s) p) ↔ P₂ p) →
      (fun p => if P p then some ((Tr.app τ₁ τ₂).read p) else none) =
        orcApp (fun p => if P₁ p then some (τ₁.read p) else none)
          (fun p => if P₂ p then some (τ₂.read p) else none)
  | [], _, _, τ₂, P, _, P₂, _, _, _, _, h2 => funext fun p => by
      show (if P p then some (τ₂.read p) else none) = if P₂ p then some (τ₂.read p) else none
      exact if_congr (h2 p) rfl rfl
  | r :: s, t, (m, c, τ₁), τ₂, P, P₁, P₂, _, _, _, h1, h2 => funext fun p => by
      cases p with
      | inl p =>
          show (if P (.inl p) then some (r.rd m.1 p) else none) =
            if P₁ (.inl p) then some (r.rd m.1 p) else none
          exact if_congr (h1 (.inl p)) rfl rfl
      | inr p =>
          exact congrFun
            (orcApp_read τ₁ τ₂ (fun p => P (.inr p)) (fun p => P₁ (.inr p)) P₂
              (fun p => h1 (.inr p)) h2) p

theorem dview_ext {X : Type} {E : ExtSpec} {Q : InteractiveOracleProof X E} {a b : DView Q}
    (h1 : a.plains = b.plains) (h2 : a.ext = b.ext) (h3 : a.orc = b.orc) : a = b := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  obtain rfl : a1 = b1 := h1
  obtain rfl : a2 = b2 := h2
  obtain rfl : a3 = b3 := h3
  rfl

open Classical in
theorem mem_given {Xi Xo : Type} {Ei Eo : ExtSpec} (R : IOR Xi Ei Xo Eo) (ρ : Rho R.shape)
    (T : Finset (OPos R.shape)) (p : Ei.Pos) :
    p ∈ R.given ρ T ↔ p ∈ R.extReads ρ ∨ ∃ q, (q ∈ R.reads ρ ∨ q ∈ T) ∧ p ∈ R.tie ρ q := by
  unfold IOR.given
  rw [Finset.mem_union, Finset.mem_biUnion]
  simp only [Finset.mem_union]

/-! ## 2. The disclosed view of the composition -/

section View
variable {X Xl : Type} {E0 Eo : ExtSpec} (F : IOR X E0 Xl Eo) (Q : BIOP Xl Eo)

open Classical in
/-- The sources, in F's oracles, of all that Q's verifier reads. -/
def furth0 (ρ : Rho (F.shape ++ Q.ior.shape)) : Finset (OPos F.shape) :=
  (Q.ior.extReads (Rho.snd (s := F.shape) ρ)).biUnion (F.srcO (Rho.fst ρ))

open Classical in
/-- The further positions at which F is simulated: the part of T in F's shape, and the sources of
all that Q's simulator is given. -/
def furth (ρ : Rho (F.shape ++ Q.ior.shape))
    (T : Finset (OPos (F.shape ++ Q.ior.shape))) : Finset (OPos F.shape) :=
  OPos.partL T ∪
    (Q.ior.given (Rho.snd (s := F.shape) ρ) (OPos.partR (s := F.shape) T)).biUnion
      (F.srcO (Rho.fst ρ))

open Classical in
/-- The disclosed view of the composition with the further positions T, from the two parts and given
answers of the shared oracle. Of F's view, which was made at more positions, only what the
composition shows is kept. -/
def glue (ρ : Rho (F.shape ++ Q.ior.shape))
    (T : Finset (OPos (F.shape ++ Q.ior.shape))) (ans : E0.Pos → Option E0.Sym)
    (v : F.View) (d : DView Q.ior.toInteractiveOracleProof) :
    DView (F.seq Q.ior).toInteractiveOracleProof where
  plains := Plains.app v.plains d.plains
  ext := fun p => if p ∈ (F.seq Q.ior).given ρ T then ans p else none
  orc := orcApp
    (fun p =>
      if (p ∈ F.reads (Rho.fst ρ) ∨ p ∈ furth0 F Q ρ) ∨ p ∈ OPos.partL T ∨ F.blinded p = false then
        v.orc p
      else none) d.orc

theorem blinded_left (p : OPos F.shape) : (F.seq Q.ior).blinded (OPos.left p) = F.blinded p := by
  simp only [IOR.seq, OPos.split_left]

theorem blinded_right (p : OPos Q.ior.shape) :
    (F.seq Q.ior).blinded (OPos.right (s := F.shape) p) = Q.ior.blinded p := by
  simp only [IOR.seq, OPos.split_right]

open Classical in
theorem tie_left (ρ : Rho (F.shape ++ Q.ior.shape)) (p : OPos F.shape) :
    (F.seq Q.ior).tie ρ (OPos.left p) = F.tie (Rho.fst ρ) p := by
  simp only [IOR.seq, OPos.split_left]

open Classical in
theorem tie_right (ρ : Rho (F.shape ++ Q.ior.shape)) (p : OPos Q.ior.shape) :
    (F.seq Q.ior).tie ρ (OPos.right (s := F.shape) p) =
      (Q.ior.tie (Rho.snd (s := F.shape) ρ) p).biUnion (F.srcE (Rho.fst ρ)) ∪
        ((Q.ior.tie (Rho.snd (s := F.shape) ρ) p).biUnion (F.srcO (Rho.fst ρ))).biUnion
          (F.tie (Rho.fst ρ)) := by
  simp only [IOR.seq, OPos.split_right]

theorem mem_partL {s t : Shape} (T : Finset (OPos (s ++ t))) (p : OPos s) :
    p ∈ OPos.partL T ↔ OPos.left p ∈ T :=
  Finset.mem_preimage

theorem mem_partR {s t : Shape} (T : Finset (OPos (s ++ t))) (p : OPos t) :
    p ∈ OPos.partR (s := s) T ↔ OPos.right (s := s) p ∈ T :=
  Finset.mem_preimage

open Classical in
theorem mem_reads_left (ρ : Rho (F.shape ++ Q.ior.shape)) (p : OPos F.shape) :
    OPos.left p ∈ (F.seq Q.ior).reads ρ ↔ p ∈ F.reads (Rho.fst ρ) ∨ p ∈ furth0 F Q ρ := by
  show OPos.left p ∈
      (F.reads (Rho.fst ρ) ∪ furth0 F Q ρ).image OPos.left ∪
        (Q.ior.reads (Rho.snd (s := F.shape) ρ)).image (OPos.right (s := F.shape)) ↔
    _
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image, ← Finset.mem_union]
  constructor
  · rintro (⟨q, hq, h⟩ | ⟨q, _, h⟩)
    · rwa [← OPos.left_injective h]
    · exact absurd h.symm (OPos.left_ne_right p q)
  · exact fun h => Or.inl ⟨p, h, rfl⟩

open Classical in
theorem mem_reads_right (ρ : Rho (F.shape ++ Q.ior.shape)) (p : OPos Q.ior.shape) :
    OPos.right (s := F.shape) p ∈ (F.seq Q.ior).reads ρ ↔
    p ∈ Q.ior.reads (Rho.snd (s := F.shape) ρ) := by
  show OPos.right (s := F.shape) p ∈
      (F.reads (Rho.fst ρ) ∪ furth0 F Q ρ).image OPos.left ∪
        (Q.ior.reads (Rho.snd (s := F.shape) ρ)).image (OPos.right (s := F.shape)) ↔
    _
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro (⟨q, _, h⟩ | ⟨q, hq, h⟩)
    · exact absurd h (OPos.left_ne_right q p)
    · rwa [← OPos.right_injective h]
  · exact fun h => Or.inr ⟨p, h, rfl⟩

open Classical in
theorem furth0_sub (ρ : Rho (F.shape ++ Q.ior.shape)) (T : Finset (OPos (F.shape ++ Q.ior.shape)))
    {p : OPos F.shape} (h : p ∈ furth0 F Q ρ) : p ∈ furth F Q ρ T := by
  obtain ⟨q, hq, hp⟩ := Finset.mem_biUnion.mp h
  exact Finset.mem_union_right
    _ (Finset.mem_biUnion.mpr ⟨q, (mem_given _ _ _ _).mpr (Or.inl hq), hp⟩)

/-- Under `h₁`, `h₂`, `hans`: the disclosed view of a joined transcript, with further positions, is
glued from F's view and Q's disclosed view. -/
theorem dviewT_app (y : E0.Str) (yy : Eo.Str) (ρ : Rho (F.shape ++ Q.ior.shape))
    (T : Finset (OPos (F.shape ++ Q.ior.shape))) (τ₁ : Tr F.shape) (τ₂ : Tr Q.ior.shape)
    (h₁ : τ₁.rho = Rho.fst ρ) (h₂ : τ₂.rho = Rho.snd (s := F.shape) ρ)
    (ans : E0.Pos → Option E0.Sym)
    (hans : ∀ p ∈ (F.seq Q.ior).given ρ T, ans p = some (E0.rd y p)) :
    (F.seq Q.ior).dviewT T y (Tr.app τ₁ τ₂) =
      glue F Q ρ T ans (F.view (furth F Q ρ T) τ₁)
        (Q.ior.dviewT (OPos.partR (s := F.shape) T) yy τ₂) := by
  classical
  have hρ : (Tr.app τ₁ τ₂).rho = ρ := by rw [Tr.rho_app, h₁, h₂, Rho.app_fst_snd]
  subst hρ
  refine dview_ext (Tr.plains_app τ₁ τ₂) (funext fun p => ?_) ?_
  · by_cases hp : p ∈ (F.seq Q.ior).given (Tr.app τ₁ τ₂).rho T
    · exact (if_pos hp).trans ((hans p hp).symm.trans (if_pos hp).symm)
    · exact (if_neg hp).trans (if_neg hp).symm
  · have hf : (fun p =>
      if (p ∈ F.reads (Rho.fst (Tr.app τ₁ τ₂).rho) ∨ p ∈ furth0 F Q (Tr.app τ₁ τ₂).rho) ∨
        p ∈ OPos.partL T ∨ F.blinded p = false
          then (F.view (furth F Q (Tr.app τ₁ τ₂).rho T) τ₁).orc p else none)
        = fun p =>
          if (p ∈ F.reads (Rho.fst (Tr.app τ₁ τ₂).rho) ∨ p ∈ furth0 F Q (Tr.app τ₁ τ₂).rho) ∨
              p ∈ OPos.partL T ∨
              F.blinded p = false then some (τ₁.read p)
          else none := by
      funext p
      by_cases hp : (p ∈ F.reads (Rho.fst (Tr.app τ₁ τ₂).rho) ∨ p ∈ furth0 F Q (Tr.app τ₁ τ₂).rho) ∨
        p ∈ OPos.partL T ∨ F.blinded p = false
      · rw [if_pos hp, if_pos hp]
        refine if_pos ?_
        rcases hp with (hp | hp) | hp | hp
        · exact Or.inl (h₁ ▸ hp)
        · exact Or.inr (Or.inl (furth0_sub F Q _ T hp))
        · exact Or.inr (Or.inl (Finset.mem_union_left _ hp))
        · exact Or.inr (Or.inr hp)
      · rw [if_neg hp, if_neg hp]
    show _ = orcApp _ _
    rw [hf]
    refine @orcApp_read _ _ τ₁ τ₂
      (fun p =>
        p ∈ (F.seq Q.ior).reads (Tr.app τ₁ τ₂).rho ∨ p ∈ T ∨ (F.seq Q.ior).blinded p = false)
      (fun p =>
        (p ∈ F.reads (Rho.fst (Tr.app τ₁ τ₂).rho) ∨ p ∈ furth0 F Q (Tr.app τ₁ τ₂).rho) ∨
        p ∈ OPos.partL T ∨ F.blinded p = false)
      (fun p => p ∈ Q.ior.reads τ₂.rho ∨ p ∈ OPos.partR (s := F.shape) T ∨ Q.ior.blinded p = false)
      _ _ _ (fun p => ?_) (fun p => ?_)
    · beta_reduce
      rw [mem_reads_left, blinded_left, mem_partL]
    · beta_reduce
      rw [mem_reads_right, blinded_right, mem_partR, ← h₂]

end View

/-! ## 3. What Q's simulator is given, computed from F's view and given answers of the shared oracle
-/

section View
variable {X Xl : Type} {E0 Ej : ExtSpec} (F : IOR X E0 Xl (E0.prod Ej)) (Q : BIOP Xl (E0.prod Ej))

open Classical in
/-- Some implicit instance and transcript, the transcript showing the view v at ρ₁ and T. -/
def rep (ρ₁ : Rho F.shape) (T : Finset (OPos F.shape)) (v : F.View) :
    Option (E0.Str × Tr F.shape) :=
  if h : ∃ a : E0.Str × Tr F.shape, a.2.rho = ρ₁ ∧ F.view T a.2 = v then some h.choose else none

open Classical in
/-- From what F's run shows and given answers of the shared oracle: the explicit part that F's
verifier outputs, and the symbols that Q's simulator is given. -/
def info (x : X) (ρ : Rho (F.shape ++ Q.ior.shape))
    (T : Finset (OPos (F.shape ++ Q.ior.shape)))
    (ans : E0.Pos → Option E0.Sym) (v : Option F.View) :
    Option (Xl × ((E0.prod Ej).Pos → Option (E0.prod Ej).Sym)) :=
  v.bind fun v =>
      (rep F (Rho.fst ρ) (furth F Q ρ T) v).bind fun a => (F.out x a.1 a.2).map fun xl =>
    (xl, fun p => if p ∈ Q.ior.given (Rho.snd (s := F.shape) ρ) (OPos.partR (s := F.shape) T) then
      (match p with
        | .inl p => (ans p).map Sum.inl
        | .inr q => some (Sum.inr (Ej.rd (F.imp a.1 a.2).2 q))) else none)

variable {F}

theorem read_eq_of_view {T : Finset (OPos F.shape)} {τ τ' : Tr F.shape} (hρ : τ.rho = τ'.rho)
    (hv : F.view T τ = F.view T τ') (p : OPos F.shape) (hp : p ∈ F.reads τ.rho ∨ p ∈ T) :
    τ.read p = τ'.read p := by
  classical
  have h := congrFun (congrArg IOR.View.orc hv) p
  have e1 : (F.view T τ).orc p = some (τ.read p) :=
    if_pos (hp.elim Or.inl fun h => Or.inr (Or.inl h))
  have e2 : (F.view T τ').orc p = some (τ'.read p) :=
    if_pos (hp.elim (fun h => Or.inl (hρ ▸ h)) fun h => Or.inr (Or.inl h))
  rw [e1, e2] at h
  exact Option.some.inj h

variable (F)

open Classical in
/-- Under `hsl`: a position of the shared oracle that Q's simulator is given is one that the
simulator of the composition is given. -/
theorem mem_given_seq (hsl : ∀ ρ p, F.srcE ρ (Sum.inl p) = {p} ∧ F.srcO ρ (Sum.inl p) = ∅)
    (ρ : Rho (F.shape ++ Q.ior.shape)) (T : Finset (OPos (F.shape ++ Q.ior.shape))) (p : E0.Pos)
    (hp : Sum.inl p ∈ Q.ior.given (Rho.snd (s := F.shape) ρ) (OPos.partR (s := F.shape) T)) :
    p ∈ (F.seq Q.ior).given ρ T := by
  have hs : p ∈ F.srcE (Rho.fst ρ) (Sum.inl p) := by
    rw [(hsl _ p).1]
    exact Finset.mem_singleton_self p
  rcases (mem_given _ _ _ _).mp hp with hp | ⟨p', hp', ht⟩
  · refine (mem_given _ _ _ _).mpr (Or.inl ?_)
    show p ∈ F.extReads (Rho.fst ρ) ∪
        (Q.ior.extReads (Rho.snd (s := F.shape) ρ)).biUnion (F.srcE (Rho.fst ρ))
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨Sum.inl p, hp, hs⟩)
  · refine (mem_given _ _ _ _).mpr (Or.inr ⟨OPos.right (s := F.shape) p', ?_, ?_⟩)
    · rcases hp' with h | h
      · exact Or.inl ((mem_reads_right F Q ρ p').mpr h)
      · exact Or.inr ((mem_partR T p').mp h)
    · rw [tie_right]
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨Sum.inl p, ht, hs⟩)

/-- Under the hypotheses below: on the view of a run, `info` returns the true output and the true
symbols. -/
theorem info_view (hL : F.IsLocal) (hE : ∀ ρ, F.extReads ρ = ∅)
    (hsE : ∀ ρ q, F.srcE ρ (Sum.inr q) = ∅)
    (hsl : ∀ ρ p, F.srcE ρ (Sum.inl p) = {p} ∧ F.srcO ρ (Sum.inl p) = ∅) (x : X) (y : E0.Str)
    (xl : Xl) (ρ : Rho (F.shape ++ Q.ior.shape)) (T : Finset (OPos (F.shape ++ Q.ior.shape)))
    (τ : Tr F.shape) (hτ : τ.rho = Rho.fst ρ) (hout : F.out x y τ = some xl)
    (ans : E0.Pos → Option E0.Sym)
    (hans : ∀ p ∈ (F.seq Q.ior).given ρ T, ans p = some (E0.rd y p)) :
    info F Q x ρ T ans (some (F.view (furth F Q ρ T) τ)) =
      some (xl, (E0.prod Ej).ans
            (Q.ior.given (Rho.snd (s := F.shape) ρ) (OPos.partR (s := F.shape) T))
            (y, (F.imp y τ).2)) := by
  classical
  have hex : ∃ a : E0.Str × Tr F.shape,
      a.2.rho = Rho.fst ρ ∧ F.view (furth F Q ρ T) a.2 = F.view (furth F Q ρ T) τ :=
    ⟨(y, τ), hτ, rfl⟩
  obtain ⟨ha1, ha2⟩ := hex.choose_spec
  have hrep : rep F (Rho.fst ρ) (furth F Q ρ T) (F.view (furth F Q ρ T) τ) = some hex.choose :=
    dif_pos hex
  generalize hex.choose = a at ha1 ha2 hrep
  have hρ : τ.rho = a.2.rho := hτ.trans ha1.symm
  have hpl : τ.plains = a.2.plains := (congrArg IOR.View.plains ha2).symm
  have ho : F.out x a.1 a.2 = some xl := by
    rw [← hout]
    refine (hL.out x y a.1 τ a.2 hρ hpl (fun p hp => ?_) fun p hp =>
      read_eq_of_view hρ ha2.symm p (Or.inl hp)).symm
    rw [hE] at hp
    exact absurd hp (Finset.notMem_empty p)
  show ((rep F (Rho.fst ρ) (furth F Q ρ T) (F.view (furth F Q ρ T) τ)).bind fun a =>
      (F.out x a.1 a.2).map fun xl => _) = _
  rw [hrep]
  show ((F.out x a.1 a.2).map fun xl => _) = _
  rw [ho]
  refine congrArg some (Prod.ext rfl (funext fun p => ?_))
  by_cases hp : p ∈ Q.ior.given (Rho.snd (s := F.shape) ρ) (OPos.partR (s := F.shape) T)
  · refine (if_pos hp).trans (Eq.trans ?_ (if_pos hp).symm)
    cases p with
    | inl p =>
        show (ans p).map Sum.inl = some (Sum.inl (E0.rd y p))
        rw [hans p (mem_given_seq F Q hsl ρ T p hp)]
        rfl
    | inr q =>
        have h := hL.imp y a.1 τ a.2 (Sum.inr q) hρ hpl (fun p hp' => by
          rw [hsE] at hp'
          exact absurd hp' (Finset.notMem_empty p)) (fun p hp' => read_eq_of_view hρ ha2.symm p (Or.inr (by
            rw [hτ] at hp'
            exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨Sum.inr q, hp, hp'⟩))))
        have h' : (Sum.inr (Ej.rd (F.imp y τ).2 q) : E0.Sym ⊕ Ej.Sym) =
            Sum.inr (Ej.rd (F.imp a.1 a.2).2 q) := h
        show some (Sum.inr (Ej.rd (F.imp a.1 a.2).2 q) : E0.Sym ⊕ Ej.Sym) =
          some (Sum.inr (Ej.rd (F.imp y τ).2 q))
        rw [h']
  · exact (if_neg hp).trans (if_neg hp).symm

end View

end OnlineHon
end Iop
