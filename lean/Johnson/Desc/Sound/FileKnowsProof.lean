-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FileKnowsProof.lean: the proof of `FileKnows` (Johnson/Desc/Sound/FileRule.lean).

The road, for each of the three chains: `chainRule` (FoldIsRowProof.lean), carried to the chain's
own list of rounds (`chainOwn`, by `know_cast`); the condition in front taken into the relation
(`know_all`); along the function that makes the chain's first record and the one that packs what it
hands on (`know_sim`, with `stage_map`); behind the silent round (`know_front`); and the equation
that the row's stage puts out just that (`know_congr`). At the first chain: a stage whose first own
tree has the number 0 does not read the trees at hand (`stage_zero`).

Limits: those of the sheet.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FileRule
import Johnson.Desc.Sound.KnowMoves
import Johnson.Desc.Sound.FoldIsRowProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open _root_.Iop.Reduction (orOff)
open _root_.Compile.Joined (plainRound)

/-- Knowledge soundness hangs on what a reduction puts out alone. -/
theorem know_congr {A B WA WB : Type} (K : Reduction A B) (out' : A → Iop.Tr K.shape → Option B)
    (h : ∀ a τ, out' a τ = K.out a τ) (on : A → Prop) (RA : A → WA → Prop) (RB : B → WB → Prop)
    (ext : A → Iop.Tr K.shape → WB → WA) (ε : Err K.shape) (k : K.Know on RA RB ext ε) :
    (⟨K.shape, out'⟩ : Reduction A B).Know on RA RB ext ε := by
  intro a ha
  refine Doomed.mono _ _ ?_ (k a ha)
  intro τ hτ b w hb hw
  exact hτ b w ((h a τ).symm.trans hb) hw

variable {C : CK}

/-- `ChainRule`'s conclusion at the chain's own list of rounds. -/
theorem chainOwn {S Cl W : Type} {F : Frame} (name : String) (on : ℕ → S × F.E.Str → Prop)
    (R : ℕ → S × F.E.Str → W → Prop) (d : W) (p : Piece C F S Cl W) (l : List (Piece C F S Cl W))
    (ds : List RDT) (e : rowData p l = ds) (h : (rowIOR p l).shape = uLT C ds) (ht : Tiled p l)
    (hg : EachGood on R 0 (p :: l)) :
    (chainIOR C F name ((p :: l).map (·.b)) p.base ds (rowBack p l)).red.Know (on 0) (R 0)
      (orOff (on (1 + l.length)) (R (1 + l.length))) (extOwn p l ds h d) (errOwn p l ds h) := by
  subst e
  exact know_cast h _ _ _ _ _ _ (chainRule S Cl W C F name on R d p l h ht hg)

/-- A stage whose run first makes a record of the instance and at the end packs what it hands on. -/
theorem stage_map {Xi Xo S S' : Type} (St : StageD) (r : S → Fmt.View → Option S') (i : Xi → S)
    (o : Xi → S' → Xo) (x : Xi) (y : St.Ei.Str) (τ : Iop.Tr (uLT C St.ds)) :
    (stageIOR C St fun x v => (r (i x) v).map (o x)).red.out (x, y) τ =
      ((stageIOR C St r).red.out (i x, y) τ).map fun b => (o x b.1, b.2) := by
  show ((if sTests C St y τ then (r (i x) (sView C St y τ)).map (o x) else none).map fun xo =>
      (xo, ((y.1, sLeft C St y τ) : St.Eo.Str))) =
    ((if sTests C St y τ then r (i x) (sView C St y τ) else none).map fun xo =>
      (xo, ((y.1, sLeft C St y τ) : St.Eo.Str))).map fun b => (o x b.1, b.2)
  cases sTests C St y τ with
  | false => rfl
  | true => cases r (i x) (sView C St y τ) <;> rfl

section Zero
variable (a : ℕ) (L : List LeftT) (ds : List RDT) (key : ℕ → ℕ)
  (y₁ : (oneExternalString (2 ^ a) SgX).Str) (e : (EjOf []).Str) (z : (EjOf L).Str) (τ : Iop.Tr (uLT C ds))

theorem zero_depth :
    (⟨a, 0, [], ds, key, L⟩ : StageD).depth = (⟨a, 0, L, ds, key, L⟩ : StageD).depth := by
  funext j
  show (if j < 0 then _ else _) = (if j < 0 then _ else _)
  rw [if_neg (Nat.not_lt_zero j), if_neg (Nat.not_lt_zero j)]

theorem zero_wants (ρ : Iop.Rho (uLT C ds)) :
    sWants C ⟨a, 0, [], ds, key, L⟩ ρ = sWants C ⟨a, 0, L, ds, key, L⟩ ρ := by
  show wantsOf a (⟨a, 0, [], ds, key, L⟩ : StageD).depth ds _ =
    wantsOf a (⟨a, 0, L, ds, key, L⟩ : StageD).depth ds _
  rw [zero_depth]

theorem zero_col (w : Want) :
    sCol C ⟨a, 0, [], ds, key, L⟩ (y₁, e) τ w = sCol C ⟨a, 0, L, ds, key, L⟩ (y₁, z) τ w := by
  cases w with
  | table item x => rfl
  | tree j x => simp [sCol_tree]

theorem zero_view :
    sView C ⟨a, 0, [], ds, key, L⟩ (y₁, e) τ = sView C ⟨a, 0, L, ds, key, L⟩ (y₁, z) τ := by
  unfold sView
  simp only [zero_wants, zero_col a L ds key y₁ e z τ]

theorem zero_tests :
    sTests C ⟨a, 0, [], ds, key, L⟩ (y₁, e) τ = sTests C ⟨a, 0, L, ds, key, L⟩ (y₁, z) τ := by
  unfold sTests
  rw [zero_wants]
  rfl

theorem zero_left :
    sLeft C ⟨a, 0, [], ds, key, L⟩ (y₁, e) τ = sLeft C ⟨a, 0, L, ds, key, L⟩ (y₁, z) τ := by
  funext p
  show (sCol C ⟨a, 0, [], ds, key, L⟩ (y₁, e) τ _).getD [] =
    (sCol C ⟨a, 0, L, ds, key, L⟩ (y₁, z) τ _).getD []
  rw [zero_col a L ds key y₁ e z τ]

/-- A stage whose first own tree has the number 0 does not read the trees at hand. -/
theorem stage_zero {Xi Xo : Type} (r : Xi → Fmt.View → Option Xo) (x : Xi) :
    (stageIOR C ⟨a, 0, [], ds, key, L⟩ r).red.out (x, (y₁, e)) τ =
      (stageIOR C ⟨a, 0, L, ds, key, L⟩ r).red.out (x, (y₁, z)) τ := by
  show ((if sTests C ⟨a, 0, [], ds, key, L⟩ (y₁, e) τ then
        r x (sView C ⟨a, 0, [], ds, key, L⟩ (y₁, e) τ) else none).map fun xo =>
      (xo, (y₁, sLeft C ⟨a, 0, [], ds, key, L⟩ (y₁, e) τ))) =
    ((if sTests C ⟨a, 0, L, ds, key, L⟩ (y₁, z) τ then
        r x (sView C ⟨a, 0, L, ds, key, L⟩ (y₁, z) τ) else none).map fun xo =>
      (xo, (y₁, sLeft C ⟨a, 0, L, ds, key, L⟩ (y₁, z) τ)))
  rw [zero_tests a L ds key y₁ e z τ, zero_view a L ds key y₁ e z τ,
    zero_left a L ds key y₁ e z τ]

end Zero

section Main
variable {D : WholeD} {all : List LeftT} {Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 : Type} (tF : TF) (tJ : TJ)
  (t3 : T3) (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (Q : Places D all S₁ S₂ S₃ W)
  (okF : Y → TF → Bool) (okJ : X₁ → TJ → Bool) (ok3 : X₂ → T3 → Bool)
  (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT C D.ds₁) (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT C D.ds₂)
  (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT C D.ds₃)

/-- The first chain's decision as a reduction over its own rounds. -/
abbrev Three.K₁ (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) :
    Reduction (S₁ × (EAll D all).Str) (S₁ × (EAll D all).Str) :=
  (chainIOR C (frameAt D all D.key₁ T.ft₁) T.n₁ ((T.p₁ :: T.l₁).map (·.b)) T.p₁.base D.ds₁
    (rowBack T.p₁ T.l₁)).red

abbrev Three.K₂ (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) :
    Reduction (S₂ × (EAll D all).Str) (S₂ × (EAll D all).Str) :=
  (chainIOR C (frameAt D all D.key₂ T.ft₂) T.n₂ ((T.p₂ :: T.l₂).map (·.b)) T.p₂.base D.ds₂
    (rowBack T.p₂ T.l₂)).red

abbrev Three.K₃ (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) :
    Reduction (S₃ × (EAll D all).Str) (S₃ × (EAll D all).Str) :=
  (chainIOR C (frameAt D all D.key₃ T.ft₃) T.n₃ ((T.p₃ :: T.l₃).map (·.b)) T.p₃.base D.ds₃
    (rowBack T.p₃ T.l₃)).red

/-- What the row's first stage puts out behind its silent round. -/
def Three.outA (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) :
    Y × (oneExternalString (2 ^ D.a) SgX).Str → Iop.Tr (uLT C D.ds₁) → Option (X₁ × (EAll D all).Str) :=
  fun a τ => (T.K₁.out (T.in₁ a.1, (a.2, fun _ => [])) τ).map fun b => (T.out₁ a.1 b.1, b.2)

def Three.outB (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) :
    X₁ × (EAll D all).Str → Iop.Tr (uLT C D.ds₂) → Option (X₂ × (EAll D all).Str) :=
  fun a τ => (T.K₂.out (T.in₂ a.1, a.2) τ).map fun b => (T.out₂ a.1 b.1, b.2)

def Three.outC (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) :
    X₂ × (EAll D all).Str → Iop.Tr (uLT C D.ds₃) → Option Unit :=
  fun a τ => (lastIOR C (D.st₃ all) T.run₃).out a.1 a.2 τ

theorem eqA (hb : T.p₁.base = 0) (a : Y × (oneExternalString (2 ^ D.a) SgX).Str)
    (τ : Iop.Tr (plainRound TF tF :: uLT C D.ds₁)) :
    (T.row tF tJ t3 okF okJ ok3).S₁.ior.red.out a τ =
      if okF a.1 τ.1.2 then T.outA a τ.2.2 else none := by
  have e : (stageIOR C (D.st₁ all) T.run₁).red.out (a.1, (a.2, fun p => p.1.elim0)) τ.2.2 =
      T.outA a τ.2.2 := by
    unfold Three.outA Three.K₁
    rw [hb]
    exact (stage_map (D.st₁ all) _ T.in₁ T.out₁ a.1 (a.2, fun p => p.1.elim0) τ.2.2).trans
      (congrArg _ (stage_zero D.a all D.ds₁ D.key₁ a.2 (fun p => p.1.elim0) (fun _ => []) τ.2.2 _
        (T.in₁ a.1)))
  rw [← e]
  show ((if okF a.1 τ.1.2 then
      (stageIOR C (D.st₁ all) T.run₁).out a.1 (a.2, fun p => p.1.elim0) τ.2.2 else none).map _) = _
  cases okF a.1 τ.1.2 <;> rfl

theorem eqB (hb : T.p₂.base = D.t₁) (a : X₁ × (EAll D all).Str)
    (τ : Iop.Tr (plainRound TJ tJ :: uLT C D.ds₂)) :
    (T.row tF tJ t3 okF okJ ok3).S₂.ior.red.out a τ =
      if okJ a.1 τ.1.2 then T.outB a τ.2.2 else none := by
  have e : (stageIOR C (D.st₂ all all) T.run₂).red.out a τ.2.2 = T.outB a τ.2.2 := by
    unfold Three.outB Three.K₂
    rw [hb]
    exact stage_map (D.st₂ all all) _ T.in₂ T.out₂ a.1 a.2 τ.2.2
  rw [← e]
  show ((if okJ a.1 τ.1.2 then (stageIOR C (D.st₂ all all) T.run₂).out a.1 a.2 τ.2.2 else none).map
    _) = _
  cases okJ a.1 τ.1.2 <;> rfl

theorem file_know₁ (hf : T.Fits) (hg : EachGood Q.on₁ Q.R₁ 0 (T.p₁ :: T.l₁)) (hgl : T.Glue₁ Q) :
    ((T.row tF tJ t3 okF okJ ok3).links (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).K₁.Know
      (fun a => Q.on₁ 0 (T.in₁ a.1, (a.2, fun _ => [])))
      (fun a w => Q.R₁ 0 (T.in₁ a.1, (a.2, fun _ => [])) w) (T.mid₁ Q)
      (fun a τ w => extOwn T.p₁ T.l₁ D.ds₁ h₁ T.d (T.in₁ a.1, (a.2, fun _ => [])) τ.2.2 w)
      (0, errOwn T.p₁ T.l₁ D.ds₁ h₁) := by
  have kc := chainOwn T.n₁ Q.on₁ Q.R₁ T.d T.p₁ T.l₁ D.ds₁ hf.data₁ h₁ hf.tiled₁ hg
  have kA := know_sim T.K₁ T.outA _ _ _ _ _
    (fun a => Q.on₁ 0 (T.in₁ a.1, (a.2, fun _ => [])))
    (fun a w => Q.R₁ 0 (T.in₁ a.1, (a.2, fun _ => [])) w) (T.mid₁ Q)
    (fun a τ w => extOwn T.p₁ T.l₁ D.ds₁ h₁ T.d (T.in₁ a.1, (a.2, fun _ => [])) τ w)
    (fun a' ha' => Or.inr ⟨(T.in₁ a'.1, (a'.2, fun _ => [])), ha', fun τ b' w' hb' hw' => by
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hb'
      exact ⟨b, w', hb, hgl a'.1 b w' hw', id⟩⟩) kc
  have kF := know_front (plainRound TF tF) ⟨uLT C D.ds₁, T.outA⟩ (fun a m => okF a.1 m.2) _ _ _ _ _
    kA
  exact know_congr _ _ (eqA tF tJ t3 T okF okJ ok3 hf.base₁) _ _ _ _ _ kF

theorem file_know₂ (hf : T.Fits) (hg : EachGood Q.on₂ Q.R₂ 0 (T.p₂ :: T.l₂)) (hgl : T.Glue₂ Q) :
    ((T.row tF tJ t3 okF okJ ok3).links (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).K₂.Know
      (fun _ => True) (T.mid₁ Q) (T.mid₂ Q)
      (fun a τ w => extOwn T.p₂ T.l₂ D.ds₂ h₂ T.d (T.in₂ a.1, a.2) τ.2.2 w)
      (0, errOwn T.p₂ T.l₂ D.ds₂ h₂) := by
  have kc := know_all _ _ _ _ _ _
    (chainOwn T.n₂ Q.on₂ Q.R₂ T.d T.p₂ T.l₂ D.ds₂ hf.data₂ h₂ hf.tiled₂ hg)
  have kB := know_sim T.K₂ T.outB _ _ _ _ _ (fun _ => True) (T.mid₁ Q) (T.mid₂ Q)
    (fun a τ w => extOwn T.p₂ T.l₂ D.ds₂ h₂ T.d (T.in₂ a.1, a.2) τ w)
    (fun a' _ => Or.inr ⟨(T.in₂ a'.1, a'.2), trivial, fun τ b' w' hb' hw' => by
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hb'
      exact ⟨b, w', hb, hgl a'.1 b w' hw', id⟩⟩) kc
  have kF := know_front (plainRound TJ tJ) ⟨uLT C D.ds₂, T.outB⟩ (fun a m => okJ a.1 m.2) _ _ _ _ _
    kB
  exact know_congr _ _ (eqB tF tJ t3 T okF okJ ok3 hf.base₂) _ _ _ _ _ kF

theorem eqC (a : X₂ × (EAll D all).Str) (τ : Iop.Tr (plainRound T3 t3 :: uLT C D.ds₃)) :
    (T.row tF tJ t3 okF okJ ok3).S₃.out a.1 a.2 τ =
      if ok3 a.1 τ.1.2 then T.outC a τ.2.2 else none := rfl

/-- Where the third chain has no first record, it refuses. -/
theorem outC_none (a : X₂ × (EAll D all).Str) (τ : Iop.Tr (uLT C D.ds₃)) (hi : T.in₃ a.1 = none) :
    T.outC a τ = none := by
  have hr : T.run₃ a.1 (sView C (D.st₃ all) a.2 τ) = false := by
    unfold Three.run₃
    rw [hi]
    rfl
  show (if (sTests C (D.st₃ all) a.2 τ && T.run₃ a.1 (sView C (D.st₃ all) a.2 τ)) = true then
    some () else none) = none
  rw [hr, Bool.and_false]
  rfl

/-- Where the third chain says yes, its fold has put out from its first record, and the last test
says yes of what it has put out. -/
theorem outC_some (hb : T.p₃.base = D.t₁ + D.t₂) (a : X₂ × (EAll D all).Str)
    (τ : Iop.Tr (uLT C D.ds₃)) (s : S₃) (hi : T.in₃ a.1 = some s) (u : Unit)
    (h : T.outC a τ = some u) : ∃ b, T.K₃.out (s, a.2) τ = some b ∧ T.fin a.1 b.1 = true := by
  have h' : (if (sTests C (D.st₃ all) a.2 τ && T.run₃ a.1 (sView C (D.st₃ all) a.2 τ)) = true then
      some () else none) = some u := h
  unfold Three.K₃
  rw [hb]
  show ∃ b, ((if sTests C (D.st₃ all) a.2 τ then
      foldRun (frameAt D all D.key₃ T.ft₃) T.n₃ ((T.p₃ :: T.l₃).map (·.b)) (rowBack T.p₃ T.l₃) s
        (sView C (D.st₃ all) a.2 τ) else none).map fun xo =>
      (xo, ((a.2.1, sLeft C ⟨D.a, D.t₁ + D.t₂, all, D.ds₃, D.key₃, all⟩ a.2 τ) :
        (EAll D all).Str))) = some b ∧ T.fin a.1 b.1 = true
  cases ht : sTests C (D.st₃ all) a.2 τ with
  | false =>
    rw [ht, Bool.false_and] at h'
    cases h'
  | true =>
    rw [ht, Bool.true_and] at h'
    cases hr : T.run₃ a.1 (sView C (D.st₃ all) a.2 τ) with
    | false =>
      rw [hr] at h'
      cases h'
    | true =>
      unfold Three.run₃ at hr
      rw [hi] at hr
      have hr' : (match foldRun (frameAt D all D.key₃ T.ft₃) T.n₃ ((T.p₃ :: T.l₃).map (·.b))
          (rowBack T.p₃ T.l₃) s (sView C (D.st₃ all) a.2 τ) with
        | some s' => T.fin a.1 s'
        | none => false) = true := hr
      cases hfr : foldRun (frameAt D all D.key₃ T.ft₃) T.n₃ ((T.p₃ :: T.l₃).map (·.b))
          (rowBack T.p₃ T.l₃) s (sView C (D.st₃ all) a.2 τ) with
      | none =>
        rw [hfr] at hr'
        cases hr'
      | some s' =>
        rw [hfr] at hr'
        exact ⟨_, rfl, hr'⟩

theorem file_know₃ (hf : T.Fits) (hg : EachGood Q.on₃ Q.R₃ 0 (T.p₃ :: T.l₃)) (hgl : T.Ends Q) :
    ((T.row tF tJ t3 okF okJ ok3).links (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).K₃.Know
      (fun _ => True) (T.mid₂ Q) (fun (_ : Unit) (_ : Unit) => True)
      (fun a τ (_ : Unit) =>
        ((T.in₃ a.1).map fun s => extOwn T.p₃ T.l₃ D.ds₃ h₃ T.d (s, a.2) τ.2.2 T.wEnd).getD T.d)
      (0, errOwn T.p₃ T.l₃ D.ds₃ h₃) := by
  have kc := know_all _ _ _ _ _ _
    (chainOwn T.n₃ Q.on₃ Q.R₃ T.d T.p₃ T.l₃ D.ds₃ hf.data₃ h₃ hf.tiled₃ hg)
  have kC := know_sim T.K₃ T.outC _ _ _ _ _ (fun _ => True) (T.mid₂ Q)
    (fun (_ : Unit) (_ : Unit) => True)
    (fun a τ _ =>
      ((T.in₃ a.1).map fun s => extOwn T.p₃ T.l₃ D.ds₃ h₃ T.d (s, a.2) τ T.wEnd).getD T.d)
    (fun a' _ => by
      cases hi : T.in₃ a'.1 with
      | none => exact Or.inl fun τ => outC_none T a' τ hi
      | some s =>
        refine Or.inr ⟨(s, a'.2), trivial, fun τ b' w' hb' _ => ?_⟩
        obtain ⟨b, h1, h2⟩ := outC_some T hf.base₃ a' τ s hi b' hb'
        refine ⟨b, T.wEnd, h1, hgl a'.1 b h2, fun h => ⟨s, hi, ?_⟩⟩
        show orOff (Q.on₃ 0) (Q.R₃ 0) (s, a'.2) (((T.in₃ a'.1).map fun s =>
          extOwn T.p₃ T.l₃ D.ds₃ h₃ T.d (s, a'.2) τ T.wEnd).getD T.d)
        rw [hi]
        exact h) kc
  have kF := know_front (plainRound T3 t3) ⟨uLT C D.ds₃, T.outC⟩ (fun a m => ok3 a.1 m.2) _ _ _ _ _
    kC
  exact know_congr _ _ (eqC tF tJ t3 T okF okJ ok3) _ _ _ _ _ kF

end Main

/-- **The rule of composition across the three chains, for one request.** -/
theorem fileKnows : FileKnows := by
  intro C D all Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 tF tJ t3 T Q okF okJ ok3 h₁ h₂ h₃ hf g₁ g₂ g₃ hgl
  exact ⟨file_know₁ tF tJ t3 T Q okF okJ ok3 h₁ h₂ h₃ hf g₁ hgl.glue₁,
    file_know₂ tF tJ t3 T Q okF okJ ok3 h₁ h₂ h₃ hf g₂ hgl.glue₂,
    file_know₃ tF tJ t3 T Q okF okJ ok3 h₁ h₂ h₃ hf g₃ hgl.ends,
    fun _ _ _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩

end VerifiableInference.Desc.Sound
