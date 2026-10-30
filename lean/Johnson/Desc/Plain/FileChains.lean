-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/FileChains.lean: `fold_three_chains`: the rule of composition ACROSS THE THREE
CHAINS of a file, in the plain form: from one `Leads` a block to the three premises of
Johnson/Desc/Plain/Doors.lean (`PlainFile.Leads3`) and Keyed.lean (`Leads3K`), AT THE LIBRARY's ROW
AT THE THREE FOLDS (`Three.row`, Johnson/Desc/Sound/FileRule.lean).

Taken from Johnson/Desc/Sound/: `Three`, `Three.row`, `Three.Fits`, `errOwn` (definitions); `eqA`,
`eqB`, `eqC`, `outC_none`, `outC_some` (FileKnowsProof.lean: equations of what the row's stages put
out). Not taken: `Places`, `Three.snd`, `mid₁`, `mid₂`, `Glued`, `FileKnows`. A piece's W and ext,
and `Three.d`,
`Three.wEnd`, are idle.

  `PPlaces`: at each boundary of each chain a condition; for each block a relation.
  `plainOf`: the `PlainFile`: its three decisions are the row's three stages. M, L₁, L₂ are letters:
    WHAT IS KNOWN OF THE FILE's STATEMENT once the first chain has handed on b and b is true; what
    is claimed of what the first | the second chain hands on.
  `Glues`: three implications WITHOUT ANY GAME, one at each chain's end, from "there are statements
    at all the boundaries, each in its block's relation to the one before" (`steps`).
  `fold_three_chains`, `fold_three_chainsK`.

Limits. Those of FoldChain.lean, Doors.lean, Keyed.lean. `Three.fin` reads what the second chain
handed on and the third chain's end, not the instance: the file's own last test on the instance is
spent in
`ties` (Doors.lean), from the file's yes.

-/
import Johnson.Desc.Plain.FoldChainK
import Johnson.Desc.Sound.FileKnowsProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Plain
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open _root_.Iop.Reduction (steps)
open _root_.Compile.Joined (plainRound)
open _root_.TypedOracleCompiler.Joined (PlainFile)
open VerifiableInference.Desc.Sound

variable {C : CK}

/-- `fold_chain`'s conclusion at the chain's own list of rounds. -/
theorem chainOwn_leads {S Cl W : Type} {F : Frame} (name : String) (on : ℕ → S × F.E.Str → Prop)
    (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (ds : List RDT) (e : rowData p l = ds)
    (h : (rowIOR p l).shape = uLT C ds) (ht : Tiled p l) (he : EachLeads on Q 0 (p :: l)) :
    (chainIOR C F name ((p :: l).map (·.b)) p.base ds (rowBack p l)).red.Leads (on 0)
      (steps Q 0 l.length) (errOwn p l ds h) := by
  subst e
  exact Reduction.leads_cast h _ _ _ _ (fold_chain name on Q p l h ht he)

theorem chainOwn_leadsK {S Cl W κ : Type} {F : Frame} (name : String)
    (key : ℕ → S × F.E.Str → κ) (on : ℕ → S × F.E.Str → Prop)
    (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (ds : List RDT) (e : rowData p l = ds)
    (h : (rowIOR p l).shape = uLT C ds) (ht : Tiled p l) (he : EachLeadsK key on Q 0 (p :: l)) :
    (chainIOR C F name ((p :: l).map (·.b)) p.base ds (rowBack p l)).red.LeadsK (key 0) (on 0)
      (steps Q 0 l.length) (errOwn p l ds h) := by
  subst e
  exact Reduction.leadsK_cast h _ _ _ _ _ (fold_chainK name key on Q p l h ht he)

/-- At each boundary of each chain a condition; for each block a relation. -/
structure PPlaces (D : WholeD) (all : List LeftT) (S₁ S₂ S₃ : Type) where
  on₁ : ℕ → S₁ × (EAll D all).Str → Prop
  Q₁ : ℕ → S₁ × (EAll D all).Str → S₁ × (EAll D all).Str → Prop
  on₂ : ℕ → S₂ × (EAll D all).Str → Prop
  Q₂ : ℕ → S₂ × (EAll D all).Str → S₂ × (EAll D all).Str → Prop
  on₃ : ℕ → S₃ × (EAll D all).Str → Prop
  Q₃ : ℕ → S₃ × (EAll D all).Str → S₃ × (EAll D all).Str → Prop

section Main
variable {D : WholeD} {all : List LeftT} {Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 : Type} (tF : TF) (tJ : TJ)
  (t3 : T3) (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (Pl : PPlaces D all S₁ S₂ S₃)
  (okF : Y → TF → Bool) (okJ : X₁ → TJ → Bool) (ok3 : X₂ → T3 → Bool)
  (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT C D.ds₁) (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT C D.ds₂)
  (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT C D.ds₃)
  (M : Y × (oneExternalString (2 ^ D.a) SgX).Str → X₁ × (EAll D all).Str → Prop)
  (L₁ : X₁ × (EAll D all).Str → Prop) (L₂ : X₂ × (EAll D all).Str → Prop)
  (d : X₁ × (EAll D all).Str)

/-- **The file in the plain form: its three decisions are the row's three stages.** -/
def plainOf : PlainFile (chainsOf C D tF tJ t3) (Y × (oneExternalString (2 ^ D.a) SgX).Str) where
  A₁ := X₁ × (EAll D all).Str
  A₂ := X₂ × (EAll D all).Str
  out₁ := (T.row tF tJ t3 okF okJ ok3).S₁.ior.red.out
  out₂ := (T.row tF tJ t3 okF okJ ok3).S₂.ior.red.out
  out₃ := fun a τ => (T.row tF tJ t3 okF okJ ok3).S₃.out a.1 a.2 τ
  on₀ := fun a => Pl.on₁ 0 (T.in₁ a.1, (a.2, fun _ => []))
  on₁ := fun a => Pl.on₂ 0 (T.in₂ a.1, a.2)
  on₂ := fun a => ∀ s, T.in₃ a.1 = some s → Pl.on₃ 0 (s, a.2)
  M := M
  L₁ := L₁
  L₂ := L₂
  ε₁ := (0, errOwn T.p₁ T.l₁ D.ds₁ h₁)
  ε₂ := (0, errOwn T.p₂ T.l₂ D.ds₂ h₂)
  ε₃ := (0, errOwn T.p₃ T.l₃ D.ds₃ h₃)
  d := d

/-- **Three implications without any game**, one at each chain's end. -/
structure Glues : Prop where
  g₁ : ∀ (x : Y) (y : (oneExternalString (2 ^ D.a) SgX).Str) (b : S₁ × (EAll D all).Str),
    Pl.on₁ 0 (T.in₁ x, (y, fun _ => [])) →
    steps Pl.Q₁ 0 T.l₁.length (T.in₁ x, (y, fun _ => [])) b →
    Pl.on₂ 0 (T.in₂ (T.out₁ x b.1), b.2) ∧
      (L₁ (T.out₁ x b.1, b.2) → M (x, y) (T.out₁ x b.1, b.2))
  g₂ : ∀ (a : X₁ × (EAll D all).Str) (b : S₂ × (EAll D all).Str),
    Pl.on₂ 0 (T.in₂ a.1, a.2) → steps Pl.Q₂ 0 T.l₂.length (T.in₂ a.1, a.2) b →
    (∀ s, T.in₃ (T.out₂ a.1 b.1) = some s → Pl.on₃ 0 (s, b.2)) ∧
      (L₂ (T.out₂ a.1 b.1, b.2) → L₁ a)
  g₃ : ∀ (a : X₂ × (EAll D all).Str) (s : S₃) (b : S₃ × (EAll D all).Str),
    T.in₃ a.1 = some s → Pl.on₃ 0 (s, a.2) → steps Pl.Q₃ 0 T.l₃.length (s, a.2) b →
    T.fin a.1 b.1 = true → L₂ a

variable {T Pl M L₁ L₂}

theorem file_leads₁ (hf : T.Fits) (he : EachLeads Pl.on₁ Pl.Q₁ 0 (T.p₁ :: T.l₁))
    (G : Glues T Pl M L₁ L₂) :
    (plainOf tF tJ t3 T Pl okF okJ ok3 h₁ h₂ h₃ M L₁ L₂ d).K₁.Leads
      (fun a => Pl.on₁ 0 (T.in₁ a.1, (a.2, fun _ => [])))
      (fun a b => Pl.on₂ 0 (T.in₂ b.1, b.2) ∧ (L₁ b → M a b))
      (0, errOwn T.p₁ T.l₁ D.ds₁ h₁) := by
  have kc := chainOwn_leads T.n₁ Pl.on₁ Pl.Q₁ T.p₁ T.l₁ D.ds₁ hf.data₁ h₁ hf.tiled₁ he
  have kA := Reduction.leads_sim T.K₁ T.outA _ _ _
    (fun a => Pl.on₁ 0 (T.in₁ a.1, (a.2, fun _ => [])))
    (fun a b => Pl.on₂ 0 (T.in₂ b.1, b.2) ∧ (L₁ b → M a b))
    (fun a' ha' => Or.inr ⟨(T.in₁ a'.1, (a'.2, fun _ => [])), ha', fun τ b' hb' => by
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hb'
      exact ⟨b, hb, fun hq => G.g₁ a'.1 a'.2 b ha' hq⟩⟩) kc
  have kF := Reduction.leads_front (plainRound TF tF) ⟨uLT C D.ds₁, T.outA⟩
    (fun a m => okF a.1 m.2) _ _ _ kA
  exact Reduction.leads_congr _ _ (eqA tF tJ t3 T okF okJ ok3 hf.base₁) _ _ _ kF

theorem file_leads₂ (hf : T.Fits) (he : EachLeads Pl.on₂ Pl.Q₂ 0 (T.p₂ :: T.l₂))
    (G : Glues T Pl M L₁ L₂) :
    (plainOf tF tJ t3 T Pl okF okJ ok3 h₁ h₂ h₃ M L₁ L₂ d).K₂.Leads
      (fun a => Pl.on₂ 0 (T.in₂ a.1, a.2))
      (fun a b => (∀ s, T.in₃ b.1 = some s → Pl.on₃ 0 (s, b.2)) ∧ (L₂ b → L₁ a))
      (0, errOwn T.p₂ T.l₂ D.ds₂ h₂) := by
  have kc := chainOwn_leads T.n₂ Pl.on₂ Pl.Q₂ T.p₂ T.l₂ D.ds₂ hf.data₂ h₂ hf.tiled₂ he
  have kB := Reduction.leads_sim T.K₂ T.outB _ _ _ (fun a => Pl.on₂ 0 (T.in₂ a.1, a.2))
    (fun a b => (∀ s, T.in₃ b.1 = some s → Pl.on₃ 0 (s, b.2)) ∧ (L₂ b → L₁ a))
    (fun a' ha' => Or.inr ⟨(T.in₂ a'.1, a'.2), ha', fun τ b' hb' => by
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hb'
      exact ⟨b, hb, fun hq => G.g₂ a' b ha' hq⟩⟩) kc
  have kF := Reduction.leads_front (plainRound TJ tJ) ⟨uLT C D.ds₂, T.outB⟩
    (fun a m => okJ a.1 m.2) _ _ _ kB
  exact Reduction.leads_congr _ _ (eqB tF tJ t3 T okF okJ ok3 hf.base₂) _ _ _ kF

theorem file_leadsK₂ {κ : Type} (key : ℕ → S₂ × (EAll D all).Str → κ) (hf : T.Fits)
    (he : EachLeadsK key Pl.on₂ Pl.Q₂ 0 (T.p₂ :: T.l₂)) (G : Glues T Pl M L₁ L₂) :
    (plainOf tF tJ t3 T Pl okF okJ ok3 h₁ h₂ h₃ M L₁ L₂ d).K₂.LeadsK
      (fun a => key 0 (T.in₂ a.1, a.2)) (fun a => Pl.on₂ 0 (T.in₂ a.1, a.2))
      (fun a b => (∀ s, T.in₃ b.1 = some s → Pl.on₃ 0 (s, b.2)) ∧ (L₂ b → L₁ a))
      (0, errOwn T.p₂ T.l₂ D.ds₂ h₂) := by
  have kc := chainOwn_leadsK T.n₂ key Pl.on₂ Pl.Q₂ T.p₂ T.l₂ D.ds₂ hf.data₂ h₂ hf.tiled₂ he
  have kB := Reduction.leadsK_sim T.K₂ T.outB (key 0) (fun a => key 0 (T.in₂ a.1, a.2)) id _ _ _
    (fun a => Pl.on₂ 0 (T.in₂ a.1, a.2))
    (fun a b => (∀ s, T.in₃ b.1 = some s → Pl.on₃ 0 (s, b.2)) ∧ (L₂ b → L₁ a))
    (fun a' ha' => Or.inr ⟨(T.in₂ a'.1, a'.2), rfl, ha', fun τ b' hb' => by
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hb'
      exact ⟨b, hb, fun hq => G.g₂ a' b ha' hq⟩⟩) kc
  have kF := Reduction.leadsK_front (plainRound TJ tJ) ⟨uLT C D.ds₂, T.outB⟩
    (fun a m => okJ a.1 m.2) _ _ _ _ kB
  exact Reduction.leadsK_congr _ _ (eqB tF tJ t3 T okF okJ ok3 hf.base₂) _ _ _ _ kF

theorem file_leads₃ (hf : T.Fits) (he : EachLeads Pl.on₃ Pl.Q₃ 0 (T.p₃ :: T.l₃))
    (G : Glues T Pl M L₁ L₂) :
    (plainOf tF tJ t3 T Pl okF okJ ok3 h₁ h₂ h₃ M L₁ L₂ d).K₃.Leads
      (fun a => ∀ s, T.in₃ a.1 = some s → Pl.on₃ 0 (s, a.2)) (fun a _ => L₂ a)
      (0, errOwn T.p₃ T.l₃ D.ds₃ h₃) := by
  have kc := chainOwn_leads T.n₃ Pl.on₃ Pl.Q₃ T.p₃ T.l₃ D.ds₃ hf.data₃ h₃ hf.tiled₃ he
  have kC := Reduction.leads_sim T.K₃ T.outC _ _ _
    (fun a => ∀ s, T.in₃ a.1 = some s → Pl.on₃ 0 (s, a.2)) (fun a (_ : Unit) => L₂ a)
    (fun a' ha' => by
      cases hi : T.in₃ a'.1 with
      | none => exact Or.inl fun τ => outC_none T a' τ hi
      | some s =>
        refine Or.inr ⟨(s, a'.2), ha' s hi, fun τ b' hb' => ?_⟩
        obtain ⟨b, k1, k2⟩ := outC_some T hf.base₃ a' τ s hi b' hb'
        exact ⟨b, k1, fun hq => G.g₃ a' s b hi (ha' s hi) hq k2⟩) kc
  have kF := Reduction.leads_front (plainRound T3 t3) ⟨uLT C D.ds₃, T.outC⟩
    (fun a m => ok3 a.1 m.2) _ _ _ kC
  exact Reduction.leads_congr _ _ (eqC tF tJ t3 T okF okJ ok3) _ _ _ kF

/-- **fold_three_chains: the rule of composition across the three chains, in the plain form.** -/
theorem fold_three_chains (hf : T.Fits) (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 (T.p₁ :: T.l₁))
    (e₂ : EachLeads Pl.on₂ Pl.Q₂ 0 (T.p₂ :: T.l₂)) (e₃ : EachLeads Pl.on₃ Pl.Q₃ 0 (T.p₃ :: T.l₃))
    (G : Glues T Pl M L₁ L₂) :
    (plainOf tF tJ t3 T Pl okF okJ ok3 h₁ h₂ h₃ M L₁ L₂ d).Leads3 :=
  ⟨file_leads₁ tF tJ t3 okF okJ ok3 h₁ h₂ h₃ d hf e₁ G,
    file_leads₂ tF tJ t3 okF okJ ok3 h₁ h₂ h₃ d hf e₂ G,
    file_leads₃ tF tJ t3 okF okJ ok3 h₁ h₂ h₃ d hf e₃ G⟩

/-- **The same, the shared chain with keys: paid once for a batch.** -/
theorem fold_three_chainsK {κ : Type} (key : ℕ → S₂ × (EAll D all).Str → κ) (hf : T.Fits)
    (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 (T.p₁ :: T.l₁))
    (e₂ : EachLeadsK key Pl.on₂ Pl.Q₂ 0 (T.p₂ :: T.l₂))
    (e₃ : EachLeads Pl.on₃ Pl.Q₃ 0 (T.p₃ :: T.l₃)) (G : Glues T Pl M L₁ L₂) :
    (plainOf tF tJ t3 T Pl okF okJ ok3 h₁ h₂ h₃ M L₁ L₂ d).Leads3K
      (fun a : X₁ × (EAll D all).Str => key 0 (T.in₂ a.1, a.2)) :=
  ⟨file_leads₁ tF tJ t3 okF okJ ok3 h₁ h₂ h₃ d hf e₁ G,
    file_leadsK₂ tF tJ t3 okF okJ ok3 h₁ h₂ h₃ d key hf e₂ G,
    file_leads₃ tF tJ t3 okF okJ ok3 h₁ h₂ h₃ d hf e₃ G⟩

end Main

end VerifiableInference.Desc.Plain

#print axioms VerifiableInference.Desc.Plain.fold_three_chains
#print axioms VerifiableInference.Desc.Plain.fold_three_chainsK
