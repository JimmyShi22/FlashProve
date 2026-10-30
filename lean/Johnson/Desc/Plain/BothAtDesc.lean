-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/BothAtDesc.lean: the two-part form for a batch (Johnson/Desc/Plain/Both.lean)
ALONG A CHAIN, ACROSS THE THREE CHAINS, AND AT A DESCRIPTION's OWN DECISION.

  `EachLeadsBN key on Q N`: for each block of the shared chain, three clauses: `LeadsBN` at its own
    errors; the hand-over of the condition (NOT handed the block's output, though `LeadsBN.seq`
    would hand it on); the law of keys. `fold_chainB`: then the chain's own decision has
    `LeadsBN` at the blocks' errors in a row. `EachLeadsK.bothN`: a row with keys alone is the case
    εO = 0.
  `PlainFile.Leads3B`, `PlainFile.knowsJB`, `proofSound_plainJB`; `fold_three_chainsB`.
  `proofSound_at_descB`: `CompilerSoundnessConditionStatements.proofSound` at runP := F.run: as `proofSound_at_desc`
    (AtDesc.lean), with e₂ : EachLeadsBN … N, N the object's number of slots. NO FACTOR N STANDS IN
    FRONT OF THE SHARED CHAIN's LIST: it stands inside each shared block's own errors, at the part
    that hangs on a slot alone.
Limits: those of AtDesc.lean and Both.lean.

-/
import Johnson.Desc.Plain.Both
import Johnson.Desc.Plain.AtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Desc.Plain
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open _root_.Iop.Reduction (steps)
open _root_.Compile.Joined (plainRound)
open _root_.TypedOracleCompiler.Joined (PlainFile)
open VerifiableInference.Desc.Sound

variable {S Cl W κ : Type} {C : CK} {F : Frame}

/-- **What is asked of each block of a shared chain: three clauses.** The law for a batch in two
parts; the hand-over of the condition; the law of keys. -/
def EachLeadsBN (key : ℕ → S × F.E.Str → κ) (on : ℕ → S × F.E.Str → Prop)
    (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop) (N : ℕ) : ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | i, p :: l =>
    p.ior.red.LeadsBN (key i) (on i) (Q i) N p.err ∧ (∀ a b, on i a → Q i a b → on (i + 1) b) ∧
      p.ior.red.KeyLaw (key i) (key (i + 1)) ∧ EachLeadsBN key on Q N (i + 1) l

theorem EachLeadsK.bothN {key : ℕ → S × F.E.Str → κ} {on : ℕ → S × F.E.Str → Prop}
    {Q : ℕ → S × F.E.Str → S × F.E.Str → Prop} (N : ℕ) :
    ∀ (l : List (Piece C F S Cl W)) (i : ℕ), EachLeadsK key on Q i l → EachLeadsBN key on Q N i l
  | [], _, _ => trivial
  | _ :: l, i, h => ⟨h.1.bothN N, h.2.1, h.2.2.1, EachLeadsK.bothN N l (i + 1) h.2.2.2⟩

theorem row_leadsBN (key : ℕ → S × F.E.Str → κ) (on : ℕ → S × F.E.Str → Prop)
    (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop) (N : ℕ) :
    ∀ (l : List (Piece C F S Cl W)) (p : Piece C F S Cl W) (i : ℕ),
      EachLeadsBN key on Q N i (p :: l) →
      (rowIOR p l).red.LeadsBN (key i) (on i) (steps Q i l.length) N (rowErr p l)
  | [], _, _, h => h.1
  | q :: l, p, i, h =>
      Reduction.leadsBN_congr (p.ior.red.seq (rowIOR q l).red) _
        (fun a τ => IOR.red_seq_out p.ior (rowIOR q l) a τ) _ _ _ _ _
        (Reduction.LeadsBN.seq h.1 (row_leadsBN key on Q N l q (i + 1) h.2.2.2)
          (fun a _ b ha _ hq => h.2.1 a b ha hq) h.2.2.1)

/-- **fold_chain for a batch, in two parts.** -/
theorem fold_chainB (name : String) (key : ℕ → S × F.E.Str → κ) (on : ℕ → S × F.E.Str → Prop)
    (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop) (N : ℕ) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (h : (rowIOR p l).shape = uLT C (rowData p l))
    (ht : Tiled p l) (he : EachLeadsBN key on Q N 0 (p :: l)) :
    (foldRed name ((p :: l).map (·.b)) p l h).LeadsBN (key 0) (on 0) (steps Q 0 l.length) N
      (rowErr p l) :=
  Reduction.leadsBN_congr (rowIOR p l).red _ (fun a τ => foldIsRow S Cl W C F name p l h ht a τ)
    _ _ _ _ _ (row_leadsBN key on Q N l p 0 he)

theorem chainOwn_leadsBN (name : String) (key : ℕ → S × F.E.Str → κ)
    (on : ℕ → S × F.E.Str → Prop) (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop) (N : ℕ)
    (p : Piece C F S Cl W) (l : List (Piece C F S Cl W)) (ds : List RDT) (e : rowData p l = ds)
    (h : (rowIOR p l).shape = uLT C ds) (ht : Tiled p l)
    (he : EachLeadsBN key on Q N 0 (p :: l)) :
    (chainIOR C F name ((p :: l).map (·.b)) p.base ds (rowBack p l)).red.LeadsBN (key 0) (on 0)
      (steps Q 0 l.length) N (errOwn p l ds h) := by
  subst e
  exact Reduction.leadsBN_cast h _ _ _ _ _ _ (fold_chainB name key on Q N p l h ht he)

end VerifiableInference.Desc.Plain

namespace TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)
open _root_.CompileK.Joined (allKind_const)

namespace PlainFile
variable {G : Chains} {Y : Type} {E : ExtSpec} (P : PlainFile G (Y × E.Str)) {κ₁ κ₂ : Type}

/-- **The three premises, the shared chain's in two parts.** -/
structure Leads3B (N : ℕ) (k₁ : P.A₁ → κ₁) : Prop where
  l₁ : P.K₁.Leads P.on₀ (fun a b => P.on₁ b ∧ (P.L₁ b → P.M a b)) P.ε₁
  l₂ : P.K₂.LeadsBN k₁ P.on₁ (fun b c => P.on₂ c ∧ (P.L₂ c → P.L₁ b)) N P.ε₂
  l₃ : P.K₃.Leads P.on₂ (fun c _ => P.L₂ c) P.ε₃

theorem knowsJB {Y' : Type} (f : Y' → Y) (N : ℕ) {k₁ : P.A₁ → κ₁} {k₂ : P.A₂ → κ₂}
    (h : P.Leads3B N k₁) (hJ : G.aJ = RAnn.ofShared .sh G.rJ) (F₁ : E.Str → κ₁)
    (key₁ : ∀ (a : Y' × E.Str) τ b, P.out₁ (f a.1, a.2) τ = some b → k₁ b = F₁ a.2)
    (g₂ : κ₁ → Tr G.c₂ → κ₂) (key₂ : ∀ b τ c, P.out₂ b τ = some c → k₂ c = g₂ (k₁ b) τ) :
    (P.links.comap f).KnowsJ N k₁ k₂ where
  l₁ := LinkJ.ofLocal (allKind_const (fun _ => rfl) G.c₁) N
    (fun a ha => (h.l₁.toKnow (RB := fun b (_ : Unit) => P.on₁ b → P.L₁ b) _ P.d
      fun _ _ _ _ hq hw => hq.2 (hw hq.1)) (f a.1, a.2) ha) F₁ fun a τ b hb => key₁ a τ b hb
  l₂ := by
    have hA : G.A₂ = RoundSplits.const (RAnn.ofShared .sh) G.c₂ := by
      show (G.aJ, RoundSplits.const (RAnn.ofShared .sh) G.s₂) = _
      rw [hJ]
      rfl
    have := LeadsBN.toLinkJ (K := P.K₂) h.l₂ (key₂ := k₂)
      (RA := fun b (_ : Unit) => P.on₁ b → P.L₁ b) (RB := fun c (_ : Unit) => P.on₂ c → P.L₂ c)
      (fun _ _ _ => ()) (fun b _ c _ _ hq hw hb => (hq hb).2 (hw (hq hb).1)) g₂ key₂
    rw [← hA] at this
    exact this
  l₃ := LinkJ.ofLocal (allKind_const (fun _ => rfl) G.c₃) N
    (fun c _ => by
      by_cases hc : P.on₂ c
      · exact Doomed.mono _ _ (fun _ hτ u _ hu _ _ => hτ u hu) (h.l₃ c hc)
      · exact Doomed.of_forall _ _ fun _ _ _ _ _ hc' => absurd hc' hc)
    (fun _ => ()) fun _ _ _ _ => rfl
  hands₁ := fun _ _ _ _ _ => trivial
  hands₂ := fun _ _ _ _ _ => trivial

end PlainFile

/-- **The proof file's hypothesis of the top, the shared chain in two parts.** -/
theorem proofSound_plainJB {I X Wn : Type} (L : HolographicProtocol I X) {G : Chains}
    (D : Desc G (X × L.Rec) (oneExternalString L.wordLength L.Symbol)) (hB : L.onlineBatch = D.batch)
    (Rno : I → X → Wn → Prop) (w₀ : Wn) (P : PlainFile G ((X × L.Rec) × (oneExternalString L.wordLength L.Symbol).Str))
    {κ₁ κ₂ : Type} {k₁ : P.A₁ → κ₁} {k₂ : P.A₂ → κ₂}
    (hl : L.late = none) (h : P.Leads3B L.maxBatchSize k₁) (hJ : G.aJ = RAnn.ofShared .sh G.rJ)
    (F₁ : L.Rec → (oneExternalString L.wordLength L.Symbol).Str → κ₁)
    (key₁ : ∀ x rec y τ b, P.out₁ ((x, rec), y) τ = some b → k₁ b = F₁ rec y)
    (g₂ : κ₁ → Tr G.c₂ → κ₂) (key₂ : ∀ b τ c, P.out₂ b τ = some c → k₂ c = g₂ (k₁ b) τ)
    (decides : ∀ x rec y (τ : Tr G.sh), D.accept (x, rec) y τ = true →
      (P.links.all.out ((L.early x, rec), y) τ).isSome = true)
    (ties : ∀ x rec y (τ : Tr G.sh) b, D.accept (x, rec) y τ = true →
      P.out₁ ((L.early x, rec), y) (Tr.fst (s := G.c₁) (t := G.c₂ ++ G.c₃) τ) = some b →
      (P.on₀ ((L.early x, rec), y) → P.M ((L.early x, rec), y) b) → L.relB Rno rec x y w₀)
    {εs : ℝ≥0∞} (worst : P.links.worstMid ≤ εs) :
    ∃ (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
      (ε : Err L.onlineBatch.loc.shape), Err.Below ε εs ∧
      ∀ rec, (L.batAt rec).SndBKT L.maxBatchSize L.early L.late (L.relB Rno rec)
        (fun x y τ => wit (x, rec) y τ) ε :=
  proofSound_at_links L D Rno (fun _ => w₀) hB hl
    (fun rec => P.knowsJB (fun x : X => (x, rec)) L.maxBatchSize h hJ (F₁ rec)
      (fun a τ b hb => key₁ a.1 rec a.2 τ b hb) g₂ key₂) decides
    (fun x rec y τ hacc hR => by
      obtain ⟨b, hb⟩ := P.first_of_all _ τ (decides x rec y τ hacc)
      refine ties x rec y τ b hacc hb fun ho => ?_
      have := hR ho
      rwa [P.ext_eq _ τ b hb] at this) worst

end TypedOracleCompiler.Joined

namespace VerifiableInference.Desc.Plain
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open _root_.Iop.Reduction (steps)
open _root_.Compile.Joined (plainRound)
open _root_.TypedOracleCompiler.Joined (PlainFile)
open VerifiableInference.Desc.Sound

section Main
variable {C : CK} {D : WholeD} {all : List LeftT} {Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 : Type} (tF : TF)
  (tJ : TJ) (t3 : T3) {T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W} {Pl : PPlaces D all S₁ S₂ S₃}
  (okF : Y → TF → Bool) (okJ : X₁ → TJ → Bool) (ok3 : X₂ → T3 → Bool)
  (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT C D.ds₁) (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT C D.ds₂)
  (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT C D.ds₃)
  {M : Y × (oneExternalString (2 ^ D.a) SgX).Str → X₁ × (EAll D all).Str → Prop}
  {L₁ : X₁ × (EAll D all).Str → Prop} {L₂ : X₂ × (EAll D all).Str → Prop}
  (d : X₁ × (EAll D all).Str)

theorem file_leadsBN₂ {κ : Type} {N : ℕ} (key : ℕ → S₂ × (EAll D all).Str → κ) (hf : T.Fits)
    (he : EachLeadsBN key Pl.on₂ Pl.Q₂ N 0 (T.p₂ :: T.l₂)) (G : Glues T Pl M L₁ L₂) :
    (plainOf tF tJ t3 T Pl okF okJ ok3 h₁ h₂ h₃ M L₁ L₂ d).K₂.LeadsBN
      (fun a => key 0 (T.in₂ a.1, a.2)) (fun a => Pl.on₂ 0 (T.in₂ a.1, a.2))
      (fun a b => (∀ s, T.in₃ b.1 = some s → Pl.on₃ 0 (s, b.2)) ∧ (L₂ b → L₁ a)) N
      (0, errOwn T.p₂ T.l₂ D.ds₂ h₂) := by
  have kc := chainOwn_leadsBN T.n₂ key Pl.on₂ Pl.Q₂ N T.p₂ T.l₂ D.ds₂ hf.data₂ h₂ hf.tiled₂ he
  have kB := Reduction.leadsBN_comap T.K₂ T.outB (fun a => (T.in₂ a.1, a.2)) (key 0) _ _ N _
    (fun a b => (∀ s, T.in₃ b.1 = some s → Pl.on₃ 0 (s, b.2)) ∧ (L₂ b → L₁ a))
    (fun a' τ b' ha' hb' => by
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hb'
      exact ⟨b, hb, fun hq => G.g₂ a' b ha' hq⟩) kc
  have kF := Reduction.leadsBN_front (plainRound TJ tJ) ⟨uLT C D.ds₂, T.outB⟩
    (fun a m => okJ a.1 m.2) _ _ _ N _ kB
  exact Reduction.leadsBN_congr _ _ (eqB tF tJ t3 T okF okJ ok3 hf.base₂) _ _ _ _ _ kF

/-- **fold_three_chains, the shared chain in two parts.** -/
theorem fold_three_chainsB {κ : Type} {N : ℕ} (key : ℕ → S₂ × (EAll D all).Str → κ) (hf : T.Fits)
    (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 (T.p₁ :: T.l₁))
    (e₂ : EachLeadsBN key Pl.on₂ Pl.Q₂ N 0 (T.p₂ :: T.l₂))
    (e₃ : EachLeads Pl.on₃ Pl.Q₃ 0 (T.p₃ :: T.l₃)) (G : Glues T Pl M L₁ L₂) :
    (plainOf tF tJ t3 T Pl okF okJ ok3 h₁ h₂ h₃ M L₁ L₂ d).Leads3B N
      (fun a : X₁ × (EAll D all).Str => key 0 (T.in₂ a.1, a.2)) :=
  ⟨file_leads₁ tF tJ t3 okF okJ ok3 h₁ h₂ h₃ d hf e₁ G,
    file_leadsBN₂ tF tJ t3 okF okJ ok3 h₁ h₂ h₃ d key hf e₂ G,
    file_leads₃ tF tJ t3 okF okJ ok3 h₁ h₂ h₃ d hf e₃ G⟩

end Main
end VerifiableInference.Desc.Plain

namespace VerifiableInference.OnPublicFiles
open Hiop OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open _root_.Compile.Joined (Chains Desc worst_le)
open _root_.CompileK.Joined (Row)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

variable {a : ℕ} (Kc : ConfLetters a) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
  (runK : Kc.conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → TFp → TJp → T3p → Bool)
  (eL : LinkProtocolWithLeafCoding Kc.conf.Rec a) (N : ℕ) (early : Kc.conf.X → Kc.conf.X)
  (F : FileDescription (Kc.conf.X × Kc.conf.Rec)) (all : List LeftT) {X₁ X₂ W κ : Type}
  (T : ThreeAt (ckP .two) (DP.at a) all F X₁ X₂ W)
  (Pl : PPlaces (DP.at a) all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
  (h₁ : (rowIOR (atDesc F T).p₁ (atDesc F T).l₁).shape = uLT (ckP .two) (DP.at a).ds₁)
  (h₂ : (rowIOR (atDesc F T).p₂ (atDesc F T).l₂).shape = uLT (ckP .two) (DP.at a).ds₂)
  (h₃ : (rowIOR (atDesc F T).p₃ (atDesc F T).l₃).shape = uLT (ckP .two) (DP.at a).ds₃)
  (M : (Kc.conf.X × Kc.conf.Rec) × (oneExternalString (2 ^ (DP.at a).a) SgX).Str →
    (F.XiPub × F.S₁) × (EAll (DP.at a) all).Str → Prop)
  (L₁ : (F.XiPub × F.S₁) × (EAll (DP.at a) all).Str → Prop)
  (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DP.at a) all).Str → Prop)
  (d : (F.XiPub × F.S₁) × (EAll (DP.at a) all).Str)
  (key : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll (DP.at a) all).Str → κ)

variable (P : (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
    none).Provers)
  (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                    none) P)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early
                                     none) P)

/-- **`CompilerSoundnessConditionStatements.proofSound` at a description's own decision, from one plain law a block; a shared
block's own errors bear "what hangs on the key, once, and what hangs on a slot's own statement, N
times".** -/
theorem proofSound_at_descB (w₀ : Kc.conf.Cells) (hO : OfDesc F T) (hf : (atDesc F T).Fits)
    (fit : RowFit (DP.at a) all all)
    (e₁ : EachLeads Pl.on₁ Pl.Q₁ 0 ((atDesc F T).p₁ :: (atDesc F T).l₁))
    (e₂ : EachLeadsBN key Pl.on₂ Pl.Q₂ N 0 ((atDesc F T).p₂ :: (atDesc F T).l₂))
    (e₃ : EachLeads Pl.on₃ Pl.Q₃ 0 ((atDesc F T).p₃ :: (atDesc F T).l₃))
    (G : Glues (atDesc F T) Pl M L₁ L₂)
    (pubEarly : ∀ x rec, F.pub (early x, rec) = F.pub (x, rec))
    (F₁ : Kc.conf.Rec → (oneExternalString (2 ^ (DP.at a).a) SgX).Str → κ)
    (oneKey : ∀ x rec y τ b,
      (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).out₁ ((x, rec), y) τ = some b →
      key 0 ((atDesc F T).in₂ b.1, b.2) = F₁ rec y)
    (tie : ∀ x rec (y : (oneExternalString (2 ^ (DP.at a).a) SgX).Str)
      (τ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh) (s₁ : F.S₁) (s₂ : F.S₂) (s₃ : F.S₃)
      (z : (EAll (DP.at a) all).Str),
      F.okStart (x, rec) = true →
      silP (x, rec) ((chainsOf (ckP .two) (DP.at a) tFp tJp t3p).msgF τ).2
        ((chainsOf (ckP .two) (DP.at a) tFp tJp t3p).msgJ τ).2
        ((chainsOf (ckP .two) (DP.at a) tFp tJp t3p).msg3 τ).2 = true →
      F.fin (x, rec) s₁ s₂ s₃ = true →
      (Pl.on₁ 0 ((atDesc F T).in₁ (early x, rec), (y, fun _ => [])) →
        M ((early x, rec), y) ((F.pub (x, rec), s₁), z)) →
      Kc.conf.D y rec = none ∨ ∃ i, Kc.conf.D y rec = some i ∧ Kc.conf.Rno i x w₀)
    (b₁ : Err.Below (errOwn (atDesc F T).p₁ (atDesc F T).l₁ (DP.at a).ds₁ h₁) U.εs)
    (b₂ : Err.Below (errOwn (atDesc F T).p₂ (atDesc F T).l₂ (DP.at a).ds₂ h₂) U.εs)
    (b₃ : Err.Below (errOwn (atDesc F T).p₃ (atDesc F T).l₃ (DP.at a).ds₃ h₃) U.εs) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols (filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP
                                                               F.run eL N early none) P Tl U) := by
  have decides : ∀ x rec y (τ : Tr (chainsOf (ckP .two) (DP.at a) tFp tJp t3p).sh),
      (wholeDesc (ckP .two) (DP.at a) tFp tJp t3p silP F.run).accept (x, rec) y τ = true →
      ((plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d).links.all.out
        ((early x, rec), y) τ).isSome = true := by
    intro x rec y τ ha
    have ho := out_of_acceptP Kc DP tFp tJp t3p silP F _ y τ ha
    have ho' := Sound.wholeMono (ckP .two) (DP.at a) _ _ _ _ tFp tJp t3p silP
      (fun _ _ _ _ => true) F.run F.run (x, rec) (x, rec) (fun _ _ _ _ => rfl)
      (fun _ _ _ h => h) y τ ho
    exact descDecides (ckP .two) (DP.at a) all _ X₁ X₂ W _ _ _ tFp tJp t3p F T (fun _ _ => true)
      (fun _ _ => true) (fun _ _ => true) (fun _ _ _ _ => true)
      (idleSnd tFp tJp t3p (atDesc F T) _ _ _ h₁ h₂ h₃) hO fit (fun _ _ _ _ _ => rfl)
      (fun _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ _ _ _ => rfl) (x, rec) (early x, rec) y τ
      (pubEarly x rec) (fun _ _ _ _ => rfl) ho'
  exact proofSound_plainJB
    ((filesOf Kc .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL N early none).withProvers P)
    (wholeDesc (ckP .two) (DP.at a) tFp tJp t3p silP F.run) rfl Kc.conf.Rno w₀
    (plainP Kc DP tFp tJp t3p F all T Pl h₁ h₂ h₃ M L₁ L₂ d)
    (k₁ := fun b => key 0 ((atDesc F T).in₂ b.1, b.2)) (k₂ := fun _ => ()) rfl
    (fold_three_chainsB tFp tJp t3p _ _ _ h₁ h₂ h₃ d key hf e₁ e₂ e₃ G) rfl F₁ oneKey
    (fun _ _ => ()) (fun _ _ _ _ => rfl) decides
    (fun x rec y τ b ha hb hM => by
      have ho := out_of_acceptP Kc DP tFp tJp t3p silP F _ y τ ha
      obtain ⟨s₁, s₂, s₃, -, hstart, hr₁, -, -, -, hfin⟩ :=
        wholeGivesEnds (ckP .two) (DP.at a) _ _ _ _ tFp tJp t3p F silP (x, rec) y τ ho
      have hsil := ((wholeIOR_out_iff (ckP .two) (DP.at a) tFp tJp t3p y τ silP F.run (x, rec)).1
        ((congrArg Option.isSome ho).trans rfl)).2.2.2.1
      have hfirst := first_is tFp tJp t3p (atDesc F T) (fun _ _ => true) (fun _ _ => true)
        (fun _ _ => true) fit (early x, rec) y τ b hb
      rw [(runsAtDesc (ckP .two) (DP.at a) all _ X₁ X₂ W F T hO).1,
        descRun₁_reads F (x, rec) (early x, rec) (pubEarly x rec), hr₁] at hfirst
      have hb1 : b = ((F.pub (x, rec), s₁), b.2) :=
        Prod.ext (Option.some.inj hfirst).symm rfl
      rw [hb1] at hM
      exact tie x rec y τ s₁ s₂ s₃ b.2 hstart hsil hfin hM)
    (max_le (worst_le (show Err.Below _ U.εs from ⟨by simp, b₁⟩))
      (max_le (worst_le (show Err.Below _ U.εs from ⟨by simp, b₂⟩))
        (worst_le (show Err.Below _ U.εs from ⟨by simp, b₃⟩))))

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.Desc.Plain.fold_chainB
#print axioms VerifiableInference.Desc.Plain.fold_three_chainsB
#print axioms TypedOracleCompiler.Joined.proofSound_plainJB
#print axioms VerifiableInference.OnPublicFiles.proofSound_at_descB
