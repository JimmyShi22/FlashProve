-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Batch3SWire.lean: THE WIRING OF THE BATCH's GENERIC PROTOCOL IN ITS SKELETON FORM
(Slice/Batch3S.lean), AND ITS LAWS. BESIDE Slice/Batch3Wire.lean, which stands.
The text is Batch3Wire's: where that has a Shape t as a parameter, this has a skeleton tail T : List
RS. The rounds' wires are THE SAME TERMS: Front.wire, Seam.wireA, the maker's wireS, wireSh.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
  wLoS | wShS, their laws and depths     a local | shared stretch's wires before a skeleton tail
  BD.wS₃, wSJ, wiresS
  wqBS D K chal o dec : ProtocolQueryLayout 256 (K + 1) (BatchPS D dec).up
  batchPS_opens      the verifier reads at most nFront + G.nOpen positions (Plain3Count's
    asksL_own_len | asksL_ext_len0, stretch by stretch)
  wqBS_okg       THE WIRING OBEYS THE LAWS, under Batch3Wire's hypotheses to the letter
  wqBS_okg_pull  with challenges as hash blocks: from the front's laws, "K blocks are enough for
    every round", "no round has more than 64 bits of work"
The rounds' wires: also Seam.wire; PQ.wiresSL stands where the old has wL: the same two clauses.
WHAT IS NOT SAID. That the PROTOCOLS are one is not shown in this library; no theorem ties this
WIRING to wqB (their types differ by the equation of the two protocols).

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Batch3S
import OnBytes.TypedOracleCompiler.Slice.Batch3Wire

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open TypedOracleCompiler.Iop TypedOracleCompiler.Run Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.Twin (RS PS)

section
variable (C : PQ.CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (T : List RS)

/-- a local stretch's wires, before what follows -/
def wLoS (At : RoundSplits (_root_.Run.Twin.up T)) (Wt : RoundsQueryLayout 256 (K + 1) (_root_.Run.Twin.up T) At) :
    (ds : List PQ.RD) → RoundsQueryLayout 256 (K + 1) (shA C T ds) (annLoS C T At ds)
  | [] => Wt
  | d :: ds => (PQ.wireS C K chal d, wLoS At Wt ds)

/-- a shared stretch's wires, before what follows -/
def wShS (At : RoundSplits (_root_.Run.Twin.up T)) (Wt : RoundsQueryLayout 256 (K + 1) (_root_.Run.Twin.up T) At) :
    (ds : List PQ.RD) → RoundsQueryLayout 256 (K + 1) (shA C T ds) (annShS C T At ds)
  | [] => Wt
  | d :: ds => (wireSh C K chal d, wShS At Wt ds)

theorem wLoS_okg (At : RoundSplits (_root_.Run.Twin.up T))
    (Wt : RoundsQueryLayout 256 (K + 1) (_root_.Run.Twin.up T) At)
    (ht : RoundsQueryLayout.OKG (_root_.Run.Twin.up T) At Wt) :
    ∀ ds : List PQ.RD, PQ.ChalUnif C K chal ds → (∀ d ∈ ds, d.entry.work ≤ 64) →
      RoundsQueryLayout.OKG (shA C T ds) (annLoS C T At ds) (wLoS C K chal T At Wt ds)
  | [], _, _ => ht
  | d :: ds, hc, hw =>
    ⟨PQ.wireS_okg C K chal d (hc d List.mem_cons_self) (hw d List.mem_cons_self),
      wLoS_okg At Wt ht ds (fun e he => hc e (List.mem_cons_of_mem _ he)) fun e he =>
        hw e (List.mem_cons_of_mem _ he)⟩

theorem wShS_okg (At : RoundSplits (_root_.Run.Twin.up T))
    (Wt : RoundsQueryLayout 256 (K + 1) (_root_.Run.Twin.up T) At)
    (ht : RoundsQueryLayout.OKG (_root_.Run.Twin.up T) At Wt) :
    ∀ ds : List PQ.RD, PQ.ChalUnif C K chal ds → (∀ d ∈ ds, d.entry.work ≤ 64) →
      RoundsQueryLayout.OKG (shA C T ds) (annShS C T At ds) (wShS C K chal T At Wt ds)
  | [], _, _ => ht
  | d :: ds, hc, hw =>
    ⟨wireSh_okg C K chal d (hc d List.mem_cons_self) (hw d List.mem_cons_self),
      wShS_okg At Wt ht ds (fun e he => hc e (List.mem_cons_of_mem _ he)) fun e he =>
        hw e (List.mem_cons_of_mem _ he)⟩

theorem wLoS_depth (n : ℕ) (At : RoundSplits (_root_.Run.Twin.up T))
    (Wt : RoundsQueryLayout 256 (K + 1) (_root_.Run.Twin.up T) At)
    (ht : RoundsQueryLayout.DepthLe n (_root_.Run.Twin.up T) At Wt) :
    ∀ ds : List PQ.RD, (∀ d ∈ ds, PQ.depthOf d.trees ≤ n) →
      RoundsQueryLayout.DepthLe n (shA C T ds) (annLoS C T At ds) (wLoS C K chal T At Wt ds)
  | [], _ => ht
  | d :: ds, h =>
    ⟨⟨fun _ he => (by cases he),
        fun e he => le_trans (PQ.le_depthOf d.trees e he) (h d List.mem_cons_self)⟩,
      wLoS_depth n At Wt ht ds fun e he => h e (List.mem_cons_of_mem _ he)⟩

theorem wShS_depth (n : ℕ) (At : RoundSplits (_root_.Run.Twin.up T))
    (Wt : RoundsQueryLayout 256 (K + 1) (_root_.Run.Twin.up T) At)
    (ht : RoundsQueryLayout.DepthLe n (_root_.Run.Twin.up T) At Wt) :
    ∀ ds : List PQ.RD, (∀ d ∈ ds, PQ.depthOf d.trees ≤ n) →
      RoundsQueryLayout.DepthLe n (shA C T ds) (annShS C T At ds) (wShS C K chal T At Wt ds)
  | [], _ => ht
  | d :: ds, h =>
    ⟨⟨fun e he => le_trans (PQ.le_depthOf d.trees e he) (h d List.mem_cons_self),
        fun _ he => (by cases he)⟩,
      wShS_depth n At Wt ht ds fun e he => h e (List.mem_cons_of_mem _ he)⟩

end

namespace BD
variable (D : BD) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → D.G.C.Ch e k) (o : D.G.Ones)

def wS₃ : RoundsQueryLayout 256 (K + 1) (_root_.Run.Twin.up D.S₃) D.annS₃ :=
  (D.G.s3.wire (K + 1) o.c3, PQ.wiresSL D.G.C K chal D.G.ds₃)

def wSJ : RoundsQueryLayout 256 (K + 1) (_root_.Run.Twin.up D.SJ) D.annSJ :=
  (D.G.s2.wireA D.aJ (K + 1) o.c2, wShS D.G.C K chal D.S₃ D.annS₃ (D.wS₃ K chal o) D.G.ds₂)

def wiresS : RoundsQueryLayout 256 (K + 1) D.shS D.annS :=
  (D.F.wire (K + 1), wLoS D.G.C K chal D.SJ D.annSJ (D.wSJ K chal o) D.G.ds₁)

end BD

/-- The wiring of the skeleton's protocol. -/
def wqBS {X : Type} (D : BD) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → D.G.C.Ch e k) (o : D.G.Ones)
    (dec : X → ((p : D.F.r.Pos) → D.F.r.Sym p) → D.F.r.Plain → PQ.View → PQ.View → PQ.View → Bool) :
    ProtocolQueryLayout 256 (K + 1) (BatchPS D dec).up :=
  ⟨D.wiresS K chal o, we1 D.G.a, D.decOS, D.nFront + D.G.nOpen, D.maxDepth⟩

/-- the verifier reads at most nFront + G.nOpen positions -/
theorem batchPS_opens (D : BD)
    (f₁ : PQ.DrawnFits D.G.C D.G.ds₁) (f₂ : PQ.DrawnFits D.G.C D.G.ds₂)
        (f₃ : PQ.DrawnFits D.G.C D.G.ds₃) (ρ : Rho D.shS) :
    (D.frontPosS ∪ ((D.asksS ρ).filterMap D.ownS).toFinset).card +
      (((D.asksS ρ).filterMap (Ask.ext D.G.a)).toFinset).card ≤ D.nFront + D.G.nOpen := by
  have ho : ∀ k z, D.ownS (Ask.stored k z) = none := fun _ _ => rfl
  have hx : ∀ n z, Ask.ext D.G.a (Ask.own n z) = none := fun _ _ => rfl
  have h1 : ((D.asksS ρ).filterMap D.ownS).toFinset.card ≤ PQ.nOpen
      D.G.ds₁ + (PQ.nOpen D.G.ds₂ + PQ.nOpen D.G.ds₃) := by
    refine le_trans (List.toFinset_card_le _) ?_
    unfold BD.asksS
    rw [List.filterMap_append, List.filterMap_append, List.length_append, List.length_append]
    exact Nat.add_le_add (asksL_own_len D.G.a D.G.all D.G.xs₁ D.ownS ho D.G.C 0 D.G.ds₁ f₁ _)
      (Nat.add_le_add (asksL_own_len D.G.a D.G.all D.G.xs₂ D.ownS ho D.G.C 0 D.G.ds₂ f₂ _)
        (asksL_own_len D.G.a D.G.all D.G.xs₃ D.ownS ho D.G.C 0 D.G.ds₃ f₃ _))
  have h2 : (((D.asksS ρ).filterMap (Ask.ext D.G.a)).toFinset).card ≤
      (D.G.xs₁.map (·.count)).sum + ((D.G.xs₂.map (·.count)).sum + (D.G.xs₃.map (·.count)).sum) :=
          by
    refine le_trans (List.toFinset_card_le _) ?_
    unfold BD.asksS
    rw [List.filterMap_append, List.filterMap_append, List.length_append, List.length_append]
    exact Nat.add_le_add (asksL_ext_len0 D.G.a D.G.all D.G.xs₁ _ hx D.G.ds₁ _)
      (Nat.add_le_add (asksL_ext_len0 D.G.a D.G.all D.G.xs₂ _ hx D.G.ds₂ _)
        (asksL_ext_len0 D.G.a D.G.all D.G.xs₃ _ hx D.G.ds₃ _))
  have h3 : (D.frontPosS ∪ ((D.asksS ρ).filterMap D.ownS).toFinset).card ≤
      D.nFront + ((D.asksS ρ).filterMap D.ownS).toFinset.card :=
    le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right
        (le_trans Finset.card_image_le (le_of_eq rfl)) _)
  unfold Stretches.nOpen
  omega

/-- THE WIRING OBEYS THE LAWS. -/
theorem wqBS_okg {X : Type} (D : BD) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → D.G.C.Ch e k)
    (o : D.G.Ones)
    (dec : X → ((p : D.F.r.Pos) → D.F.r.Sym p) → D.F.r.Plain → PQ.View → PQ.View → PQ.View → Bool)
    (hF : D.F.Laws)
    (c₁ : PQ.ChalUnif D.G.C K chal D.G.ds₁) (c₂ : PQ.ChalUnif D.G.C K chal D.G.ds₂)
    (c₃ : PQ.ChalUnif D.G.C K chal D.G.ds₃)
    (f₁ : PQ.DrawnFits D.G.C D.G.ds₁) (f₂ : PQ.DrawnFits D.G.C D.G.ds₂)
        (f₃ : PQ.DrawnFits D.G.C D.G.ds₃)
    (w₁ : ∀ d ∈ D.G.ds₁, d.entry.work ≤ 64) (w₂ : ∀ d ∈ D.G.ds₂, d.entry.work ≤ 64)
    (w₃ : ∀ d ∈ D.G.ds₃, d.entry.work ≤ 64) : (wqBS D K chal o dec).OKG where
  sh := by
    have h₃ : RoundsQueryLayout.OKG (_root_.Run.Twin.up D.S₃) D.annS₃ (D.wS₃ K chal o) :=
      ⟨D.G.s3.wire_okg _ _, PQ.wiresS_okg D.G.C K chal D.G.ds₃ c₃ w₃⟩
    have h₂ : RoundsQueryLayout.OKG (_root_.Run.Twin.up D.SJ) D.annSJ (D.wSJ K chal o) :=
      ⟨D.G.s2.wireA_okg _ _ _, wShS_okg D.G.C K chal D.S₃ D.annS₃ (D.wS₃ K chal o) h₃ D.G.ds₂ c₂ w₂⟩
    exact ⟨D.F.wire_okg _ hF, wLoS_okg D.G.C K chal D.SJ D.annSJ (D.wSJ K chal o) h₂ D.G.ds₁ c₁ w₁⟩
  ext := we1_ok D.G.a
  opens := fun _ ρ _ => batchPS_opens D f₁ f₂ f₃ ρ
  depth := by
    have hm : D.G.maxDepth ≤ D.maxDepth := le_max_left _ _
    have d₁ : ∀ d ∈ D.G.ds₁, PQ.depthOf d.trees ≤ D.maxDepth := fun d hd => le_trans
      (le_trans ((PQ.foldl_max_le (fun d : PQ.RD => PQ.depthOf d.trees) D.G.ds₁ 0).2 d hd)
        (le_trans (le_max_left _ _) (le_max_left _ _))) hm
    have d₂ : ∀ d ∈ D.G.ds₂, PQ.depthOf d.trees ≤ D.maxDepth := fun d hd => le_trans
      (le_trans ((PQ.foldl_max_le (fun d : PQ.RD => PQ.depthOf d.trees) D.G.ds₂ 0).2 d hd)
        (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _))) hm
    have d₃ : ∀ d ∈ D.G.ds₃, PQ.depthOf d.trees ≤ D.maxDepth := fun d hd => le_trans
      (le_trans ((PQ.foldl_max_le (fun d : PQ.RD => PQ.depthOf d.trees) D.G.ds₃ 0).2 d hd)
        (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _))) hm
    have h₃ : RoundsQueryLayout.DepthLe D.maxDepth (_root_.Run.Twin.up D.S₃) D.annS₃ (D.wS₃ K chal o) :=
      ⟨D.G.s3.wire_depth _ _ _, PQ.depthSL D.G.C K chal _ D.G.ds₃ d₃⟩
    have h₂ : RoundsQueryLayout.DepthLe D.maxDepth (_root_.Run.Twin.up D.SJ) D.annSJ (D.wSJ K chal o) :=
      ⟨⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩,
        wShS_depth D.G.C K chal D.S₃ _ D.annS₃ (D.wS₃ K chal o) h₃ D.G.ds₂ d₂⟩
    exact ⟨⟨fun _ h => (by cases h), fun e he => le_trans (le_foldl_max D.F.depths 0 e (Or.inl he)) (le_max_right _ _)⟩,
      wLoS_depth D.G.C K chal D.SJ _ D.annSJ (D.wSJ K chal o) h₂ D.G.ds₁ d₁⟩

/-- WITH CHALLENGES AS HASH BLOCKS THE WIRING IS LAWFUL. -/
theorem wqBS_okg_pull {X : Type} (D : BD) (f : Fmt.Fld) (K : ℕ) (o : (D.atP f).G.Ones)
    (dec : X → ((p : D.F.r.Pos) → D.F.r.Sym p) → D.F.r.Plain → PQ.View → PQ.View → PQ.View → Bool)
        (hF : D.F.Laws)
    (hK : ∀ d ∈ D.G.ds₁ ++ (D.G.ds₂ ++ D.G.ds₃), (_root_.Run.bsRound f d.entry d.kind).b ≤ K)
    (hw : ∀ d ∈ D.G.ds₁ ++ (D.G.ds₂ ++ D.G.ds₃), d.entry.work ≤ 64) :
    (wqBS (D.atP f) K (_root_.Run.chalP f K) o dec).OKG :=
  wqBS_okg (D.atP f) K (_root_.Run.chalP f K) o dec hF
    (planPull_unif f K D.G.ds₁ fun d hd => hK d (List.mem_append_left _ hd))
    (planPull_unif f K D.G.ds₂ fun d hd =>
      hK d (List.mem_append_right _ (List.mem_append_left _ hd)))
    (planPull_unif f K D.G.ds₃ fun d hd =>
      hK d (List.mem_append_right _ (List.mem_append_right _ hd)))
    (planPull_drawn f D.G.ds₁) (planPull_drawn f D.G.ds₂) (planPull_drawn f D.G.ds₃)
    (fun d hd => hw d (List.mem_append_left _ hd))
    (fun d hd => hw d (List.mem_append_right _ (List.mem_append_left _ hd)))
    (fun d hd => hw d (List.mem_append_right _ (List.mem_append_right _ hd)))

end TypedOracleCompiler.Slice
