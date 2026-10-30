-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Batch3Wire.lean: THE WIRING OF THE BATCH's GENERIC PROTOCOL (Slice/Batch3.lean),
BY THE MAKER, AND ITS LAWS. After Slice/Plain3Wire.lean.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
  Front.wire, wire_okg     the front's wire: its trees are the SLOT's own (the front is a local
    round); lawful, if the front's data are (Front.Laws)
  Seam.wireA, wireA_okg    a seam's wire under ANY annotation (the joining round's): no tree, no
    position
  wireSh, wireSh_okg   THE WIRE OF A SHARED WRITTEN ROUND: the maker's wireS WITH THE TWO
    COMPONENTS SWAPPED: one tree for each of the round's shapes OVER THE SHARED COMPONENT m_0
    (depth0, posAt0, pr0, gr0); the slot's component has none
  wLo, wSh                 a stretch's wires, local | shared, before what follows, under any
    annotation of what follows
  BD.wires, wqB        the wiring of the batch protocol: the stored table's wire is Plain3Wire's
    we1; at most (the front's positions + Plain3's nOpen) openings; depths up to the greatest of
    Plain3's and the front's
  wqB_okg              IT OBEYS THE SIBLING's LAWS (ProtocolQueryLayout.OKG), under the library's three
    hypotheses stretch by stretch and the front's laws
  wqB_okg_pull         with challenges as hash blocks: from "K blocks are enough for every
    round", "at most 64 bits of work a round" and the front's laws ALONE
OF THE EIGHT CLAUSES THAT WrittenB.OK ASKS OF A BUILDER THESE ARE HAD FOR EVERY SUCH DATA: wire
(wqB_okg), loc (batch3_local), coh (ann_coherent, FROM the joining round's), ext (we1_which |
we1_leaf). IN PART: extDepth: the stored table's wire has the depth G.a (we1_depth): that W.depth is
G.a is the whole wiring's matter; late: ann_localTo serves every n up to the first stretch's length;
"0 < n" and which n is the interface's (WHERE late MUST BE none the clause is empty and ann_localTo
serves nobody). NOT HERE: backS, backP (how symbols and plain parts are written into bodies and
queries, and read back): the string bodies are made as for Plain3. That ALL EIGHT can be had over
these two files is not shown in this library.
WHAT IS NOT SAID. All that Slice/Batch3.lean's head leaves out. A LIMIT THAT WEIGHS (the library's):
uniform verifier messages hold with challenges as hash blocks, not as sampled values. The laws know
neither maxRt nor that a round's trees are as many as its items' roots.
IN A SHARED ROUND ONE VERIFIER MESSAGE SERVES ALL SLOTS: that is the frame's (Kind.sh); no law of a
wire speaks of it. ONE TOY, in a file of this project that is not in this library, runs a shared
round, the joining round, (G), (F3) to (F5)
and the request tree through Front.one', Front.wire, wireSh, wqB and Batch3 (another toy's front, in
another such file,
has 256 verifier messages: it is no Front). The front's wire has the flag for pruned walks OFF (each
front opening its own climb); all written rounds have it on. Front.Laws does not bound the number of
the front's trees: above maxRt the verifier refuses all. A seam made by Seam.written G.C d keeps the
OLD kit after BD.atP (it turns G.C alone).

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Batch3
import OnBytes.TypedOracleCompiler.Slice.Plain3Wire

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open TypedOracleCompiler.Iop TypedOracleCompiler.Run Rom _root_.Compile Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## The front; a seam under any annotation -/

def Front.wire (F : Front) (K : ℕ) : WireRB 256 K F.r (RAnn.allLocal F.r) where
  pt := F.pt
  depth0 := []
  depthJ := F.depths
  tree := F.tree
  place := F.place
  posAt0 := fun _ _ => none
  posAtJ := F.posAt
  chal := fun _ => F.c

theorem Front.wire_okg (F : Front) (K : ℕ) (h : F.Laws) : (F.wire K).OKG where
  place_lt0 := fun _ e => by cases e
  place_ltJ := fun p _ => h.place_lt p
  posAt0_place := fun _ e => by cases e
  posAtJ_place := fun p _ => h.posAt_place p
  place_posAt0 := fun _ _ _ e => by cases e
  place_posAtJ := fun k j p e => ⟨rfl, h.place_posAt k j p e⟩
  no0 := fun _ _ _ => rfl
  noJ := fun k hk j => h.no k hk j
  chal_unif := by
    haveI := F.one
    exact PQ.unif_unique _
  gr0_ok := fun _ e => by cases e
  grJ_ok := fun _ e => by cases e

def Seam.wireA (s : Seam) (a : RAnn s.r) (K : ℕ) (c : s.r.Chal) : WireRB 256 K s.r a where
  pt := (s.wire K c).pt
  depth0 := []
  depthJ := []
  tree := fun _ => 0
  place := fun _ => 0
  posAt0 := fun _ _ => none
  posAtJ := fun _ _ => none
  chal := fun _ => c

theorem Seam.wireA_okg (s : Seam) (a : RAnn s.r) (K : ℕ) (c : s.r.Chal) : (s.wireA a K c).OKG :=
  { place_lt0 := fun p => (s.noPos.false p).elim, place_ltJ := fun p => (s.noPos.false p).elim
    posAt0_place := fun p => (s.noPos.false p).elim, posAtJ_place := fun p => (s.noPos.false p).elim
    place_posAt0 := fun _ _ _ h => by cases h
    place_posAtJ := fun _ _ _ h => by cases h
    no0 := fun _ _ _ => rfl, noJ := fun _ _ _ => rfl
    chal_unif := by
      haveI := s.one
      exact PQ.unif_unique _
    gr0_ok := fun _ e => by cases e
    grJ_ok := fun _ e => by cases e }

/-! ## A shared written round -/

section
variable (C : PQ.CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- the wire of a shared written round: the maker's wireS with the two components swapped -/
def wireSh (d : PQ.RD) : WireRB 256 (K + 1) (PQ.roundS C d).up
    (RAnn.ofShared .sh (PQ.roundS C d).up) where
  pt := (PQ.wireS C K chal d).pt
  depth0 := (PQ.wireS C K chal d).depthJ
  depthJ := []
  tree := (PQ.wireS C K chal d).tree
  place := (PQ.wireS C K chal d).place
  posAt0 := (PQ.wireS C K chal d).posAtJ
  posAtJ := fun _ _ => none
  chal := (PQ.wireS C K chal d).chal
  pr0 := (PQ.wireS C K chal d).prJ
  gr0 := (PQ.wireS C K chal d).grJ
  grJ := none

theorem wireSh_okg (d : PQ.RD)
    (hc : (unif (Fin K → Dig 256)).map (chal d.entry d.kind) = unif (C.Ch d.entry d.kind))
    (hw : d.entry.work ≤ 64) : (wireSh C K chal d).OKG :=
  have h := PQ.wireS_okg C K chal d hc hw
  { place_lt0 := fun p _ => h.place_ltJ p rfl
    place_ltJ := fun _ e => by cases e
    posAt0_place := fun p _ => h.posAtJ_place p rfl
    posAtJ_place := fun _ e => by cases e
    place_posAt0 := fun k j p e => ⟨rfl, (h.place_posAtJ k j p e).2⟩
    place_posAtJ := fun _ _ _ e => by cases e
    no0 := h.noJ
    noJ := fun _ _ _ => rfl
    chal_unif := h.chal_unif
    gr0_ok := h.grJ_ok
    grJ_ok := fun _ e => by cases e }

/-- a local stretch's wires, before what follows -/
def wLo (t : Shape) (At : RoundSplits t) (Wt : RoundsQueryLayout 256 (K + 1) t At) :
    (ds : List PQ.RD) → RoundsQueryLayout 256 (K + 1) (PQ.uL C ds ++ t) (annLo C t At ds)
  | [] => Wt
  | d :: ds => (PQ.wireS C K chal d, wLo t At Wt ds)

/-- a shared stretch's wires, before what follows -/
def wSh (t : Shape) (At : RoundSplits t) (Wt : RoundsQueryLayout 256 (K + 1) t At) :
    (ds : List PQ.RD) → RoundsQueryLayout 256 (K + 1) (PQ.uL C ds ++ t) (annSh C t At ds)
  | [] => Wt
  | d :: ds => (wireSh C K chal d, wSh t At Wt ds)

theorem wLo_okg (t : Shape) (At : RoundSplits t) (Wt : RoundsQueryLayout 256 (K + 1) t At) (ht : RoundsQueryLayout.OKG t At Wt) :
    ∀ ds : List PQ.RD, PQ.ChalUnif C K chal ds → (∀ d ∈ ds, d.entry.work ≤ 64) →
      RoundsQueryLayout.OKG (PQ.uL C ds ++ t) (annLo C t At ds) (wLo C K chal t At Wt ds)
  | [], _, _ => ht
  | d :: ds, hc, hw =>
    ⟨PQ.wireS_okg C K chal d (hc d List.mem_cons_self) (hw d List.mem_cons_self),
      wLo_okg t At Wt ht ds (fun e he => hc e (List.mem_cons_of_mem _ he)) fun e he =>
        hw e (List.mem_cons_of_mem _ he)⟩

theorem wSh_okg (t : Shape) (At : RoundSplits t) (Wt : RoundsQueryLayout 256 (K + 1) t At) (ht : RoundsQueryLayout.OKG t At Wt) :
    ∀ ds : List PQ.RD, PQ.ChalUnif C K chal ds → (∀ d ∈ ds, d.entry.work ≤ 64) →
      RoundsQueryLayout.OKG (PQ.uL C ds ++ t) (annSh C t At ds) (wSh C K chal t At Wt ds)
  | [], _, _ => ht
  | d :: ds, hc, hw =>
    ⟨wireSh_okg C K chal d (hc d List.mem_cons_self) (hw d List.mem_cons_self),
      wSh_okg t At Wt ht ds (fun e he => hc e (List.mem_cons_of_mem _ he)) fun e he =>
        hw e (List.mem_cons_of_mem _ he)⟩

theorem wLo_depth (n : ℕ) (t : Shape) (At : RoundSplits t) (Wt : RoundsQueryLayout 256 (K + 1) t At)
    (ht : RoundsQueryLayout.DepthLe n t At Wt) :
    ∀ ds : List PQ.RD, (∀ d ∈ ds, PQ.depthOf d.trees ≤ n) →
      RoundsQueryLayout.DepthLe n (PQ.uL C ds ++ t) (annLo C t At ds) (wLo C K chal t At Wt ds)
  | [], _ => ht
  | d :: ds, h =>
    ⟨⟨fun _ he => (by cases he),
        fun e he => le_trans (PQ.le_depthOf d.trees e he) (h d List.mem_cons_self)⟩,
      wLo_depth n t At Wt ht ds fun e he => h e (List.mem_cons_of_mem _ he)⟩

theorem wSh_depth (n : ℕ) (t : Shape) (At : RoundSplits t) (Wt : RoundsQueryLayout 256 (K + 1) t At)
    (ht : RoundsQueryLayout.DepthLe n t At Wt) :
    ∀ ds : List PQ.RD, (∀ d ∈ ds, PQ.depthOf d.trees ≤ n) →
      RoundsQueryLayout.DepthLe n (PQ.uL C ds ++ t) (annSh C t At ds) (wSh C K chal t At Wt ds)
  | [], _ => ht
  | d :: ds, h =>
    ⟨⟨fun e he => le_trans (PQ.le_depthOf d.trees e he) (h d List.mem_cons_self),
        fun _ he => (by cases he)⟩,
      wSh_depth n t At Wt ht ds fun e he => h e (List.mem_cons_of_mem _ he)⟩

end

/-! ## The whole -/

namespace BD
variable (D : BD) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → D.G.C.Ch e k) (o : D.G.Ones)

/-- the greatest depth of a tree of the front -/
def frontDepth : ℕ := D.F.depths.foldl max 0

def maxDepth : ℕ := max D.G.maxDepth D.frontDepth

/-- the number of the front's positions -/
def nFront : ℕ := @Fintype.card _ D.F.pt.finPos

def wJ : RoundsQueryLayout 256 (K + 1) D.shJ D.annJ :=
  (D.G.s2.wireA D.aJ (K + 1) o.c2, wSh D.G.C K chal D.G.sh₃ D.ann₃ (D.G.w₃ K chal o) D.G.ds₂)

def wires : RoundsQueryLayout 256 (K + 1) D.sh D.ann :=
  (D.F.wire (K + 1), wLo D.G.C K chal D.shJ D.annJ (D.wJ K chal o) D.G.ds₁)

end BD

/-- The wiring of the batch protocol. -/
def wqB {X : Type} (D : BD) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → D.G.C.Ch e k) (o : D.G.Ones)
    (dec : X → ((p : D.F.r.Pos) → D.F.r.Sym p) → D.F.r.Plain → PQ.View → PQ.View → PQ.View → Bool) :
    ProtocolQueryLayout 256 (K + 1) (BatchP D dec) :=
  ⟨D.wires K chal o, we1 D.G.a, D.decO, D.nFront + D.G.nOpen, D.maxDepth⟩

theorem le_foldl_max : ∀ (l : List ℕ) (b e : ℕ), (e ∈ l ∨ e ≤ b) → e ≤ l.foldl max b
  | [], _, _, h => h.elim (fun h => by cases h) id
  | a :: l, b, e, h => le_foldl_max l (max b a) e (by
      rcases h with h | h
      · rcases List.mem_cons.1 h with rfl | h'
        · exact Or.inr (le_max_right _ _)
        · exact Or.inl h'
      · exact Or.inr (le_trans h (le_max_left _ _)))

/-- THE WIRING OBEYS THE LAWS. -/
theorem wqB_okg {X : Type} (D : BD) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → D.G.C.Ch e k)
    (o : D.G.Ones)
    (dec : X → ((p : D.F.r.Pos) → D.F.r.Sym p) → D.F.r.Plain → PQ.View → PQ.View → PQ.View → Bool)
    (hF : D.F.Laws)
    (c₁ : PQ.ChalUnif D.G.C K chal D.G.ds₁) (c₂ : PQ.ChalUnif D.G.C K chal D.G.ds₂)
    (c₃ : PQ.ChalUnif D.G.C K chal D.G.ds₃)
    (f₁ : PQ.DrawnFits D.G.C D.G.ds₁) (f₂ : PQ.DrawnFits D.G.C D.G.ds₂)
        (f₃ : PQ.DrawnFits D.G.C D.G.ds₃)
    (w₁ : ∀ d ∈ D.G.ds₁, d.entry.work ≤ 64) (w₂ : ∀ d ∈ D.G.ds₂, d.entry.work ≤ 64)
    (w₃ : ∀ d ∈ D.G.ds₃, d.entry.work ≤ 64) : (wqB D K chal o dec).OKG where
  sh := by
    have h₃ : RoundsQueryLayout.OKG D.G.sh₃ D.ann₃ (D.G.w₃ K chal o) :=
      ⟨D.G.s3.wire_okg _ _, wL_okg D.G.C K chal D.G.ds₃ c₃ w₃⟩
    have h₂ : RoundsQueryLayout.OKG D.shJ D.annJ (D.wJ K chal o) :=
      ⟨D.G.s2.wireA_okg _ _ _, wSh_okg D.G.C K chal D.G.sh₃ D.ann₃ (D.G.w₃ K chal o) h₃
          D.G.ds₂ c₂ w₂⟩
    exact ⟨D.F.wire_okg _ hF, wLo_okg D.G.C K chal D.shJ D.annJ (D.wJ K chal o) h₂ D.G.ds₁ c₁ w₁⟩
  ext := we1_ok D.G.a
  opens := fun x ρ pl => by
    have h := plain3_opens D.G (dec x (fun p => D.F.pt.zero p) D.F.r.dPlain) f₁ f₂ f₃ ()
        (D.toRho ρ) (D.toPl pl)
    have h1 : (D.frontPos ∪ (((D.G.asksAt (D.toRho ρ)).filterMap D.G.own).toFinset.image
        D.posB)).card ≤
        D.nFront + ((D.G.asksAt (D.toRho ρ)).filterMap D.G.own).toFinset.card :=
      le_trans (Finset.card_union_le _ _) (Nat.add_le_add
        (le_trans Finset.card_image_le (le_of_eq rfl)) Finset.card_image_le)
    show (D.frontPos ∪ (((D.G.asksAt (D.toRho ρ)).filterMap D.G.own).toFinset.image D.posB)).card +
      (((D.G.asksAt (D.toRho ρ)).filterMap (Ask.ext D.G.a)).toFinset).card ≤ D.nFront + D.G.nOpen
    have h' : ((D.G.asksAt (D.toRho ρ)).filterMap D.G.own).toFinset.card +
      (((D.G.asksAt (D.toRho ρ)).filterMap (Ask.ext D.G.a)).toFinset).card ≤ D.G.nOpen := h
    omega
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
    have h₃ : RoundsQueryLayout.DepthLe D.maxDepth D.G.sh₃ D.ann₃ (D.G.w₃ K chal o) :=
      ⟨D.G.s3.wire_depth _ _ _, wL_depth D.G.C K chal _ D.G.ds₃ d₃⟩
    have h₂ : RoundsQueryLayout.DepthLe D.maxDepth D.shJ D.annJ (D.wJ K chal o) :=
      ⟨⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩,
        wSh_depth D.G.C K chal _ D.G.sh₃ D.ann₃ (D.G.w₃ K chal o) h₃ D.G.ds₂ d₂⟩
    exact ⟨⟨fun _ h => (by cases h), fun e he => le_trans (le_foldl_max D.F.depths 0 e (Or.inl he)) (le_max_right _ _)⟩,
      wLo_depth D.G.C K chal _ D.shJ D.annJ (D.wJ K chal o) h₂ D.G.ds₁ d₁⟩

/-- the stored table's tree is at most as deep as the wiring's bound (what QueryLayout.OKG's clause depthB
asks) -/
theorem BD.a_le_maxDepth (D : BD) : D.G.a ≤ D.maxDepth :=
    le_trans (Slice.a_le_maxDepth D.G) (le_max_left _ _)

/-- the data at challenges as hash blocks -/
@[reducible] def BD.atP (D : BD) (f : Fmt.Fld) : BD := { D with G := D.G.atP f }

/-- WITH CHALLENGES AS HASH BLOCKS THE WIRING IS LAWFUL: from the front's laws, "K blocks are
enough for every round" and "no round has more than 64 bits of work" alone. -/
theorem wqB_okg_pull {X : Type} (D : BD) (f : Fmt.Fld) (K : ℕ) (o : (D.atP f).G.Ones)
    (dec : X → ((p : D.F.r.Pos) → D.F.r.Sym p) → D.F.r.Plain → PQ.View → PQ.View → PQ.View → Bool)
        (hF : D.F.Laws)
    (hK : ∀ d ∈ D.G.ds₁ ++ (D.G.ds₂ ++ D.G.ds₃), (_root_.Run.bsRound f d.entry d.kind).b ≤ K)
    (hw : ∀ d ∈ D.G.ds₁ ++ (D.G.ds₂ ++ D.G.ds₃), d.entry.work ≤ 64) :
    (wqB (D.atP f) K (_root_.Run.chalP f K) o dec).OKG :=
  wqB_okg (D.atP f) K (_root_.Run.chalP f K) o dec hF
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
