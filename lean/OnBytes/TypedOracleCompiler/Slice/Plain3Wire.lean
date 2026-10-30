-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Plain3Wire.lean: the wiring of the protocol in three stretches, by the maker, and
its laws. New: no file of the library or of OnBytes/Slice has its like.

Plain3 G dec (OnBytes/TypedOracleCompiler/Slice/Plain3.lean: over rounds' data with a list of trees a round) has
the shape seam, first stretch, two seams, second stretch, seam,
third stretch, and one stored table as its external string.
  Seam.wire  a seam's wire: no tree, no position; its one verifier message
  wL, wApp  a stretch's wires, round by round the maker's wireS (OnBytes/TypedOracleCompiler/Run/PlanQS.lean): one
      tree for each of a round's shapes; alone, or before what follows
  we1 a  the wire of the one string: the library's WireE.one (2 ^ a) SgX, depth a, one walk over a
      pruned set of paths: Run/PlanQX.lean's weX on one string. which p = 0, leaf p = p.val
      (we1_which, we1_leaf)
  wq3 G K chal dec the wiring of the protocol
  wq3_okg  it obeys the sibling's laws (ProtocolQueryLayout.OKG), under the library's three hypotheses, stretch
      by stretch: uniform blocks give uniform verifier messages; what is drawn holds at most the
      entry's number of positions; at most 64 bits of work a round.
The wiring computes: a seam's one verifier message is an argument of Seam.wire (Stretches.Ones names
the four) and is not chosen (Round has only "Nonempty Chal"): a chosen one could not stand on a
run's path. G's seams are seams by type (three conditions each).
A limit that weighs (the library's, Run/PlanQSLaws.lean's head): ChalUnif is false, with challenges
as sampled values, for every round that draws a field element; it holds with challenges as hash
blocks: wq3_okg_pull (at the library's ckP f, chalP f K: every round's number of blocks ≤ K and work
≤ 64: nothing else assumed).
wq3_okg is silent on this: the compiled chain is one chain through all seven pieces (each seam's
query holds the link before it; at a seam no root is taken and the plain part is hashed); the file
has three chains with three labels.
No statement on soundness. Nothing on how queries are spelled, on a parser, on the hash or on a
file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Plain3Local
import OnBytes.TypedOracleCompiler.Slice.Plain3Count
import Iop.WireOK
import OnBytes.TypedOracleCompiler.Run.PlanPull

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open TypedOracleCompiler.Iop TypedOracleCompiler.Run Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## A seam -/

def Seam.wire (s : Seam) (K : ℕ) (c : s.r.Chal) : WireRB 256 K s.r (RAnn.allLocal s.r) where
  pt := { finPos := @Fintype.ofIsEmpty _ s.noPos
          decPos := fun p _ => (s.noPos.false p).elim
          ofSyms := fun _ => s.r.dOrc
          rd_ofSyms := fun _ p => (s.noPos.false p).elim
          ofSyms_rd := fun _ => s.noOrc.elim _ _
          zero := fun p => (s.noPos.false p).elim }
  depth0 := []
  depthJ := []
  tree := fun _ => 0
  place := fun _ => 0
  posAt0 := fun _ _ => none
  posAtJ := fun _ _ => none
  chal := fun _ => c

theorem Seam.wire_okg (s : Seam) (K : ℕ) (c : s.r.Chal) : (s.wire K c).OKG :=
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

theorem Seam.wire_depth (s : Seam) (K n : ℕ) (c : s.r.Chal) :
    (∀ e ∈ (s.wire K c).depth0, e ≤ n) ∧ (∀ e ∈ (s.wire K c).depthJ, e ≤ n) :=
  ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩

/-! ## Stretches -/

section
variable (C : PQ.CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- a stretch's wires -/
def wL : (ds : List PQ.RD) → RoundsQueryLayout 256 (K + 1) (PQ.uL C ds) (RoundSplits.allLocal (PQ.uL C ds))
  | [] => ()
  | d :: ds => (PQ.wireS C K chal d, wL ds)

/-- a stretch's wires, before what follows -/
def wApp (t : Shape) (Wt : RoundsQueryLayout 256 (K + 1) t (RoundSplits.allLocal t)) :
    (ds : List PQ.RD) → RoundsQueryLayout 256 (K + 1) (PQ.uL C ds ++ t) (RoundSplits.allLocal (PQ.uL C ds ++ t))
  | [] => Wt
  | d :: ds => (PQ.wireS C K chal d, wApp t Wt ds)

theorem wL_okg : ∀ ds : List PQ.RD, PQ.ChalUnif C K chal ds → (∀ d ∈ ds, d.entry.work ≤ 64) →
    RoundsQueryLayout.OKG (PQ.uL C ds) (RoundSplits.allLocal (PQ.uL C ds)) (wL C K chal ds)
  | [], _, _ => trivial
  | d :: ds, hc, hw =>
    ⟨PQ.wireS_okg C K chal d (hc d List.mem_cons_self) (hw d List.mem_cons_self),
      wL_okg ds (fun e he => hc e (List.mem_cons_of_mem _ he)) fun e he =>
        hw e (List.mem_cons_of_mem _ he)⟩

theorem wApp_okg (t : Shape) (Wt : RoundsQueryLayout 256 (K + 1) t (RoundSplits.allLocal t))
    (ht : RoundsQueryLayout.OKG t (RoundSplits.allLocal t) Wt) :
    ∀ ds : List PQ.RD, PQ.ChalUnif C K chal ds → (∀ d ∈ ds, d.entry.work ≤ 64) →
      RoundsQueryLayout.OKG (PQ.uL C ds ++ t) (RoundSplits.allLocal (PQ.uL C ds ++ t)) (wApp C K chal t Wt ds)
  | [], _, _ => ht
  | d :: ds, hc, hw =>
    ⟨PQ.wireS_okg C K chal d (hc d List.mem_cons_self) (hw d List.mem_cons_self),
      wApp_okg t Wt ht ds (fun e he => hc e (List.mem_cons_of_mem _ he)) fun e he =>
        hw e (List.mem_cons_of_mem _ he)⟩

theorem wL_depth (n : ℕ) : ∀ ds : List PQ.RD, (∀ d ∈ ds, PQ.depthOf d.trees ≤ n) →
    RoundsQueryLayout.DepthLe n (PQ.uL C ds) (RoundSplits.allLocal (PQ.uL C ds)) (wL C K chal ds)
  | [], _ => trivial
  | d :: ds, h =>
    ⟨⟨fun _ he => (by cases he),
        fun e he => le_trans (PQ.le_depthOf d.trees e he) (h d List.mem_cons_self)⟩,
      wL_depth n ds fun e he => h e (List.mem_cons_of_mem _ he)⟩

theorem wApp_depth (n : ℕ) (t : Shape) (Wt : RoundsQueryLayout 256 (K + 1) t (RoundSplits.allLocal t))
    (ht : RoundsQueryLayout.DepthLe n t (RoundSplits.allLocal t) Wt) :
    ∀ ds : List PQ.RD, (∀ d ∈ ds, PQ.depthOf d.trees ≤ n) →
      RoundsQueryLayout.DepthLe n (PQ.uL C ds ++ t) (RoundSplits.allLocal (PQ.uL C ds ++ t)) (wApp C K chal t Wt ds)
  | [], _ => ht
  | d :: ds, h =>
    ⟨⟨fun _ he => (by cases he),
        fun e he => le_trans (PQ.le_depthOf d.trees e he) (h d List.mem_cons_self)⟩,
      wApp_depth n t Wt ht ds fun e he => h e (List.mem_cons_of_mem _ he)⟩

end

/-! ## The one string -/

/-- the wire of the one string -/
def we1 (a : ℕ) : WireE (oneExternalString (2 ^ a) PQ.SgX) :=
  { WireE.one (2 ^ a) PQ.SgX (0, []) with pr := true, depth := a }

theorem we1_ok (a : ℕ) : (we1 a).OK :=
  ⟨(WireE.one_ok (2 ^ a) PQ.SgX (0, [])).nodup, (WireE.one_ok (2 ^ a) PQ.SgX (0, [])).complete,
    (WireE.one_ok (2 ^ a) PQ.SgX (0, [])).build_rd⟩

theorem we1_depth (a : ℕ) : (we1 a).depth = a := rfl
theorem we1_which (a : ℕ) (p : Fin (2 ^ a)) : (we1 a).which p = 0 := rfl
theorem we1_leaf (a : ℕ) (p : Fin (2 ^ a)) : (we1 a).leaf p = p.val := rfl

/-! ## The whole -/

/-- the four seams' verifier messages (each seam has one: they are named, so that the wiring
computes) -/
structure Stretches.Ones (G : Stretches) where
  c0 : G.s0.r.Chal
  c1 : G.s1.r.Chal
  c2 : G.s2.r.Chal
  c3 : G.s3.r.Chal

namespace Stretches
variable (G : Stretches) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → G.C.Ch e k) (o : G.Ones)

/-- the greatest depth of a tree, the stored table's among them -/
def maxDepth : ℕ :=
  max (max (PQ.maxDepth G.ds₁) (max (PQ.maxDepth G.ds₂) (PQ.maxDepth G.ds₃))) G.a

/-- the fourth seam's and the third stretch's wires -/
def w₃ : RoundsQueryLayout 256 (K + 1) G.sh₃ (RoundSplits.allLocal G.sh₃) :=
  (G.s3.wire (K + 1) o.c3, wL G.C K chal G.ds₃)

/-- the second and third seams', the second stretch's, and what follows -/
def w₂ : RoundsQueryLayout 256 (K + 1) G.sh₂ (RoundSplits.allLocal G.sh₂) :=
  (G.s1.wire (K + 1) o.c1, G.s2.wire (K + 1) o.c2, wApp G.C K chal G.sh₃ (G.w₃ K chal o) G.ds₂)

def wires : RoundsQueryLayout 256 (K + 1) G.sh (RoundSplits.allLocal G.sh) :=
  (G.s0.wire (K + 1) o.c0, wApp G.C K chal G.sh₂ (G.w₂ K chal o) G.ds₁)

end Stretches

/-- The wiring of the protocol in three stretches. -/
def wq3 (G : Stretches) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → G.C.Ch e k) (o : G.Ones)
    (dec : PQ.View → PQ.View → PQ.View → Bool) :
    ProtocolQueryLayout 256 (K + 1) (BatchInteractiveOracleProof.ofProto (Plain3 G dec)) :=
  ⟨G.wires K chal o, we1 G.a, G.decO, G.nOpen, G.maxDepth⟩

/-- THE WIRING OBEYS THE LAWS. -/
theorem wq3_okg (G : Stretches) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → G.C.Ch e k) (o : G.Ones)
    (dec : PQ.View → PQ.View → PQ.View → Bool)
    (c₁ : PQ.ChalUnif G.C K chal G.ds₁) (c₂ : PQ.ChalUnif G.C K chal G.ds₂)
    (c₃ : PQ.ChalUnif G.C K chal G.ds₃)
    (f₁ : PQ.DrawnFits G.C G.ds₁) (f₂ : PQ.DrawnFits G.C G.ds₂) (f₃ : PQ.DrawnFits G.C G.ds₃)
    (w₁ : ∀ d ∈ G.ds₁, d.entry.work ≤ 64) (w₂ : ∀ d ∈ G.ds₂, d.entry.work ≤ 64)
    (w₃ : ∀ d ∈ G.ds₃, d.entry.work ≤ 64) : (wq3 G K chal o dec).OKG where
  sh := by
    have h₃ : RoundsQueryLayout.OKG G.sh₃ (RoundSplits.allLocal G.sh₃) (G.w₃ K chal o) :=
      ⟨G.s3.wire_okg _ _, wL_okg G.C K chal G.ds₃ c₃ w₃⟩
    have h₂ : RoundsQueryLayout.OKG G.sh₂ (RoundSplits.allLocal G.sh₂) (G.w₂ K chal o) :=
      ⟨G.s1.wire_okg _ _, G.s2.wire_okg _ _, wApp_okg G.C K chal G.sh₃ (G.w₃ K chal o)
          h₃ G.ds₂ c₂ w₂⟩
    exact ⟨G.s0.wire_okg _ _, wApp_okg G.C K chal G.sh₂ (G.w₂ K chal o) h₂ G.ds₁ c₁ w₁⟩
  ext := we1_ok G.a
  opens := plain3_opens G dec f₁ f₂ f₃
  depth := by
    have d₁ : ∀ d ∈ G.ds₁, PQ.depthOf d.trees ≤ G.maxDepth := fun d hd =>
      le_trans ((PQ.foldl_max_le (fun d : PQ.RD => PQ.depthOf d.trees) G.ds₁ 0).2 d hd)
        (le_trans (le_max_left _ _) (le_max_left _ _))
    have d₂ : ∀ d ∈ G.ds₂, PQ.depthOf d.trees ≤ G.maxDepth := fun d hd =>
      le_trans ((PQ.foldl_max_le (fun d : PQ.RD => PQ.depthOf d.trees) G.ds₂ 0).2 d hd)
        (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _))
    have d₃ : ∀ d ∈ G.ds₃, PQ.depthOf d.trees ≤ G.maxDepth := fun d hd =>
      le_trans ((PQ.foldl_max_le (fun d : PQ.RD => PQ.depthOf d.trees) G.ds₃ 0).2 d hd)
        (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _))
    have h₃ : RoundsQueryLayout.DepthLe G.maxDepth G.sh₃ (RoundSplits.allLocal G.sh₃) (G.w₃ K chal o) :=
      ⟨G.s3.wire_depth _ _ _, wL_depth G.C K chal _ G.ds₃ d₃⟩
    have h₂ : RoundsQueryLayout.DepthLe G.maxDepth G.sh₂ (RoundSplits.allLocal G.sh₂) (G.w₂ K chal o) :=
      ⟨G.s1.wire_depth _ _ _, G.s2.wire_depth _ _ _,
        wApp_depth G.C K chal _ G.sh₃ (G.w₃ K chal o) h₃ G.ds₂ d₂⟩
    exact ⟨G.s0.wire_depth _ _ _, wApp_depth G.C K chal _ G.sh₂ (G.w₂ K chal o) h₂ G.ds₁ d₁⟩

/-- the data at challenges as hash blocks -/
@[reducible] def Stretches.atP (G : Stretches) (f : Fmt.Fld) : Stretches :=
    { G with C := _root_.Run.ckP f }

/-- WITH CHALLENGES AS HASH BLOCKS THE WIRING IS LAWFUL, NOTHING ELSE ASSUMED but that K blocks
are enough for every round and no round has more than 64 bits of work. -/
theorem wq3_okg_pull (G : Stretches) (f : Fmt.Fld) (K : ℕ) (o : (G.atP f).Ones)
    (dec : PQ.View → PQ.View → PQ.View → Bool)
    (hK : ∀ d ∈ G.ds₁ ++ (G.ds₂ ++ G.ds₃), (_root_.Run.bsRound f d.entry d.kind).b ≤ K)
    (hw : ∀ d ∈ G.ds₁ ++ (G.ds₂ ++ G.ds₃), d.entry.work ≤ 64) :
    (wq3 (G.atP f) K (_root_.Run.chalP f K) o dec).OKG :=
  wq3_okg (G.atP f) K (_root_.Run.chalP f K) o dec
    (planPull_unif f K G.ds₁ fun d hd => hK d (List.mem_append_left _ hd))
    (planPull_unif f K G.ds₂ fun d hd =>
      hK d (List.mem_append_right _ (List.mem_append_left _ hd)))
    (planPull_unif f K G.ds₃ fun d hd =>
      hK d (List.mem_append_right _ (List.mem_append_right _ hd)))
    (planPull_drawn f G.ds₁) (planPull_drawn f G.ds₂) (planPull_drawn f G.ds₃)
    (fun d hd => hw d (List.mem_append_left _ hd))
    (fun d hd => hw d (List.mem_append_right _ (List.mem_append_left _ hd)))
    (fun d hd => hw d (List.mem_append_right _ (List.mem_append_right _ hd)))

/-- the stored table's tree is at most as deep as the wiring's bound (what QueryLayout.OKG's clauses
depthT … ask) -/
theorem a_le_maxDepth (G : Stretches) : G.a ≤ G.maxDepth := le_max_right _ _

end TypedOracleCompiler.Slice
