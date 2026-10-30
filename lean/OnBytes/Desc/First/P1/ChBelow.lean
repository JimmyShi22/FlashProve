-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/ChBelow.lean: WHEN THE WRITTEN COUNTS OF A CHAIN'S STRETCH LIE BELOW THE CAP:
from the clause on one written round's count (`RoundBelow`, OnBytes/Slice/ManyErr.lean),
asked round by round against the list of the chain's own typed counts. Definitions and statements
with their proofs. Bookkeeping on lists: no count is priced here.

The written counts of a stretch (`Maps.err`, OnBytes/Flat/CarrySMaps.lean) are, at each written
round that is read, the typed count times the sampler's number w; `RoundBelow e d εs` says that e ·
w is at most εs times the number of d's written challenges; `Err.Below` (Iop/InteractiveOracleProof.lean) asks that
of every round; `Err.le_cap_of_below_inv` (Iop/ErrCap.lean) then gives "at most the cap `Err.cap k`,
entry by entry". The maps of OnBytes/Desc/First/P1/ChMaps.lean read every written round, so all that
is asked is a relation between two plain lists.

  `readRds M`: the written rounds that the maps M read. `below_of_list`: `Err.Below (M.err ε) εs`
    from `RoundBelow`, pair by pair, between the list of the typed counts and that list.
  `ChM.maps_reads`: the maps of a chain's data read every written round, in order.
  `ChM.below_of`, `ChM.le_cap`: at the chain's own errors (`Ch.eps`), from
    `List.Forall₂ (fun e d => RoundBelow e (toRD d) _) c.nums ds` (`Ch.nums`, Cb/Pv/Att/Chain.lean).
  `ScR.Below`, `TailBelow`: that relation for the chain of a layers' sub-proof's own rounds, piece
    by piece: a sumcheck's counts are 1, then 2 for each variable, then the further variable's
    degree, then 0. `TailM.below`, `own_le_cap`, `ownFirst_le_cap`.

Limits. No count is shown to be small, no written round is named: `RoundBelow` is a premise at every
round. What a share of the written challenges is worth is said in other files of the library.
Nothing on soundness.
-/
import OnBytes.Desc.First.P1.OwnMaps
import OnBytes.Slice.ManyErr
import Iop.ErrCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open Iop Prob IOR Run Cb TWhole Cb.Pv.Lay Cb.Pv.Att Johnson.L5.Layers Johnson.L5.Door
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open scoped ENNReal

/-- The clause on one typed count at one written round. -/
abbrev RdBelow (εs : ℝ≥0∞) (e : ℕ) (d : RDT) : Prop := RoundBelow e (toRD d) εs

/-- The written rounds that are read. -/
def readRds : {ds : List RDT} → {s' : Shape} → Maps ds s' → List RDT
  | _, _, .nil => []
  | _, _, .step (d := d) _ rest => d :: readRds rest
  | _, _, .skip _ rest => readRds rest

/-- The written counts are shares of at most εs, from the clause pair by pair. -/
theorem below_of_list (εs : ℝ≥0∞) : ∀ {ds : List RDT} {s' : Shape} (M : Maps ds s') (ε : Err s'),
    List.Forall₂ (RdBelow εs) (TWhole.errList ε) (readRds M) → Err.Below (M.err ε) εs
  | _, _, .nil, _, _ => trivial
  | _, _, .step (d := d) _ rest, (e, ε), h => by
      have h' : List.Forall₂ (RdBelow εs) (e :: TWhole.errList ε) (d :: readRds rest) := h
      cases h' with
      | cons h1 h2 => exact ⟨h1, below_of_list εs rest ε h2⟩
  | _, _, .skip _ rest, ε, h =>
      ⟨by rw [Nat.cast_zero]; exact zero_le _, below_of_list εs rest ε h⟩

theorem readRds_app : ∀ {ds es : List RDT} {s' t' : Shape} (M : Maps ds s') (N : Maps es t'),
    readRds (M.app N) = readRds M ++ readRds N
  | _, _, _, _, .nil, _ => rfl
  | _, _, _, _, .step (d := d) _ rest, N => congrArg (d :: ·) (readRds_app rest N)
  | _, _, _, _, .skip _ rest, N => readRds_app rest N

theorem readRds_castT {ds : List RDT} {s' t' : Shape} (h : s' = t') (M : Maps ds s') :
    readRds (M.castT h) = readRds M := by
  subst h
  rfl

theorem errList_along {s t : Shape} (h : s = t) (δ : Err t) :
    TWhole.errList (h ▸ δ) = TWhole.errList δ := by
  subst h
  rfl

theorem midMaps_reads {A : Type} (n : ℕ) (num : A → ℕ) (dY dV : RDT) :
    ∀ ds : List RDT, readRds (midMaps n num dY dV ds) = ds ++ [dY, dV]
  | [] => rfl
  | d :: ds => congrArg (d :: ·) (midMaps_reads n num dY dV ds)

variable {M : Type}

namespace ChM

/-- **The maps of a chain's data read every written round, in order.** -/
theorem maps_reads : ∀ {X : Type} {c : Ch GE M X} {ds : List RDT} (D : ChM c ds),
    readRds D.maps = ds
  | _, _, _, .done _ => rfl
  | _, _, _, .ride (Y := Y) (n := n) dE vs dY dV DY num hf rest => by
      show readRds ((rideMaps Y n dE vs dY dV DY num hf).app rest.maps) = _
      rw [readRds_app, maps_reads rest]
      show (dE :: readRds (Maps.castT _ (midMaps DY num dY dV vs))) ++ _ = _
      rw [readRds_castT, midMaps_reads]
  | _, _, _, .draw1 d rest => by
      show readRds ((Maps.step (mDraw d) .nil).app rest.maps) = _
      rw [readRds_app, maps_reads rest]
      rfl
  | _, _, _, .drawPt (g := g) d rest => by
      show readRds ((Maps.step (mPoint g d) .nil).app rest.maps) = _
      rw [readRds_app, maps_reads rest]
      rfl
  | _, _, _, .send (n := n) d rest => by
      show readRds ((Maps.step (mSend n d) .nil).app rest.maps) = _
      rw [readRds_app, maps_reads rest]
      rfl

/-- **The written counts at the chain's own errors are shares of at most εs.** -/
theorem below_of (εs : ℝ≥0∞) (Ex : ExtSpec) {X : Type} {c : Ch GE M X} {ds : List RDT}
    (D : ChM c ds) (h : List.Forall₂ (RdBelow εs) c.nums ds) :
    Err.Below ((D.mapsR Ex).err (c.eps Ex)) εs := by
  unfold mapsR
  rw [Maps.err_castT]
  refine below_of_list εs D.maps _ ?_
  rw [errList_along (Ch.shape_R Ex c).symm, Ch.errList_eps, maps_reads]
  exact h

/-- **They are at most the cap.** -/
theorem le_cap (k : ℕ) (Ex : ExtSpec) {X : Type} {c : Ch GE M X} {ds : List RDT} (D : ChM c ds)
    (h : List.Forall₂ (RdBelow ((2 : ℝ≥0∞)⁻¹ ^ k)) c.nums ds) :
    Err.le ((D.mapsR Ex).err (c.eps Ex)) (Err.cap k (uLT (ckP .two) ds)) :=
  Err.le_cap_of_below_inv k _ (below_of _ Ex D h)

end ChM

/-! ### The chain of a layers' sub-proof's own rounds -/

theorem forall₂_rep {α β : Type} {R : α → β → Prop} (a : α) : ∀ l : List β, (∀ b ∈ l, R a b) →
    List.Forall₂ R (List.replicate l.length a) l
  | [], _ => .nil
  | b :: l, h => .cons (h b List.mem_cons_self)
      (forall₂_rep a l fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))

/-- The clause at a masked sumcheck's written rounds; DY: the further variable's degree. -/
structure ScR.Below (εs : ℝ≥0∞) (DY : ℕ) (r : ScR) : Prop where
  e : RdBelow εs 1 r.dE
  v : ∀ d ∈ r.vs, RdBelow εs 2 d
  y : RdBelow εs DY r.dY
  z : RdBelow εs 0 r.dV

theorem StgM.below {εs : ℝ≥0∞} {X : Type} {S : Stg GE M X} {r : ScR} (W : StgM S r)
    (h : r.Below εs W.DY) (Ow : S.Nx → M → Prop) {next : Ch GE M S.Nx} {ds : List RDT}
    (hn : List.Forall₂ (RdBelow εs) next.nums ds) :
    List.Forall₂ (RdBelow εs) (S.stage Ow next).nums (r.all ++ ds) := by
  show List.Forall₂ (RdBelow εs) ((1 :: (S.L.T.par.fmt.map PFmt.n ++ [0])) ++ next.nums)
    ((r.dE :: (r.vs ++ [r.dY, r.dV])) ++ ds)
  rw [W.hf, List.map_append, List.map_replicate, List.append_assoc]
  exact List.rel_append (.cons h.e (List.rel_append (forall₂_rep _ r.vs h.v)
    (.cons h.y (.cons h.z .nil)))) hn

/-- The clause at every written round from the limbs' scalars on. -/
structure TailBelow (εs : ℝ≥0∞) {X : Type} {T : LayTail GE M X} {R : TailR} (W : TailM T R) :
    Prop where
  l : RdBelow εs T.eL R.dL
  n : RdBelow εs T.eN R.dN
  s1 : R.r1.Below εs W.w1.DY
  t1 : RdBelow εs 1 R.t1
  p : RdBelow εs T.eP R.dP
  s2 : R.r2.Below εs W.w2.DY
  s3 : R.r3.Below εs W.w3.DY
  d4 : RdBelow εs (T.n4 - 1) R.d4
  s4 : R.r4.Below εs W.w4.DY
  s5 : R.r5.Below εs W.w5.DY
  t5 : RdBelow εs 1 R.t5
  r : RdBelow εs T.eR R.dR
  s6 : R.r6.Below εs W.w6.DY
  t6 : RdBelow εs 1 R.t6
  w : RdBelow εs T.eW R.dW
  s7 : R.r7.Below εs W.w7.DY

theorem TailM.below {εs : ℝ≥0∞} {X : Type} {T : LayTail GE M X} {R : TailR} (W : TailM T R)
    (H : TailBelow εs W) : List.Forall₂ (RdBelow εs) T.ch.nums R.all :=
  .cons H.l (.cons H.n (W.w1.below H.s1 _ (.cons H.t1 (.cons H.p (W.w2.below H.s2 _
    (W.w3.below H.s3 _ (.cons H.d4 (W.w4.below H.s4 _ (W.w5.below H.s5 _ (.cons H.t5
      (.cons H.r (W.w6.below H.s6 _ (.cons H.t6 (.cons H.w (W.w7.below H.s7 _ .nil)))))))))))))))

/-- **The own rounds' written counts are at most the cap.** -/
theorem own_le_cap (k : ℕ) (Ex : ExtSpec) {X : Type} (A : LayOwn GE M X) {dT : RDT} {R : TailR}
    (W : TailM A.tail R) (hT : RdBelow ((2 : ℝ≥0∞)⁻¹ ^ k) A.eT dT)
    (H : TailBelow ((2 : ℝ≥0∞)⁻¹ ^ k) W) :
    Err.le (((ownM A dT W).mapsR Ex).err (A.ch.eps Ex))
      (Err.cap k (uLT (ckP .two) ([dT] ++ R.all))) :=
  ChM.le_cap k Ex _ (.cons hT (W.below H))

/-- **The first sub-proof's.** -/
theorem ownFirst_le_cap (k : ℕ) (Ex : ExtSpec) {X : Type} (A : LayOwnFirst GE M X)
    {dT dA dB : RDT} {R : TailR} (W : TailM A.tail R) (hT : RdBelow ((2 : ℝ≥0∞)⁻¹ ^ k) A.eT dT)
    (hA : RdBelow ((2 : ℝ≥0∞)⁻¹ ^ k) A.eA dA) (hB : RdBelow ((2 : ℝ≥0∞)⁻¹ ^ k) A.eB dB)
    (H : TailBelow ((2 : ℝ≥0∞)⁻¹ ^ k) W) :
    Err.le (((ownFirstM A dT dA dB W).mapsR Ex).err (A.ch.eps Ex))
      (Err.cap k (uLT (ckP .two) ([dT] ++ ([dA] ++ ([dB] ++ R.all))))) :=
  ChM.le_cap k Ex _ (.cons hT (.cons hA (.cons hB (W.below H))))

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.ChM.below_of
#print axioms OnBytes.Desc.First.P1.ChM.le_cap
#print axioms OnBytes.Desc.First.P1.own_le_cap
#print axioms OnBytes.Desc.First.P1.ownFirst_le_cap
