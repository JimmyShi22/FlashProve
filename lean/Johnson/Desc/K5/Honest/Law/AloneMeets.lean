-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/AloneMeets.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: THE VERIFIER's WRITTEN CLAIM ON A SCALAR THAT IS SENT BY ITSELF IS WORTH THE
SLOT'S WORTH LESS THE PROVER's VALUE, READ. Two definitions of premises, and statements with their
proofs.

The verifier's claims on these scalars are written forms "slot less the pieces' weighted sum of a
reader of a table" (Johnson/Desc/First/Att/Claims/Say.lean, Say58.lean list them). In a world in
which every table is true of some matrices the tree has each reader's worth as a read of the
matrices' cells (Claims/MeanRd.lean, Claims/KeysLin.lean, Claims/EndsVA.lean, Claims/EndsVB.lean).
Johnson/Desc/K5/Honest/Law/ReadAlone.lean has the prover's value as the same read of the prover's
cells. Here the two are joined. So a clause "the claim is worth 0" follows from "the slot is worth
the prover's value, read" by one rewrite.

Main names:
  `CellsAre`         the premise: the matrices hold, at the library's address of each valid name,
                     what the prover's input has under that name, read
  `PiecesFit`        the premise: each piece names a layer and a head of the shape; public
  `less_meets`       the claim's worth, over the kind's own pieces
  `plane_meets_below`, `plane_meets_on`   R and PV
  `mv_meets`, `zc_meets`, `ib_meets`      MV, ZC, IB_k
  `rh_meets`, `rhp_meets`   RH and RH2; RHP and RHP2
  `m6_meets`         M6_b: here the claim is "slot = reader", and the reader is worth the prover's
                     value

EVERY STATEMENT IS CONDITIONAL; `less_meets` and the four tools on their own premises alone. The
premises, and who is meant to show each:
  `AttAt` (Johnson/Road/Rows/AttRead.lean): the shape is the planner's, the matrices fit, and EVERY
    TABLE OF THE LIST IS TRUE OF THE MATRICES IN THE WORLD: whoever lays the world.
  `CellsAre`: whoever lays the matrices of the prover's input.
  `TabAt`, `AsAt`: the table lies in the list with the named weights; `InLong` and the premises
    "hin": the indices read lie in the table; the points' lengths; `PiecesFit`: public, or drawn
    from the return of the verifier's functions: the caller's.
Limits. For RH2 and RHP2 the table's weights are asked at the points of these scalars' own list; the
verifier lays the table at another list's points and tests that they are the same. For a plane the
table's weights are asked at the unit's own last coordinates; the verifier lays them at the lookup's
point's and tests the same. Nothing here says that a premise holds at any place. No property is
claimed by a definition.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.ReadAlone
import Johnson.Desc.First.Att.Claims.KeysLin
import Johnson.Desc.First.Att.Claims.Say58
import Johnson.Desc.First.Att.Claims.Any

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (W1 RemP ScoreP geoOf)
open Inst.Model.AttSeg (Raw Dim rd2 rd3 mxV denV)
open K5Law (pwBack remBack InLong)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} {tl : HTailF2} {K3 : ℕ} {M : Mats K}
  {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}

/-! ## The premises -/

/-- **The premise on the cells**: the matrices hold, at the library's address of each valid name,
what the prover's input has under that name, read. -/
def CellsAre (ρ : Reading K) (S : Attention.Shape) (M : Mats K) (w : K5In) : Prop :=
  ∀ q : Raw, q.Valid (L5.dimOf S) → cellsK S M q = tOf ρ w q

/-- **The premise on a list of pieces**: each names a layer and a head of the shape. Public. -/
def PiecesFit (S : Attention.Shape) (pw : Array W1) : Prop :=
  ∀ p ∈ pw.toList, p.lam < S.Lam ∧ p.a < S.HA

/-- A piece's pair number is a pair's. -/
theorem PiecesFit.pair {S : Attention.Shape} {pw : Array W1} (Pf : PiecesFit S pw) {p : W1}
    (hp : p ∈ pw.toList) : p.lam * S.HA + p.a < (L5.dimOf S).nb := by
  obtain ⟨h1, h2⟩ := Pf p hp
  have h3 : (p.lam + 1) * S.HA ≤ S.Lam * S.HA := Nat.mul_le_mul_right _ h1
  rw [Nat.add_mul, Nat.one_mul] at h3
  show p.lam * S.HA + p.a < S.Lam * S.HA
  omega

/-! ## Tools -/

/-- **The claim "slot less the pieces' weighted sum of a reader"**, over the kind's own pieces. -/
theorem less_meets (s : ℕ) (pw : Array W1) (fv : PW → Aff) (V : W1 → K)
    (hV : ∀ p ∈ pw.toList, (fv { lam := p.lam, a := p.a, wp := p.wp }).value ρ W = V p) :
    (Fo.lessF (Aff.slot s) (pwBack pw) fv).value ρ W =
      W.slot s - (pw.toList.map fun p => ρ.val p.wp * V p).sum := by
  rw [K5Law.lessF_value, Aff.value_slot]
  congr 1
  unfold K5Law.pwBack
  rw [Array.toList_map, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun p hp => by
    show ρ.val p.wp * _ = _
    rw [hV p hp])

/-- A read reads its array at heads and tokens of the shape alone. -/
theorem rd2_on (D : Dim) (vg Ψ : ℕ → K) {a a' : ℕ → ℕ → K}
    (e : ∀ g < D.nG, ∀ i < D.T, a g i = a' g i) : rd2 D vg Ψ a = rd2 D vg Ψ a' := by
  unfold rd2
  exact sum_congr rfl fun g hg => sum_congr rfl fun i hi => by
    rw [e g (mem_range.mp hg) i (mem_range.mp hi)]

/-- The same with channels. -/
theorem rd3_on (D : Dim) (vg Ψ vn : ℕ → K) {a a' : ℕ → ℕ → ℕ → K}
    (e : ∀ g < D.nG, ∀ i < D.T, ∀ n < D.ch, a g i n = a' g i n) :
    rd3 D vg Ψ vn a = rd3 D vg Ψ vn a' := by
  unfold rd3
  exact sum_congr rfl fun g hg => sum_congr rfl fun i hi => sum_congr rfl fun n hn => by
    rw [e g (mem_range.mp hg) i (mem_range.mp hi) n (mem_range.mp hn)]

/-- A sum over heads and tokens, for one pair. -/
theorem read_row (ρ : Reading K) {D : Dim} {zg tk : Array E} {vg Ψ : ℕ → K} {f : ℕ → ℕ → E}
    {a : ℕ → ℕ → K} (hg : zg.size = D.lg) (hvg : ∀ j < D.lg, pt ρ zg j = vg j)
    (ht : tk.size = D.T) (hΨ : ∀ i < D.T, ρ.val (tk.getD i zeroE) = Ψ i)
    (hf : ∀ g i, ρ.val (f g i) = a g i) :
    ρ.val (under (P.eqTab zg) fun hk => under tk fun i => f hk i) = rd2 D vg Ψ a := by
  rw [read_under_eq ρ hg hvg]
  unfold rd2
  refine sum_congr rfl fun g _ => ?_
  rw [read_under, ht, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [hΨ i (mem_range.mp hi), hf]
  ring

/-! ## The meetings -/

variable (A : AttAt ρ W tl K3 M h lid cf fs) (w : K5In) (hc : CellsAre ρ h.S M w)
include A hc

/-- **R and PV below the diagonal**: a member of a plane claim. CONDITIONAL on what the head lists.
-/
theorem plane_meets_below {u : RemP} (hD : u.isD = false)
    (Tb : AsAt h h.t.tA (lastN u.z h.S.cf.lmS)) (hz : u.z.size = h.S.nM) (Pf : PiecesFit h.S u.pw)
    {x : ℕ} (hx : x < 5)
    (hin : ∀ p ∈ u.pw.toList,
      ∀ hi < (eqTab (u.z.extract 0 ((if false then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
        Rows.planeFirst h.S x p.lam p.a false >>> h.S.cf.lmS + hi <
          (h.t.tabLen.lookup h.t.tA).getD 0) :
    (Fo.planeMember h K3 (remBack u) x).value ρ W =
      W.slot (u.s0 + x) - ρ.val (planeOf (geoOf h.S) w u x) := by
  have N := norm_of_hid A.shape
  rw [read_planeOf]
  show (Fo.lessF (Aff.slot (u.s0 + x)) (pwBack u.pw) fun y =>
    Fo.planeF h K3 h.t.tA x y.lam y.a u.z u.isD).value ρ W = _
  refine less_meets _ u.pw _ _ fun p hp => ?_
  rw [hD, K5Law.planeF_below A Tb hz (Pf p hp).2 (hin p hp), hz]
  refine Blocks.ext_congr (fun X hX => ?_) _
  rw [N.nM] at hX
  exact hc (.c .M x (p.lam * h.S.HA + p.a) X) ⟨hx, Pf.pair hp, hX⟩

/-- **R and PV on the diagonal.** CONDITIONAL on what the head lists. -/
theorem plane_meets_on {u : RemP} (hD : u.isD = true)
    (Tb : AsAt h h.t.tA (lastN u.z h.S.cf.lmS)) (hz : u.z.size = h.S.nD) (Pf : PiecesFit h.S u.pw)
    {x : ℕ} (hx : x < 5)
    (hin : ∀ p ∈ u.pw.toList,
      ∀ hi < (eqTab (u.z.extract 0 ((if true then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
        Rows.planeFirst h.S x p.lam p.a true >>> h.S.cf.lmS + hi <
          (h.t.tabLen.lookup h.t.tA).getD 0) :
    (Fo.planeMember h K3 (remBack u) x).value ρ W =
      W.slot (u.s0 + x) - ρ.val (planeOf (geoOf h.S) w u x) := by
  have N := norm_of_hid A.shape
  rw [read_planeOf]
  show (Fo.lessF (Aff.slot (u.s0 + x)) (pwBack u.pw) fun y =>
    Fo.planeF h K3 h.t.tA x y.lam y.a u.z u.isD).value ρ W = _
  refine less_meets _ u.pw _ _ fun p hp => ?_
  rw [hD, K5Law.planeF_on A Tb hz (Pf p hp).2 (hin p hp), hz]
  refine Blocks.ext_congr (fun X hX => ?_) _
  rw [N.nD] at hX
  exact hc (.c .D x (p.lam * h.S.HA + p.a) X) ⟨hx, Pf.pair hp, hX⟩

/-- **MV**: the clause on a softmax-table unit's maximum. CONDITIONAL on what the head lists. -/
theorem mv_meets {k : ScoreP} {tM s : ℕ}
    (Tb : TabAt tl h tM h.S.cf.NAs h.S.T (Attention.tok h.S k.wI k.zi))
    (hz : k.zg.size = h.S.cf.lgk) (Pf : PiecesFit h.S k.pw)
    (hin : ∀ p ∈ k.pw.toList, ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4,
      h.S.oMr + (l * h.S.Lam + p.lam) * h.S.cf.H + (g * h.S.HA + p.a) <
        (h.t.tabLen.lookup tM).getD 0) :
    (Fo.lessF (Aff.slot s) (pwBack k.pw) fun x =>
      Fo.readMaximumF h K3 tM k.zg x.lam x.a).value ρ W =
      W.slot s - ρ.val (maxAt (geoOf h.S) w k) := by
  have H : Sized (⟨h.S, default⟩ : Pub5) := sized_of_hid A.shape
  rw [show ρ.val (maxAt (geoOf h.S) w k) = _ from read_maxAt ρ (P := ⟨h.S, default⟩) w H hz]
  refine less_meets s k.pw _ _ fun p hp => ?_
  rw [K5Law.readMaximumF_rd2 A Tb (Nat.le_of_eq hz.symm) (Pf p hp).2 (hin p hp)]
  refine rd2_on _ _ _ fun g hg i hi => ?_
  unfold mxV
  exact sum_congr rfl fun l hl => by
    rw [hc (.mx l (p.lam * h.S.HA + p.a) g i) ⟨mem_range.mp hl, Pf.pair hp, hg, hi⟩]
    rfl

/-- **ZC**: at the pieces and points of the list of the remainders' low bits the right side's value
is `zcAt`. CONDITIONAL on what the head lists. -/
theorem zc_meets {pw : Array W1} {zg zi : Array E} {t s : ℕ}
    (Tb : TabAt tl h t h.S.cf.NAs h.S.T (eqTab zi)) (hz : zg.size = h.S.cf.lgk)
    (hi : zi.size = h.S.cf.lt) (Pf : PiecesFit h.S pw)
    (hin : ∀ p ∈ pw.toList, ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4,
      h.S.oZr + (l * h.S.Lam + p.lam) * h.S.cf.H + (g * h.S.HA + p.a) <
        (h.t.tabLen.lookup t).getD 0) :
    (Fo.lessF (Aff.slot s) (pwBack pw) fun x =>
      Fo.readDenominatorF h K3 t zg x.lam x.a).value ρ W =
      W.slot s - ρ.val (atRow (geoOf h.S) pw zg zi w.zd) := by
  have H : Sized (⟨h.S, default⟩ : Pub5) := sized_of_hid A.shape
  rw [show ρ.val (atRow (geoOf h.S) pw zg zi w.zd) = _ from
    read_rows ρ (P := ⟨h.S, default⟩) (f := w.zd) (a := denV (tOf ρ w)) hz (fun _ _ => rfl)
      (size_eqTab_tok (hi.trans H.lt)) (fun _ _ => rfl) (read_zd ρ w)]
  refine less_meets s pw _ _ fun p hp => ?_
  rw [K5Law.readDenominatorF_rd2 A Tb (Nat.le_of_eq hz.symm) (Pf p hp).2 (hin p hp)]
  refine rd2_on _ _ _ fun g hg i hi' => ?_
  unfold denV
  exact sum_congr rfl fun l hl => by
    rw [hc (.den l (p.lam * h.S.HA + p.a) g i) ⟨mem_range.mp hl, Pf.pair hp, hg, hi'⟩]
    rfl

/-- **IB_k**: at the pieces and points of the list of the indices the right side's value is member k
of `ibAt`'s list. CONDITIONAL on what the head lists. -/
theorem ib_meets {pw : Array W1} {zg zi : Array E} {t s k : ℕ} (hk : k < h.S.cf.lt)
    (Tb : TabAt tl h t h.S.cf.NAs h.S.T (eqTab zi)) (hz : zg.size = h.S.cf.lgk)
    (hi : zi.size = h.S.cf.lt) (Pf : PiecesFit h.S pw)
    (hin : ∀ p ∈ pw.toList, ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 1,
      h.S.oIb + (l * h.S.Lam + p.lam) * (h.S.cf.lt * h.S.cf.H) +
        (k * h.S.cf.H + g * h.S.HA + p.a) < (h.t.tabLen.lookup t).getD 0) :
    (Fo.lessF (Aff.slot s) (pwBack pw) fun x =>
      Fo.readIndexBitF h K3 t zg x.lam x.a k).value ρ W =
      W.slot s - ρ.val (atRow (geoOf h.S) pw zg zi (w.ibit k)) := by
  have H : Sized (⟨h.S, default⟩ : Pub5) := sized_of_hid A.shape
  rw [show ρ.val (atRow (geoOf h.S) pw zg zi (w.ibit k)) = _ from
    read_rows ρ (P := ⟨h.S, default⟩) (f := w.ibit k) (a := Inst.Model.AttSeg.ibV (tOf ρ w) k) hz
      (fun _ _ => rfl) (size_eqTab_tok (hi.trans H.lt)) (fun _ _ => rfl) (read_ibit ρ w k)]
  refine less_meets s pw _ _ fun p hp => ?_
  rw [K5Law.readIndexBitF_rd2 A Tb (Nat.le_of_eq hz.symm) (Pf p hp).2 (hin p hp)]
  refine rd2_on _ _ _ fun g hg i hi' => ?_
  exact hc (.ib k (p.lam * h.S.HA + p.a) g i) ⟨hk.trans_eq H.lt, Pf.pair hp, hg, hi'⟩

/-- **RH and RH2**: at a list's own pieces and points the right side's value is `rhAt`, `rh2At`.
CONDITIONAL on what the head lists. -/
theorem rh_meets {pw : Array W1} {zg zi zc : Array E} {t s : ℕ}
    (Tb : TabAt tl h t (h.S.cf.NAs + 1) (2 ^ h.S.cf.la) (blockRows (lowOf h.S zc) (eqTab zi)))
    (hz : zg.size = h.S.cf.lgk) (hi : zi.size = h.S.cf.lt) (hzc : zc.size = h.S.cf.ldh)
    (Pf : PiecesFit h.S pw)
    (I : ∀ p ∈ pw.toList, InLong h t (atRh h.S) p.lam (fun g => g * h.S.HA + p.a) zc) :
    (Fo.lessF (Aff.slot s) (pwBack pw) fun x =>
      Fo.readHeadT h K3 t (atRh h.S) zg zc x.lam x.a).value ρ W =
      W.slot s - ρ.val (atChan (geoOf h.S) pw zg zi zc w.rh) := by
  have H : Sized (⟨h.S, default⟩ : Pub5) := sized_of_hid A.shape
  have ht := size_eqTab_tok (P := ⟨h.S, default⟩) (hi.trans H.lt)
  rw [show ρ.val (atChan (geoOf h.S) pw zg zi zc w.rh) = _ from
    read_chans ρ (P := ⟨h.S, default⟩) (f := w.rh) (a := fun b g i n => tOf ρ w (.qh b g i n)) hz
      (fun _ _ => rfl) ht (fun _ _ => rfl) hzc (fun _ _ => rfl) fun _ _ _ _ => rfl]
  refine less_meets s pw _ _ fun p hp => ?_
  rw [K5Law.readHeadT_qh A Tb (ht.trans H.T.symm) (Nat.le_of_eq hz.symm) hzc (Pf p hp).2 (I p hp)]
  exact rd3_on _ _ _ _ fun g hg i hi' n hn => hc _ ⟨Pf.pair hp, hg, hi', hn⟩

/-- **RHP and RHP2.** CONDITIONAL on what the head lists. -/
theorem rhp_meets {pw : Array W1} {zg zi zc : Array E} {t s : ℕ}
    (Tb : TabAt tl h t (h.S.cf.NAs + 1) (2 ^ h.S.cf.la) (blockRows (lowOf h.S zc) (eqTab zi)))
    (hz : zg.size = h.S.cf.lgk) (hi : zi.size = h.S.cf.lt) (hzc : zc.size = h.S.cf.ldh)
    (Pf : PiecesFit h.S pw)
    (I : ∀ p ∈ pw.toList, InLong h t (atRhp h.S) p.lam (fun g => g * h.S.HA + p.a) zc) :
    (Fo.lessF (Aff.slot s) (pwBack pw) fun x =>
      Fo.readHeadT h K3 t (atRhp h.S) zg zc x.lam x.a).value ρ W =
      W.slot s - ρ.val (atChan (geoOf h.S) pw zg zi zc w.rhp) := by
  have H : Sized (⟨h.S, default⟩ : Pub5) := sized_of_hid A.shape
  have ht := size_eqTab_tok (P := ⟨h.S, default⟩) (hi.trans H.lt)
  rw [show ρ.val (atChan (geoOf h.S) pw zg zi zc w.rhp) = _ from
    read_chans ρ (P := ⟨h.S, default⟩) (f := w.rhp) (a := fun b g i n => tOf ρ w (.qh' b g i n)) hz
      (fun _ _ => rfl) ht (fun _ _ => rfl) hzc (fun _ _ => rfl) fun _ _ _ _ => rfl]
  refine less_meets s pw _ _ fun p hp => ?_
  rw [K5Law.readHeadT_qh' A Tb (ht.trans H.T.symm) (Nat.le_of_eq hz.symm) hzc (Pf p hp).2 (I p hp)]
  exact rd3_on _ _ _ _ fun g hg i hi' n hn => hc _ ⟨Pf.pair hp, hg, hi', hn⟩

/-- **M6_b**: the claim is "slot = reader"; the reader is worth member b of the list of the row
maxima that the prover sends, written out. CONDITIONAL on what the head lists. -/
theorem m6_meets {tg ti : Array E} {t b : ℕ} (hb : b < h.S.NP)
    (Tb : TabAt tl h t h.S.cf.NAs h.S.T (eqTab ti)) (hz : tg.size = h.S.cf.lgk)
    (hi : ti.size = h.S.cf.lt)
    (hin : ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4,
      h.S.oMr + (l * h.S.Lam + b / h.S.HA) * h.S.cf.H + (g * h.S.HA + b % h.S.HA) <
        (h.t.tabLen.lookup t).getD 0) :
    (Fo.readMaximumF h K3 t tg (b / h.S.HA) (b % h.S.HA)).value ρ W =
      ρ.val (under (P.eqTab tg) fun hk => under (P.eqTab ti) fun i => w.mx b hk i) := by
  have H : Sized (⟨h.S, default⟩ : Pub5) := sized_of_hid A.shape
  have hHA : 0 < h.S.HA := by
    rcases Nat.eq_zero_or_pos h.S.HA with e | e
    · have hb' : b < h.S.Lam * h.S.HA := hb
      rw [e, Nat.mul_zero] at hb'
      exact absurd hb' (Nat.not_lt_zero _)
    · exact e
  rw [K5Law.readMaximumF_rd2 A Tb (Nat.le_of_eq hz.symm) (Nat.mod_lt _ hHA) hin,
    Nat.div_add_mod' b h.S.HA,
    read_row ρ (D := L5.dimOf h.S) (f := w.mx b) (a := mxV (tOf ρ w) b) hz (fun _ _ => rfl)
      (size_eqTab_tok (P := ⟨h.S, default⟩) (hi.trans H.lt)) (fun _ _ => rfl) (read_mx ρ w b)]
  refine rd2_on _ _ _ fun g hg i hi' => ?_
  unfold mxV
  exact sum_congr rfl fun l hl => by rw [hc (.mx l b g i) ⟨mem_range.mp hl, hb, hg, hi'⟩]

end H2K5.Honest

#print axioms H2K5.Honest.PiecesFit.pair
#print axioms H2K5.Honest.less_meets
#print axioms H2K5.Honest.rd2_on
#print axioms H2K5.Honest.rd3_on
#print axioms H2K5.Honest.read_row
#print axioms H2K5.Honest.plane_meets_below
#print axioms H2K5.Honest.plane_meets_on
#print axioms H2K5.Honest.mv_meets
#print axioms H2K5.Honest.zc_meets
#print axioms H2K5.Honest.ib_meets
#print axioms H2K5.Honest.rh_meets
#print axioms H2K5.Honest.rhp_meets
#print axioms H2K5.Honest.m6_meets
