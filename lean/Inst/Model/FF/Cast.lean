-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/FF/Cast.lean: the field relation of a feed-forward segment, formed over the integers.

  The looked-up values (keys in Lean names) are polynomials in cells of the matrices af, ad, ar, qa,
  xin, xout (`Mx`, Inst/Model/FF/Index.lean) and in entries of the matrix W, with public integer
  coefficients. So a key can be formed over the integers and reduced afterwards; the same is true of
  the identities (J1) to (J11) (`Idn`, Inst/Model/FF/Trace.lean). The families of keys: `Fam`,
  Inst/Model/FF/Index.lean. Words of this library: lean/GLOSSARY.md.
    `castT t`            an integer trace, mapped into a ring
    `val_cast` .. `Ad_cast`
                         every array and every function of the cells commutes with the map from the
                         integers to a ring
    `key_cast`, `idn_cast`
                         so do the keys of the 34 families and the identities
    `Cast.layerCast'`, `embCast`
                         reading the weights from the matrix W commutes with that map
    `RFraw`              the field relation for a function on all names of cells, with the weights
                         as integers
    `rf_iff`             for an integer matrix W mapped into F, `RFraw` at the weights and the
                         embedding read from W is equivalent to the relation of `trace`
                         (Inst/Model/FF/Trace.lean), on functions on the valid names
    `rfraw_of_int`       `RFraw` over the integers implies `RFraw` over every commutative ring
    `key_inLut`, `idn_modEq`
                         `RFraw` over `ZMod p`, as congruences modulo p
  Some small lemmas have the prefix `Cast`. After the same part of Inst/Model/Att/Trace.lean.

  Scales: the instance argument `[scl : Scl]` (Inst/Model/Scl.lean, Inst/Model/FF/Index.lean). A
  theorem marked "omit scl in" reads no scale.
-/
import Inst.Model.FF.Trace
import Inst.Model.Common.TableKeys

set_option autoImplicit false

/- The default instance `Scl.ref` (the reference scales) is switched off in this file: whatever
reads scales takes `[scl : Scl]`. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Inst.Model.FFSeg

variable [scl : Scl]

open Finset
open Site (site high)

/-- an integer trace, mapped into a ring -/
def castT {R : Type} [CommRing R] (t : Cell → ℤ) : Cell → R := fun c => ((t c : ℤ) : R)

section Cast
variable {R : Type} [CommRing R] (D : Dim) (t : Cell → ℤ) (tb : Tables) (L0 : ℕ) (w : ℕ → LayerW)

omit scl in
theorem castT_int : (castT t : Cell → ℤ) = t := funext fun _ => Int.cast_id

omit scl in
theorem val_cast (X : Arr) (a j i : ℕ) :
    val (castT t : Cell → R) X a j i = ((val t X a j i : ℤ) : R) := by
  unfold val castT
  push_cast
  rfl

omit scl in
theorem xS_cast (s j i : ℕ) : xS D (castT t : Cell → R) s j i = ((xS D t s j i : ℤ) : R) :=
  val_cast t _ _ _ _

omit scl in
theorem bS_cast (s l j i : ℕ) : bS D (castT t : Cell → R) s l j i = ((bS D t s l j i : ℤ) : R) :=
  rfl

omit scl in
theorem led_cast (ν i : ℕ) : led (castT t : Cell → R) ν i = fun n => ((led t ν i n : ℤ) : R) :=
  funext fun _ => val_cast t _ _ _ _

omit scl in
theorem ledR_cast (ν i : ℕ) :
    Ledger.R (led (castT t : Cell → R) ν i) = ((Ledger.R (led t ν i) : ℤ) : R) := by
  rw [led_cast]
  exact (Ledger.map_R (Int.castRingHom R) (led t ν i)).symm

omit scl in
theorem Cast.ledR_cast' (ν i : ℕ) :
    Ledger.R (fun n => ((led t ν i n : ℤ) : R)) = ((Ledger.R (led t ν i) : ℤ) : R) :=
  (Ledger.map_R (Int.castRingHom R) (led t ν i)).symm

omit scl in
theorem gw_cast (l x i : ℕ) : gw (castT t : Cell → R) l x i = ((gw t l x i : ℤ) : R) := by
  unfold gw
  simp only [val_cast]
  push_cast
  rfl

omit scl in
theorem lw_cast (l x i : ℕ) : lw (castT t : Cell → R) l x i = ((lw t l x i : ℤ) : R) := by
  unfold lw
  simp only [val_cast]
  push_cast
  rfl

omit scl in
theorem mr_cast (l i : ℕ) : mr D (castT t : Cell → R) l i = ((mr D t l i : ℤ) : R) := by
  unfold mr
  simp only [val_cast]
  push_cast
  rfl

omit scl in
theorem hh_cast (l j i : ℕ) : hh (castT t : Cell → R) l j i = ((hh t l j i : ℤ) : R) := by
  unfold hh
  simp only [val_cast]
  push_cast
  rfl

omit scl in
theorem Aq_cast (l x i : ℕ) :
    Aq D (castT t : Cell → R) (fun l => LW.ofInt R (w l)) l x i =
      ((Aq D t (fun l => LW.ofInt ℤ (w l)) l x i : ℤ) : R) := by
  unfold Aq LW.ofInt
  simp only [val_cast]
  push_cast
  rfl

omit scl in
theorem Ak_cast (l x i : ℕ) :
    Ak D (castT t : Cell → R) (fun l => LW.ofInt R (w l)) l x i =
      ((Ak D t (fun l => LW.ofInt ℤ (w l)) l x i : ℤ) : R) := by
  unfold Ak LW.ofInt
  simp only [val_cast]
  push_cast
  rfl

omit scl in
theorem Av_cast (l x i : ℕ) :
    Av D (castT t : Cell → R) (fun l => LW.ofInt R (w l)) l x i =
      ((Av D t (fun l => LW.ofInt ℤ (w l)) l x i : ℤ) : R) := by
  unfold Av LW.ofInt
  simp only [val_cast]
  push_cast
  rfl

omit scl in
theorem AY_cast (l x i : ℕ) :
    AY D (castT t : Cell → R) (fun l => LW.ofInt R (w l)) l x i =
      ((AY D t (fun l => LW.ofInt ℤ (w l)) l x i : ℤ) : R) := by
  unfold AY
  split_ifs
  · exact Aq_cast D t w l x i
  · exact Ak_cast D t w l _ i

omit scl in
theorem Y'_cast (l x i : ℕ) :
    Y' D (castT t : Cell → R) tb L0 (fun l => LW.ofInt R (w l)) l x i =
      ((Y' D t tb L0 (fun l => LW.ofInt ℤ (w l)) l x i : ℤ) : R) := by
  unfold Y'
  dsimp only
  simp only [AY_cast]
  split_ifs <;> push_cast <;> rfl

omit scl in
theorem Ag_cast (l x i : ℕ) :
    Ag D (castT t : Cell → R) (fun l => LW.ofInt R (w l)) l x i =
      ((Ag D t (fun l => LW.ofInt ℤ (w l)) l x i : ℤ) : R) := by
  unfold Ag LW.ofInt
  simp only [val_cast]
  split_ifs <;> push_cast <;> rfl

omit scl in
theorem Au_cast (l x i : ℕ) :
    Au D (castT t : Cell → R) (fun l => LW.ofInt R (w l)) l x i =
      ((Au D t (fun l => LW.ofInt ℤ (w l)) l x i : ℤ) : R) := by
  unfold Au LW.ofInt
  simp only [val_cast]
  split_ifs <;> push_cast <;> rfl

omit scl in
theorem Ad_cast (l x i : ℕ) :
    Ad D (castT t : Cell → R) (fun l => LW.ofInt R (w l)) l x i =
      ((Ad D t (fun l => LW.ofInt ℤ (w l)) l x i : ℤ) : R) := by
  unfold Ad LW.ofInt
  simp only [val_cast, hh_cast]
  split_ifs <;> push_cast <;> rfl

omit scl in
theorem Cast.site_cast (A q rh : ℤ) (k : ℕ) :
    site (A : R) (q : R) (rh : R) k = ((site A q rh k : ℤ) : R) := by
  unfold site
  push_cast
  ring

/-- The keys commute with the map from the integers to a ring. -/
theorem key_cast (s : Fam) (l x i : ℕ) :
    key D (castT t : Cell → R) tb L0 (fun l => LW.ofInt R (w l)) s l x i =
      ((key D t tb L0 (fun l => LW.ofInt ℤ (w l)) s l x i : ℤ) : R) := by
  cases s <;>
    simp only [key, site, high, Site.ssite_eq, Site.shigh_eq, val_cast, xS_cast, gw_cast, lw_cast,
        mr_cast, led_cast, Cast.ledR_cast', Ag_cast, Au_cast, Ad_cast, Av_cast, Y'_cast] <;>
    (try simp only [LW.ofInt, Int.cast_id]) <;>
    push_cast <;>
    first | rfl | ring

/-- The identities commute with the map from the integers to a ring. -/
theorem idn_cast (emb : Mat) (tok : ℕ → ℕ) (j : Idn) :
    idnVal D (castT t : Cell → R) (fun a b => ((emb a b : ℤ) : R)) tok j =
      ((idnVal D t emb tok j : ℤ) : R) := by
  cases j with
  | jn k ν i =>
    have h := Ledger.map_idn (Int.castRingHom R) (led t ν i) (npOf D ν)
      (Ledger.Wsum D.d fun l j => bS D t ν l j i) k
    simp only [eq_intCast] at h
    show Ledger.idn (npOf D ν) (Ledger.Wsum D.d fun l j => bS D (castT t : Cell → R) ν l j i)
        (led (castT t : Cell → R) ν i) k =
      ((Ledger.idn (npOf D ν) (Ledger.Wsum D.d fun l j => bS D t ν l j i) (led t ν i) k : ℤ) : R)
    rw [h, led_cast]
    congr 1
    funext s
    have h2 := Ledger.map_Wsum (Int.castRingHom R) D.d (fun l j => bS D t ν l j i) s
    simp only [eq_intCast] at h2
    rw [h2]
    rfl
  | j10 l' i =>
    unfold idnVal
    simp only [val_cast]
    push_cast
    rfl
  | j11 j i =>
    unfold idnVal
    simp only [xS_cast]
    push_cast
    rfl

end Cast

/-! ## Reading the weights from W -/

section Layers
variable {R : Type} [CommRing R] (P : Params) (k : ℕ) (W : Mat)

omit scl in
theorem Cast.entryR_cast (n : ℕ) (U : Layout.UnitS) (i : List ℕ) :
    entryR P k (fun y c => ((W y c : ℤ) : R)) n U i = ((Layout.rd P k W n U i : ℤ) : R) := by
  unfold entryR Layout.rd Layout.entry
  push_cast
  rfl

omit scl in
theorem Cast.matR_cast (r c : ℕ) (f : ℕ → ℕ → ℤ) :
    matR r c (fun j x => ((f j x : ℤ) : R)) = fun j x => ((Layout.mat r c f j x : ℤ) : R) := by
  funext j x
  unfold matR Layout.mat
  split_ifs <;> simp

omit scl in
/-- Reading a layer's weights from W commutes with the map from the integers to a ring. -/
theorem Cast.layerCast' (L : ℕ) :
    layerR P k (fun y c => ((W y c : ℤ) : R)) L = LW.ofInt R (Layout.layerOf P k W L) := by
  unfold layerR LW.ofInt Layout.layerOf
  simp only [Cast.entryR_cast, Cast.matR_cast, LW.mk.injEq]
  refine ⟨trivial, trivial, trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (funext j x; split_ifs <;> simp)

omit scl in
theorem embCast :
    embR P k (fun y c => ((W y c : ℤ) : R)) =
      fun a b => (((Layout.weightsOf P k W).Emb a b : ℤ) : R) := by
  unfold embR Layout.weightsOf
  simp only [Cast.entryR_cast, Cast.matR_cast]

end Layers


/-! ## The relation on all names -/

/-- The field relation of the segment for a function on all names of cells, with the weights and the
embedding as integers: (1) every valid cell is below 2^18 in absolute value, (2) every key is an
entry of its table, (3) the identities hold; keys and identities are formed in F. -/
def RFraw (D : Dim) (tb : Tables) (L0 : ℕ) (first : Bool) (F : Type) [CommRing F] (w : ℕ → LayerW)
    (emb : Mat) (tok : ℕ → ℕ) (t : Cell → ℤ) : Prop :=
  (∀ c : Cell, c.Valid D → |t c| < 2 ^ 18) ∧
  (∀ q : KeyName D,
    key D (castT t : Cell → F) tb L0 (fun l => LW.ofInt F (w l))
        q.val.1 q.val.2.1 q.val.2.2.1 q.val.2.2.2 ∈
      lutSet (lut tb (call q.val.1))) ∧
  ∀ j : Idn,
    j.Valid D first → idnVal D (castT t : Cell → F) (fun a b => ((emb a b : ℤ) : F)) tok j = 0

section Raw
variable (D : Dim) (tb : Tables) (L0 : ℕ) (first : Bool)

omit scl in
theorem rd_cast {R : Type} [CommRing R] (s : {c : Cell // c.Valid D} → ℤ) :
    (rd D s : Cell → R) = castT (rd D s : Cell → ℤ) := by
  funext n
  show (if h : n.Valid D then ((s ⟨n, h⟩ : ℤ) : R) else 0) =
    (((if h : n.Valid D then ((s ⟨n, h⟩ : ℤ) : ℤ) else 0 : ℤ) : ℤ) : R)
  by_cases h : n.Valid D
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h, Int.cast_zero]

/-- For an integer matrix W mapped into F, the relation of `trace`, on functions on the valid names,
is equivalent to `RFraw` at the weights and the embedding read from W. -/
theorem rf_iff (kW : ℕ) (F : Type) [CommRing F] (tok : ℕ → ℕ)
    (W : Mat) (s : {c : Cell // c.Valid D} → ℤ) :
    (trace D tb kW L0 first F).RF tok (fun y c => ((W y c : ℤ) : F)) s ↔
    RFraw D tb L0 first F (fun l => Layout.layerOf D.P kW W (L0 + l))
      (Layout.weightsOf D.P kW W).Emb tok (rd D s) := by
  have hrd : ∀ c : {c : Cell // c.Valid D}, (rd D s : Cell → ℤ) c.val = s c := fun c => by
    unfold rd
    rw [dif_pos c.2]
    exact Int.cast_id
  have hk : ∀ q : KeyName D, (trace D tb kW L0 first F).key tok (fun y c => ((W y c : ℤ) : F)) s q =
      key D (castT (rd D s : Cell → ℤ) : Cell → F) tb L0
        (fun l => LW.ofInt F (Layout.layerOf D.P kW W (L0 + l)))
        q.val.1 q.val.2.1 q.val.2.2.1 q.val.2.2.2 := fun q => by
    show key D (rd D s) tb L0
        (fun l => layerR D.P kW (fun y c => ((W y c : ℤ) : F)) (L0 + l)) _ _ _ _ = _
    simp only [Cast.layerCast']
    rw [rd_cast]
  have hj : ∀ j : {j : Idn // j.Valid D first},
      (trace D tb kW L0 first F).idn tok (fun y c => ((W y c : ℤ) : F)) s j =
        idnVal D (castT (rd D s : Cell → ℤ) : Cell → F)
          (fun a b => (((Layout.weightsOf D.P kW W).Emb a b : ℤ) : F)) tok j.val := fun j => by
    show idnVal D (rd D s) (embR D.P kW fun y c => ((W y c : ℤ) : F)) tok j.val = _
    rw [embCast, rd_cast]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun c hc => ?_, fun q => ?_, fun j hj' => ?_⟩
    · rw [hrd ⟨c, hc⟩]
      exact h1 ⟨c, hc⟩
    · rw [← hk q]
      exact h2 q
    · rw [← hj ⟨j, hj'⟩]
      exact h3 ⟨j, hj'⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun c => ?_, fun q => ?_, fun j => ?_⟩
    · rw [← hrd c]
      exact h1 c.val c.2
    · show (trace D tb kW L0 first F).key tok _ s q ∈ lutSet (lut tb (call q.val.1))
      rw [hk q]
      exact h2 q
    · rw [hj j]
      exact h3 j.val j.2

variable (w : ℕ → LayerW) (emb : Mat) (tok : ℕ → ℕ) (t : Cell → ℤ)

/-- The relation over the integers gives the relation over every commutative ring. -/
theorem rfraw_of_int (F : Type) [CommRing F] (h : RFraw D tb L0 first ℤ w emb tok t) :
    RFraw D tb L0 first F w emb tok t := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun q => ?_, fun j hj => ?_⟩
  · obtain ⟨ι, hι, he⟩ := h2 q
    rw [castT_int] at he
    refine ⟨ι, hι, ?_⟩
    rw [key_cast, he]
    simp
  · have h3' := h3 j hj
    rw [castT_int] at h3'
    have h4 : idnVal D t emb tok j = 0 := h3'
    rw [idn_cast, h4, Int.cast_zero]

/-- Under `RFraw` over `ZMod p`, every integer key of the relation is congruent modulo p to an entry
of its table. -/
theorem key_inLut (p : ℕ) (h : RFraw D tb L0 first (ZMod p) w emb tok t) {s : Fam} {l x i : ℕ}
    (hl : l < D.nl) (hs : present s l = true) (hx : x < len D s) (hi : i < D.T) :
    TableKeys.InLut (p : ℤ) (lut tb (call s))
      (key D t tb L0 (fun l => LW.ofInt ℤ (w l)) s l x i) := by
  obtain ⟨ι, hι, he⟩ := h.2.1 ⟨(s, l, x, i), hl, hs, hx, hi⟩
  rw [key_cast] at he
  exact (TableKeys.inLut_iff_cast (ZMod p) p _ _).2 ⟨ι, hι, he⟩

/-- Under `RFraw` over `ZMod p`, every valid integer identity is congruent to 0 modulo p. -/
theorem idn_modEq (p : ℕ) (h : RFraw D tb L0 first (ZMod p) w emb tok t)
    {j : Idn} (hj : j.Valid D first) :
    idnVal D t emb tok j ≡ 0 [ZMOD (p : ℤ)] := by
  have he := h.2.2 j hj
  rw [idn_cast, CharP.intCast_eq_zero_iff (ZMod p) p] at he
  exact Int.modEq_zero_iff_dvd.2 he

end Raw

end Inst.Model.FFSeg
