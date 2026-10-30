-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyWrap23.lean. THE KEY FILE, CHAINS 2 | 3: THE WRAP: FROM A ROW «AT ONE y ON BOTH SIDES» (the form in which a kind's files type a row over these tables: after a text of ours, not in this repository) TO Keeps AT A PIECE. GENERAL IN THE BLOCK AND IN THE BORDER k: for a row that opens NO NEW PIN (no sending).
  claim₂_cell              PROVED: a claim of the shared chain reads of the strings the stored cells alone
  rides₂ | (rides₃: KeyKeeps23.lean)    PROVED: at one record every item rides back along the strings: GENERAL IN THE LIST O
  free₂_strs | free₃_strs  PROVED: the promise's last letter rides forward along the strings (coll reads the cells alone)
  onAt_strs                PROVED: so does the promise, where its last letter does
  keeps₂_of_row | keeps₃_of_row   PROVED: **THE WRAP**: a piece pc whose base lies behind every open pin's tree; no new pin behind; and THE ROW: «∀ a rs gs b y, roundsFit … → pc.b.decide a (rs.map noDigest) gs = .ok b → on k at (a, y) → on (k + 1) at (b, y) ∧ ∀ w, rel (k + 1) at (b, y) w → rel k at (a, y) w»
                           ⟹ pc.ior.red.Keeps (on k) (on (k + 1)) (L k) (L (k + 1)) pc.err. THE ROW MAY SPEND roundsFit (PieceFits.lean).
WHAT IS LEFT AT A SEAT: that pc.b is held ‹the kind's block› (held_decide: KeyKeeps23 | PaidKeeps) and that the kind's block's yes gives the kind's plain facts (Laid | Joined | SplitLaid …) OVER THE SEATED TEXT; hbase (public: the piece's base).
Nothing on soundness.
-/
import Johnson.RunOne.KeyKeeps23
import Johnson.Desc.Plain.PieceFits

set_option autoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain VerifiableInference.Desc.Sound

section
variable {XI Cells M Smp Rec Cl W : Type} {C : CK} (F : FileDescription XI) (Fr₂ Fr₃ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (G₃ : Reading (P₃ × St₃) Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat) (idx : List Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (src : St₃ → Bool) (off₂ off₃ : Nat → Nat) (t₁ : Nat)

/-- A claim of the shared chain reads of the strings the stored cells alone. -/
theorem claim₂_cell (c : Nat) (n : String) (z : P₂ × St₂) (y y' : Strs) (w : Wit Cells Unit M) (h : y'.cell = y.cell)
    (hu : (meaning₂ S K₁ R enc rad).claim c n z y' w) : (meaning₂ S K₁ R enc rad).claim c n z y w := by
  simp only [meaning₂, claim₂, NearUAt] at hu ⊢
  rw [h] at hu
  exact hu

/-- **At one record every item of the shared chain rides back along the strings.** -/
theorem rides₂ (O : List KItem) (i : KItem) (hi : i ∈ O) (z : P₂ × St₂) (y y' : Strs) (w : Wit Cells Unit M) (Hy : StrsStay F at_ O y y')
    (hu : i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) z y' w) : i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) z y w := by
  cases i with
  | pinT => exact rides_pinT2 G₂ z z y y' w ⟨fun _ _ => rfl, rfl⟩ Hy.cell hu
  | pin k => exact rides_pin2 F G₂ _ _ z z y y' w ⟨fun _ _ => rfl, rfl⟩ (Hy.word k (mem_pinned O k hi)) hu
  | claim c n => exact claim₂_cell S K₁ R enc rad c n z y y' w Hy.cell hu
  | _ => exact hu

theorem free₂_strs (k : Nat) (hc : CellOnly coll) (z : P₂ × St₂) (y y' : Strs) (Hy : StrsStay F at_ (open₂ k) y y')
    (hf : Free₂ F G₂ at_ S K₁ R coll last₁ off₂ k z y) : Free₂ F G₂ at_ S K₁ R coll last₁ off₂ k z y' :=
  { hf with
    record := freeAt_rides coll G₂ hc z y y' Hy.cell hf.record
    shown := fun j hj => shownAt_ride F at_ j y y' (Hy.word j hj) (hf.shown j hj) }

theorem free₃_strs (k : Nat) (hc : CellOnly coll) (z : P₃ × St₃) (y y' : Strs) (Hy : StrsStay F at_ (open₃ k) y y')
    (hf : Free₃ F G₃ at_ S K₁ R coll off₂ off₃ k z y) : Free₃ F G₃ at_ S K₁ R coll off₂ off₃ k z y' :=
  { hf with
    record := freeAt_rides coll G₃ hc z y y' Hy.cell hf.record
    shown := fun j hj => shownAt_ride F at_ j y y' (Hy.word j hj) (hf.shown j hj) }

end

section
variable {XI P St Cells M Smp Rec : Type} (F : FileDescription XI) (G : Reading (P × St) Cells M Smp Rec) (at_ : Where) (Mg : KMeaning P St (Wit Cells Unit M))

/-- **The promise rides forward along the strings**, where its last letter does. -/
theorem onAt_strs (shape : St → Bool) (free : P × St → Strs → Prop) (O : List KItem) (z : P × St) (y y' : Strs) (Hy : StrsStay F at_ O y y')
    (hfree : free z y → free z y') (h : onAt F G at_ Mg shape free O z y) : onAt F G at_ Mg shape free O z y' := by
  rcases h with hn | ⟨h1, h2, h3, h4⟩
  · exact Or.inl hn
  · refine Or.inr ⟨h1, h2, hfree h3, fun k hk o s ho hs m m' hm hm' => ?_⟩
    exact h4 k hk o s ho hs m m' ((member_congr F G o _ _ y y' s m (Hy.word k hk)).1 hm) ((member_congr F G o _ _ y y' s m' (Hy.word k hk)).1 hm')

theorem strsStay_sub {O O' : List KItem} {y y' : Strs} (h : StrsStay F at_ O y y') (hs : ∀ k ∈ pinned O', k ∈ pinned O) : StrsStay F at_ O' y y' :=
  ⟨h.cell, fun k hk => h.word k (hs k hk)⟩

end

section
variable {XI Cells M Smp Rec Cl W : Type} {C : CK} (F : FileDescription XI) (Fr₂ Fr₃ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (G₃ : Reading (P₃ × St₃) Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat) (idx : List Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (src : St₃ → Bool) (off₂ off₃ : Nat → Nat) (t₁ : Nat)

/-- **THE WRAP, the shared chain.** -/
theorem keeps₂_of_row (pc : Piece C Fr₂ (P₂ × St₂) Cl W) (k : Nat) (hbase : ∀ j ∈ pinned (open₂ k), (at_ j).1 < pc.base)
    (hpin : ∀ j ∈ pinned (open₂ (k + 1)), j ∈ pinned (open₂ k)) (hc : CellOnly coll)
    (row : ∀ z rs gs z' y, roundsFit pc.b.rounds rs = true → pc.b.decide z (rs.map noDigest) gs = .ok z' →
      onAt F G₂ at_ (meaning₂ S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a k d)) (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ k) (open₂ k) z y →
      onAt F G₂ at_ (meaning₂ S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a (k + 1) d)) (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ (k + 1)) (open₂ (k + 1)) z' y ∧
        ∀ w, relAt F G₂ at_ (meaning₂ S K₁ R enc rad) (open₂ (k + 1)) z' y w → relAt F G₂ at_ (meaning₂ S K₁ R enc rad) (open₂ k) z y w) :
    pc.ior.red.Keeps (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ k) (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ (k + 1))
      (L₂ F Fr₂ G₂ at_ S K₁ R enc rad k) (L₂ F Fr₂ G₂ at_ S K₁ R enc rad (k + 1)) pc.err := by
  unfold Reduction.Keeps
  refine Reduction.Leads.of_sure (K := pc.ior.red) pc.err fun x τ x' hx hb => ?_
  have hd := piece_decides_at pc x τ x' hb
  have hf := (piece_fits_at pc x τ x' hb).1
  have Hy := strsStay_sub F at_ (strsStay_of_out F Fr₂ at_ pc (open₂ k) hbase x x' τ hb) hpin
  obtain ⟨r1, r2⟩ := row x.1 _ _ x'.1 (strsOf Fr₂ x.2) hf hd hx
  refine ⟨onAt_strs F G₂ at_ _ _ _ _ x'.1 _ _ Hy (free₂_strs F G₂ at_ S K₁ R coll last₁ off₂ (k + 1) hc x'.1 _ _ Hy) r1, fun ⟨w, hw⟩ => ⟨w, r2 w fun i hi => ?_⟩⟩
  exact rides₂ F G₂ at_ S K₁ R enc rad (open₂ (k + 1)) i hi x'.1 _ _ w Hy (hw i hi)

/-- **THE WRAP, the last chain.** -/
theorem keeps₃_of_row (pc : Piece C Fr₃ (P₃ × St₃) Cl W) (k : Nat) (hbase : ∀ j ∈ pinned (open₃ k), (at_ j).1 < pc.base)
    (hpin : ∀ j ∈ pinned (open₃ (k + 1)), j ∈ pinned (open₃ k)) (hT : KItem.pinT ∉ open₃ (k + 1)) (hc : CellOnly coll)
    (row : ∀ z rs gs z' y, roundsFit pc.b.rounds rs = true → pc.b.decide z (rs.map noDigest) gs = .ok z' →
      onAt F G₃ at_ (meaning₃ S K₁ R) (shapeB₃ S K₁ a idx src t₁ k) (Free₃ F G₃ at_ S K₁ R coll off₂ off₃ k) (open₃ k) z y →
      onAt F G₃ at_ (meaning₃ S K₁ R) (shapeB₃ S K₁ a idx src t₁ (k + 1)) (Free₃ F G₃ at_ S K₁ R coll off₂ off₃ (k + 1)) (open₃ (k + 1)) z' y ∧
        ∀ w, relAt F G₃ at_ (meaning₃ S K₁ R) (open₃ (k + 1)) z' y w → relAt F G₃ at_ (meaning₃ S K₁ R) (open₃ k) z y w) :
    pc.ior.red.Keeps (on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ k) (on₃ F Fr₃ G₃ at_ S K₁ R a idx coll src off₂ off₃ t₁ (k + 1))
      (L₃ F Fr₃ G₃ at_ S K₁ R k) (L₃ F Fr₃ G₃ at_ S K₁ R (k + 1)) pc.err := by
  unfold Reduction.Keeps
  refine Reduction.Leads.of_sure (K := pc.ior.red) pc.err fun x τ x' hx hb => ?_
  have hd := piece_decides_at pc x τ x' hb
  have hf := (piece_fits_at pc x τ x' hb).1
  have Hy := strsStay_sub F at_ (strsStay_of_out F Fr₃ at_ pc (open₃ k) hbase x x' τ hb) hpin
  obtain ⟨r1, r2⟩ := row x.1 _ _ x'.1 (strsOf Fr₃ x.2) hf hd hx
  refine ⟨onAt_strs F G₃ at_ _ _ _ _ x'.1 _ _ Hy (free₃_strs F G₃ at_ S K₁ R coll off₂ off₃ (k + 1) hc x'.1 _ _ Hy) r1, fun ⟨w, hw⟩ => ⟨w, r2 w fun i hi => ?_⟩⟩
  exact rides₃ F G₃ at_ S K₁ R (open₃ (k + 1)) hT i hi x'.1 _ _ w Hy (hw i hi)

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.rides₂
#print axioms Johnson.RunOne.KeyRows23.onAt_strs
#print axioms Johnson.RunOne.KeyRows23.keeps₂_of_row
#print axioms Johnson.RunOne.KeyRows23.keeps₃_of_row
