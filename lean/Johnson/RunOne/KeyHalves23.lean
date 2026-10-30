-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyHalves23.lean: THE SHARED CHAIN's THREE ROWS OF K14 THAT DRAW (2.1 «LIN point» · 2.4 «LOC» · 2.7 «LIN zeta»): THE JOINING OF THE TWO HALVES INTO THE TABLES' Keeps, BESIDE keeps₂_of_row (KeyWrap23.lean:85), which serves the rows without a draw. THE PROMISE's FORWARD HALF: for certain, at one y · THE CHANCE's HALF: at the piece's own errors · THE JOINING: here.
OBJECT: Keeps (on₂ … k) (on₂ … (k + 1)) (L₂ … k) (L₂ … (k + 1)) pc.err · USER: keepsAt_of_law₂ at the fields r2_1 | r2_4 | r2_7 · LETTERS: all the tables'; pc; k; Ch.
  keeps₂_of_halves    PROVED: with a letter Ch (z' : P₂ × St₂) (y : Strs): WHAT OF THE PROMISE BEHIND CHANCE PAYS: it stands in the chance's half's conclusion AT THE STRINGS BEHIND and in the forward half's premises AT THE STRINGS IN FRONT; hCh: it reads the stored table's cells alone
  keeps₂_of_halves'   PROVED: Ch := True: 2.4 | 2.7's form
  (2.1 goes by keeps₂_of_halves'.)
Nothing on soundness.
-/
import Johnson.RunOne.KeyWrap23

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain VerifiableInference.Desc.Sound

section
variable {XI Cells M Smp Rec Cl W : Type} {C : CK} (F : FileDescription XI) (Fr₂ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (S : LinShape) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)

/-- **THE JOINING OF THE TWO HALVES.** -/
theorem keeps₂_of_halves (pc : Piece C Fr₂ (P₂ × St₂) Cl W) (k : Nat) (hbase : ∀ j ∈ pinned (open₂ k), (at_ j).1 < pc.base)
    (hpin : ∀ j ∈ pinned (open₂ (k + 1)), j ∈ pinned (open₂ k)) (hc : CellOnly coll)
    (Ch : P₂ × St₂ → Strs → Prop) (hCh : ∀ z, CellOnly fun y (_ : Unit) => Ch z y)
    (fwd : ∀ z rs gs z' y, roundsFit pc.b.rounds rs = true → pc.b.decide z (rs.map noDigest) gs = .ok z' →
      onAt F G₂ at_ (meaning₂ S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a k d)) (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ k) (open₂ k) z y →
      Ch z' y →
      onAt F G₂ at_ (meaning₂ S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a (k + 1) d)) (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ (k + 1)) (open₂ (k + 1)) z' y)
    (chance : pc.ior.red.Leads (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ k)
      (fun x x' => Ch x'.1 (strsOf Fr₂ x'.2) ∧ (L₂ F Fr₂ G₂ at_ S K₁ R enc rad (k + 1) x' → L₂ F Fr₂ G₂ at_ S K₁ R enc rad k x)) pc.err) :
    pc.ior.red.Keeps (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ k) (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ (k + 1))
      (L₂ F Fr₂ G₂ at_ S K₁ R enc rad k) (L₂ F Fr₂ G₂ at_ S K₁ R enc rad (k + 1)) pc.err := by
  unfold Reduction.Keeps
  refine Reduction.Leads.conseq chance (fun _ h => h) fun x τ x' hx hb hQ => ⟨?_, hQ.2⟩
  have hd := piece_decides_at pc x τ x' hb
  have hf := (piece_fits_at pc x τ x' hb).1
  have Hy0 := strsStay_of_out F Fr₂ at_ pc (open₂ k) hbase x x' τ hb
  have Hy := strsStay_sub F at_ Hy0 hpin
  have hch : Ch x'.1 (strsOf Fr₂ x.2) := ((hCh x'.1) (strsOf Fr₂ x.2) (strsOf Fr₂ x'.2) () Hy0.cell).1 hQ.1
  have r1 := fwd x.1 _ _ x'.1 (strsOf Fr₂ x.2) hf hd hx hch
  exact onAt_strs F G₂ at_ _ _ _ _ x'.1 _ _ Hy (free₂_strs F G₂ at_ S K₁ R coll last₁ off₂ (k + 1) hc x'.1 _ _ Hy) r1

/-- **2.4 | 2.7's form**: chance pays nothing of the promise. -/
theorem keeps₂_of_halves' (pc : Piece C Fr₂ (P₂ × St₂) Cl W) (k : Nat) (hbase : ∀ j ∈ pinned (open₂ k), (at_ j).1 < pc.base)
    (hpin : ∀ j ∈ pinned (open₂ (k + 1)), j ∈ pinned (open₂ k)) (hc : CellOnly coll)
    (fwd : ∀ z rs gs z' y, roundsFit pc.b.rounds rs = true → pc.b.decide z (rs.map noDigest) gs = .ok z' →
      onAt F G₂ at_ (meaning₂ S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a k d)) (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ k) (open₂ k) z y →
      onAt F G₂ at_ (meaning₂ S K₁ R enc rad) (fun d => LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a (k + 1) d)) (Free₂ F G₂ at_ S K₁ R coll last₁ off₂ (k + 1)) (open₂ (k + 1)) z' y)
    (chance : pc.ior.red.Leads (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ k)
      (fun x x' => L₂ F Fr₂ G₂ at_ S K₁ R enc rad (k + 1) x' → L₂ F Fr₂ G₂ at_ S K₁ R enc rad k x) pc.err) :
    pc.ior.red.Keeps (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ k) (on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ (k + 1))
      (L₂ F Fr₂ G₂ at_ S K₁ R enc rad k) (L₂ F Fr₂ G₂ at_ S K₁ R enc rad (k + 1)) pc.err :=
  keeps₂_of_halves F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ pc k hbase hpin hc (fun _ _ => True) (fun _ _ _ _ _ => Iff.rfl)
    (fun z rs gs z' y h1 h2 h3 _ => fwd z rs gs z' y h1 h2 h3)
    (Reduction.Leads.conseq chance (fun _ h => h) fun _ _ _ _ _ h => ⟨trivial, h⟩)

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.keeps₂_of_halves
#print axioms Johnson.RunOne.KeyRows23.keeps₂_of_halves'
