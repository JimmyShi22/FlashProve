-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRow24At.lean: ROW 2.4 OF THE KEY FILE's TABLE OF JOINTS,
THE CHANCE's HALF (Johnson/RunOne/KeyRow24.lean: loc_back₂), AT A STRETCH OF ONE WRITTEN ROUND: four
of its premises PAID by K14's files' own laws: the carriage (G | fits | hread: posMaps |
posMaps_ok, and pos_reads, which stands in Johnson/Desc/K14/Law/LocReadAt.lean,
cut out of loc_goodIn4's proof) and the columns (hcols: shown_stored).
ON EMPTINESS: as KeyRow24.lean's head: NO MEMBER OF on₂ … 4 IS SHOWN BY ANYBODY: IT MAY BE TRUE
AND EMPTY AT THE REAL PROTOCOL, AND COUNTS AS CLOSING NOTHING.
OBJECT: posAt b base d logN columns e ext: BY rfl it is pieceOf b base [d] [] ⟨ext, the written
errors at e⟩ · USER: keeps₂_of_halves, at the maker's piece number 4 · TWO DEBTS AT THAT CALL,
NOT PAID HERE: (i) Err.le ((posMaps d logN columns).err (e, ())) (rest₂ 4 [d]).err (keeps_same):
IT TIES THE TABLES' LETTER rad TO THE MAKER's CAP: left to K14's files: a number at the key file's
code (K14_rounds at «LOC»; by keeps_same_cap from Err.Below … 2⁻¹²⁸) · (ii) that the maker's stretch
at n = 4 IS [d] with hd | ho (keepsAt_of_law₂ asks the law at EVERY base ds back at which the row
holds the piece): the frame's data (Johnson/Top/Fire/Code/RowCut.lean | others), hd by K14's files'
loc_sendsDraws; where the data are short (ds = []) there is no yes: loc_back₂_empty · LETTERS: as
KeyRow24.lean's; d: the stretch's one round's data; e: the written count.
  loc_back₂_empty   PROVED: at a stretch without a round the block says no: every law of the form «a
    yes gives» holds
  loc_back₂_at   PROVED FROM: hd (the written round draws «columns» positions below 2 ^ logN and no
    element) · ho (it opens no tree) · he (the count) · hl · hbase · hsame · hpins · henc · hA
Nothing on soundness.
-/
import Johnson.RunOne.KeyRow24
import Johnson.Desc.K14.Law.LocReadAt
import Johnson.Desc.Sound.Tiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open _root_.Run (ckP)
open _root_.Iop (Reduction Err)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain
    VerifiableInference.Desc.Sound
open _root_.Desc.Plain (Par)
open _root_.Desc.K14.Law (posAt pos_reads posMaps posMaps_ok shown_stored)

section
variable {XI Cells M Smp Rec Cl W : Type} (F : FileDescription XI) (Fr₂ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where)
  (p : Par) (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)
variable {K : Type} [Field K] (ρ : Model.Reading K)

/-- **ROW 2.4, THE CHANCE's HALF, at a stretch of one written round.** -/
theorem loc_back₂_at (b : Block (P₂ × St₂) Cl) (base : Nat) (d : RDT) {ns : Nat}
    (hd : OnBytes.Slice.SendsDraws (toRD d) ns 0 p.S.fold.columns p.S.fold.index.code.logN) (ho :
        d.opens = [])
    (e : Nat) (he : (2 ^ p.S.fold.index.code.logN - rad - 1) ^ p.S.fold.columns ≤ e)
    (ext : (P₂ × St₂) × Fr₂.E.Str → _root_.Iop.Tr (uLT (ckP .two) [d]) → W → W)
    (hl : ∀ z rs gs z', b.decide z rs gs = .ok z' → z'.1 = z.1 ∧ _root_.Desc.K14.loc p z.2 rs gs =
        some z'.2)
    (hbase : ∀ j ∈ pinned (open₂ 4), (at_ j).1 < base)
    (hsame : ∀ x y, R.same x y ↔ ρ.val x = ρ.val y)
    (hpins : ∀ z z' : P₂ × St₂, z'.1 = z.1 → z'.2.st.oracles = z.2.st.oracles → z'.2.st.codes =
        z.2.st.codes → SamePins G₂ z z')
    (henc : EncIs ρ p.S.fold enc) (hA : p.S.fold.index.code.logN ≤ Fr₂.a) :
    (posAt (F := Fr₂) b base d p.S.fold.index.code.logN p.S.fold.columns e ext).ior.red.Leads
      (on₂ F Fr₂ G₂ at_ p.S K₁ R enc rad a coll last₁ off₂ 4)
      (fun x x' => L₂ F Fr₂ G₂ at_ p.S K₁ R enc rad 5 x' → L₂ F Fr₂ G₂ at_ p.S K₁ R enc rad 4 x)
      (posAt (F := Fr₂) b base d p.S.fold.index.code.logN p.S.fold.columns e ext).err :=
  loc_back₂ F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ ρ
    (posAt (F := Fr₂) b base d p.S.fold.index.code.logN p.S.fold.columns e ext) hl hbase hsame hpins
        henc hA e he
    (fun x τ _ cols _ hg => shown_stored (posAt (F := Fr₂) b base d p.S.fold.index.code.logN
        p.S.fold.columns e ext) d rfl ho x.2 τ _ cols hg)
    (fun _ => (posMaps d p.S.fold.index.code.logN p.S.fold.columns).carry)
    (fun _ => (posMaps d p.S.fold.index.code.logN p.S.fold.columns).fits (posMaps_ok hd) _)
    (pos_reads b base d hd e ext)

/-- **At a stretch without a round there is no yes.** -/
theorem loc_back₂_empty {C : CK} (b : Block (P₂ × St₂) Cl) (base : Nat) (x₀ : Rest C Fr₂ (P₂ × St₂)
    W [])
    (hl : ∀ z rs gs z', b.decide z rs gs = .ok z' → z'.1 = z.1 ∧ _root_.Desc.K14.loc p z.2 rs gs =
        some z'.2)
    (on : (P₂ × St₂) × Fr₂.E.Str → Prop) (Q : (P₂ × St₂) × Fr₂.E.Str → (P₂ × St₂) × Fr₂.E.Str →
        Prop) :
    (pieceOf b base [] [] x₀).ior.red.Leads on Q x₀.err :=
  Reduction.Leads.of_sure (K := (pieceOf b base [] [] x₀).ior.red) x₀.err fun x τ x' _ hb => by
    obtain ⟨_, k4⟩ := hl _ _ _ _ (piece_decides_at (pieceOf b base [] [] x₀) x τ x' hb)
    obtain ⟨r, _, hr, _⟩ := _root_.Desc.K14.Law.loc_one p _ _ _ _ k4
    cases hr

/-- The piece is the maker's form of a piece, by rfl. -/
theorem posAt_is (b : Block (P₂ × St₂) Cl) (base : Nat) (d : RDT) (lg t e : Nat)
    (ext : (P₂ × St₂) × Fr₂.E.Str → _root_.Iop.Tr (uLT (ckP .two) [d]) → W → W) :
    posAt (F := Fr₂) b base d lg t e ext = pieceOf b base [d] [] ⟨ext, (posMaps d lg t).err ((e, ())
        : Nat × Unit)⟩ := rfl

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.loc_back₂_at
#print axioms Johnson.RunOne.KeyRows23.posAt_is
