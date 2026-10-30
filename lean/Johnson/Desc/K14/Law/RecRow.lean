-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/RecRow.lean: "(rec_gamma)" in the form of the rule of composition WITH ITS OWN
CLAIM IN FRONT, so that the law tells the block that lays the constraints from an idle one; and the
tooth: at a small instance a block that hands its record on unturned does NOT have that law.

The quiet law (rec_goodIn3, rec_goodIn3') carries what every border holds back through the block; a
block that does nothing has it too. What "(rec_gamma)" is for: since its constraints lie on G_u, a
witness of whose words all constraints on G_u hold at the test meets (rec_gamma)'s equation at every
seed of the record.
  RecAll          (rec_gamma)'s equation at every seed of the record.
  rec_goodInR     in front: Base, a claim Q that goes back, AND RecAll; behind: Base and Q.
  PlacedU.grows, on4_tiny   the promise holds at the small instance.
  idlePiece, idle_out       a block without a round that hands its record on, at a stretch without a
                  round; it says yes at every statement.
  idle_lacks_rec  **the tooth**: the idle block does not have the law of rec_goodInR.
  idle_lacks      the like for any promise behind that fails of a statement at which the promise in
                  front holds: so the idle block lacks the joinings' law (On6 | On7) wherever On6
                  holds and On7 does not.

What is not claimed. No statement with On6 and without On7 is shown: the joinings' tooth is under
that premise. The premises of the quiet law stay; «the pin goes back» is asked UNDER THE PROMISE IN
FRONT OF THE BLOCK ALONE, not of every statement. The small
instance is no instance of a release. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.Tiles
import Johnson.Desc.K14.Law.RecSound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows Block noDigest roundlessBlock)
open VerifiableInference.Desc.Sound (Frame Piece EachGoodIn goodIn_of_sure)
open _root_.Run.PQ (CK)

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)

/-- (rec_gamma)'s equation at every seed of the record. -/
def RecAll (p : Par) (d : St) (m : Words K) : Prop :=
  ∀ x ∈ d.loc.key.seeds.zipIdx, RecAt ρ p d m x

variable {W : Type} {C : CK} {F : Frame} (rw : W → Words K) (Pin : St × F.E.Str → W → Prop)

/-- **"(rec_gamma)" with its own claim in front.** -/
theorem rec_goodInR (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (pc : Piece C F St Unit W)
    (hpc : pc.b = b3) (hext : ∀ a τ w, pc.ext a τ w = w) (Prm : St × F.E.Str → Prop)
    (hback : ∀ a τ b w, On4 P.par a → Prm a → pc.ior.red.out a τ = some b → Pin b w → Pin a w)
    (Q : St × F.E.Str → Words K → Prop)
    (hQ : ∀ (a : St × F.E.Str) τ (b : St × F.E.Str) m, b.2 = pc.ior.imp a.2 τ → Onward a.1 b.1 →
      b.1.loc = a.1.loc → Q b m → Q a m) :
    pc.GoodIn (fun a => On4 P.par a ∧ Prm a) (On4 P.par)
      (fun a w => (Base ρ rw Pin a w ∧ Q a (rw w)) ∧ RecAll ρ P.par a.1 (rw w))
      (fun a w => Base ρ rw Pin a w ∧ Q a (rw w)) := by
  refine goodIn_of_sure pc _ _ _ _ fun a τ b ha' hout => ?_
  obtain ⟨ha, hprm⟩ := ha'
  obtain ⟨hy, gs, hd⟩ := piece_yes pc a τ b hout
  have k3 := (quiet_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl).1 _ _ gs _ (hpc ▸ hd)
  obtain ⟨o, l⟩ := onward_laysRec P.par a.1 b.1 _ k3
  refine ⟨ha.onward o l, fun w hw => ?_⟩
  obtain ⟨⟨hpin, hU, hO⟩, hq⟩ := hw
  rw [hext]
  refine ⟨⟨⟨hback a τ b w ha hprm hout hpin, ?_, ?_⟩, hQ a τ b _ hy o l hq⟩, ?_⟩
  · rw [← l]; exact hU.back ρ o
  · rw [← l]; exact hO.back ρ o
  · obtain ⟨e, re, se⟩ := hU
    rw [l] at re se
    exact recSound ρ P.par a.1 b.1 e _ (rw w) k3 re se ha.1 (ha.2 e.st (o.grows.trans re.grows))

/-! ## The tooth -/

/-- A statement that grows keeps o_u's table. -/
theorem PlacedU.grows {T T' : Statement} {S : FoldeqShape} {u : FoldedRow} (h : PlacedU T S u)
    (x : Oracle) (hx : T.oracles[u.oracle]? = some x) (h0 : x.shape.mainRows ≠ 0)
    (g : Grows T T') : PlacedU T' S u := by
  obtain ⟨x', hx', gx⟩ := g.2.2 _ x hx
  have t := tableBits_main T _ x hx h0 false
  have t' := tableBits_main T' _ x' hx' (by rw [gx.1]; exact h0) false
  refine ⟨t'.1, ?_, h.room, h.roomTail, h.aligned⟩
  rw [t'.2, gx.1, g.1, ← t.2]
  exact h.bits

/-- The promise holds at the small instance, whatever the oracles are. -/
theorem on4_tiny (y : F.E.Str) : On4 tinyRP ((tinyRD, y) : St × F.E.Str) :=
  ⟨tinyR_ok, fun _ g => tinyR_placed.grows { shape := { code := 1, mainRows := 1 } } rfl
    (by decide) g⟩

/-- A block without a round that hands its record on, at a stretch without a round. -/
def idlePiece (C : CK) (F : Frame) (W : Type) (base : Nat) : Piece C F St Unit W :=
  ⟨roundlessBlock "idle" 2 none 3 .ok, base, [], [], fun _ _ w => w, ()⟩

/-- It says yes at every statement and hands the record on. -/
theorem idle_out (base : Nat) (s : St) (y : F.E.Str) :
    (idlePiece C F W base).ior.red.out (s, y) () =
      some (s, (idlePiece C F W base).ior.imp y ()) := rfl

/-- The idle block lacks every law whose promise behind fails of a record at which the promise in
front holds. -/
theorem idle_lacks (base : Nat) (on on' : St × F.E.Str → Prop) (R R' : St × F.E.Str → W → Prop)
    (s : St) (y : F.E.Str) (h : on (s, y))
    (h' : ¬ on' (s, (idlePiece C F W base).ior.imp y ())) :
    ¬ (idlePiece C F W base).GoodIn on on' R R' :=
  fun g => h' ((g (s, y) h) _ (idle_out base s y)).1

/-- **The tooth**: the idle block does not have the law of "(rec_gamma)" with its claim in front. -/
theorem idle_lacks_rec (base : Nat) (y : F.E.Str) :
    ¬ (idlePiece C F Unit base).GoodIn (On4 tinyRP) (On4 tinyRP)
      (fun a w => (Base ρ (fun _ _ _ _ => 0) (fun _ _ => True) a w ∧ True) ∧
        RecAll ρ tinyRP a.1 (fun _ _ _ => 0))
      (fun a w => Base ρ (fun _ _ _ _ => 0) (fun _ _ => True) a w ∧ True) := by
  intro g
  have hH : ∀ gi, HoldsAt ρ tinyRD gi (fun _ _ _ => (0 : K)) := fun gi =>
    ⟨tinyRD, Reaches.refl _ _, fun r hr => by simp [rowsOn, tinyRD, tinyRT] at hr⟩
  have h := ((g (tinyRD, y) (on4_tiny y)) _ (idle_out base tinyRD y)).2 ()
    ⟨⟨trivial, hH _, hH _⟩, trivial⟩
  exact tinyR_never ρ (h.2 _ (by simp [tinyRD]))

end Desc.K14.Law
