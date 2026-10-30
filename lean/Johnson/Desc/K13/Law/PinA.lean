-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/PinA.lean: kind K13's laws with a pin that reads the whole statement, the
record and the oracles. Statements with their proofs.

In Johnson/Desc/K13/Law/Good2.lean and Johnson/Desc/K13/Law/AtM4.lean the pin reads the oracles
alone. Where several messages lie near one word, the oracles alone fix no message: what fixes it is
a sample, and the sample's rows lie in the record. So here the pin is a relation between a statement
and a witness; that it fixes what the rows read is asked under the condition in front; that it goes
back is asked at a yes. The laws with the narrower pin are instances.
Main names:
  `RowsHoldA rw Pin`, `BehindA P rwM rwW Pin`: as `RowsHold` and `Behind`, the pin at the statement.
  `goodIn_keep`: a promise that every yes keeps may stand on both sides. General in the piece.
  `atM3_goodInA`: the law of the batching's joined block.
  `rowsB_coreA`, `atM4_goodInA`, `commit_goodInA`: the same at the place of W's commitment.
  `jointA`: the two pieces in a row.
Used of `verify-on-bytes`: nothing beside what the files named above name.

What is not claimed. That a pin of the protocol meets the three premises (it fixes the matrix and
the ledger's mask entries under the condition in front; it goes back at a yes of each of the three
blocks). `Declared` is a test on a plan's written rounds: an evaluation at two stored sets' public
files, a small and a full-size one, said yes, and five controls said no; no theorem says it of a
plan. `WIs` is given by no law yet. The number nR of the matrix's rows is a free letter. A pin that
holds of nobody meets the premises, and the laws are idle at it.

-/
import Johnson.Desc.K13.Law.Joint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice Iop Run
open OnBytes.Flat OnBytes.Maker
open OnBytes.Means (Words)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece EachGoodIn)

variable {Cl W : Type} {nR : ℕ}

/-- The witness is pinned at the statement, and all rows on the table are true. -/
def RowsHoldA {F : Frame} {k : ℕ} (rw : W → Wit GE nR k) (Pin : S × F.E.Str → W → Prop)
    (a : S × F.E.Str) (w : W) : Prop :=
  Pin a w ∧ ∀ r ∈ a.1.rows, Holds ρg (rw w) r

/-- What stands behind the block behind W's commitment, the pin at the statement. -/
def BehindA {F : Frame} (P : Where) (rwM : W → Fin nR → (Fin P.lin.kCol → Bool) → GE)
    (rwW : W → Words GE) (Pin : S × F.E.Str → W → Prop) (b : S × F.E.Str) (w : W) : Prop :=
  Pin b w ∧ OnBytes.Means.Holds ρg b.1.st (rwW w) ∧
    ∀ l, linAt b.1 = some l →
      WIs (rwM w) (rwW w) l.claim.g l.w (linLayW b.1.st.codes P.lin)

/-- A promise that every yes keeps may stand on both sides. General in the piece. -/
theorem goodIn_keep {T : Type} {C : PQ.CK} {F : Frame} (p : Piece C F T Cl W)
    (on on' Prm : T × F.E.Str → Prop) (R R' : T × F.E.Str → W → Prop)
    (h : p.GoodIn on on' R R')
    (hkeep : ∀ a τ b, p.ior.red.out a τ = some b → Prm a → Prm b) :
    p.GoodIn (fun a => on a ∧ Prm a) (fun b => on' b ∧ Prm b) R R' := by
  intro a ha
  refine Doomed.mono _ _ ?_ (h a ha.1)
  intro τ hτ b hb
  exact ⟨⟨(hτ b hb).1, hkeep a τ b hb ha.2⟩, (hτ b hb).2⟩

/-- **The law of the batching's joined block**, the pin at the statement. k: the number of the
variables' written rounds. -/
theorem atM3_goodInA (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hD : Declared P dZ d0 ds) (k : ℕ) (hk : ds.length = k) (rw : W → Wit GE nR k)
    (Pin : S × F.E.Str → W → Prop) (on : S × F.E.Str → Prop)
    (hdet : ∀ a w w', on a → Pin a w → Pin a w' → AgreeAt a.1.out.indexMasks (rw w) (rw w'))
    (hback : ∀ a τ b w, (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).ior.red.out a τ = some b →
      Pin b w → Pin a w) :
    (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).GoodIn on (FrontOk P)
      (RowsHoldA rw Pin) (RowsHoldA rw Pin) := by
  subst hk
  obtain ⟨nZ, aZ, hZ⟩ := sends_of_entry (d := dZ) (by rw [hD.sigma.1]; rfl)
    (by rw [hD.sigma.1]; rfl) (by rw [hD.sigma.1]; rfl) (by rw [hD.sigma.1]; exact Nat.zero_le 1)
    (by rw [hD.sigma.1]; exact Nat.zero_le 64) hD.sigma.2.1 hD.sigma.2.2
  obtain ⟨n0, a0, h0⟩ := sends_of_entry (d := d0) (by rw [hD.eps.1]; rfl) (by rw [hD.eps.1]; rfl)
    (by rw [hD.eps.1]; rfl) (by rw [hD.eps.1]; exact Nat.zero_le 1)
    (by rw [hD.eps.1]; exact Nat.zero_le 64) hD.eps.2.1 hD.eps.2.2
  have hs : ∀ d ∈ ds, ∃ n a, SendsDraws (toRD d) n 1 0 a := fun d hd => by
    obtain ⟨he, hk⟩ := hD.vars d hd
    exact sends_of_entry (by rw [he]; rfl) (by rw [he]; rfl) (by rw [he]; rfl)
      (by rw [he]; exact Nat.zero_le 1) (by rw [he]; exact Nat.zero_le 64) hk.1 hk.2
  intro a ha
  have h := atM3_goodIn2 (Cl := Cl) F P base dZ d0 ds hD.len hZ h0 hs rw (fun _ w => Pin a w)
    (fun a' => a' = a) (fun a' w w' e h1 h2 => by subst e; exact hdet _ w w' ha h1 h2)
    (fun _ _ _ _ _ h => h) a rfl
  refine Doomed.mono _ _ ?_ h
  intro τ hτ b hb
  obtain ⟨h1, h2⟩ := hτ b hb
  exact ⟨h1, fun w hw =>
    ⟨hback a τ b w hb hw.1, (h2 w ⟨hback a τ b w hb hw.1, hw.2⟩).2⟩⟩

/-- What goes back over the block behind W's commitment, at its own decision. -/
theorem rowsB_coreA {F : Frame} {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (rowsB (Cl := Cl) atS P).decide s rs gs = .ok s')
    (rwM : W → Fin nR → (Fin P.lin.kCol → Bool) → GE) (rwW : W → Words GE)
    (Pin : S × F.E.Str → W → Prop) (y : F.E.Str) (hon : FrontOk P ((s, y) : S × F.E.Str)) (w : W)
    (hp : Pin (s', y) w → Pin (s, y) w) (hw : BehindA P rwM rwW Pin (s', y) w) :
    RowsHoldA (fun w => witOf (rwM w) (rwW w)) Pin (s, y) w :=
  ⟨hp hw.1, (rowsB_core h rwM rwW (fun _ _ => True) y hon w ⟨trivial, hw.2.1, hw.2.2⟩).2⟩

/-- **The law of the joined block at the place of W's commitment**, the pin at the statement. -/
theorem atM4_goodInA {F : Frame} (P : Where) (pcW : Piece (ckP .two) F S Cl W)
    (on : S × F.E.Str → Prop) (R : S × F.E.Str → W → Prop)
    (rwM : W → Fin nR → (Fin P.lin.kCol → Bool) → GE) (rwW : W → Words GE)
    (Pin : S × F.E.Str → W → Prop)
    (hp : ∀ s s' y w, (rowsB (Cl := Cl) atS P).decide s [] [] = .ok s' → Pin (s', y) w →
      Pin (s, y) w)
    (hW : pcW.GoodIn on (FrontOk P) R (RowsHoldA (fun w => witOf (rwM w) (rwW w)) Pin)) :
    (Piece.then pcW "W's commitment, the own group and (Eval)" (rowsB atS P)).GoodIn on
      (fun b => EvalLaid P b.1) R (BehindA P rwM rwW Pin) :=
  goodIn_then pcW _ (rowsB atS P) rfl on (FrontOk P) (fun b => EvalLaid P b.1) R _ _ hW
    fun s s' y hon hd => ⟨rowsB_lays hd y hon,
      fun w hw => rowsB_coreA hd rwM rwW Pin y hon w (hp s s' y w hd) hw⟩

/-- A piece whose block keeps the chain's end has what it owes, the pin at the statement. -/
theorem commit_goodInA {F : Frame} (P : Where) (pcW : Piece (ckP .two) F S Cl W)
    (hext : ∀ a τ w, pcW.ext a τ w = w) (hK : KeepsEnd pcW.b) {k : ℕ} (rw : W → Wit GE nR k)
    (Pin : S × F.E.Str → W → Prop)
    (hback : ∀ a τ b w, pcW.ior.red.out a τ = some b → Pin b w → Pin a w) :
    pcW.GoodIn (FrontOk P) (FrontOk P) (RowsHoldA rw Pin) (RowsHoldA rw Pin) := by
  intro a ha
  refine Doomed.mono _ _ ?_
    (commit_goodIn P pcW hext hK rw (fun _ _ => True) (fun _ _ _ _ _ h => h) a ha)
  intro τ hτ b hb
  obtain ⟨h1, h2⟩ := hτ b hb
  refine ⟨h1, fun w hw => ?_⟩
  have h3 := h2 w ⟨trivial, hw.2⟩
  rw [hext] at h3 ⊢
  exact ⟨hback a τ b w hb hw.1, h3.2⟩

/-- The relations at the three places of the row, the pin at the statement. -/
def jointRA {F : Frame} (P : Where) (rwM : W → Fin nR → (Fin P.lin.kCol → Bool) → GE)
    (rwW : W → Words GE) (Pin : S × F.E.Str → W → Prop) : ℕ → S × F.E.Str → W → Prop
  | 0 | 1 => RowsHoldA (fun w => witOf (rwM w) (rwW w)) Pin
  | _ => BehindA P rwM rwW Pin

/-- The conditions at the three places of the row; on: the condition in front. -/
def jointOnA {F : Frame} (P : Where) (on : S × F.E.Str → Prop) : ℕ → S × F.E.Str → Prop
  | 0 => on
  | 1 => FrontOk P
  | _ => fun b => EvalLaid P b.1

/-- **The two pieces in a row**, the pin at the statement. -/
theorem jointA (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hD : Declared P dZ d0 ds) (rwM : W → Fin nR → (Fin P.lin.kCol → Bool) → GE)
    (rwW : W → Words GE) (Pin : S × F.E.Str → W → Prop) (on : S × F.E.Str → Prop)
    (hdet : ∀ a w w', on a → Pin a w → Pin a w' →
      AgreeAt a.1.out.indexMasks (witOf (rwM w) (rwW w)) (witOf (rwM w') (rwW w')))
    (hback3 : ∀ a τ b w, (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).ior.red.out a τ = some b →
      Pin b w → Pin a w)
    (pcW : Piece (ckP .two) F S Cl W) (hext : ∀ a τ w, pcW.ext a τ w = w) (hK : KeepsEnd pcW.b)
    (hbackW : ∀ a τ b w, pcW.ior.red.out a τ = some b → Pin b w → Pin a w)
    (hbackR : ∀ s s' y w, (rowsB (Cl := Cl) atS P).decide s [] [] = .ok s' → Pin (s', y) w →
      Pin (s, y) w) :
    EachGoodIn (jointOnA P on) (jointRA P rwM rwW Pin) 0
      [pieceM3 F P base dZ d0 ds,
        Piece.then pcW "W's commitment, the own group and (Eval)" (rowsB atS P)] :=
  ⟨atM3_goodInA F P base dZ d0 ds hD P.lin.kCol hD.len.symm _ Pin on hdet hback3,
    atM4_goodInA P pcW (FrontOk P) _ rwM rwW Pin hbackR
      (commit_goodInA P pcW hext hK _ Pin hbackW),
    trivial⟩

end VerifiableInference.Desc.K13.Law
