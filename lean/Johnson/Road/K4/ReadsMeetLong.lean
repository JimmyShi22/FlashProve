-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/ReadsMeetLong.lean: on true reads, the entries of the array of reads that hold a
block of a limb of the stream, or of the tensors s and u, where the verifier can name them, are
worth the library's cells of these names, extended over the block's features and the positions.

Johnson/Road/K4/ReadsMeet.lean says what an entry of a short table is worth. This file does the same
for the long tables that the claims on the squares and on the gated products read. An entry of a
long table holds a block of 2^ls features. Johnson/Road/FormsKeysIdnL.lean (entry_long) has what the
FORM of such an entry is worth; here it is said of the entry itself, readAtW
(Johnson/Road/Rows/LayerTermsPort.lean), at the places that the verifier's claims name.

Main names:
  `long_meet`: an entry that the verifier can name in a true long table of a tied array.
  `sqI_meet`: limb l of block kh of the stream that comes in, in the table named xbI@Z_V.
  `sqA_meet`: limb l of block kh of layer i of the tensor xs, in the table named af@Z_V.
  `tensor_meet`: limb l of block jh of layer i of the tensor of an array that is read by blocks, in
    any family of tables that is true of the tensor's matrix; `gS_meet`, `gU_meet`: for s and u.
Limits. LongTrue speaks only of entries for which U3at returns a form, while readAtW is defined at
every place: each statement asks that U3at returns. Fits and TrueAt3 are premises. FOR THE TENSORS s
AND u THE TRUTH OF THE TABLE IS A PREMISE OF ITS OWN (R), at any first entry tb and any point: no
record here says that the tables named af@Z_a and af@Z_b are true,
and nothing here ties tb to these names. The weights of a block's features are written from
coordinate 0 of the letter lowV or lo on. That these letters are coordinates of the verifier's
points is not said here. No library-side entry occurs. Nothing on soundness.


-/
import Johnson.Road.Rows.LayerTermsPort
import Johnson.Road.FormsKeysIdnL

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open Finset
open OnBytes.Model (Reading World Aff TenAt tenCell)
open OnBytes.Model.Layer (Env Ten)
open OnBytes.Road.Rows (readAtW U3at_read)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell Arr)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} {v : Env} {c : Cells K}
  {t : Cell → K}

/-- An entry of a true long table of the matrix mat, at the place of limb l of block jh of layer i
of an array A that is tied to that matrix and whose layer begins at a whole block: if the verifier
can name it (U3at returns a form), the entry of the reads is worth the sum over the block's features
r, under the equality weights of lo, of the extension of the library's cell over the positions at
uu. -/
theorem long_meet {tb mat lt : ℕ} {A : Arr} {pl : TenAt} {lo uu : ℕ → K} (T : Tied c t A mat pl)
    (R : LongTrue ρ W v tb mat v.y.ls lt c lo uu) (hS2 : v.y.S2 = 2 ^ v.y.ls) {l i jh : ℕ}
    (hal : v.y.S2 ∣ tenCell pl l i 0) {a : Aff}
    (h : v.U3at tb (tenCell pl l i 0 / v.y.S2 + jh) = some a) :
    readAtW W v tb (tenCell pl l i 0 / v.y.S2 + jh) =
      ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lo r *
        Blocks.ext lt (fun p => t ⟨A, l, i, jh * 2 ^ v.y.ls + r, p⟩) uu :=
  (U3at_read (ρ := ρ) h).symm.trans (entry_long T R hS2 hal h)

section Records

variable [scl : Scl] {D : Dim} {low u lowV uV uP uR lowE uE : ℕ → K}

/-- The stream that comes in, at the squares' point: from Fits (the tie of the array x0 and the
whole blocks) and TrueAt3 (the table named xbI@Z_V is true at lowV, uV), where U3at returns. -/
theorem sqI_meet (F : Fits ρ W v D c t low u) (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE) :
    ∀ tI, v.tabAt "xbI@Z_V" = some tI → ∀ l kh a,
      v.U3at tI (tenCell v.y.xb l 0 0 / v.y.S2 + kh) = some a →
      readAtW W v tI (tenCell v.y.xb l 0 0 / v.y.S2 + kh) =
        ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lowV r *
          Blocks.ext D.lT (fun p => t ⟨.x0, l, 0, kh * 2 ^ v.y.ls + r, p⟩) uV := by
  intro tI hI l kh a h
  obtain ⟨_, _, _, _, _, _, _, _, _, T0, _, _, _, _, _, halb, _⟩ := F.stream
  exact long_meet T0 (T3.xiV tI hI) F.S2 (halb l) h

/-- Layer i of the tensor xs, the stream after write number i + 1 of the group, at the squares'
point: from Fits and TrueAt3 (the table named af@Z_V is true at lowV, uV), where U3at returns. -/
theorem sqA_meet (F : Fits ρ W v D c t low u) (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE) :
    ∀ tA txs, v.tabAt "af@Z_V" = some tA → v.y.T_ "xs" = some txs → ∀ i l kh a,
      v.U3at tA (tenCell txs.place l i 0 / v.y.S2 + kh) = some a →
      readAtW W v tA (tenCell txs.place l i 0 / v.y.S2 + kh) =
        ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lowV r *
          Blocks.ext D.lT (fun p => t ⟨.xs, l, i, kh * 2 ^ v.y.ls + r, p⟩) uV := by
  intro tA txs hA hxs i l kh a h
  obtain ⟨_, _, _, txs', _, _, _, hxs', hm, _, _, Ts, _, _, _, _, hals⟩ := F.stream
  obtain rfl : txs' = txs := Option.some.inj (hxs'.symm.trans hxs)
  exact long_meet Ts (by rw [hm]; exact T3.afV tA hA) F.S2 (hals i l) h

/-- The tensor of an array A that is read by blocks, in a family of tables that begins at tb and is
true of the tensor's matrix at lo, uu (R, a premise): from Fits come the tie of A to the tensor and
the whole blocks. -/
theorem tensor_meet (F : Fits ρ W v D c t low u) {A : Arr} (hA : readLong A = true) {X : Ten}
    (hX : v.y.T_ (arrName A) = some X) {tb : ℕ} {lo uu : ℕ → K}
    (R : LongTrue ρ W v tb X.mat v.y.ls D.lT c lo uu) {l i jh : ℕ} {a : Aff}
    (h : v.U3at tb (tenCell X.place l i 0 / v.y.S2 + jh) = some a) :
    readAtW W v tb (tenCell X.place l i 0 / v.y.S2 + jh) =
      ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lo r *
        Blocks.ext D.lT (fun p => t ⟨A, l, i, jh * 2 ^ v.y.ls + r, p⟩) uu := by
  obtain ⟨ten, b, h1, T, _, hal⟩ := F.long A hA
  unfold Env.tensorAt at h1
  obtain ⟨tn, htn, h2⟩ := bind_some h1
  obtain ⟨tb', _, h3⟩ := bind_some h2
  have e1 : tn = ten := (Prod.mk.inj (Option.some.inj h3)).1
  have e2 : tn = X := Option.some.inj (htn.symm.trans hX)
  obtain rfl : ten = X := e1.symm.trans e2
  exact long_meet T R F.S2 (hal i l) h

/-- The tensor s: tensor_meet at the array sl. -/
theorem gS_meet (F : Fits ρ W v D c t low u) {X : Ten} (hX : v.y.T_ "s" = some X) {tb : ℕ}
    {lo uu : ℕ → K} (R : LongTrue ρ W v tb X.mat v.y.ls D.lT c lo uu) {l i jh : ℕ} {a : Aff}
    (h : v.U3at tb (tenCell X.place l i 0 / v.y.S2 + jh) = some a) :
    readAtW W v tb (tenCell X.place l i 0 / v.y.S2 + jh) =
      ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lo r *
        Blocks.ext D.lT (fun p => t ⟨.sl, l, i, jh * 2 ^ v.y.ls + r, p⟩) uu :=
  tensor_meet F (A := .sl) rfl hX R h

/-- The tensor u: tensor_meet at the array up. -/
theorem gU_meet (F : Fits ρ W v D c t low u) {X : Ten} (hX : v.y.T_ "u" = some X) {tb : ℕ}
    {lo uu : ℕ → K} (R : LongTrue ρ W v tb X.mat v.y.ls D.lT c lo uu) {l i jh : ℕ} {a : Aff}
    (h : v.U3at tb (tenCell X.place l i 0 / v.y.S2 + jh) = some a) :
    readAtW W v tb (tenCell X.place l i 0 / v.y.S2 + jh) =
      ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lo r *
        Blocks.ext D.lT (fun p => t ⟨.up, l, i, jh * 2 ^ v.y.ls + r, p⟩) uu :=
  tensor_meet F (A := .up) rfl hX R h

end Records

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.long_meet
#print axioms OnBytes.Road.K4.sqI_meet
#print axioms OnBytes.Road.K4.sqA_meet
#print axioms OnBytes.Road.K4.tensor_meet
#print axioms OnBytes.Road.K4.gS_meet
#print axioms OnBytes.Road.K4.gU_meet
