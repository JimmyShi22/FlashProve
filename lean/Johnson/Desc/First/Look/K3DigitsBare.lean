-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3DigitsBare.lean: the lookup on the digits of a segment's approximate range
proof: (1) BEHIND AN ACCEPT OF THE WHOLE SEATED SUB-PROTOCOL THE ROWS THAT THE LOOKUP's VERIFIER HAS
HEARD NAME NO ENTRY OF A VIRTUAL ROW (Bare, OnBytes/Tie/Pv/Led/LedRowsLook.lean); (2) two of the
row's sentences under names, so that they can be stated at a term: DigObjR (the field fObj of
DigMeanR and DigRestR, its text) and DigMaskR (what its payer asks of the state behind, under the
same hands). Definitions, one theorem. NO SOUNDNESS IS CLAIMED.

Main names.
  k3_digits_seated_bare: at an accept of a piece that holds «below B'», B' narrowing K3.theStated's
    value at the digits' address, from a state whose ledger has its sizes: whatever is heard at the
    digits' seat behind has bare rows.
  DigObjR: fObj's own text, laid by program. DigMaskR: under fObj's hands: MaskOk
    (K3DigitsMask.lean) at the part that segAt? reads off the state behind.
HOW. theStated_yes_digits (K3DigitsSeatedYes.lean) · digits_bare
(Johnson/Top/H/Keep/RowsAreBare.lean) at the sub-protocol's own .ok · the step without a round
behind it leaves tl? (quietHead_ok, quietDigits_ok, tl_putFork).
OBJECT. As in K3DigitsSeatedYes.lean.
USER. digObjR_mgAll (Johnson/Desc/Sound/MgAt/K3DigitsObj.lean).
LETTERS. Those of k3_digits_seated_turns; those of DigMeanR; ms.
IS IT EMPTY? The theorem's premises are an accept and Sized F. The two definitions are sentences:
shown at no term here.


Compiled with the whole library.
Limits. Nothing on hiding.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3MeansDigR
import Johnson.Desc.First.Look.K3DigitsMask
import Johnson.Top.H.Keep.RowsAreBare

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open Cb.Fo.Pin
open VerifiableInference.Desc.First (ModelPart Item Pub Meaning Numbers shift)

section
variable {Cl : Type} {Fr : Frame}

/-- **BEHIND AN ACCEPT OF THE WHOLE SEATED SUB-PROTOCOL THE HEARD ROWS ARE BARE.** -/
theorem k3_digits_seated_bare {W : Type} (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B B' : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (hN : B'.Narrows B) (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (q : Piece (ckP .two) Fr Desc.First.S Cl W) (hq : q.b = below B') (hback : q.back = [])
    (u v : Desc.First.S × Fr.E.Str) (τ : Tr (uLT (ckP .two) q.ds))
    (hout : q.ior.red.out u τ = some v) {F : Fork} (hf : u.1.fork? = some F)
    (hS : OnBytes.PscRun.Sized F) :
    ∀ g, (Desc.K3.seatDigits claim).heard v.1 = some g →
      ∀ f ∈ g.rows.toList, OnBytes.Road.Rows.Bare f := by
  obtain ⟨-, -, -, cols, hd⟩ := piece_hears_below q B' hq hback u τ v hout
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc u.1 v.1 _ cols
      (hN.2 _ _ _ _ hd)
  obtain ⟨g₀, hg₀, hb⟩ := digits_bare claim a.piece laid sent P' [] u.1 s' _ gs' hyes hf hS
  have hh : v.1.tl? = s'.tl? := by
    rcases hstep with e | ⟨f, hf', hfs⟩
    · rw [e]
    · unfold Desc.K3.quietAt at hf'
      simp only [if_true] at hf'
      split at hf'
      · obtain rfl := Option.some.inj hf'
        obtain ⟨ah, c, ha, -, e⟩ := Desc.K3.quietHead_ok X s' v.1 hfs
        rw [e]
        simp [Desc.First.S.tl?, ha]
      · split at hf' <;> split at hf' <;>
          (obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hf'
           obtain ⟨F', -, -, e⟩ := Desc.K3.quietDigits_ok _ _ s' v.1 hfs
           rw [e, tl_putFork])
  intro g hg f hm
  have hg' : v.1.tl?.bind (·.heard) = some g := hg
  have hg1 : s'.tl?.bind (·.heard) = some g₀ := hg₀
  rw [hh, hg1] at hg'
  obtain rfl := Option.some.inj hg'
  exact hb f hm

end

section
variable {P Cl Cells Tok : Type} {Fr : Frame} (X : Verify.Public)
  (Dn : Desc.First.Look.Sent) (L : K3Letters Cells Tok) (N : Numbers)
  (Mg : Meaning P (Desc.Wit Cells Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop) (claim : Aff → Cl)

local notation "WT" => Desc.Wit Cells Tok MsgT
local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "SET" => Params.settingOf X.P.frame
set_option quotPrecheck false in
local notation "PieceT" => Piece (ckP .two) Fr (P × Desc.First.S) Cl WT

/-- **The field fObj, under a name.** -/
def DigObjR (k l : ℕ) (sub : ModelPart) (x : Desc.First.Look.Place) (tl : HTailF2) (q : PieceT)
    (b' : Desc.Block Desc.First.S Cl) : Prop :=
  ∀ B', SeatOf b' B' → ∀ (z : P) a τ b,
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (ckP .two) Fr Desc.First.S Cl WT).ior.red.out a τ = some b →
    onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
    a.1.failed = none → SameBut a.1 b.1 →
    Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace SET true x) b.1 = true →
    DigLeft a.1 b.1 → onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) (k + 1) b →
    ∀ w, Mg.forms l (7 + shift sub) "objects" (z, b.1) (strsOf Fr b.2) w →
    ∀ g F', (Desc.K3.seatDigits claim).fork b.1 = some F' →
    (Desc.K3.seatDigits claim).heard b.1 = some g →
    K3OutRows tl.f9 5 x.F.next
      (digNu x tl Dn L.rad (fun j => L.seat x.link true j.1) L.arr w) Reading.gl g F'

/-- **What its payer asks of the state behind, under the same hands.** -/
def DigMaskR (ms : List Mem) (k l : ℕ) (x : Desc.First.Look.Place) (q : PieceT)
    (b' : Desc.Block Desc.First.S Cl) : Prop :=
  ∀ B', SeatOf b' B' → ∀ (z : P) a τ b,
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (ckP .two) Fr Desc.First.S Cl WT).ior.red.out a τ = some b →
    onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
    a.1.failed = none → SameBut a.1 b.1 →
    Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace SET true x) b.1 = true →
    DigLeft a.1 b.1 → onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) (k + 1) b →
    ∀ p, Desc.K9.segAt? b.1 = some p →
      MaskOk x Dn L.rad (fun j => L.seat x.link true j.1) ms (N.group l) p

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_digits_seated_bare
