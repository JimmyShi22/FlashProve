-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsConstr.lean: TWO PREMISES OF K4's ROW AT THE TABLE OF JOINTS ARE THEOREMS AT
THE TABLE's AUTHORS' OWN FILLING OF THE ITEM constr (`P5J.constrQAt`, Johnson/P5J/MeansQ.lean): the
filler's line for the part idn, and `SmallRides` (Johnson/Road/K4/K4Pins.lean). By unfolding. No
draw, no count.

  **`idn_constrQAt`**: `constrQAt hd put H headPart digitsPart (2 g) idn a y w`, from: 2 g is not
    the head's segment hd · at every matrix Wi and every request xx: `NormField` and `EmbField`
    (Johnson/Road/Rows/LayerTop.lean) at the record's shape, scale file and layout, at group g, at
    `(H.hid w).MG g`.
  `hid_seat_MG`: at H := `P5J.hidAtSeat` that list is `Meaning.mgOf X.y (ownW …) g`
    (Johnson/Road/K4/K4PinsIdn.lean), by the make.
  **`smallRides_constrQAt`**: `SmallRides Zt m Mg Fr base`, from: Mg's field constr is
    `constrQAt hd put H headPart digitsPart` · m is not hd · H's decoder is the table's own
    (`H.dec = fun a y => decT y.cell a`) · the line table of `RecRides` at decT.

STANDS OVER Johnson/P5J/MeansQ.lean (to type against,
not to lean on), which stands in this tree.

OBJECT: none of its own. USER: Johnson/Road/K4/K4PinsEnd.lean; meant: whoever lays `k4_own_all`
(Johnson/Road/K4/K4PinsAll.lean) at that meaning: its fields fillI and small. LETTERS: hd, put, H,
headPart, digitsPart, decT, Mg: free.

Limits. K04_law IS NOT PROVED BY THIS. IT WILL TURN WHEN THAT FILLING TURNS. `idn_constrQAt` asks
its clauses at every Wi and xx: more than the item says (it speaks at the indices that the decoded
matrix holds): in a group that is not the first that costs nothing (K4PinsIdn.lean's `idn_fields`);
IN THE FIRST GROUP IT IS TOO MUCH TO ASK (the identity on the embedding reads Wi). At the head's
segment the part small reads a letter (headPart) at the statement: not covered.
-/
import Johnson.Road.K4.K4PinsIdn
import Johnson.P5J.MeansQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open OnBytes.Model.Verify (Public layerShape)
open OnBytes.Road.Rows.Norms (NormField EmbField)
open VerifiableInference.Desc (Wit Strs)
open VerifiableInference.Desc.First (S Meaning Numbers)
open VerifiableInference.Desc.Sound (Frame Mem MsgT strsOf)
open Cb.Pv.Tail (Size)
open Inst.Model (Mat)

/-- **The filler's line for the part idn, at the table's authors' filling.** -/
theorem idn_constrQAt {X : Public} {P W : Type} {rows cols : ℕ} (hd : ℕ)
    (put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq) (H : P5J.HidAt X P W rows cols)
    (headPart : P5J.TPart → Cm.Idx → P × P5J.TS → Strs → W → Prop)
    (digitsPart : ℕ → P × P5J.TS → Strs → W → Prop) (g : ℕ) (hne : 2 * g ≠ hd) (a : P × P5J.TS)
    (y : Strs) (w : W)
    (h : ∀ (Wi : Mat) (xx : Cm.Seg.XI),
      NormField (layerShape X.P) X.layers.sc X.y g ((H.hid w).MG g) Wi xx ∧
        EmbField (layerShape X.P) X.layers.sc X.y g ((H.hid w).MG g) Wi xx) :
    P5J.constrQAt hd put H headPart digitsPart (2 * g) .idn a y w := by
  unfold P5J.constrQAt
  rw [if_neg (by decide)]
  refine ⟨fun h' => absurd h' (by decide), fun M i _ _ => ?_⟩
  rw [if_neg hne, if_pos (Nat.mul_mod_right 2 g), Nat.mul_div_cancel_left g (by decide)]
  exact h i.mat _

/-- At `P5J.hidAtSeat` the list of group g is `Meaning.mgOf` of the segments' own lists. -/
theorem hid_seat_MG (X : Public) {P Cells Tok : Type} {rows cols : ℕ} (cs : OnBytes.Codes)
    (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (s : ℕ → Size)
    (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (tokV : Tok → Fin Inst.Model.ppref.V)
    (req : P × P5J.TS → P5J.TReq)
    (dec : P × P5J.TS → Strs → Option (Fin rows → Fin cols → VerifiableInference.OnPublicFiles.Flat.GE))
    (h1 : VerifiableInference.Desc.Sound.SeatsNamed arr N s seat)
    (h2 : VerifiableInference.Desc.Sound.GroupsSeated ms N) (w : Wit Cells Tok MsgT) (g : ℕ) :
    ((P5J.hidAtSeat X cs arr ms N s seat tokV req dec h1 h2).hid w).MG g =
      Meaning.mgOf X.y (ownW arr ms N s seat cs w) g := rfl

/-- **`SmallRides` at the table's authors' filling**, where its decoder is the table's own. -/
theorem smallRides_constrQAt {X : Public} {P Tok : Type} {rows cols : ℕ} {Fr : Frame} (hd : ℕ)
    (put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq)
    (H : P5J.HidAt X P
      (Wit (Fin rows → Fin cols → VerifiableInference.OnPublicFiles.Flat.GE) Tok MsgT) rows cols)
    (headPart : P5J.TPart → Cm.Idx → P × P5J.TS → Strs →
      Wit (Fin rows → Fin cols → VerifiableInference.OnPublicFiles.Flat.GE) Tok MsgT → Prop)
    (digitsPart : ℕ → P × P5J.TS → Strs →
      Wit (Fin rows → Fin cols → VerifiableInference.OnPublicFiles.Flat.GE) Tok MsgT → Prop)
    (decT : (ℕ → Option (ℕ × List UInt64)) → P × S →
      Option (Fin rows → Fin cols → VerifiableInference.OnPublicFiles.Flat.GE))
    (hdec : H.dec = fun a y => decT y.cell a) (Zt : P) (m : ℕ) (hm : m ≠ hd)
    (Mg : Meaning P (Wit (Fin rows → Fin cols → VerifiableInference.OnPublicFiles.Flat.GE) Tok MsgT))
    (hM : Mg.constr = P5J.constrQAt hd put H headPart digitsPart) (base : ℕ)
    (ht : ∀ (s s' : S) (c : ℕ → Option (ℕ × List UInt64)), OnBytes.Desc.First.K4.Rest s s' →
      decT c (Zt, s') = decT c (Zt, s)) :
    SmallRides Zt m Mg Fr base := by
  intro x y w h hy
  rw [hM] at hy ⊢
  unfold P5J.constrQAt at hy ⊢
  rw [if_neg (by decide)] at hy ⊢
  refine ⟨hy.1, fun M i hd' hH => ?_⟩
  have e : H.dec (Zt, y.1) (strsOf Fr y.2) = H.dec (Zt, x.1) (strsOf Fr x.2) := by
    rw [hdec]
    show decT (strsOf Fr y.2).cell (Zt, y.1) = decT (strsOf Fr x.2).cell (Zt, x.1)
    rw [cell_same h, ht x.1 y.1 _ h.rest]
  have h0 := hy.2 M i (e.trans hd') hH
  rw [if_neg hm] at h0 ⊢
  by_cases hp : m % 2 = 0
  · rw [if_pos hp] at h0 ⊢
    exact h0
  · rw [if_neg hp] at h0 ⊢
    exact h0

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.idn_constrQAt
#print axioms OnBytes.Road.K4.hid_seat_MG
#print axioms OnBytes.Road.K4.smallRides_constrQAt
