-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12PaysGameV.lean: THE LAW OF THE PROXIMITY TEST WITH NOTHING PROMISED OF THE RECORD (k12_gameV, Johnson/Desc/K12/Coin/GameLabels.lean; first arm) IS A LAW SUCH AS `Pays` ASKS (Johnson/RunOne/Law/K12AtField.lean). One statement; its proof is one call. IT SHOWS THAT THE FORM FITS; NOTHING ON WHETHER THE PREMISES CAN BE MET AT A TABLE.
OBJECT. `Pays Fr π R R' B' on L n base (dB :: dt) [] x'`.
USER. Whoever pays a field of the key file's tables at a seat of the proximity test's first arm.
LETTERS. All free. Premises: AtPlace · the radii are r's · johOk π r · batOneOk π · the first round's error e is at least "BAT"'s count · LabelsPub π num nl base: A TEST ON THE PLAN: of each opening that the first switch declares, its source's number through the file is nl of its label, and lies below the base · (e, εt) is at most the row's errors · (I2).

  pays_gameV: the statement. The law promises nothing of the record. (I2), the last premise: "one tuple for all rows" stands at the oracles that `nuOf π nl t` names: a place of the record's own book by the label of the tree there.
Limits. As empty as its premises: no non-degenerate instance of (I2) is shown at any table; that
LabelsPub holds at a place of the key file is not shown here (at the key file's rows 2.9 and 3.2,
under that file's section premises (in scope, the planner's and the laws' tests passed, the written
key file): place_29, place_32, K12PlaceAtName.lean) (Where this and lean/THEOREM.md differ, the page
holds.) (at the proof file's last chain's own test no nl can serve: no_label_numAt,
Johnson/Desc/K12/Law/LabelsClash.lean). The first arm alone. Nothing on soundness, nothing on
hiding.

-/
import Johnson.RunOne.Law.K12AtField
import Johnson.Desc.K12.Coin.GameLabels

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12PaysGameV
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K12.Coin
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0)
open H2K.First (batOneOk)
open Johnson.RunOne.Law.K12AtField (Pays)

variable {W H S Cl : Type} {Fr : Frame} (π : P12) (R : S → T12 → Prop) (R' : S → T12 → S → Prop)
  (B' : Block (H × S) Cl) (on L : ℕ → (H × S) × Fr.E.Str → Prop) (n : ℕ)
  (num : Fmt.TreeSource → ℕ) (nl : ℕ → ℕ) (Lc mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
  (base : ℕ) (dB : RDT) (dt : List RDT) (e : ℕ) (εt : Err (uLT (ckP .two) dt))
  (x' : Rest (ckP .two) Fr (H × S) W (dB :: dt))

/-- **Nothing is owed of the record in front.** -/
theorem pays_gameV (r : Fmt.M1.Stage → ℕ) (hA : AtPlace Fr π num Lc mC mS mW rad base dB dt εt)
    (hr : ∀ s, rad s = r s.st) (hj : johOk π r = true) (hb : batOneOk π = true)
    (he : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e) (hpl : LabelsPub π num nl base)
    (hle : Err.le ((e, εt) : Err (uLT (ckP .two) (dB :: dt))) x'.err)
    (h2 : ∀ a τ b, on n a → (pieceOf B' base (dB :: dt) [] x').ior.red.out a τ = some b →
      (∃ t t', R a.1.2 t ∧ (R' a.1.2 t' b.1.2 ∧ b.1.1 = a.1.1) ∧
        QN π (NTuple Fr π (nuOf π nl t) rad rd) (t, a.2)) →
      on (n + 1) b ∧ (L (n + 1) b → L n a)) :
    Pays Fr π R R' B' on L n base (dB :: dt) [] x' :=
  ⟨(e, εt), _, _,
    k12_gameV Fr W π num nl Lc mC mS mW rad rd base dB dt (fun _ _ w => w) e εt r hA hr hj hb he hpl,
    hle, fun _ _ _ _ => trivial, h2⟩

end Johnson.RunOne.Law.K12PaysGameV

#print axioms Johnson.RunOne.Law.K12PaysGameV.pays_gameV
