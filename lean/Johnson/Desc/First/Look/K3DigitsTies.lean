-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3DigitsTies.lean: the lookup on the digits of a link's smallness test: THE
TIES BETWEEN THE END THEOREM's CONDITIONS AND RELATIONS (DigOn, DigOn', DigFront, DigBehind:
K3DigitsGoodIn.lean) AND WHAT THE TABLE OF JOINTS PROMISES AND NAMES AT THE LOOKUP's TWO BORDERS:
THE LOWER STOREY: at the carried record and plain strings, free of the table's own files: the
table's clauses stand as NAMED PREMISES, in this file's letters. Small statements with their proofs.
NO SOUNDNESS IS CLAIMED.

The ties are numbered as the table's door numbers them: t1: the promise in front gives the condition
in front · t2: the condition behind, with the promise in front and the yes, gives the promise behind
· t3: what the row opens, at the statement behind, gives the relation behind · t4: the relation in
front gives what the row closes, at the statement in front.

Main names.
  sized_of_sizedB: the Bool sizedB (Johnson/Desc/First/Look/K3Borders.lean) gives the library's
    Sized.
  k3OnIn_ledger: k3OnIn's yes: a ledger is open, sized, and stands at the place's first slot.
  heardAt_digits: K3Borders.lean's reader of what was heard, at the digits, is seatDigits' own.
  k3_digits_t1: OwnIs, «no collision» at every member (CfAt) and k3OnIn give DigOn.
  k3_digits_t3: PinSig, DigOn', and the three items of the row out (K3OutRows, K3OutPlanes,
    K3OutKeys: Johnson/Top/H/K3RowOut.lean) AT WHATEVER g AND F' THE RECORD HOLDS give DigBehind.
  digBehind_items: the other way: DigBehind gives PinSig and the three items so read.
  k3_digits_t4: DigFront gives «every digit is a row of its table» (DgP.DigIn) and PinSig.
Limits. t2 IS NOT HERE. t1 IS THIN: two of its three premises are DigOn's own conjuncts; what it
adds is that k3OnIn gives the open, sized ledger. t1's three premises: OwnIs stands in no clause of
the table's promise that we have read; CfAt at every member wants each member's seat among the
tenants whose pins are open; k3OnIn is no clause of that promise yet. t3 and t4 are unfoldings:
THEIR WEIGHT LIES IN HOW THE TABLE's LETTERS (forms, worth, constr at the digits' part, pin) ARE
FILLED: nothing on that here. t3 needs DigOn' at the statement behind: without it no g and F' are at
hand.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsGoodIn
import Johnson.Desc.First.Look.K3CallerOwn
import Johnson.Desc.First.Look.K3Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

/-- The Bool on the ledger's three arrays gives the library's Sized. -/
theorem sized_of_sizedB {Gk : Fork} (h : Desc.K3.sizedB Gk = true) : OnBytes.PscRun.Sized Gk := by
  simp only [Desc.K3.sizedB, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- What the promise in front says of the ledger. -/
theorem k3OnIn_ledger {p : Desc.First.Look.P} {s : Desc.First.S}
    (h : Desc.K3.k3OnIn p s = true) :
    ∃ Fk, s.fork? = some Fk ∧ OnBytes.PscRun.Sized Fk ∧ Fk.next = p.first := by
  unfold Desc.K3.k3OnIn at h
  split at h
  · rename_i hh _
    simp only [Bool.and_eq_true] at h
    obtain ⟨-, hany⟩ := h
    cases hf : s.fork? with
    | none =>
      rw [hf] at hany
      simp at hany
    | some Fk =>
      rw [hf] at hany
      have h2 : (Fk.next == p.first && Desc.K3.sizedB Fk &&
          Desc.K3.freeB Fk p.first (Model.Forest.elems hh)) = true := hany
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      exact ⟨Fk, rfl, sized_of_sizedB h2.1.2, h2.1.1⟩
  · cases h

/-- At the digits the borders' reader of what was heard is the seat's own. -/
theorem heardAt_digits {Cl : Type} (claim : Aff → Cl) (s : Desc.First.S) :
    Desc.K3.heardAt true s = (Desc.K3.seatDigits claim).heard s := rfl

section
variable {S Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {x : Desc.First.Look.Place} {tl : HTailF2} {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ}
  (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)

local notation "theL" => DgP.digL5 Cb.Gl.E tl (enOf x.arrays) (mkOf x.arrays) x.F.next Unit

/-- **t1, the lower storey.** -/
theorem k3_digits_t1
    (smp : Desc.First.S → (i : Fin (digList x D rad).length) → Option ((digSg x D rad).om i).Smp)
    (claim : Aff → Cl) {set : Params.Setting} (a : Desc.First.S × Fr.E.Str)
    (hOwn : OwnIs D x.link a.1)
    (hCf : ∀ i, CfAt G D.codes (digList x D rad) seatT smp i a.1 (strsOf Fr a.2))
    (hIn : Desc.K3.k3OnIn (Desc.First.Look.P.ofPlace set true x) a.1 = true) :
    DigOn G x D rad seatT smp (Desc.K3.seatDigits claim).fork (OwnIs D x.link) a := by
  obtain ⟨Fk, hf, hz, -⟩ := k3OnIn_ledger hIn
  exact ⟨hOwn, fun i _ => hCf i, Fk, hf, hz⟩

variable (smp : S → (i : Fin (digList x D rad).length) → Option ((digSg x D rad).om i).Smp)
  (fork : S → Option Fork) (heard : S → Option Forest.Heard) (Own : S → Prop)

/-- **t3, the lower storey.** -/
theorem k3_digits_t3 (b : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT)
    (hPin : PinSig G D.codes (digList x D rad) seatT smp arr (fun _ => True) b.1 (strsOf Fr b.2) w)
    (hOn' : DigOn' G x tl D rad seatT smp fork heard Own b)
    (hRows : ∀ g F', fork b.1 = some F' → heard b.1 = some g →
      K3OutRows tl.f9 5 x.F.next (digNu x tl D rad seatT arr w) Reading.gl g F')
    (hPlanes : ∀ g F', fork b.1 = some F' → heard b.1 = some g →
      K3OutPlanes tl.f9 5 x.F.next (digNu x tl D rad seatT arr w) Reading.gl g F')
    (hKeys : ∀ g F', fork b.1 = some F' → heard b.1 = some g →
      K3OutKeys tl.f9 5 x.F.next (digNu x tl D rad seatT arr w)
        (forK Cb.Gl.E theL () (zext (digMu x D rad seatT arr w))) Reading.gl g F') :
    DigBehind G x tl D rad seatT arr smp fork heard b w := by
  obtain ⟨-, -, g, F', hf, hh, -, -⟩ := hOn'
  exact ⟨hPin, g, F', hf, hh, hRows g F' hf hh, hPlanes g F' hf hh, hKeys g F' hf hh⟩

/-- **The other way**: the relation behind gives the pins and the three items, at whatever g and F'
the record holds. -/
theorem digBehind_items (b : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT)
    (h : DigBehind G x tl D rad seatT arr smp fork heard b w) :
    PinSig G D.codes (digList x D rad) seatT smp arr (fun _ => True) b.1 (strsOf Fr b.2) w ∧
      ∀ g F', fork b.1 = some F' → heard b.1 = some g →
        K3OutRows tl.f9 5 x.F.next (digNu x tl D rad seatT arr w) Reading.gl g F' ∧
        K3OutPlanes tl.f9 5 x.F.next (digNu x tl D rad seatT arr w) Reading.gl g F' ∧
        K3OutKeys tl.f9 5 x.F.next (digNu x tl D rad seatT arr w)
          (forK Cb.Gl.E theL () (zext (digMu x D rad seatT arr w))) Reading.gl g F' := by
  obtain ⟨hp, g₀, F₀, hf₀, hh₀, hK⟩ := h
  refine ⟨hp, fun g F' hf hh => ?_⟩
  obtain rfl : F₀ = F' := Option.some.inj (hf₀.symm.trans hf)
  obtain rfl : g₀ = g := Option.some.inj (hh₀.symm.trans hh)
  exact hK

/-- **t4, the lower storey.** -/
theorem k3_digits_t4 (a : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT)
    (h : DigFront G x tl D rad seatT arr smp a w) :
    DgP.DigIn tl (enOf x.arrays) (digMu x D rad seatT arr w) ∧
      PinSig G D.codes (digList x D rad) seatT smp arr (fun _ => True) a.1 (strsOf Fr a.2) w :=
  ⟨h.2, h.1⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.sized_of_sizedB
#print axioms VerifiableInference.OnPublicFiles.k3OnIn_ledger
#print axioms VerifiableInference.OnPublicFiles.k3_digits_t1
#print axioms VerifiableInference.OnPublicFiles.k3_digits_t3
#print axioms VerifiableInference.OnPublicFiles.digBehind_items
#print axioms VerifiableInference.OnPublicFiles.k3_digits_t4
#print axioms VerifiableInference.OnPublicFiles.heardAt_digits
