-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/NormsWorld.lean: what a later ledger's world holds under the slots of the
norms' hidden sums, hidden products and hidden claimed sum; and that the slots' numbers are public.
Definitions, statements and proofs.

The per-position bridge reads the hidden sums and products off the world (`Run.Wt`, `Run.Pt`), and
some of its sets of bad elements read them. `Run.Ledger` says nothing of these slots.

  `prodsOf`: what round k0 + muV + 6 sent: the norms' products as shown.
  `sPvAt`, `sClAt`, `norms_slots0`, `norms_slots`: THE SLOTS' NUMBERS ARE PUBLIC: each of sW, the
    squares' end values' slot, sPv, the claimed sum's slot, the products' sumcheck's first own slot
    and its end values' first slot is the ledger's next slot in front plus a formula in public
    sizes.
  `norms_world0`, `norms_world`: in the world of every ledger later than the hearing's, the hidden
    value under slot sW + j is what round k0 sent at place j less the mask entry of that slot; the
    like for sPv + m and round k0 + muV + 6; and the hidden claimed sum of the products' sumcheck
    is what that sumcheck's first round sent first, less the mask entry of its slot. So these
    hidden values are functions of the mask and of what the tape sent in front of the drawn
    elements gam, om and the products' eps.
  `masksAt`, `masks_at`: the masks that `runD6_ledger` lays (`masksOf`, a term of what was heard)
    are a term of the mask, the public record and the ledger's next slot in front alone.

The statements without 0 are typed of a record that differs from the stretch's own in the fields tT
and KT alone. One direction: from a return.
-/
import Johnson.Road.K4.NormsRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.PscRun (Sized Filled hideRun_ok)
open OnBytes.Desc.First.P1 (level_world tsc_world slot_worldOf levelIn_heard tscIn_heard tapeCl)

variable {K : Type} [Field K] (ρ : Reading K)

/-- What round k0 + muV + 6 has to send: the norms' products. -/
def prodsOf (P : Pub) (g : Nat) (t : Tape) : Array E :=
  (((t.drop (k0 g + P.rd.muV + 6)).head?.map (·.sent)).getD []).toArray

/-- The first slot of the norms' products, n the ledger's next slot in front of the stretch. -/
def sPvAt (P : Pub) (n : Nat) : Nat := n + ledNS P.y.h.xl * P.y.NI + 1 + 2 * P.rd.muV + 2 + 2

/-- The slot of the products' claimed sum. -/
def sClAt (P : Pub) (n : Nat) : Nat := sPvAt P n + ledNP P.y.h.xl * P.y.NI

include ρ in
/-- **The slots' numbers are public.** -/
theorem norms_slots0 {P : Pub} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape} {H : Heard}
    (hF : Sized F) (h : hearNorms engFl P g fo F t = some (H, G, u)) :
    H.sW = F.next ∧
      H.wpl.sL = F.next + ledNS P.y.h.xl * P.y.NI + 1 + 2 * P.rd.muV + 2 ∧
      H.sPv = sPvAt P F.next ∧ H.tV.sCl = sClAt P F.next ∧
      H.tV.p.first = sClAt P F.next + 1 ∧
      H.tV.sEnd = sClAt P F.next + 1 + 1 + 2 * P.y.h.lt + 2 := by
  obtain ⟨F4, F7, F8, rhoI, vW, vP, gam, om, w0, wI, d0, dI, e0, l0, hPV, e3, hvW, hsW, hF4, hgp,
    e5, lI, hrho, c7, e7, hvP, hsPv, hF8, hom, c10, _⟩ := hearNorms_tape h
  have hF' : Sized ({ F with next := F.next + ledNS P.y.h.xl * P.y.NI } : Fork) := hF
  obtain ⟨hSa, hS4, _, _⟩ := hideRun_ok _ F4 F.next vW oneE hF' hF4
  have n4 : F4.next = F.next + ledNS P.y.h.xl * P.y.NI := hSa.next
  obtain ⟨_, hS7, n7, _⟩ := level_world ρ (fun _ => 0) (fun _ _ _ => 0) hS4 c7
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsL, _⟩ := levelIn_heard c7
  have hF7' : Sized ({ F7 with next := F7.next + ledNP P.y.h.xl * P.y.NI } : Fork) := hS7
  obtain ⟨hSb, hS8, _, _⟩ := hideRun_ok _ F8 F7.next vP oneE hF7' hF8
  have n8 : F8.next = F7.next + ledNP P.y.h.xl * P.y.NI := hSb.next
  obtain ⟨_, _, hfirst, hsEnd, _⟩ := tsc_world ρ (fun _ => 0) (fun _ _ _ => 0) hS8 c10
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hsCl, _⟩ := tscIn_heard c10
  have hlen : (H.PV.toList.take P.y.h.lt).length = P.y.h.lt := by
    rw [hPV, List.length_take]
    show min P.y.h.lt d0.length = P.y.h.lt
    rw [l0, Nat.min_self]
  have e7' : F7.next = sPvAt P F.next := by
    unfold sPvAt
    rw [n7, n4]
  have e8' : F8.next = sClAt P F.next := by
    unfold sClAt
    rw [n8, e7']
  exact ⟨hsW, by rw [hsL, n4], by rw [hsPv, e7'], by rw [hsCl, e8'], by rw [hfirst, e8'],
    by rw [hsEnd, e8', hlen]⟩

/-- **The hidden sums and products, in a later ledger's world.** -/
theorem norms_world0 (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) {P : Pub} {g : Nat}
    {fo : Forest.Heard} {F G Hl : Fork} {t u : Tape} {H : Heard} (hF : Sized F)
    (h : hearNorms engFl P g fo F t = some (H, G, u)) (lH : Fo.Later G Hl) :
    (∀ j, j < ledNS P.y.h.xl * P.y.NI → (Hl.worldOf ρ mask entry).slot (H.sW + j) =
      ρ.val ((sumsOf g t).getD j zeroE) - mask (H.sW + j)) ∧
    (∀ m, m < ledNP P.y.h.xl * P.y.NI → (Hl.worldOf ρ mask entry).slot (H.sPv + m) =
      ρ.val ((prodsOf P g t).getD m zeroE) - mask (H.sPv + m)) ∧
    (Hl.worldOf ρ mask entry).slot H.tV.sCl =
      ρ.val (tapeCl (t.drop (k0 g + P.rd.muV + 7))) - mask H.tV.sCl := by
  obtain ⟨F4, F7, F8, rhoI, vW, vP, gam, om, w0, wI, d0, dI, e0, l0, hPV, e3, hvW, hsW, hF4, hgp,
    e5, lI, hrho, c7, e7, hvP, hsPv, hF8, hom, c10, _⟩ := hearNorms_tape h
  have s1 : sumsOf g t = vW := by
    unfold sumsOf
    rw [e3, sent_cons, Array.toArray_toList]
  have s2 : prodsOf P g t = vP := by
    unfold prodsOf
    rw [e7, sent_cons, Array.toArray_toList]
  have hF' : Sized ({ F with next := F.next + ledNS P.y.h.xl * P.y.NI } : Fork) := hF
  obtain ⟨_, hS4, hin4, _⟩ := hideRun_ok _ F4 F.next vW oneE hF' hF4
  obtain ⟨l47, hS7, _, _⟩ := level_world ρ mask entry hS4 c7
  have hF7' : Sized ({ F7 with next := F7.next + ledNP P.y.h.xl * P.y.NI } : Fork) := hS7
  have l7 : Fo.Later F7 ({ F7 with next := F7.next + ledNP P.y.h.xl * P.y.NI } : Fork) :=
    ⟨by show F7.next ≤ F7.next + ledNP P.y.h.xl * P.y.NI; omega, rfl,
      fun _ hj => ⟨hj, rfl, rfl⟩⟩
  obtain ⟨_, hS8, hin8, _⟩ := hideRun_ok _ F8 F7.next vP oneE hF7' hF8
  have l78 := l7.trans (Fo.hideRun_later hF7' hF8)
  obtain ⟨l8G, _, _, _, _, _, _, hv⟩ := tsc_world ρ mask entry hS8 c10
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hsCl, _⟩ := tscIn_heard c10
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have q := hin4 j (by rw [hvW]; exact hj)
    have r := (((l47.trans l78).trans l8G).trans lH).keep (F.next + j) q.2.2.1
    rw [hsW, s1, slot_worldOf, r.2.1, r.2.2, q.2.2.2.1, q.2.2.2.2, ρ.one]
    ring
  · intro m hm
    have q := hin8 m (by rw [hvP]; exact hm)
    have r := (l8G.trans lH).keep (F7.next + m) q.2.2.1
    rw [hsPv, s2, slot_worldOf, r.2.1, r.2.2, q.2.2.2.1, q.2.2.2.2, ρ.one]
    ring
  · have e := (hv Hl lH).1
    rw [e, hsCl]

/-- The same of a record that differs in the two fields alone that the next stretch fills. -/
theorem norms_world (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) {P : Pub} {g : Nat}
    {fo : Forest.Heard} {F G Hl : Fork} {t u : Tape} {H1 H : Heard} {a : Option Tsc} {b : Aff}
    (hF : Sized F) (h : hearNorms engFl P g fo F t = some (H1, G, u))
    (hH : H = { H1 with tT := a, KT := b }) (lH : Fo.Later G Hl) :
    (∀ j, j < ledNS P.y.h.xl * P.y.NI → (Hl.worldOf ρ mask entry).slot (H.sW + j) =
      ρ.val ((sumsOf g t).getD j zeroE) - mask (H.sW + j)) ∧
    (∀ m, m < ledNP P.y.h.xl * P.y.NI → (Hl.worldOf ρ mask entry).slot (H.sPv + m) =
      ρ.val ((prodsOf P g t).getD m zeroE) - mask (H.sPv + m)) ∧
    (Hl.worldOf ρ mask entry).slot H.tV.sCl =
      ρ.val (tapeCl (t.drop (k0 g + P.rd.muV + 7))) - mask H.tV.sCl := by
  subst hH
  exact norms_world0 ρ mask entry (H := H1) hF h lH

include ρ in
/-- The same of a record that differs in the two fields alone that the next stretch fills. -/
theorem norms_slots {P : Pub} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape}
    {H1 H : Heard} {a : Option Tsc} {b : Aff} (hF : Sized F)
    (h : hearNorms engFl P g fo F t = some (H1, G, u)) (hH : H = { H1 with tT := a, KT := b }) :
    H.sW = F.next ∧
      H.wpl.sL = F.next + ledNS P.y.h.xl * P.y.NI + 1 + 2 * P.rd.muV + 2 ∧
      H.sPv = sPvAt P F.next ∧ H.tV.sCl = sClAt P F.next ∧
      H.tV.p.first = sClAt P F.next + 1 ∧
      H.tV.sEnd = sClAt P F.next + 1 + 1 + 2 * P.y.h.lt + 2 := by
  subst hH
  exact norms_slots0 ρ (H := H1) hF h

/-- The mask entries beneath the two sumchecks, at the slots' public numbers. n: the ledger's next
slot in front of the stretch. -/
def masksAt (mask : ℕ → K) (P : Pub) (n : Nat) : D6.Bridge.Masks K where
  hS := fun i => mask (n + ledNS P.y.h.xl * P.y.NI + i)
  mS := fun e => mask (n + ledNS P.y.h.xl * P.y.NI + 1 + 2 * P.rd.muV + 2 + e)
  hP := fun i => mask (sClAt P n + 1 + i)
  mP := fun e => mask (sClAt P n + 1 + 1 + 2 * P.y.h.lt + 2 + e)

include ρ in
/-- **The masks stand in front of the tape.** -/
theorem masks_at (mask : ℕ → K) {P : Pub} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape}
    {H1 H : Heard} {a : Option Tsc} {b : Aff} (hF : Sized F)
    (h : hearNorms engFl P g fo F t = some (H1, G, u)) (hH : H = { H1 with tT := a, KT := b }) :
    masksOf mask H (F.next + ledNS P.y.h.xl * P.y.NI) = masksAt mask P F.next := by
  obtain ⟨_, hsL, _, _, hfirst, hsEnd⟩ := norms_slots ρ hF h hH
  unfold masksOf masksAt
  rw [hsL, hfirst, hsEnd]

end OnBytes.Desc.First.K4
