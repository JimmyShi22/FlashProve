-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/FrontOf.lean: the merge's law in the three items with the typed statement
read off the record by a written reader, and the condition in front as one Boolean on the record.
Definitions, and theorems with their proofs.

In `merge_table` (Johnson/Top/H0/MergeLaw/ItemsFront.lean) the reader rd of the typed statement is a
letter, under three conditions in front. Here rd is written down, and the three conditions are one
test that can be evaluated.

Main names:
  `frontIn`: the typed statement off the record: the head's claim, for each of the place's claims,
    and the head's ledger; at a record outside the head's link, or without a claim: defaults.
  `frontB`: a Boolean on the record, at the place's and the slots' numbers: the record stands in the
    head's link; the claim and what the head heard are laid; the slot of the claim's value is the
    number's; the ledger's three arrays have one entry for each slot; the claim is on the place's
    unit.
  `front_of_B`: where `frontB` says yes: `FrontReads` at `frontIn`, the arrays' sizes, and "the
  claim
    is on the place's unit".
  `merge_table_of`: `merge_table` at rd := `frontIn`, on the statements at which `frontB` says yes.

Limits. That the record in front of the merge's place passes `frontB` at a plan's numbers is not
shown. What stays a premise beside that: as ItemsFront.lean's head says. It is no soundness of the
protocol. Nothing on hiding.

-/
import Johnson.Top.H0.MergeLaw.ItemsFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR Cb Cb.Pv.Lay Johnson.L5.Layers TWhole
open OnBytes (E zeroE)
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading)
open VerifiableInference.Desc.Sound (Frame Piece below)
open Johnson.Desc.First.ForkMerge (HeadMergeP mergeEntries)
open K11Caller (MergeIn GS noRd)
open _root_.Run (ckP)
open scoped ENNReal

/-- The typed statement, read off the record. -/
def frontIn (n : ℕ) (s : S) : MergeIn n :=
  match s.here with
  | .head a => ⟨fun _ => a.claim.getD default, a.F⟩
  | _ => ⟨fun _ => default, default⟩

variable {Pl : K11Caller.Place} (N : K11Caller.Nums Pl)

/-- The condition in front, as a test on the record. -/
def frontB (s : S) : Bool :=
  match s.here with
  | .head a =>
    match a.claim, a.x with
    | some claim, some x0 =>
      N.svA == #[x0.sV] && a.F.vp.size == a.F.ns && a.F.mf.size == a.F.ns &&
        a.F.gotF.size == a.F.ns && (List.finRange Pl.n).all fun i => claim.ui == Pl.ui i
    | _, _ => false
  | _ => false

/-- What the test's yes gives. -/
theorem front_of_B {s : S} (h : frontB N s = true) :
    FrontReads N (frontIn Pl.n s) s ∧ (∀ b, s.here = .head b → OnBytes.PscRun.Sized b.F) ∧
      ∀ i, ((frontIn Pl.n s).cl i).ui = Pl.ui i := by
  unfold frontB at h
  cases hh : s.here with
  | head a =>
    rw [hh] at h
    cases hcl : a.claim with
    | none => simp [hcl] at h
    | some claim =>
      cases hx : a.x with
      | none => simp [hcl, hx] at h
      | some x0 =>
        simp only [hcl, hx, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange,
          true_implies] at h
        obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
        have ef : frontIn Pl.n s = ⟨fun _ => claim, a.F⟩ := by
          unfold frontIn
          rw [hh]
          show (⟨fun _ => a.claim.getD default, a.F⟩ : MergeIn Pl.n) = _
          rw [hcl]
          rfl
        refine ⟨?_, ?_, ?_⟩
        · intro b claim' x0' hb hcl' hx'
          have eb : b = a := by
            rw [hh] at hb
            exact (Here.head.inj hb).symm
          subst eb
          rw [hcl] at hcl'
          rw [hx] at hx'
          rw [ef, ← Option.some.inj hcl', ← Option.some.inj hx']
          exact ⟨rfl, fun _ => rfl, h1⟩
        · intro b hb
          have eb : b = a := (Here.head.inj hb).symm
          subst eb
          exact ⟨h2, h3, h4⟩
        · intro i
          rw [ef]
          exact h5 i
  | _ => rw [hh] at h; exact absurd h (by simp)

variable {F : Frame} {W : Type}

/-- **THE MERGE's LAW AT A PIECE, IN THE THREE ITEMS, THE TYPED STATEMENT READ OFF THE RECORD.** -/
theorem merge_table_of (P : HeadMergeP) (hlay : Pl.lay = P.lay) (h1 : Pl.n = 1)
    (hk0 : 0 < Pl.lay.lk) (hnum : N.first + 1 + 2 * P.lay.lk + 2 = P.nMsg)
    (hunit : ∀ a u, Pl.lay.U[Pl.ui a]? = some u → OnBytes.Road.UnitOK Pl.lay.lk u) (L : List RDT)
    (he : L.map (·.entry) = mergeEntries P.lay.lk 1 P.work)
    (hkd : ∀ d ∈ L, Fmt.kindOf d.entry.name = some d.kind) :
    ∃ (dZ d0 : RDT) (ds : List RDT) (dY dV : RDT) (hk : ds.length = (GS Reading.gl N (noRd N)).k),
      L = dZ :: d0 :: (ds ++ [dY, dV]) ∧
      ∀ (base : ℕ) (ext : S × F.E.Str → Tr (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV]))) → W → W)
        (cellOf : S × F.E.Str → ℕ → ℕ → GE) (maskOf idxOf : S × F.E.Str → ℕ → GE),
        (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).ior.red.Leads
          (fun a => frontB N a.1 = true)
          (fun a a' => ItemsSay N (cellOf a) (maskOf a) (idxOf a) (frontIn Pl.n a.1) a'.1)
          (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).err ∧
        Err.Below (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).err
          ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨dZ, d0, ds, dY, dV, hk, hL, hall⟩ :=
    merge_table (F := F) (W := W) N P hlay h1 hk0 hnum hunit L he hkd
  refine ⟨dZ, d0, ds, dY, dV, hk, hL, fun base ext cellOf maskOf idxOf => ?_⟩
  obtain ⟨hleads, hbelow⟩ := hall base ext (fun a => frontIn Pl.n a.1) cellOf maskOf idxOf
  exact ⟨hleads.conseq (fun a h => front_of_B N h) fun _ _ _ _ _ hq => hq, hbelow⟩

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.front_of_B
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_table_of
