-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/ULayPins.lean: THE PREMISE hSt OF THE LINE "forms" AT THE PINNED VALUE (forms_pins,
Johnson/Road/K4/FormsAtPins.lean) AT THE LAYERS' ARM OFF THE PUBLIC PARAMETERS (uLAt,
Johnson/Road/K4/ULayAt.lean): two texts of "the matrices unpacked from the data's symbols" are one
function wherever every symbol array has a name.

  `matsOfB_data`: matsOfB A tl (Johnson/Road/K4/K4PinsCellQ.lean) is matsOfData tl at A's list of
    arrays' names (Johnson/Desc/Sound/DataMats.lean), where each symbol array of tl has a name in
    that list. WHERE ONE HAS NONE THE TWO PART: matsOfData reads 0, matsOfB the cell at (0, "").
  `named_of_arrays`: the test arraysPlanB (Johnson/Road/K4/Rec/Arrays.lean) gives these names.
  `hSt_pins`: StatedIs of the one stated function at uLay tl fun _ B => matsOfB A tl B: forms_pins'
    hSt, at one verifier's state.
No new argument.
Limits. PREMISES of hSt_pins, none paid here: the verifier's state stands in a layers' link (hs) ·
hl: its open link's number is m · htl: tlAt X m = some tl (tlAt_plan,
Johnson/Road/K4/K4PinsScope.lean, has it at tl := the group's public parameters') · hnm: names m is
A's list of names · hn: each symbol array has a name. Met through Lean at no member. K04_law, the
law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.ULayAt
import Johnson.Road.K4.Rec.Arrays

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model
open OnBytes.Road.K4.Rec (RecPlan arraysPlanB arrayPlan_of_B)
open Cb.Pv.Tail (cellValS)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.Look (tlAt cellJ szOf)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ Stated UFn StatedIs uBySort linkNo matsOfData symOfData
  dataByAddr)

variable {Cells : Type} (A : PinPlan Cells)

/-- The two unpackings are one function, where every symbol array has a name. -/
theorem matsOfB_data (tl : HTailF2)
    (hn : ∀ μ : Fin (szOf tl).NM, ∃ bn, (A.D.arrayOf.getD A.link #[])[tl.gtTree.getD μ.val 0]? =
      some bn) (B : Bound GQ) :
    matsOfB A tl B = matsOfData tl (A.D.arrayOf.getD A.link #[]) B := by
  have es : (fun (μ : Fin (szOf tl).NM) (i : Fin (Alg.symRows ((szOf tl).m μ)))
      (c' : Fin ((szOf tl).k μ)) =>
      B.cell (((A.D.arrayOf.getD A.link #[])[tl.gtTree.getD μ.val 0]?).getD (0, "")).1
        (((A.D.arrayOf.getD A.link #[])[tl.gtTree.getD μ.val 0]?).getD (0, "")).2 i.val c'.val) =
      symOfData tl (A.D.arrayOf.getD A.link #[]) B := by
    funext μ i c'
    obtain ⟨bn, hb⟩ := hn μ
    show _ = dataByAddr _ B (.cell (tl.gtTree.getD μ.val 0) i.val c'.val)
    simp only [dataByAddr, hb, Option.getD_some]
  funext a r c
  unfold matsOfB matsOfData
  rw [es]
  cases cellJ (szOf tl) a r c with
  | none => rfl
  | some j => rfl

/-- The test on the arrays gives the names. -/
theorem named_of_arrays {tl : HTailF2} {own : List (ℕ × ℕ)} {R : RecPlan} {n m : ℕ}
    (hB : arraysPlanB A tl own R n m = true) (μ : Fin (szOf tl).NM) :
    ∃ bn, (A.D.arrayOf.getD A.link #[])[tl.gtTree.getD μ.val 0]? = some bn := by
  obtain ⟨H⟩ := arrayPlan_of_B A (List.all_eq_true.1 hB μ (List.mem_finRange μ))
  exact ⟨H.bn, H.named⟩

/-- **forms_pins' hSt at the arm off the public parameters**, under hs hl htl hnm hn. -/
theorem hSt_pins (X : Verify.Public) (names : ℕ → Array (ℕ × String)) (uA uH : ℕ → UFn) {s : S}
    {b : LayOwn} {m : ℕ} {tl : HTailF2} (hs : s.here = .lay b) (hl : linkNo s = m)
    (htl : tlAt X m = some tl) (hnm : names m = A.D.arrayOf.getD A.link #[])
    (hn : ∀ μ : Fin (szOf tl).NM, ∃ bn, (A.D.arrayOf.getD A.link #[])[tl.gtTree.getD μ.val 0]? =
      some bn) :
    StatedIs (Stated.of (uBySort (uLAt X names) uA uH)) (uLay tl fun _ B => matsOfB A tl B) s := by
  refine (statedIs_uLAt X names uA uH hs).congr ?_
  have e : (fun (_ : S) (B : Bound GQ) => matsOfData tl (A.D.arrayOf.getD A.link #[]) B) =
      fun _ B => matsOfB A tl B := by
    funext _ B
    exact (matsOfB_data A tl hn B).symm
  unfold uLAt
  rw [hl, htl, hnm, Option.getD_some, e]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.matsOfB_data
#print axioms OnBytes.Road.K4.named_of_arrays
#print axioms OnBytes.Road.K4.hSt_pins
