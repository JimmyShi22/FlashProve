-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Led/LedWorld.lean: from the committed entries to the world in which the shipped Lean
verifier's forms have their values; stated once, for every sub-proof.

The theorems on the forms of a sub-proof (OnBytes/Model/HideLaws.lean and what is built on it) speak
of a world W: a value for every slot and for every entry of a virtual row. This file says which
world that is, and what "the form a is worth 0 in W" has to do with the proof file.

The four names.
  portWorld ρ Y F m (LedPort.lean; portWorld_eq, portWorld_slot, portWorld_entry): the world that
    the committed entries m give at the verifier's state F. Under slot j lies what was shown less
    the factor times the committed mask entry. An entry of a virtual row is the row's combination
    of the committed cells.
  holds_iff_values: the ledger of a list of the verifier's forms holds of m if and only if each form
    is worth 0 in portWorld.
  Packed Y sym m M (LedPort.lean): the matrices M are those whose cells are packed in the symbol
    arrays of m. It is a relation: a symbol has a reading as three small cells only if the cells
    are small, which is the smallness test's claim.
  one_equation_iff and cnt_claims_le: the equation that the verifier hands to the chain holds if and
    only if the one form of the claims holds of m at theta; and if some form is not worth 0 in
    portWorld, the one form holds at no more than (first exponent + number of claims - 1) elements.

What this file does not claim. The count is for forms that are fixed before theta: the list l, the
state H at which it is read (what was shown, the factors, the virtual rows' weights) and m do not
hang on the element that is counted. At a real sub-proof they do (LedSpread.lean). That the chain's
tests give the equation, that m is what the proof file commits to, that the verifier's theta is a
uniform draw from K, and that the verifier's run adds just the list l are not stated here; for the
last see LedAdds.lean. one_equation_iff has the premises of one_equation (LedPort.lean): claims that
are added by Fork.lin alone, in one fold, with nothing between the last claim and Fork.settle. So it
does not apply to a whole run of the verifier as it stands; LedAdds.lean (settle_batch_iff) has the
form on totals that does.


-/
import OnBytes.Tie.Pv.Led.LedPort
import OnBytes.Tie.Pv.Led.LedBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows
open TWhole

variable {K J : Type} [Field K] [Fintype J] (ρ : Model.Reading K) (Y : Lay J)

/-- portWorld is the world of OnBytes/Model/HideLaws.lean at the committed mask row and cells. -/
theorem portWorld_eq (F : Model.Fork) (m : J → K) :
    portWorld ρ Y F m =
      F.worldOf ρ (Y.maskAt m) fun t r idx => Y.entryAt m t (rowWeight ρ F.trees t r) idx := rfl

/-- The ledger of a list of the verifier's forms holds of the committed entries if and only if each
form is worth 0 in the world of these entries. To be used at the state at which the one equation
is written: at an earlier state the virtual rows' weights are not set yet, so that the entries of
these rows are 0 in portWorld, and a slot that is still free holds 0. -/
theorem holds_iff_values (F : Model.Fork) (l : List Model.Aff) (m : J → K) :
    (claimsOf ρ Y F l).Holds m ↔ ∀ a ∈ l, a.value ρ (portWorld ρ Y F m) = 0 := by
  unfold claimsOf TWhole.Ledger.Holds
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact forall₂_congr fun a _ => by rw [Aff.claim_holds, ofAff_val]

/-- The equation that goes to the chain holds if and only if the one form of the claims holds of
the committed entries at theta. The premises are those of one_equation, so it does not apply to a
whole run of the verifier as it stands: see settle_batch_iff (LedAdds.lean). -/
theorem one_equation_iff (F G H : Model.Fork) (l : List Model.Aff) (used : Nat) (mc : Array E)
    (c : E) (m : J → K) (hs : F.LS.size = F.ns) (ht : F.total ρ (portWorld ρ Y H m) = 0)
    (h : F.lins l = some G)
    (hk : H.total ρ (portWorld ρ Y H m) = G.total ρ (portWorld ρ Y H m))
    (hset : H.settle used = some (mc, c)) :
    Model.treesValue ρ (portWorld ρ Y H m) H.trees + Model.maskValue ρ (Y.maskAt m) mc +
        ρ.val c = 0 ↔
      (batchAt (ρ.val F.theta)
        ((List.range' F.nClaim l.length).zip (claimsOf ρ Y H l))).Holds m := by
  rw [one_equation ρ Y F G H l used mc c m hs ht h hk hset]
  exact Iff.rfl

/-- If some form of the list is not worth 0 in the world of m, the one form of the list's claims,
under the exponents c, c + 1 and so on, holds of m at no more than c + (number of forms) - 1
elements. H and l are fixed while the element is counted. So this serves only a sub-proof without
the smallness test, whose claims and virtual rows hold theta: for these see LedSpread.lean. -/
theorem cnt_claims_le [Fintype K] (H : Model.Fork) (l : List Model.Aff) (c : Nat) (m : J → K)
    (bad : ¬ ∀ a ∈ l, a.value ρ (portWorld ρ Y H m) = 0) :
    Prob.cnt (fun x : K =>
      (batchAt x ((List.range' c l.length).zip (claimsOf ρ Y H l))).Holds m) ≤
        c + l.length - 1 := by
  apply cnt_zip_le
  · exact List.nodup_range'
  · intro e he
    have := List.mem_range'_1.1 he
    omega
  · simp [claimsOf]
  · exact fun k => bad ((holds_iff_values ρ Y H l m).1 k)

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.holds_iff_values
#print axioms OnBytes.Road.Rows.one_equation_iff
#print axioms OnBytes.Road.Rows.cnt_claims_le
