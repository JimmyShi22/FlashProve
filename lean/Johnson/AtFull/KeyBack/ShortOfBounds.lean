-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/ShortOfBounds.lean: THE SEVEN STRINGS OF PARAMETER BYTES ARE SHORT WHERE THE
SEVEN LISTS OF ROUNDS ARE FEW AND THE ITEMS SHORT: the first storey of the row «r7» of the key
file's back (BytesShort.lean beside says what that row is). NO WRITTEN VALUE STANDS IN IT:
arithmetic over Fmt.size_paramsBytes (Johnson/Flat/ParamsSize.lean) and configure_bytes
(OnBytes/Model/ReadBackMade.lean). Theorems with their proofs. NO SUB-PROTOCOL IMPORTS THIS FILE.
  fewB n l          a test with code on a list of entries: at most n entries, each name of at most
                    32 bytes. It walks the list once, in the tail of «&&», so that Lean's kernel can
                    evaluate it at a list of tens of thousands
  fewB_sum          its accept bounds the entries' bytes: at most 128 n · fewB_long_name: a negative
                    test of the arm on the names (WrittenFew.lean has one of the arm on the count)
  itemsSize I       the bytes of a list of items
  size_params_lt    Fmt.paramsBytes P cfg I with fewB 65536 P.entries, a digest of 32 bytes and
                    items of fewer than 2 ^ 22 bytes has fewer than 2 ^ 24 bytes
  short_of_bounds   of what configure returns: all seven strings, from such bounds on its seven
                    lists and on its five lists of items
  cfg_le · long_cfg   A NEGATIVE THEOREM: the digest's size is a summand of every string: where
                    configure returns at a digest of 2 ^ 64 bytes or more, the string keySecond is
                    NOT shorter than 2 ^ 64: so «cfg.size = 32» is no ornament. (Whether configure's
                    callers return at such a digest is not said.)
LIMITS. The bounds are premises. No soundness is claimed. On hiding nothing.
-/
import Johnson.Flat.ParamsSize
import Johnson.Goal.Conditions.KeyBytesFitAtScope
import OnBytes.Model.ReadBackMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.KeyBack
open OnBytes OnBytes.Params
open Lk6.AtPlan (names_small)

/-- At most n entries, each name of at most 32 bytes. -/
def fewB : Nat → List Fmt.Entry → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | n + 1, e :: l => decide ((Fmt.ascii e.name).size ≤ 32) && fewB n l

theorem fewB_sum : ∀ (n : Nat) (l : List Fmt.Entry), fewB n l = true →
    (l.map fun e => e.bytes.size).sum ≤ 128 * n
  | _, [], _ => Nat.zero_le _
  | 0, _ :: _, h => by cases h
  | n + 1, e :: l, h => by
    have h' : (decide ((Fmt.ascii e.name).size ≤ 32) && fewB n l) = true := h
    rw [Bool.and_eq_true, decide_eq_true_eq] at h'
    have ih := fewB_sum n l h'.2
    rw [List.map_cons, List.sum_cons, Fmt.size_entry]
    omega

/-- A negative test: one entry whose name has 33 bytes. -/
theorem fewB_long_name :
    fewB 1 [{ name := "123456789012345678901234567890123" }] = false := by decide

/-- The bytes of a list of items. -/
def itemsSize (I : List (String × ByteArray)) : Nat := (I.map fun x => (Fmt.item x.1 x.2).size).sum

theorem size_params_lt {P : Fmt.Plan} {cfg : ByteArray} {I : List (String × ByteArray)}
    (hP : fewB 65536 P.entries = true) (hc : cfg.size = 32) (hI : itemsSize I < 2 ^ 22) :
    (Fmt.paramsBytes P cfg I).size < 2 ^ 24 := by
  have a := fewB_sum _ _ hP
  have b := names_small
  unfold itemsSize at hI
  rw [Fmt.size_paramsBytes, hc]
  omega

/-- **The first storey: no written value.** -/
theorem short_of_bounds {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (h : configure l x cfg bits = .ok made) (hc : cfg.size = 32)
    (hk : ∀ P ∈ made.key, fewB 65536 P.plan.entries = true)
    (hp : ∀ P ∈ made.proof, fewB 65536 P.plan.entries = true)
    (he : fewB 65536 made.entry.plan.entries = true)
    (i1 : itemsSize (Plan.oneTimeItems made.sized.key) < 2 ^ 22)
    (i2 : itemsSize (madeLinItems made.sized.key.codes made.sized.key.once.shape) < 2 ^ 22)
    (i3 : itemsSize (madeEntryItems made.sized) < 2 ^ 22)
    (i4 : itemsSize (madeFirstItems l x made.sized) < 2 ^ 22)
    (i5 : itemsSize (madeLinItems made.sized.proof.codes made.sized.proof.batch.shape) < 2 ^ 22) :
    made.keyOneTime.size < 2 ^ 24 ∧ made.keyShared.size < 2 ^ 24 ∧ made.keySecond.size < 2 ^ 24 ∧
      made.entryLink.size < 2 ^ 24 ∧ made.first.size < 2 ^ 24 ∧ made.shared.size < 2 ^ 24 ∧
      made.second.size < 2 ^ 24 := by
  obtain ⟨P1, P2, P3, F, S2, S3, ek, ep, e1, e2, e3, e4, e5, e6, e7⟩ := configure_bytes h
  rw [ek] at hk
  rw [ep] at hp
  have i0 : itemsSize [] < 2 ^ 22 := by decide
  rw [e1, e2, e3, e4, e5, e6, e7]
  exact ⟨size_params_lt (hk P1 (by simp)) hc i1, size_params_lt (hk P2 (by simp)) hc i2,
    size_params_lt (hk P3 (by simp)) hc i0, size_params_lt he hc i3,
    size_params_lt (hp F (by simp)) hc i4, size_params_lt (hp S2 (by simp)) hc i5,
    size_params_lt (hp S3 (by simp)) hc i0⟩

/-- The digest's size is a summand. -/
theorem cfg_le (P : Fmt.Plan) (cfg : ByteArray) (I : List (String × ByteArray)) :
    cfg.size ≤ (Fmt.paramsBytes P cfg I).size := by
  rw [Fmt.size_paramsBytes]
  omega

/-- **A negative theorem**: at a long digest a string is long. -/
theorem long_cfg {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat} {made : Configured}
    (h : configure l x cfg bits = .ok made) (hc : 2 ^ 64 ≤ cfg.size) :
    ¬ made.keySecond.size < 2 ^ 64 := by
  obtain ⟨_, _, P3, _, _, _, _, _, _, _, e3, _⟩ := configure_bytes h
  have := cfg_le P3.plan cfg []
  rw [e3]
  omega

end AtFull.KeyBack

#print axioms AtFull.KeyBack.fewB_sum
#print axioms AtFull.KeyBack.fewB_long_name
#print axioms AtFull.KeyBack.size_params_lt
#print axioms AtFull.KeyBack.short_of_bounds
#print axioms AtFull.KeyBack.cfg_le
#print axioms AtFull.KeyBack.long_cfg
