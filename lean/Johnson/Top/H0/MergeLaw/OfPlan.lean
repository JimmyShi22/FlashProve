-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/OfPlan.lean: the merge's law at a piece (`merge_table_of`,
Johnson/Top/H0/MergeLaw/FrontOf.lean) with the place and the numbers of the slots MADE OF THE
BLOCK's OWN NUMBERS. Definitions, and theorems with their proofs.

In `merge_table_of` the place Pl and the numbers N of the slots are letters, under five premises on
public numbers (hlay, h1, hk0, hnum, hunit). Here both are terms of the block's numbers P
(`HeadMergeP`), of a unit's number and of one number more, the slot sv of the claim's value; and the
five premises are shown, for every layout that the program's `wsLayOf` returns.

Main names:
  `planPlace P h ui`: the place: the block's layout; one claim; on the unit ui.
  `planNums P h ui sv`: the numbers: as many slots as the plan says (`P.nMsg`); the sumcheck's first
    slot is P.nMsg - (2 lk + 3), lk the layout's number of column bits, as the premise hnum of
    `merge_table_of` fixes it; the claim's value stands in the slot sv; the index-mask message has
    one entry. Its three bounds follow from sv < P.nMsg and 2 lk + 3 ≤ P.nMsg.
  `merge_table_plan`: `merge_table_of` there. What is left of the premises on numbers: these two
    comparisons, and that the layout is one of `wsLayOf`'s.
  `head_is_plan`: at the reference parameters' layout and the last unit `planPlace` is `headPlace`
    (Johnson/Top/H0/K11Caller/AtFull.lean), by definition: so what that file shows of the head's
    place holds of this one.
  `scalarsOf`, `sentIn`, `svOf`: A RULE for sv off a chain's declared rounds: one slot for each
    scalar sent, counted from the round h0 on; sv: the second scalar of the last round named "PSC
    values" that sends two scalars, among the rounds from a up to b.

Limits. THE RULE `svOf` IS A DEFINITION: no theorem here reads it. It was fitted in a harness at the
small stored example and then tried at the full-size one, its numbers sealed before the record was
looked at (h0: behind the reply's round of the head's link; a, b: the stretch of the block that lays
the claim; small: sv = 1655, the first slot 2854, 2879 slots; full: sv = 2167, the first slot 3531,
3570 slots): at both the record in front of the merge holds that slot and `frontB` says yes at these
numbers: EVALUATED at two examples, not proved [not in this library]. That a made plan's layout is a
return of `wsLayOf` at the plan's shape is not shown here. The written rounds L stay a letter under
the two premises of `merge_table_of`. What stays a premise beside that: as FrontOf.lean's head says.
It is no soundness of the protocol. Nothing on hiding.

-/
import Johnson.Top.H0.MergeLaw.FrontOf
import Johnson.Top.H0.K11Caller.AtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading WsShape WsLay wsLayOf RoundName)
open VerifiableInference.Desc.Sound (Frame)
open Johnson.Desc.First.ForkMerge (HeadMergeP mergeEntries)
open K11Caller (GS noRd ofLay_pos ofLay_unit headPlace head_size)
open _root_.Run (ckP)
open scoped ENNReal

section
variable (P : HeadMergeP) {s : WsShape} {p3 : Bool} {lkW : ℕ} (h : wsLayOf s p3 lkW = .ok P.lay)
  (ui : Fin P.lay.U.size)

/-- **The place, of the block's numbers.** -/
def planPlace : K11Caller.Place := K11Caller.Place.ofLay P.lay h 1 fun _ => ui

/-- **The numbers of the slots, of the block's numbers.** -/
def planNums (sv : ℕ) (hsv : sv < P.nMsg) (hn : 2 * P.lay.lk + 3 ≤ P.nMsg) :
    K11Caller.Nums (planPlace P h ui) where
  ns := P.nMsg
  ni := 1
  first := P.nMsg - (2 * P.lay.lk + 3)
  sv := fun _ => sv
  c := 0
  hsv := fun _ => hsv
  room := by
    show P.nMsg - (2 * P.lay.lk + 3) + 2 * P.lay.lk + 2 ≤ P.nMsg
    omega
  hc := Nat.zero_lt_one

variable {F : Frame} {W : Type}

/-- **The merge's law at a piece, the place and the slots' numbers made of the block's.** -/
theorem merge_table_plan (sv : ℕ) (hsv : sv < P.nMsg) (hn : 2 * P.lay.lk + 3 ≤ P.nMsg)
    (L : List RDT) (he : L.map (·.entry) = mergeEntries P.lay.lk 1 P.work)
    (hkd : ∀ d ∈ L, Fmt.kindOf d.entry.name = some d.kind) :
    ∃ (dZ d0 : RDT) (ds : List RDT) (dY dV : RDT)
      (hk : ds.length = (GS Reading.gl (planNums P h ui sv hsv hn) (noRd _)).k),
      L = dZ :: d0 :: (ds ++ [dY, dV]) ∧
      ∀ (base : ℕ) (ext : S × F.E.Str → Tr (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV]))) → W → W)
        (cellOf : S × F.E.Str → ℕ → ℕ → GE) (maskOf idxOf : S × F.E.Str → ℕ → GE),
        (mergePiece F W P (GS Reading.gl (planNums P h ui sv hsv hn) (noRd _)) dZ d0 ds dY dV hk
            base ext).ior.red.Leads
          (fun a => frontB (planNums P h ui sv hsv hn) a.1 = true)
          (fun a a' => ItemsSay (planNums P h ui sv hsv hn) (cellOf a) (maskOf a) (idxOf a)
            (frontIn 1 a.1) a'.1)
          (mergePiece F W P (GS Reading.gl (planNums P h ui sv hsv hn) (noRd _)) dZ d0 ds dY dV hk
            base ext).err ∧
        Err.Below (mergePiece F W P (GS Reading.gl (planNums P h ui sv hsv hn) (noRd _)) dZ d0 ds dY
          dV hk base ext).err ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  merge_table_of (planNums P h ui sv hsv hn) P rfl rfl (ofLay_pos h)
    (by
      show P.nMsg - (2 * P.lay.lk + 3) + 1 + 2 * P.lay.lk + 2 = P.nMsg
      omega)
    (fun _ u hu => ofLay_unit h _ u hu) L he hkd

end

/-- At the reference parameters' layout and the last unit the place is the head's. -/
theorem head_is_plan (P : HeadMergeP) {s : WsShape} (Z : OnBytes.Road.SizedW s Inst.Model.ppref)
    (h : wsLayOf s true Inst.Model.Layout.kRef = .ok P.lay) :
    headPlace Z h = planPlace P h ⟨P.lay.U.size - 1, by rw [head_size Z h]; decide⟩ := rfl

/-! ### A rule for the slot of the claim's value -/

/-- How many scalars a declared round sends. -/
def scalarsOf (r : Fmt.DeclaredRound) : ℕ :=
  (r.entry.msg - 24 * r.entry.answers - 32 * r.entry.roots) / 24

/-- The scalars sent in the rounds from number a up to and not including b. -/
def sentIn (D : List Fmt.DeclaredRound) (a b : ℕ) : ℕ :=
  ((D.take b).drop a).foldl (fun n r => n + scalarsOf r) 0

/-- The rule. -/
def svOf (D : List Fmt.DeclaredRound) (h0 a b : ℕ) : ℕ :=
  match (((List.range (b - a)).filterMap fun i =>
      match D[a + i]? with
      | some r =>
        if r.entry.name == RoundName.pscValues.name then some (sentIn D h0 (a + i), scalarsOf r)
        else none
      | none => none).filter fun x => x.2 == 2).getLast? with
  | some x => x.1 + 1
  | none => 0

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_table_plan
#print axioms VerifiableInference.Desc.First.MergeLaw.head_is_plan
