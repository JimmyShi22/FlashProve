-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Shape/HeardTop.lean: conditional, from a return: the shape of what
the seated hearing of a lookup returns is `lookHeardSh` (Honest/K3/Shape/HeardOps.lean): all fifteen
fields of `heardAll` (Johnson/Desc/First/Shape/Tail.lean) as code of the shape
h, the ledger's count of slots and the length of its list of owed claims. Theorems.

Terms. Honest/K3/GLOSSARY.md: see there hearing, heard structure, seat, ledger, slot and shape.
`Sized F` says that the ledger's three arrays have their size.

What is shown.
  `heardAll_ext`: two shapes with the same fifteen fields (`h1` to `h15`) are one.
  `hearVia_heard`: Sized F → p.shape = some h → hearVia p F rs = some (H, G) → heardAll H =
    lookHeardSh h F.next F.owed.size.
Helper: `leaf_degrees`.

Hypotheses that remain, in `hearVia_heard`.
  `hS`: `Sized F`.
  `hs`: the parameters make the shape h.
  `hv`: the seated hearing returns.

How the proof goes. It rests on `messagesV_out` (Honest/K3/Shape/HeardWalk.lean) and on
`heard_counts` (Honest/K3/Law/DigitsBehind.lean: the numbers of the three owed claims).

Users. Honest/K3/Law/Thread/CallsParts.lean, Honest/K3/Law/Thread/DigitsParts.lean and
Honest/K3/Law/Thread/HeadParts.lean import this file.

Limits. An implication. No statement of this file says that the hearing returns. An instance:
Honest/K3/Shape/HeardGuards.lean [not in this library] (by evaluation, at a synthetic shape).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Shape.HeardWalk
import Johnson.Desc.ProofFile.Honest.K3.Law.DigitsBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Shape
open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff)
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc.First.Shape (AffSh affSh PscSh pscSh HeardAll heardAll)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.K3 (HeardV hearV messagesV leafVars faceOf toHeard toHeardG toPsc
  weightOf)
open ProofFile.Honest.K3.Law (hearV_messages)
open ProofFile.Honest.K3.Law.Digits (heard_counts)

local notation "KFace" => VerifiableInference.Desc.K3.Face

theorem heardAll_ext (a b : HeardAll) (h1 : a.shape = b.shape) (h2 : a.rows = b.rows)
    (h3 : a.leaves = b.leaves) (h4 : a.sBit = b.sBit) (h5 : a.zx = b.zx) (h6 : a.zy = b.zy)
    (h7 : a.e = b.e) (h8 : a.cEnd = b.cEnd) (h9 : a.zb0 = b.zb0) (h10 : a.zb1 = b.zb1)
    (h11 : a.tT = b.tT) (h12 : a.zk = b.zk) (h13 : a.owedObjects = b.owedObjects)
    (h14 : a.owedPlanes = b.owedPlanes) (h15 : a.owedJoin = b.owedJoin) : a = b := by
  cases a
  cases b
  simp_all

/-- The degrees of the leaves' variables, as the verifier program's structure holds them. -/
theorem leaf_degrees (f : KFace) (z : Array E) :
    ((leafVars f z).map weightOf).toArray.toList.map (·.d) =
      (List.range (f.mu + f.d)).map fun j => if j < f.d then 3 else 2 := by
  simp [leafVars, weightOf, Function.comp_def, OnBytes.Psc.Weight.equality]

/-- **The shape of what the seated hearing returns.** Conditional on the parameters making the shape
h, the return, and `Sized` in front. An instance: Honest/K3/Shape/HeardGuards.lean
[not in this library] (by evaluation).
-/
theorem hearVia_heard {p : VerifiableInference.Desc.First.Look.P}
    {h : OnBytes.Model.Forest.Shape} {F G : Fork} {rs : List Fmt.RoundView}
    {H : OnBytes.Model.Forest.Heard} (hS : Sized F) (hs : p.shape = some h)
    (hv : VerifiableInference.Desc.K3.Law.hearVia p F rs = some (H, G)) :
    heardAll H = lookHeardSh h F.next F.owed.size := by
  unfold VerifiableInference.Desc.K3.Law.hearVia at hv
  split at hv
  · rename_i h' hs'
    obtain rfl : h' = h := Option.some.inj (hs'.symm.trans hs)
    split at hv
    · obtain ⟨x, hx, hv⟩ := Option.bind_eq_some_iff.1 hv
      obtain ⟨H', hH, e⟩ := Option.map_eq_some_iff.1 hv
      obtain ⟨gv, G'⟩ := x
      obtain rfl : H' = H := congrArg (·.1) e
      obtain ⟨hok, hm⟩ := hearV_messages hx
      obtain ⟨m1, m2, m3, m4, m5, ⟨z, m6⟩, m7, m8, m9⟩ := messagesV_out hS (parts_pos hok) hm
      obtain ⟨_, c1, c2, c3⟩ := heard_counts hm
      unfold toHeard at hH
      split at hH
      · rename_i point form hk
        dsimp only at hH
        split at hH
        · have eH := Option.some.inj hH
          have hk' : gv.keys = [(point, form)] := hk
          rw [hk'] at m5
          have key : (heardVSh (faceOf h') F.next).keys.headD (0, noSh) =
              (point.size, affSh form) := by
            rw [← m5]
            rfl
          have kz : ((heardVSh (faceOf h') F.next).keys.headD (0, noSh)).1 = point.size := by
            rw [key]
          have kf : ((heardVSh (faceOf h') F.next).keys.headD (0, noSh)).2 = affSh form := by
            rw [key]
          rw [← eH]
          refine heardAll_ext _ _ rfl m1 ?_ m4 ?_ ?_ ?_ kf.symm m8 m9 ?_ ?_ c1 c2 c3
          · show PscSh.mk false true ((gv.leaves.vars.map weightOf).toArray.toList.map (·.d))
              gv.leaves.r.toArray.size gv.leaves.first (affSh gv.leaves.start) false = _
            rw [m6, leaf_degrees, List.size_toArray, m7, m2, m3]
            rfl
          · show (point.extract 0 h'.dT).size = min h'.dT _ - 0
            rw [kz, Array.size_extract]
          · show (point.extract h'.dT point.size).size = min _ _ - h'.dT
            rw [kz, Array.size_extract]
          · show ((Array.range h'.NC).map _).size = h'.NC
            simp
          · show (h'.calls.map _).size = h'.calls.size
            simp
          · show ((Array.range h'.NC).map fun c =>
                (point.extract h'.dT point.size).extract (h'.rK - h'.iota.getD c 0)
                  (point.extract h'.dT point.size).size ++ point.extract 0 h'.dT).toList.map
                (·.size) = (List.range h'.NC).map fun c =>
                  (min (min _ _ - h'.dT) (min _ _ - h'.dT) - (h'.rK - h'.iota.getD c 0)) +
                    (min h'.dT _ - 0)
            rw [kz]
            simp [Function.comp_def, Array.size_extract]
            intro a _
            rw [Nat.min_def]
            split <;> omega
        · exact nomatch hH
      · exact nomatch hH
    · exact nomatch hv
  · exact nomatch hv

end ProofFile.Honest.K3.Shape

#print axioms ProofFile.Honest.K3.Shape.heardAll_ext
#print axioms ProofFile.Honest.K3.Shape.leaf_degrees
#print axioms ProofFile.Honest.K3.Shape.hearVia_heard
