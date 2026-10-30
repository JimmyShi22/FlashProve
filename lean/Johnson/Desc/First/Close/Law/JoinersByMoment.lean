-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/JoinersByMoment.lean: WHO JOINS A LINK's GROUP (`joinersAt`,
ReqKept.lean, beside this file), PARTED AS THE PROGRAM's SENDINGS PART THEM: the code switching's
main message; the kept copies; the link's own messages of the moments 0, 1 and 2. Definitions,
statements and proofs.

Why. `shapesAre_full` (ShapesOfIds.lean) asks that a group's flags and its members' shapes are the
joiners'. A walk along the chain has them sending by sending: what the code switching joins, then
what each of the link's three sendings joins (`ReqFrame.atMoment`, OnBytes/Iop/Req.lean: the present
link's messages of one moment).
  `momentOf s l m`: the messages of link l of the shape s that are sent at the moment m.
    `atMoment_eq`: it is `f.atMoment m` at every frame f with f.shape = s and f.link = l.
  `byMoment s l`: a test: link l's messages are those of the moments 0, 1, 2, one behind the other.
    `by_moment_full`, `by_moment_small`: so it is at all 25 (5) links: by the kernel.
  `joiners_parts`: where `byMoment s l` says yes and l is not 0: `joinersAt s l` is: (the target's
    shape, false); the target's kept copies, each with its shape and its flag "kept again"; then the
    three moments' messages, each with its shape and "its life is above 0". `joiners_parts_zero`: at
    l = 0: the three moments' messages alone.
  `snd_zip_left`, `snd_zip_right`: two lemmas on lists for whoever holds numbers zipped with these
    messages: the numbers fall away under a map that reads the message alone.
Limits. Lists alone: nothing is said of a verifier's state. That a frame in front of a sending has
the shape, the link and the moment is other files' to show. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.ReqKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Params
open VerifiableInference.Desc.ReqLit

/-- The messages of link l that are sent at the moment m. -/
def momentOf (s : ReqShape) (l m : ℕ) : List ReqMessage :=
  ((s.link[l]?.map (·.messages)).getD []).filter fun x => x.moment == m

theorem atMoment_eq {f : ReqFrame} {s : ReqShape} {l : ℕ} (hs : f.shape = s) (hl : f.link = l)
    (m : ℕ) : f.atMoment m = momentOf s l m := by
  unfold ReqFrame.atMoment momentOf
  rw [hs, hl]

/-- Link l's messages are those of the moments 0, 1, 2, one behind the other. -/
def byMoment (s : ReqShape) (l : ℕ) : Bool :=
  decide ((s.link.getD l ⟨0, []⟩).messages = momentOf s l 0 ++ momentOf s l 1 ++ momentOf s l 2)

set_option maxRecDepth 100000 in
theorem by_moment_full : ((List.range 25).all fun l => byMoment shapeFull l) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem by_moment_small : ((List.range 5).all fun l => byMoment shapeSmall l) = true := by
  decide +kernel

/-- **The joiners, sending by sending**, at a link behind the first. -/
theorem joiners_parts {s : ReqShape} {l : ℕ} (h : byMoment s l = true) (hl : l ≠ 0) :
    joinersAt s l =
      (((reqGroups s).getD l {}).target.shape, false) ::
        (((reqGroups s).getD l {}).target.kept.toList.map fun k => (k.shape, k.keptAgain)) ++
      (momentOf s l 0).map (fun m => (m.shape, decide (0 < m.life))) ++
      (momentOf s l 1).map (fun m => (m.shape, decide (0 < m.life))) ++
      (momentOf s l 2).map (fun m => (m.shape, decide (0 < m.life))) := by
  unfold joinersAt
  have hb : (l == 0) = false := by simpa using hl
  rw [of_decide_eq_true h]
  simp [hb]

/-- At the first link. -/
theorem joiners_parts_zero {s : ReqShape} (h : byMoment s 0 = true) :
    joinersAt s 0 =
      (momentOf s 0 0).map (fun m => (m.shape, decide (0 < m.life))) ++
      (momentOf s 0 1).map (fun m => (m.shape, decide (0 < m.life))) ++
      (momentOf s 0 2).map (fun m => (m.shape, decide (0 < m.life))) := by
  unfold joinersAt
  rw [of_decide_eq_true h]
  simp

/-- Numbers zipped in front fall away under a map that reads the second alone. -/
theorem snd_zip_left {α β γ : Type} (a : List α) (b : List β) (g : β → γ)
    (h : a.length = b.length) : (a.zip b).map (fun p => g p.2) = b.map g := by
  have e : (a.zip b).map Prod.snd = b := List.map_snd_zip (by omega)
  calc (a.zip b).map (fun p => g p.2) = ((a.zip b).map Prod.snd).map g := by
        rw [List.map_map]; rfl
    _ = b.map g := by rw [e]

/-- Numbers zipped behind fall away under a map that reads the first alone. -/
theorem snd_zip_right {α β γ : Type} (a : List α) (b : List β) (g : α → γ)
    (h : a.length = b.length) : (a.zip b).map (fun p => g p.1) = a.map g := by
  have e : (a.zip b).map Prod.fst = a := List.map_fst_zip (by omega)
  calc (a.zip b).map (fun p => g p.1) = ((a.zip b).map Prod.fst).map g := by
        rw [List.map_map]; rfl
    _ = a.map g := by rw [e]

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.by_moment_full
#print axioms VerifiableInference.Desc.First.Close.by_moment_small
#print axioms VerifiableInference.Desc.First.Close.joiners_parts
#print axioms VerifiableInference.Desc.First.Close.joiners_parts_zero
