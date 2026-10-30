-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/AskGroups.lean

What is here. The layout of the committed weights: the groups of indices of the unit that a layer
asks for, kind by kind, each with its name, its number of indices and its class TOGETHER (the
library has the names with the classes, and the numbers, in separate lists:
Johnson/Road/FormsKeysWLay.lean, FormsKeysWv.lean). Placing a unit changes none of the three. One
definition; statements and proofs. On the library's list of asked units (layerAsks) alone.

  `askRs s l X`     name, number of indices and class of each group of the unit of kind X of
                    layer l.
  `ask_groups`      the groups of an asked unit are these.
  `placed_three`    placing changes none of the three.
  **`grp_in_ask`**    a placed group of an asked unit is one of the list.
  `grpE`            a group of the class 'E' whose numbers fit: R = o 2^z.

Not shown here. Anything on a layout that the verifier returns, on a claim or on a value: the
statements speak of the library's list of asked units. Kinds 0 to 11 alone.
No property is claimed.
-/
import Johnson.Road.FormsKeysWLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road

/-- Name, number of indices and class of each group of the unit of kind X of layer l, in order.
Above kind 11 it gives kind 11's list, and it gives a list also at a kind that the layer lacks: the
statements call it at asked units alone. -/
def askRs (s : WsShape) (l X : ℕ) : List (String × ℕ × Char) :=
  if X = 0 then [("hd", 64, 'A'), ("cd", s.dh, 'A'), ("kk", s.d, 'E')]
  else if X = 1 then [("kk", s.d, 'E'), ("x", s.dkv, 'E')]
  else if X = 2 then [("kk", s.dq, 'E'), ("x", s.d, 'E')]
  else if X = 3 ∨ X = 4 then [("kk", s.d, 'E'), ("x", s.f, 'E')]
  else if X = 5 ∨ X = 6 then [("kk", s.d, 'E'), ("x", s.fe, 'E')]
  else if X = 7 ∨ X = 8 then [("kk", s.d, 'E'), ("e", s.NE, 'E'), ("x", s.fe, 'E')]
  else if X = 9 then
    [("kk", if s.moe.getD l false = true then s.fe else s.f, 'E'), ("x", s.d, 'E')]
  else if X = 10 then [("kk", s.fe, 'E'), ("e", s.NE, 'E'), ("x", s.d, 'E')]
  else [("kk", s.d, 'E'), ("x", s.NE, 'E')]

/-- The groups of an asked unit are those of askRs. -/
theorem ask_groups {s : WsShape} {l : ℕ} {a : AskW} (ha : a ∈ layerAsks s l) :
    a.g.map (fun x => (x.name, x.R, x.cls)) = askRs s l a.X := by
  unfold layerAsks at ha
  by_cases hm : s.moe.getD l false = true
  · rw [if_pos hm] at ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with e | e | e | e | e | e | e | e | e | e <;> subst e <;>
      first | rfl | (unfold askRs; simp [hm, WsLay.E_])
  · rw [if_neg hm] at ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with e | e | e | e | e | e <;> subst e <;>
      first | rfl | (unfold askRs; simp [hm, WsLay.E_])

/-- Placing a group changes neither its name, nor its number of indices, nor its class. -/
theorem placed_three : ∀ (g : List WsGrp) (left cb : ℕ),
    (placeP g left cb).map (fun y => (y.name, y.R, y.cls)) = g.map fun y => (y.name, y.R, y.cls)
  | [], _, _ => rfl
  | x :: g, left, cb => by
    show (x.name, x.R, x.cls) ::
        (placeP g (left - tP x left) (cb + tP x left)).map (fun y => (y.name, y.R, y.cls)) =
      (x.name, x.R, x.cls) :: g.map fun y => (y.name, y.R, y.cls)
    rw [placed_three g]

/-- **A placed group of an asked unit is one of the list askRs.** -/
theorem grp_in_ask {s : WsShape} {l : ℕ} {a : AskW} (ha : a ∈ layerAsks s l) {lk : ℕ} {G : WsGrp}
    (hG : G ∈ placeP a.g lk 0) : (G.name, G.R, G.cls) ∈ askRs s l a.X := by
  rw [← ask_groups ha, ← placed_three a.g lk 0]
  exact List.mem_map_of_mem (f := fun y : WsGrp => (y.name, y.R, y.cls)) hG

/-- A group of the class 'E' whose numbers fit each other: R = o 2^z. -/
theorem grpE {G : WsGrp} (hok : GrpOK G) (hE : G.cls = 'E') : G.R = G.o * 2 ^ G.z := by
  rcases hok with ⟨-, h, -⟩ | ⟨hA, -⟩
  · exact h
  · rw [hE] at hA
    exact absurd hA (by decide)

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.ask_groups
#print axioms OnBytes.Road.K4.C.placed_three
#print axioms OnBytes.Road.K4.C.grp_in_ask
#print axioms OnBytes.Road.K4.C.grpE
