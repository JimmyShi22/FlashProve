-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/KeptPlaces.lean: THE FOUR CLAUSES `member` · `kept` · `names` · `places`
OF `FrontFitsAt` (CarryAtFull.lean) AT THE PROGRAM's OWN LAYOUT (`groupLayK cs lo s e kb hM hZ`),
THE NUMBERING no, ix a := posOf lo a.1 AND THE CLOSING's FILES' OWN NAMES `namesOf … no`
(Johnson/Desc/First/Close/Law/NamesOfShapes.lean). Theorems. It changes no other file.

  `frame_kept`: the front's frame's kept place number a, where the switch's list of kept members
    has the number o at a: its `old` is o, its rows and bits of rows are those of o's shape in the
    front's statement (off `frame_fields`, Johnson/Top/H/SwitchMapsCheck.lean, and
    `kept_rec`, SwitchKeptRec.lean).
  `KeptOrder lo kb kl L`: each kept member i of the list stands, among the layout's members with
    the flag «kept», at the place that i's number has in the list kl.
  `keptNosOf lo kb` (with code), `keptNos_of_shapes`, `keptOrder_of_shapes`: KeptOrder from
    ShapesAre · L.members = G.members · L.kept = G.kept · a sentence on lo, kb and kl alone.
  `member_at`: ShapesAre T G lo kb no · L.members = G.members ⊢ the layout's member number posOf lo
    i is no i.
  `kept_at`, `names_at`, `places_at`: **the front's frame is W₀ · KeptOrder at the front's rows'
    layout · the clause member · the front's statement has the written shape at no i ⊢ the three
    clauses**, N := namesOf cs lo s e kb hM hZ no.
Limits. `KeptOrder`, `ShapesAre` and «the written shape at no i» are premises. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.CarryAtFull
import Johnson.Desc.First.Close.Law.NamesOfShapes
import Johnson.Top.H0.K2Hears.KeptNos
import Johnson.Top.H.SwitchKeptRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice OnBytes.Params Cb Johnson.Top.H Johnson.Pack Johnson.G
open VerifiableInference.Desc.Own (keptNos switchKept_at)
open VerifiableInference.Desc.First.Close (groupLayK namesOf posOf membersOf ShapesAre pos_get)

/-- **THE FRAME's KEPT PLACE NUMBER a.** -/
theorem frame_kept {fx : _root_.Tw.K2.Front} {W₀ : SwitchFrame}
    (hW : First.K2.frameAt fx = some W₀) {a o : ℕ} (ho : (switchKept fx.f.rows)[a]? = some o) :
    ∃ k, W₀.kept[a]? = some k ∧ k.old = o ∧
      k.rows = ((First.K2.skelOf fx).oracles.getD o default).shape.mainRows ∧
      k.rowBits = ceilLog2 ((First.K2.skelOf fx).oracles.getD o default).shape.mainRows := by
  obtain ⟨-, -, -, -, -, -, -, f8⟩ := frame_fields _ _ _ _ _ W₀ hW
  have ha : a < (switchKept fx.f.rows).size := (Array.getElem?_eq_some_iff.1 ho).1
  have hlen : a < W₀.kept.length := by
    rw [f8, List.length_map, List.length_range]
    exact ha
  obtain ⟨hi, e1, e2, e3, -⟩ := kept_rec _ _ _ _ _ W₀ hW a W₀.kept[a]
    (List.getElem?_eq_getElem hlen)
  have eo : (switchKept fx.f.rows)[a] = o := by
    rw [Array.getElem?_eq_getElem hi] at ho
    exact Option.some.inj ho
  rw [eo] at e1 e2 e3
  exact ⟨_, List.getElem?_eq_getElem hlen, e1, e2, e3⟩

/-- Each kept member stands, among the layout's kept members, where its number stands in kl. -/
def KeptOrder (lo : List (OracleShape × ℕ)) (kb : Fin lo.length → Bool) (kl : List ℕ)
    (L : GroupLayout) : Prop :=
  ∀ i : Fin lo.length, memMain lo i → kb i = true →
    (keptNos L)[kl.idxOf i.val]? = some (posOf lo i)

/-- The places, among a list's members, of those with the flag. With code. -/
def keptNosOf (lo : List (OracleShape × ℕ)) (kb : Fin lo.length → Bool) : List ℕ :=
  (List.range (membersOf lo).length).filter fun w => ((membersOf lo).map kb).getD w false

/-- A layout whose members and flags are a group's that holds the written list's members has its
kept members at these places. -/
theorem keptNos_of_shapes {lo : List (OracleShape × ℕ)} {kb : Fin lo.length → Bool}
    {no : Fin lo.length → ℕ} {T : Statement} {G : Group} {L : GroupLayout}
    (H : ShapesAre T G lo kb no) (hLm : L.members = G.members) (hLk : L.kept = G.kept) :
    keptNos L = keptNosOf lo kb := by
  have hs : L.members.size = (membersOf lo).length := by
    rw [hLm, ← Array.length_toList, H.members, List.length_map]
  have hk : ∀ w, L.kept.getD w false = ((membersOf lo).map kb).getD w false := fun w => by
    rw [hLk, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, H.kept,
      List.getD_eq_getElem?_getD]
  unfold keptNos keptNosOf
  rw [hs]
  exact List.filter_congr fun w _ => hk w

/-- **KeptOrder FROM A SENTENCE ON THE WRITTEN LIST, THE FLAGS AND kl ALONE** (closed where these
are closed terms). -/
theorem keptOrder_of_shapes {lo : List (OracleShape × ℕ)} {kb : Fin lo.length → Bool}
    {no : Fin lo.length → ℕ} {T : Statement} {G : Group} {L : GroupLayout} {kl : List ℕ}
    (H : ShapesAre T G lo kb no) (hLm : L.members = G.members) (hLk : L.kept = G.kept)
    (h : ∀ i : Fin lo.length, memMain lo i → kb i = true →
      (keptNosOf lo kb)[kl.idxOf i.val]? = some (posOf lo i)) : KeptOrder lo kb kl L := by
  intro i hi hk
  rw [keptNos_of_shapes H hLm hLk]
  exact h i hi hk

/-- **THE CLAUSE member.** -/
theorem member_at {lo : List (OracleShape × ℕ)} {kb : Fin lo.length → Bool}
    {no : Fin lo.length → ℕ} {T : Statement} {G : Group} {L : GroupLayout}
    (H : ShapesAre T G lo kb no) (hLm : L.members = G.members) (i : Fin lo.length)
    (hi : i ∈ membersOf lo) : L.members[posOf lo i]? = some (no i) := by
  rw [hLm, ← Array.getElem?_toList, H.members, List.getElem?_map, pos_get lo i hi]
  rfl

section
variable (cs : Codes) (lo : List (OracleShape × ℕ)) (s : Sg) (e : ℕ) (kb : Fin lo.length → Bool)
  (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
  (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)
  (no : Fin lo.length → ℕ) (kl : List ℕ) {fx : _root_.Tw.K2.Front} {W₀ : SwitchFrame}
  (hW : First.K2.frameAt fx = some W₀) (hO : KeptOrder lo kb kl fx.f.rows.layout)
  (hno : ∀ a : {i // memMain lo i}, fx.f.rows.layout.members[posOf lo a.1]? = some (no a.1))
  (hsh : ∀ a : {i // memMain lo i}, ∃ xo, (First.K2.skelOf fx).oracles[no a.1]? = some xo ∧
    xo.shape = (lo.get a.1).1)
include hW hO hno hsh

/-- What the frame has at a kept slot's member's place. -/
theorem slot_place (κ : (groupLayK cs lo s e kb hM hZ).Kp) :
    ∃ k, W₀.kept[kl.idxOf κ.1.1.1.val]? = some k ∧ k.old = no κ.1.1.1 ∧
      k.rows = (lo.get κ.1.1.1).1.mainRows ∧
      k.rowBits = ceilLog2 (lo.get κ.1.1.1).1.mainRows := by
  have h1 := switchKept_at fx.f.rows _ _ (hO κ.1.1.1 κ.1.1.2 κ.1.2)
  have h2 := hno κ.1.1
  have eg : fx.f.rows.layout.members.getD (posOf lo κ.1.1.1) 0 = no κ.1.1.1 := by
    rw [Array.getD_eq_getD_getElem?, h2]
    rfl
  rw [eg] at h1
  obtain ⟨k, k1, k2, k3, k4⟩ := frame_kept hW h1
  obtain ⟨xo, x1, x2⟩ := hsh κ.1.1
  have ex : (First.K2.skelOf fx).oracles.getD (no κ.1.1.1) default = xo := by
    rw [Array.getD_eq_getD_getElem?, x1]
    rfl
  refine ⟨k, k1, k2, ?_, ?_⟩
  · rw [k3, ex, x2]
  · rw [k4, ex, x2]

/-- **THE CLAUSE kept.** -/
theorem kept_at (κ : (groupLayK cs lo s e kb hM hZ).Kp) :
    ∃ k, W₀.kept[kl.idxOf κ.1.1.1.val]? = some k ∧ k.old = no κ.1.1.1 ∧ κ.2.val < k.rows := by
  obtain ⟨k, k1, k2, k3, _⟩ := slot_place cs lo s e kb hM hZ no kl hW hO hno hsh κ
  exact ⟨k, k1, k2, by rw [k3]; exact κ.2.isLt⟩

/-- **THE CLAUSE names.** -/
theorem names_at (κ : (groupLayK cs lo s e kb hM hZ).Kp) :
    (namesOf cs lo s e kb hM hZ no).orc κ =
      (W₀.kept.getD (kl.idxOf κ.1.1.1.val) ⟨0, 0, 0, 0, [], 0⟩).old := by
  obtain ⟨k, k1, k2, _, _⟩ := slot_place cs lo s e kb hM hZ no kl hW hO hno hsh κ
  rw [List.getD_eq_getElem?_getD, k1]
  exact k2.symm

/-- **THE CLAUSE places.** -/
theorem places_at (κ : (groupLayK cs lo s e kb hM hZ).Kp)
    (x : (groupLayK cs lo s e kb hM hZ).s.cM.J) :
    (namesOf cs lo s e kb hM hZ no).idx κ x = κ.2.val +
      2 ^ (W₀.kept.getD (kl.idxOf κ.1.1.1.val) ⟨0, 0, 0, 0, [], 0⟩).rowBits * x.val := by
  obtain ⟨k, k1, _, _, k4⟩ := slot_place cs lo s e kb hM hZ no kl hW hO hno hsh κ
  rw [List.getD_eq_getElem?_getD, k1]
  show κ.2.val + x.val * 2 ^ ceilLog2 (lo.get κ.1.1.1).1.mainRows = κ.2.val + 2 ^ k.rowBits * x.val
  rw [k4, Nat.mul_comm]

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.frame_kept
#print axioms VerifiableInference.Desc.LinkJoin.keptOrder_of_shapes
#print axioms VerifiableInference.Desc.LinkJoin.member_at
#print axioms VerifiableInference.Desc.LinkJoin.slot_place
#print axioms VerifiableInference.Desc.LinkJoin.kept_at
#print axioms VerifiableInference.Desc.LinkJoin.names_at
#print axioms VerifiableInference.Desc.LinkJoin.places_at
