-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/MergedPoint.lean: the honest side of the kind "lookup"
(K3): every call's key point ends in the whole of the lookup's point zx, as arrays of machine words.
So the test that the hearing of the layers' own kind makes on what the lookup has heard
("internal-g-merged-point", OnBytes/Desc/First/K4/Hear.lean: the last coordinates of all calls'
points are those of zx) accepts at every structure that `toHeard` makes: it depends on no sampled
value. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: zx and zk are fields of the heard structure: the
lookup's point and the calls' key points. `toHeard` (Johnson/Desc/First/Look/K3LookupGeneral.lean) makes
the heard structure. The other kind is the layers' own kind.

What is shown.
  `lastOf_append`: the last k coordinates of A ++ B are those of B, where B has k.
  `zk_ends`: each call's key point is some array, then zx: by the text of `toHeard`.
  `merged_each`: each call's key point has the last k coordinates of zx.
  `mapM_const`: if all members of a list answer z, together they answer a list of z's.
  `merged_point`: the other kind's three lines, to the letter: both readings return, and the test
    accepts.
  `zx_size`: behind the hearing zx has as many coordinates as a tree has levels.
  `merged_at`: the same as `merged_point` at the state behind the accepting step of the
    description's own member at a layers' link.

Hypotheses that remain.
  `hg`: `toHeard` returns.
  `hk`: k is at most the number of coordinates of zx. The other kind asks this by a public test in
    front: its number is at most the trees' depth.
  `hh`: (in `zx_size`) `hearV` returns.
  In `merged_at`: the hypotheses of `calls_here` (Honest/K3/Law/Thread/StateHere.lean): `O`, `hs`,
    `hd`, `hb`, `hbs`, `hm`, `hmp`, `hpk`, `h`.

Users. `merged_of_last` (Honest/K3/Law/Thread/LookRest.lean) calls `merged_point`; `merged_link`
(Honest/K3/Law/Thread/AtLink.lean) calls `merged_at`.

Limits. Conditional on the hypotheses above. No instance of these hypotheses is exhibited in this
file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.PutFo
import Johnson.Desc.ProofFile.Honest.K3.Law.Seated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes (E)
open OnBytes.Model (Fork lastOf cutLast)
open OnBytes.Model.Forest (Shape)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (HeardV HeardG hearV toHeard toHeardG faceOf)

local notation "FS" => VerifiableInference.Desc.First.S

/-- The last k coordinates of A ++ B are those of B, where B has k. -/
theorem lastOf_append (A B : Array E) (k : Nat) (hk : k ≤ B.size) :
    lastOf (A ++ B) k = lastOf B k := by
  have e : (A ++ B).extract ((A ++ B).size - k) (A ++ B).size = B.extract (B.size - k) B.size := by
    rw [Array.size_append, Array.extract_append,
      Array.extract_empty_of_size_le_start (show A.size ≤ A.size + B.size - k by omega),
      Array.empty_append]
    congr 1 <;> omega
  unfold lastOf cutLast
  have h1 : ¬ k > (A ++ B).size := by rw [Array.size_append]; omega
  have h2 : ¬ k > B.size := by omega
  rw [if_neg h1, if_neg h2]
  show (Except.ok _ : Except String (Array E)) = Except.ok _
  rw [e]

/-- **Each call's key point is some array, then zx.** Conditional on the return of `toHeard`. -/
theorem zk_ends {h : Shape} {g : HeardG} {H : OnBytes.Model.Forest.Heard}
    (hg : toHeard h g = some H) : ∀ zk ∈ H.zk.toList, ∃ A, zk = A ++ H.zx := by
  unfold toHeard at hg
  split at hg
  · simp only at hg
    split at hg
    · cases hg
      intro zk hz
      simp only [Array.toList_map, List.mem_map] at hz
      obtain ⟨c, _, rfl⟩ := hz
      exact ⟨_, rfl⟩
    · cases hg
  · cases hg

/-- **Each call's key point has the last k coordinates of zx.** Conditional on the return of
`toHeard`, and on zx having k coordinates. -/
theorem merged_each {h : Shape} {g : HeardG} {H : OnBytes.Model.Forest.Heard}
    (hg : toHeard h g = some H) (k : Nat) (hk : k ≤ H.zx.size) :
    ∀ zk ∈ H.zk.toList, lastOf zk k = lastOf H.zx k := by
  intro zk hz
  obtain ⟨A, rfl⟩ := zk_ends hg zk hz
  exact lastOf_append A H.zx k hk

/-- If all members of a list answer z, together they answer a list of z's. -/
theorem mapM_const {α β : Type} (f : α → Option β) (z : β) :
    ∀ l : List α, (∀ x ∈ l, f x = some z) → l.mapM f = some (l.map fun _ => z)
  | [], _ => rfl
  | x :: l, hl => by
    rw [List.mapM_cons, hl x (List.mem_cons_self ..),
      mapM_const f z l fun y hy => hl y (List.mem_cons_of_mem _ hy)]
    rfl

/-- **The other kind's three lines, to the letter**: both readings return, and the test accepts.
Conditional on the return of `toHeard`, and on zx having k coordinates. -/
theorem merged_point {h : Shape} {g : HeardG} {H : OnBytes.Model.Forest.Heard}
    (hg : toHeard h g = some H) (k : Nat) (hk : k ≤ H.zx.size) :
    ∃ Z ends, (lastOf H.zx k).toOption = some Z ∧
      (H.zk.mapM fun zk => (lastOf zk k).toOption) = some ends ∧
      ends.all (· == Z) = true := by
  have hZ : (lastOf H.zx k).toOption = some (H.zx.extract (H.zx.size - k) H.zx.size) := by
    unfold lastOf cutLast
    rw [if_neg (by omega)]
    rfl
  refine ⟨_, (H.zk.toList.map fun _ => H.zx.extract (H.zx.size - k) H.zx.size).toArray, hZ, ?_, ?_⟩
  · rw [Array.mapM_eq_mapM_toList, mapM_const _ _ _ fun zk hz => by
      rw [merged_each hg k hk zk hz]; exact hZ]
    rfl
  · rw [List.all_toArray]
    refine List.all_eq_true.2 fun x hx => ?_
    obtain ⟨_, _, rfl⟩ := List.mem_map.1 hx
    exact beq_self_eq_true _

/-- **Behind the hearing zx has as many coordinates as a tree has levels.** Conditional on the
return of `hearV` and on the structure that `toHeard` makes. -/
theorem zx_size (h : Shape) {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    {H : OnBytes.Model.Forest.Heard} (hh : hearV (faceOf h) F rs = some (g, G))
    (hg : toHeard h (toHeardG g) = some H) : H.zx.size = h.dT := by
  obtain ⟨pt, form, hk, hsz⟩ := keys_of_hearV h hh
  unfold toHeard at hg
  have hk' : (toHeardG g).keys = [(pt, form)] := hk
  rw [hk'] at hg
  simp only at hg
  split at hg
  · cases hg
    show (pt.extract 0 h.dT).size = h.dT
    rw [Array.size_extract, hsz]
    show min h.dT (h.dT + h.rK) - 0 = h.dT
    omega
  · cases hg

/-- **At the state behind the member's accepting step at a layers' link**, in the form in which the
layers' own kind reads the state. Conditional on the hypotheses of `calls_here`. No instance of
these hypotheses is exhibited in this file. -/
theorem merged_at (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = false) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true) (ft : Nat) (sj sj' : FS) (n : Nat)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : m.step ft sj rs c = .ok (sj', n)) :
    ∀ a fo, sj'.here = .lay a → a.fo = some fo → ∀ k, k ≤ fo.shape.dT →
      ∃ Zp ends, (lastOf fo.zx k).toOption = some Zp ∧
        (fo.zk.mapM fun zk => (lastOf zk k).toOption) = some ends ∧
        ends.all (· == Zp) = true := by
  intro a fo ha hfo k hk
  obtain ⟨F, H, G, _, hv, hput⟩ := member_back_fo o pol lay KL Fd Z Bs base ch A B O s hs hd lot m
    hb hbs hm hmp hpk ft sj sj' n rs c h
  obtain rfl : H = fo := Option.some.inj ((hput a ha).1.symm.trans hfo)
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs'
  obtain ⟨_, f2, _⟩ := site_facts _ _ x s hsx
  obtain ⟨g, hg, hH⟩ := hearVia_back f2 hv
  refine merged_point hH k ?_
  rw [zx_size s.shape hg hH, ← (toHeard_fields hH).1]
  exact hk

#print axioms ProofFile.Honest.K3.Law.AtThr.lastOf_append
#print axioms ProofFile.Honest.K3.Law.AtThr.zk_ends
#print axioms ProofFile.Honest.K3.Law.AtThr.merged_each
#print axioms ProofFile.Honest.K3.Law.AtThr.mapM_const
#print axioms ProofFile.Honest.K3.Law.AtThr.merged_point
#print axioms ProofFile.Honest.K3.Law.AtThr.zx_size
#print axioms ProofFile.Honest.K3.Law.AtThr.merged_at

end ProofFile.Honest.K3.Law.AtThr
