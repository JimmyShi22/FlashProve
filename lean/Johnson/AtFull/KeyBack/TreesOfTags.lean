-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/TreesOfTags.lean: A CHAIN's TREES AS A TERM THAT THE KERNEL CAN EVALUATE.
General laws on `sentAt` (Johnson/G/RoundsOfPlan.lean). Statements with proofs. Nothing is
evaluated.

`treesOf c off e` (TreesKOfRounds.lean) holds `sendTag`, which cuts a label by `String.splitOn`
and reads a numeral by `String.toNat?`, and a `List.mergeSort`. By report alone the
kernel refuses the first two (Johnson/AtFull/KeyBack/SentKey.lean goes behind
Johnson/Unfolds/'s laws on the two); at the third it was seen to stop. Here the tags are
handed in as a list, and the sort is the bounded text `sortF`
(Johnson/Unfolds/MergeSort.lean).

  `sentTagged`: `sentAt`'s closing text with the tag handed in. `sentsTagged`: along a chain.
  `treesRun c ts off e`: the trees, sorted by rounds and numbered, of these.
  `sentAt_value`, `sentAt_of_tag`, `mapM_of_tags`: where `sentAt` returns, its value is
    `sentTagged`'s at the label's tag.
  `treesOf_eq`: `treesOf c off e = treesRun c ts off e`, where ts are the labels' tags and
    `sentAt` returns at every sending.
IT TAKES A RETURN: that `sentAt` returns at any chain, and which tags its labels have,
is not shown here.
Limits. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.TreesKOfRounds
import Johnson.Unfolds.MergeSort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G (ChainSends Sending)
open Johnson.G.OfPlan
open Johnson.Unfolds (sortedW sentsOf ok_of_isOk)

/-- `sentAt`'s closing text with the tag handed in; [] where no trees can be laid, which is not
reached where `sentAt` returns. -/
def sentTagged (codes : Codes) (off : Nat) (x : Sending) (tag : SendTag) : List Sent :=
  match layTrees codes x.sent.toArray with
  | some L => L.shapes.toList.zipIdx.map fun (t, i) =>
      let j := (List.range x.sent.length).find? fun j => L.tree.getD j 0 == i
      ⟨x.entry - 1 - off, t.logN, t.mainWidth + t.maskWidth,
        ((j.bind fun j => x.sent[j]?).map (·.leafClass)).getD 0, tag⟩
  | none => []

/-- The same along a chain's sendings and a list of their tags. -/
def sentsTagged (codes : Codes) (off : Nat) :
    List Sending → List (Option SendTag) → List (List Sent)
  | x :: xs, some t :: ts => sentTagged codes off x t :: sentsTagged codes off xs ts
  | _, _ => []

/-- A chain's trees, sorted by rounds and numbered, with neither `sendTag` nor `List.mergeSort`. -/
def treesRun (c : ChainSends) (ts : List (Option SendTag)) (off : Nat) (e : List Sent) :
    List (Sent × Nat) :=
  ((Johnson.Unfolds.sortF (fun a b => decide (a.round ≤ b.round))
    (((sentsTagged c.codes off c.sends ts).flatten ++ e).length + 1)
    ((sentsTagged c.codes off c.sends ts).flatten ++ e)).getD []).zipIdx

/-- Where `sentAt` returns, the label has a tag, and the value is `sentTagged`'s at it. -/
theorem sentAt_value {a : String} {codes : Codes} {off : Nat} {x : Sending} {s : List Sent}
    (h : sentAt a codes off x = .ok s) :
    ∃ t, sendTag x.label = some t ∧ s = sentTagged codes off x t := by
  unfold sentAt at h
  dsimp only at h
  split at h
  · rename_i t ht
    obtain ⟨t', hy, h⟩ := ok_of_bind h
    obtain rfl := Except.ok.inj hy
    refine ⟨t, ht, ?_⟩
    split at h
    · rename_i L hlt
      obtain ⟨L', hL', h⟩ := ok_of_bind h
      obtain rfl := Except.ok.inj hL'
      unfold sentTagged
      rw [hlt]
      exact (Except.ok.inj h).symm
    · obtain ⟨_, hy, _⟩ := ok_of_bind h
      exact nomatch hy
  · obtain ⟨_, hy, _⟩ := ok_of_bind h
    exact nomatch hy

/-- (E1) -/
theorem sentAt_of_tag {a : String} {codes : Codes} {off : Nat} {x : Sending} {tag : SendTag}
    {s : List Sent} (ht : sendTag x.label = some tag) (h : sentAt a codes off x = .ok s) :
    s = sentTagged codes off x tag := by
  obtain ⟨t, ht', hs⟩ := sentAt_value h
  obtain rfl : t = tag := Option.some.inj (ht'.symm.trans ht)
  exact hs

/-- (E2) -/
theorem mapM_of_tags (a : String) (codes : Codes) (off : Nat) :
    ∀ (xs : List Sending) (ts : List (Option SendTag)) (ls : List (List Sent)),
      (xs.map (·.label)).map sendTag = ts → xs.mapM (sentAt a codes off) = .ok ls →
      ls = sentsTagged codes off xs ts
  | [], ts, ls, ht, h => by
    rw [List.mapM_nil] at h
    obtain rfl := Except.ok.inj h
    subst ht
    rfl
  | x :: xs, ts, ls, ht, h => by
    rw [List.mapM_cons] at h
    obtain ⟨s, hs, h⟩ := ok_of_bind h
    obtain ⟨ss, hss, h⟩ := ok_of_bind h
    obtain rfl := Except.ok.inj h
    subst ht
    obtain ⟨t, htag, hv⟩ := sentAt_value hs
    simp only [List.map_cons, htag, sentsTagged]
    rw [hv, mapM_of_tags a codes off xs _ ss rfl hss]

/-- (E3) **The trees as a term that the kernel can evaluate.** -/
theorem treesOf_eq (c : ChainSends) (ts : List (Option SendTag)) (off : Nat) (e : List Sent)
    (ht : (c.sends.map (·.label)).map sendTag = ts)
    (hs : (c.sends.mapM (sentAt "" c.codes off)).isOk = true) :
    treesOf c off e = treesRun c ts off e := by
  have e1 : sentsOf c off = sentsTagged c.codes off c.sends ts :=
    mapM_of_tags "" c.codes off c.sends ts _ ht (ok_of_isOk [] hs)
  unfold treesRun
  show (sortedW (sentsOf c off) e).zipIdx = _
  rw [e1]
  unfold sortedW
  rw [Johnson.Unfolds.mergeSort_eq]

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.sentAt_value
#print axioms Johnson.AtFull.KeyBack.sentAt_of_tag
#print axioms Johnson.AtFull.KeyBack.mapM_of_tags
#print axioms Johnson.AtFull.KeyBack.treesOf_eq
