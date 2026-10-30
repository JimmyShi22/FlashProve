-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/StringsWhole.lean: a narrower test on bodies that are strings: whole bytes.

OnBytes/TypedOracleCompiler/Strings.lean's test `ok164` asks of a body at least 16 bits, the first 16 those of the
leaves' number. That is the law `leafTag` of the sibling's page (OnBytes/TypedOracleCompiler/StringsPage.lean), AND
IT IS TOO WIDE FOR THE PAGE's FIT: the identity on such bodies writes strings of 16 and of 17 bits,
while the sibling's `PageFit` (OnBytes/TypedOracleCompiler/Run/CodingAgree.lean) asks that every written string of a
leaf query is the bits of a call's string, so of whole bytes. With `pBody ok164` as a page's leaf
code, and a test `leafOK` that lets both through (the default does), `PageFit` is false, whatever
the spellings (by hand, no Lean statement).

`okWhole` asks besides: a whole number of bytes, and at least the label's 16. It still gives
`leafTag` (`pBodyW_tag`). A body that is the bits of a label under 164 and of bytes passes it if it
passes `ok164` (`okWhole_of_fit`). So, if no tree is deeper than 63, a symbol's body passes it: at
the library's generic protocol under the library's test `tagsOK` (`embT_okWhole`); at the protocol
in three stretches under the like test on the stretches' trees (`Stretches.Tags`, `embS_okWhole`).

Main definitions: `okWhole`, `tagsT`, `tagsL`, `Stretches.Tags`.
Main theorems: `pBodyW_tag`, `okWhole_of_fit`, `embT_okWhole`, `ownT_tag`, `embS_ok164`,
`embS_okWhole`.

Not claimed. THAT `PageFit` CAN BE MET AT `pBody okWhole` IS NOT SHOWN: it wants a reader of a
body's first 16 bytes as the page's spelling of a leaf, with the law that every body that passes the
test is the bits of the label that it reads and of the bytes behind it; none is given HERE:
OnBytes/TypedOracleCompiler/StringsRead.lean has a reader and, over this test, a test that has that law by itself.
No page is made. The tests on the trees' words are hypotheses here; OnBytes/TypedOracleCompiler/StringsBounds.lean
shows that both, the library's `tagsOK` and the one on the stretches' trees, hold at all trees.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.StringsPage
import OnBytes.TypedOracleCompiler.Slice.Plain3Strings

set_option autoImplicit false

namespace TypedOracleCompiler.Strings
open _root_.Run (t164 bytesToBits length_bytesToBits)

/-- A test on bodies: `ok164`, a whole number of bytes, and at least 16 bytes. -/
def okWhole (b : List Bool) : Bool :=
  ok164 b && decide (b.length % 8 = 0) && decide (128 ≤ b.length)

theorem ok164_of_okWhole {b : List Bool} (h : okWhole b = true) : ok164 b = true := by
  unfold okWhole at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.1

/-- What the identity on the bodies that pass `okWhole` writes begins with the 16 bits of the
leaves' number: the law `leafTag` of the sibling's page. -/
theorem pBodyW_tag (y m : List Bool) (h : (pBody okWhole).put y = some m) :
    16 ≤ m.length ∧ m.take 16 = t164 := by
  have h0 : (if okWhole y then some y else none) = some m := h
  by_cases hy : okWhole y = true
  · rw [if_pos hy] at h0
    cases h0
    exact pBody_tag y y (if_pos (ok164_of_okWhole hy))
  · rw [if_neg hy] at h0
    cases h0

/-- The bits of a label and of bytes pass `okWhole` if they pass `ok164`. -/
theorem okWhole_of_fit {b : List Bool} (n t i : ℕ) (z : ByteArray)
    (hb : b = bytesToBits (_root_.Fmt.label n t i) ++ bytesToBits z) (h : ok164 b = true) :
    okWhole b = true := by
  have hl : b.length = 8 * 16 + 8 * z.size := by
    rw [hb, List.length_append, length_bytesToBits, length_bytesToBits, _root_.Fmt.size_label]
  unfold okWhole
  rw [h, Bool.true_and, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff, hl]
  omega

/-- At the library's generic protocol a symbol's body passes `okWhole`, if no tree is deeper than 63
and every tree's word begins with the 16 bits (the library's test `tagsOK`). -/
theorem embT_okWhole (C : _root_.Run.PQ.CK) (salt : ℕ) (ds : List _root_.Run.PQ.RD)
    (hd : ∀ d ∈ ds, _root_.Run.PQ.posN d.tree + _root_.Run.PQ.posN d.tree ≤ 2 ^ 64)
    (hk : _root_.Run.PQ.tagsOK salt ds = true)
    (p : _root_.Iop.OPos (_root_.Run.Twin.up (_root_.Run.PQ.SOf C ds)))
    (a : _root_.Iop.OSym (_root_.Run.Twin.up (_root_.Run.PQ.SOf C ds)) p) :
    okWhole (embT C salt ds p a) = true :=
  okWhole_of_fit 164 _ _ _ (embT_fit C salt ds hd p a) (embT_ok164 C salt ds hd hk p a)

end TypedOracleCompiler.Strings

namespace TypedOracleCompiler.Slice
open _root_.Iop (Shape OPos OSym)
open _root_.Run (t164 take16 length_u64n)
open _root_.Run.PQ (leafWord leaf1_pre)
open TypedOracleCompiler.Run TypedOracleCompiler.Strings
open TypedOracleCompiler.StringsList (ownT ownT_some)

variable (salt : ℕ)

/-- The test on a round's trees: each tree's word begins with the 16 bits of the leaves' number. -/
def tagsT : List _root_.Fmt.Shape → Bool
  | [] => true
  | s :: ts => decide ((leafWord (some s) salt).take 16 = t164) && tagsT ts

/-- The same on a list of rounds. -/
def tagsL (ds : List PQ.RD) : Bool := ds.all fun d => tagsT salt d.trees

/-- Under that test an own string of a round begins with these 16 bits. -/
theorem ownT_tag : ∀ (ts : List _root_.Fmt.Shape), tagsT salt ts = true →
    ∀ (p : PQ.PosT ts) (a : PQ.SymT ts p) (m : List Bool), ownT salt ts p a = some m →
      16 ≤ m.length ∧ m.take 16 = t164
  | s :: ts, hk, .inl x, a, m, h => by
      have hk' : (decide ((leafWord (some s) salt).take 16 = t164) && tagsT salt ts) = true := hk
      rw [Bool.and_eq_true, decide_eq_true_iff] at hk'
      obtain ⟨r, rfl⟩ := leaf1_pre (some s) salt (x, a) m h
      have hl : (leafWord (some s) salt).length = 64 := length_u64n _
      exact ⟨by rw [List.length_append, hl]; omega, (take16 _ r (by rw [hl]; omega)).trans hk'.1⟩
  | s :: ts, hk, .inr p, a, m, h => by
      have hk' : (decide ((leafWord (some s) salt).take 16 = t164) && tagsT salt ts) = true := hk
      rw [Bool.and_eq_true] at hk'
      exact ownT_tag ts hk'.2 p a m h

/-- What it is for a way of writing to pass `ok164` everywhere. -/
def Passes {t : Shape} (et : (p : OPos t) → OSym t p → List Bool) : Prop :=
  ∀ p a, ok164 (et p a) = true

theorem ok164_of {m : List Bool} (h : 16 ≤ m.length ∧ m.take 16 = t164) : ok164 m = true := by
  unfold ok164
  simp [h.1, h.2]

variable (C : PQ.CK)

theorem passes_app (t : Shape) (et : (p : OPos t) → OSym t p → List Bool) (ht : Passes et) :
    ∀ (ds : List PQ.RD), (∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) →
      tagsL salt ds = true → Passes (embApp salt C t et ds)
  | [], _, _, p, a => ht p a
  | d :: ds, h, hk, .inl p, a => by
      obtain ⟨m, hm⟩ :=
        Option.isSome_iff_exists.1 (ownT_some salt d.trees (h d (List.mem_cons_self ..)) p a)
      have hk' : (tagsT salt d.trees && tagsL salt ds) = true := hk
      rw [Bool.and_eq_true] at hk'
      show ok164 ((ownT salt d.trees p a).getD []) = true
      rw [hm]
      exact ok164_of (ownT_tag salt d.trees hk'.1 p a m hm)
  | d :: ds, h, hk, .inr q, a => by
      have hk' : (tagsT salt d.trees && tagsL salt ds) = true := hk
      rw [Bool.and_eq_true] at hk'
      exact passes_app t et ht ds (fun d hd => h d (List.mem_cons_of_mem _ hd)) hk'.2 q a

theorem passes_seam (s : Seam) (t : Shape) (et : (p : OPos t) → OSym t p → List Bool)
    (ht : Passes et) : Passes (embSeam s t et)
  | .inl p, _ => (s.noPos.false p).elim
  | .inr q, a => ht q a

theorem passes_tail : ∀ (ds : List PQ.RD),
    (∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) → tagsL salt ds = true →
      Passes (embTail salt C ds)
  | [], _, _, p, _ => p.elim
  | d :: ds, h, hk, .inl p, a => by
      obtain ⟨m, hm⟩ :=
        Option.isSome_iff_exists.1 (ownT_some salt d.trees (h d (List.mem_cons_self ..)) p a)
      have hk' : (tagsT salt d.trees && tagsL salt ds) = true := hk
      rw [Bool.and_eq_true] at hk'
      show ok164 ((ownT salt d.trees p a).getD []) = true
      rw [hm]
      exact ok164_of (ownT_tag salt d.trees hk'.1 p a m hm)
  | d :: ds, h, hk, .inr q, a => by
      have hk' : (tagsT salt d.trees && tagsL salt ds) = true := hk
      rw [Bool.and_eq_true] at hk'
      exact passes_tail ds (fun d hd => h d (List.mem_cons_of_mem _ hd)) hk'.2 q a

namespace Stretches
variable (G : Stretches)

/-- The test on the trees of all three stretches. -/
def Tags : Prop :=
  tagsL salt G.ds₁ = true ∧ tagsL salt G.ds₂ = true ∧ tagsL salt G.ds₃ = true

/-- At three stretches a symbol's body passes `ok164`, if no tree is deeper than 63 and every
tree's word begins with the 16 bits. -/
theorem embS_ok164 (h : G.Shallow) (hk : G.Tags salt) : Passes (G.embS salt) :=
  passes_seam G.s0 _ _ (passes_app salt G.C G.sh₂ _
    (passes_seam G.s1 _ _ (passes_seam G.s2 _ _ (passes_app salt G.C G.sh₃ _
      (passes_seam G.s3 _ _ (passes_tail salt G.C G.ds₃ h.2.2 hk.2.2)) G.ds₂ h.2.1 hk.2.1)))
    G.ds₁ h.1 hk.1)

/-- And the narrower test `okWhole`. -/
theorem embS_okWhole (h : G.Shallow) (hk : G.Tags salt) (p : OPos G.sh) (a : OSym G.sh p) :
    okWhole (G.embS salt p a) = true :=
  okWhole_of_fit 164 _ _ _ (G.embS_fit salt h p a) (G.embS_ok164 salt h hk p a)

end Stretches

end TypedOracleCompiler.Slice
