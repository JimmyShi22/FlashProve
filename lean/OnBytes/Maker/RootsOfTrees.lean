-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/RootsOfTrees.lean: at a value of the typing of a whole file, the root under which the
compiled verifier checks an opening is the digest of the root to which the reader's walk led.

OnBytes/Maker/RootsFlat.lean has `RootsRead` for the three stretches of a file, if each opening of
the tree number j over the whole file has walked to a root whose digest is entry j of the proof
string's list of roots. OnBytes/Maker/OneRoot.lean says of a file as read: each opening of the tree
number j has walked to the root that the tree's sender sent (`TreeAt`). Here the two are joined:
the typing lays the three chains' roots in a row, and a tree's number over the whole file is its
root's place in that row.

  `rootsT_eq_roots`     the typing's roots of a chain are the digests of the roots that the chain
                        sent.
  `getElem?_wholeNo`    the n-th root of chain c stands, in the three chains' roots in a row, at the
                        number over the whole file.
  `roots_typeFile`      at a value π of `typeFile`: entry j of π's list of roots is the digest of
                        the root of the tree number j.
  `rootsRead_typeFile`  **`RootsRead` for the three stretches at a value of `typeFile`.**

The premises of the last: the three chains' values under g; W counts the first two chains' trees as
the chains as read have roots (`hn₁`, `hn₂`); each opening of a tree in the file has walked to the
root that the tree's sender sent (`hT`: OnBytes/Maker/OneRoot.lean, `own_treeAt`, has it from three
readings under a premise of its own). None is shown here.

Not claimed. Nothing on soundness (index binding included), what a root fixes, opening-form binding,
no two openings of a commitment, correctness of extraction or whatever else names a committer or a prover.

-/
import OnBytes.Maker.RootsFlat
import OnBytes.Maker.OneRoot

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening Tag)
open _root_.Run _root_.Run.PQ

/-- The typing's roots of a chain are the digests of the roots that the chain sent. -/
theorem rootsT_eq_roots (c : ChainRead) :
    rootsT c.out.rounds.toList = c.roots.map bytesToDig := by
  unfold rootsT ChainRead.roots
  congr 1
  exact List.flatMap_congr fun x _ => (OnBytes.rootsT_eq x.vals).symm

/-- The n-th root of chain c stands, in the three chains' roots in a row, at the number over the
whole file. -/
theorem getElem?_wholeNo (r : Proof.TailRead) (t₁ t₂ : ℕ) (h₁ : t₁ = r.first.roots.length)
    (h₂ : t₂ = r.shared.roots.length) :
    ∀ (c n : ℕ) (root : ByteArray), c ≤ 2 → (rootsOf3 r c)[n]? = some root →
      (r.first.roots ++ (r.shared.roots ++ r.second.roots))[Three.wholeNo t₁ t₂ (c, n)]? =
        some root
  | 0, n, root, _, h => by
    have h' : r.first.roots[n]? = some root := h
    show (_ ++ _)[0 + n]? = _
    rw [Nat.zero_add, List.getElem?_append_left (lt_of_getElem? h')]
    exact h'
  | 1, n, root, _, h => by
    have h' : r.shared.roots[n]? = some root := h
    show (_ ++ _)[t₁ + n]? = _
    rw [h₁, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_append_left (lt_of_getElem? h')]
    exact h'
  | 2, n, root, _, h => by
    show (_ ++ _)[t₁ + t₂ + n]? = _
    rw [h₁, h₂, Nat.add_assoc, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left]
    exact h
  | _ + 3, _, _, hc, _ => by omega

section File
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (a : ℕ) (W : Three.Whole)
  {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool)

/-- **Entry j of the typed list of roots is the digest of the root of the tree number j.** -/
theorem roots_typeFile (sb : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) (salt : ByteArray)
    (path : List ByteArray) (r : Proof.TailRead)
    (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch)
    (h : typeFile C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r = some π)
    (h₁ : W.t₁ = r.first.roots.length) (h₂ : W.t₂ = r.shared.roots.length) (j : ℕ)
    (root start : ByteArray) (hT : TreeAt W r j root start) :
    π.roots[j]? = some (bytesToDig root) := by
  obtain ⟨tabs, ext, -, -, h'⟩ :=
    typeFile_some C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r π h
  obtain ⟨c, n, rfl, hc, hr, -⟩ := hT
  rw [toBPrfW_roots C (WholeD.of a W) tF tJ t3 silent run pF pJ p3 tabs ext salt path r π h',
    rootsT_eq_roots, rootsT_eq_roots, rootsT_eq_roots, ← List.map_append, ← List.map_append,
    List.getElem?_map, getElem?_wholeNo r W.t₁ W.t₂ h₁ h₂ c n root hc hr]
  rfl

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} (g : Fam (typedOracleFamily 256 (K + 1) L)) {t : Tag}
  {embP : PlainPart (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ t3).ann →
    PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t)} {xin : Xi → Option X} {cms : List (Dig 256)}

/-- **`RootsRead` for the three stretches at a value of `typeFile`.** -/
theorem rootsRead_typeFile (sb : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3)
    (salt : ByteArray) (path : List ByteArray) (r : Proof.TailRead)
    (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch)
    (h : typeFile C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r = some π) (x : Xi)
    (a' : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₁)
    (b' : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₂)
    (e' : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₃)
    (h₁ : (run₁ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
      (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π).det g = some a')
    (h₂ : (run₂ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
      (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π a').det g = some b')
    (h₃ : (run₃ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
      (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π a' b').det g =
      some e')
    (hn₁ : W.t₁ = r.first.roots.length) (hn₂ : W.t₂ = r.shared.roots.length)
    (hT : ∀ j z, (j, z) ∈ ownRowsW W r → ∃ start, TreeAt W r j z.2.2.root start) :
    RootsRead W r C (WholeD.of a W).ds₁ 0 (wiresLo C K chal (WholeD.of a W).ds₁) a'.2.1.2 ∧
      RootsRead W r C (WholeD.of a W).ds₂ (WholeD.of a W).t₁
        (wiresSh C K chal (WholeD.of a W).ds₂) b'.2.1.2 ∧
      RootsRead W r C (WholeD.of a W).ds₃ ((WholeD.of a W).t₁ + (WholeD.of a W).t₂)
        (wiresLo C K chal (WholeD.of a W).ds₃) e'.2.1.2 :=
  rootsRead_of C K chal (WholeD.of a W) tF tJ t3 silent run g W r π x a' b' e' h₁ h₂ h₃
    fun j z hz => by
      obtain ⟨start, hs⟩ := hT j z hz
      exact roots_typeFile C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r π h hn₁ hn₂ j _
        start hs

end File

end OnBytes.Maker
