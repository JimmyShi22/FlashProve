-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/K/Request.lean: the program's reading of a place in the binding tree gives the
compiled verifier's check in the request tree.

A part of the tie between a reader of a file's bytes and the second form of the compiler's verifier
side (lean/OnBytes/TypedOracleCompiler/Joined/): it brings that verifier's yes, under fixed oracle functions, down
to conditions on what was read and on how these functions answer. That the reading of a real file,
and oracle functions made from the programs' hash, meet these conditions is not shown in this
folder.

Behind a first chain the program reads a word (the place), a salt and one sibling for each level of
the binding tree; it hashes the leaf, which holds the first chain's seal, and climbs to the root
(`Proof.readPlace`; opened in OnBytes/TieK/PlaceOpen.lean: `readPlace_open`, `rootOf`). The compiled
verifier of a file does the same on typed values (`reqCheck`,
OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean). This file shows: where the program's reading returns, the
typed check has the value yes under the oracle functions g, at the typed values named here: the
slot value is the first chain's seal as the program reads it. The premise `slot` of `CutsAt`
(OnBytes/TypedOracleCompiler/Joined/YesByCutsMore.lean) follows. Its premise `request` stands at the slot value c
with which the third chain's run ends. So for `request` a third fact is owed, which is not shown
here: that c is that seal, as a digest. It is a fact on how g answers the query to g behind the
first chain, and on the whole run of the first chain.

Two hypotheses on g are named. They say how g answers the two oracles of the request tree:
  `NodeCoded g cfg`: at two digests that are strings of 32 bytes, g answers with the program's hash
    of a vertex of the binding tree. To discharge it: g is made from the program's hash by a map
    from typed queries to strings that writes such a query as that hash's input.
  `LeafCoded g d cfg n rsOf`: at a seal of 32 bytes, and behind it the string `rsOf place salt`, g
    answers with the program's hash of the leaf. The program's leaf holds the depth, the place and
    the salt; the typed leaf holds a string of the prover's choice behind the slot value: `rsOf`
    says how place and salt are written there. In `request_of_place` the place in that string is
    the place from which the typed check climbs: the typed verifier itself does not compare the two.

Main names: `NodeCoded`, `LeafCoded`, `size_vertexB`, `size_bindLeaf`, `size_of_pathAt`,
`climbP_rootOf`, `climb_of_rootOf`, `climb_of_place`, `request_of_place`.

Limits: one direction, from the program's reading to the typed check. Nothing on soundness. No g is
shown to have the two properties. The place rides in the string behind the slot value
(`OneProtocolProof.rsalt`). The typed verifier takes any string there: it does not compare a place in it with
the slot's number, from which it climbs, and once the chain has joined it does not test that
string's length. So it tests less than the program does.

Terms: lean/GLOSSARY.md.

-/
import Fmt.Rules23Laws
import Run.CodingBits
import OnBytes.TieK.PlaceOpen
import OnBytes.TypedOracleCompiler.Joined.YesByCutsMore

noncomputable section

namespace TypedOracleCompiler.Joined.K
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Run (bytesToDig)
open _root_.Iop (Dig)
open OnBytes.TieK (rootOf pathAt readPlace_open)

variable {I X : Type} {K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## Sizes -/

theorem size_vertexB (cfg x y : ByteArray) : (Fmt.vertexB cfg x y).size = 32 :=
  Fmt.size_H 178 0 0 cfg (x ++ y)

theorem size_bindLeaf (d place : ℕ) (cfg closing salt : ByteArray) :
    (Fmt.bindLeaf d place cfg closing salt).size = 32 :=
  Fmt.size_H 173 _ _ cfg _

theorem size_of_slice {b : ByteArray} {i n : ℕ} {x : ByteArray} (h : Fmt.slice b i n = some x) :
    x.size = n := by
  unfold Fmt.slice at h
  split at h
  · cases h
    rw [ByteArray.size_extract]
    omega
  · cases h

/-- the siblings of a path have 32 bytes each -/
theorem size_of_pathAt (b : ByteArray) : ∀ (n i : ℕ) (path : List ByteArray),
    pathAt b n i = some path → ∀ s ∈ path, s.size = 32
  | 0, _, path, h, s, hs => by
    cases (Option.some.inj h : [] = path)
    cases hs
  | n + 1, i, path, h, s, hs => by
    unfold pathAt at h
    split at h
    · cases h
    · rename_i sib hsib
      obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 h
      rcases List.mem_cons.1 hs with rfl | hs
      · exact size_of_slice hsib
      · exact size_of_pathAt b n (i + 32) l hl s hs

/-! ## The two hypotheses on the oracle functions -/

/-- At two digests that are strings of 32 bytes, g answers the request tree's node oracle with the
program's hash of a vertex of the binding tree. A typed query to that oracle holds no tag and no
cfg: so one g can have this property for one cfg alone (but for equal hash values). Whoever uses it
for a key file and a proof file under one g must have one cfg for both. -/
def NodeCoded (g : Fam (typedOracleFamily 256 K L)) (cfg : ByteArray) : Prop :=
  ∀ x y : ByteArray, x.size = 32 → y.size = 32 →
    rnodeAt g (bytesToDig x) (bytesToDig y) = bytesToDig (Fmt.vertexB cfg x y)

/-- At a seal of 32 bytes, and behind it the string `rsOf place salt`, g answers the request tree's
leaf oracle with the program's hash of the leaf at that place of the binding tree of depth d, for
every place of the tree and every salt of n bytes. It can hold only for a map `rsOf` that is
one-to-one on these places and salts, or it would ask that two hash values are equal. For such a map
the inputs named here are different for different (seal, place, salt): a seal of 32 bytes is read
back from the first 256 bits. A typed query to that oracle holds no tag and no depth: so one g can
have this property at two depths, with maps rsOf and rsOf', only if the two maps have no value in
common (but for equal hash values): the string behind the seal must tell the depth too. -/
def LeafCoded (g : Fam (typedOracleFamily 256 K L)) (d : ℕ) (cfg : ByteArray) (n : ℕ)
    (rsOf : ℕ → ByteArray → Bits) : Prop :=
  ∀ (place : ℕ) (closing salt : ByteArray), place < 2 ^ d → closing.size = 32 → salt.size = n →
    g OracleName.rleaf (List.ofFn (bytesToDig closing) ++ rsOf place salt) =
      bytesToDig (Fmt.bindLeaf d place cfg closing salt)

/-! ## The climb -/

/-- Under `NodeCoded` the typed climb along the siblings as digests ends in the program's root. -/
theorem climbP_rootOf {g : Fam (typedOracleFamily 256 K L)} {cfg : ByteArray} (hN : NodeCoded g cfg) :
    ∀ (path : List ByteArray) (x : ByteArray) (p : ℕ), x.size = 32 → (∀ s ∈ path, s.size = 32) →
      climbP (rnodeAt g) (path.map bytesToDig) p (bytesToDig x) = bytesToDig (rootOf cfg x p path)
  | [], _, _, _, _ => rfl
  | sib :: l, x, p, hx, hp => by
    have hs : sib.size = 32 := hp sib List.mem_cons_self
    have hl : ∀ s ∈ l, s.size = 32 := fun s h => hp s (List.mem_cons_of_mem _ h)
    show climbP (rnodeAt g) (l.map bytesToDig) (p / 2)
        (if p % 2 = 0 then rnodeAt g (bytesToDig x) (bytesToDig sib)
          else rnodeAt g (bytesToDig sib) (bytesToDig x)) =
      bytesToDig (rootOf cfg
        (if p % 2 == 1 then Fmt.vertexB cfg sib x else Fmt.vertexB cfg x sib) (p / 2) l)
    by_cases h0 : p % 2 = 0
    · have h1 : (p % 2 == 1) = false := by simp [h0]
      rw [if_pos h0, h1, hN x sib hx hs]
      exact climbP_rootOf hN l _ _ (size_vertexB _ _ _) hl
    · have h1 : (p % 2 == 1) = true := by
        have : p % 2 = 1 := by omega
        simp [this]
      rw [if_neg h0, h1, hN sib x hs hx]
      exact climbP_rootOf hN l _ _ (size_vertexB _ _ _) hl

/-! ## The check -/

/-- If a root is the one to which the program's leaf leads along the siblings (`rootOf`), the typed
climb from the leaf that holds the seal, and behind it `rsOf place salt`, ends in that root. -/
theorem climb_of_rootOf {g : Fam (typedOracleFamily 256 K L)} {cfg : ByteArray} {d n : ℕ}
    {rsOf : ℕ → ByteArray → Bits} (hN : NodeCoded g cfg) (hL : LeafCoded g d cfg n rsOf)
    {closing salt root : ByteArray} {path : List ByteArray} {place : ℕ} (hcl : closing.size = 32)
    (hs : salt.size = n) (hp : ∀ s ∈ path, s.size = 32) (hlt : place < 2 ^ d)
    (hr : root = rootOf cfg (Fmt.bindLeaf d place cfg closing salt) place path) :
    climbP (rnodeAt g) (path.map bytesToDig) place
      (g OracleName.rleaf (List.ofFn (bytesToDig closing) ++ rsOf place salt)) = bytesToDig root := by
  rw [hL place closing salt hlt hcl hs, hr]
  exact climbP_rootOf hN path _ _ (size_bindLeaf _ _ _ _ _) hp

/-- Where the program's reading of the place returns, the typed climb from the leaf that holds the
first chain's seal, and behind it `rsOf place salt`, ends in the root as read. -/
theorem climb_of_place {g : Fam (typedOracleFamily 256 K L)} {s : OnBytes.Params.LinBindingShape}
    {cfg closing b : ByteArray} {i : ℕ} {pl : OnBytes.Proof.Place} {rsOf : ℕ → ByteArray → Bits}
    (h : OnBytes.Proof.readPlace s cfg closing b i = some pl) (hcl : closing.size = 32)
    (hN : NodeCoded g cfg) (hL : LeafCoded g s.logLeaves cfg s.saltBytes rsOf) :
    pl.place < 2 ^ s.logLeaves ∧
    ∃ (salt : ByteArray) (path : List ByteArray),
      salt.size = s.saltBytes ∧ path.length = s.logLeaves ∧
      pl.root = rootOf cfg (Fmt.bindLeaf s.logLeaves pl.place cfg closing salt) pl.place path ∧
      climbP (rnodeAt g) (path.map bytesToDig) pl.place
        (g OracleName.rleaf (List.ofFn (bytesToDig closing) ++ rsOf pl.place salt)) =
          bytesToDig pl.root := by
  obtain ⟨-, w, i1, salt, path, -, hw, hsalt, hpath, hlen, rfl⟩ :=
    readPlace_open s cfg closing b i pl h
  refine ⟨hw, salt, path, size_of_slice hsalt, hlen, rfl, ?_⟩
  rw [hL w.toNat closing salt hw hcl (size_of_slice hsalt)]
  exact climbP_rootOf hN path _ _ (size_bindLeaf _ _ _ _ _) (size_of_pathAt b _ _ path hpath)

/-- **Where the program's reading of the place returns, the typed check in the request tree says
yes under g**, at these typed values: the depth of the binding tree; its root as read; the place;
the siblings; the first chain's seal; and `rsOf place salt`. The place is below 2^depth. -/
theorem request_of_place {g : Fam (typedOracleFamily 256 K L)} {s : OnBytes.Params.LinBindingShape}
    {cfg closing b : ByteArray} {i : ℕ} {pl : OnBytes.Proof.Place} {rsOf : ℕ → ByteArray → Bits}
    (h : OnBytes.Proof.readPlace s cfg closing b i = some pl) (hcl : closing.size = 32)
    (hN : NodeCoded g cfg) (hL : LeafCoded g s.logLeaves cfg s.saltBytes rsOf) :
    pl.place < 2 ^ s.logLeaves ∧
    ∃ (salt : ByteArray) (path : List ByteArray),
      salt.size = s.saltBytes ∧ path.length = s.logLeaves ∧
      pl.root = rootOf cfg (Fmt.bindLeaf s.logLeaves pl.place cfg closing salt) pl.place path ∧
      (reqCheck (K := K) (L := L) s.logLeaves (bytesToDig pl.root) pl.place
        (path.map bytesToDig) (bytesToDig closing) (rsOf pl.place salt)).det g = true := by
  obtain ⟨hw, salt, path, hs, hlen, hroot, hc⟩ := climb_of_place h hcl hN hL
  exact ⟨hw, salt, path, hs, hlen, hroot,
    det_reqCheck g (by rw [List.length_map]; exact hlen) hw hc⟩

end TypedOracleCompiler.Joined.K
