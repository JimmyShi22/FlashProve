-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/KeysAreKvG.lean: the honest side of the kind "lookup" (K3). On
which key vectors the honest lookup on the calls of a group's layers runs: the library's own `kvG`
at the reader `ownG` of the sources. One definition, and theorems.

Terms. Honest/K3/GLOSSARY.md ("ask", "sources", "seated filling", "owner"). In this file: the
sources `ownSources` (Honest/K3/WitOwner.lean) hold no keys of their own and take none as a letter.
What `askOf` (Honest/K3/Wit.lean) yields at a layers' link over them is the library's joint key
vector (`jointKey`, OnBytes/Tie/Pv/Lookup/Ends/Joint.lean) of the library's key vectors of the calls
(`kvG`, OnBytes/Tie/Pv/Lookup/Ends/G.lean) at the reading `ownG` (WitOwner.lean): the cell of an
entry of the link's list at its owner's segment and name; the index's entry. The row's structure
holds that vector carried into the program's elements; `inE` (Wit.lean) reads these back.

What is shown.
  `inE_is_gl`: the reading `inE` is the library's `Reading.gl` (OnBytes/Model/HideLaws.lean).
  `keysG`: key number n of call q: `kvG` at the reader `ownG`.
  `askLayers_key`, `askLayers_tied`: the row's key, read back, is `jointKey` of `keysG`; the first
    over `ownSources`, the second over `tiedOwnSources`, the seated filling. Neither has a
    hypothesis.
  `jointKey_at`: the joint vector at place x of tree y.
  `askLayers_tree`: the row's key at place x of tree y is the key of the tree's call, moved by the
    shift.
  `askLayers_call`: key number n of call q stands in the row's structure at place n mod 2 ^ dT of
    the tree number first q + n / 2 ^ dT.
  `keysG_free`, `keysG_rest`: at a padding place the key is the table's padding value. The first: at
    a column that no segment lists. The second: at a segment of routed experts on a layer that has
    none.

Hypotheses that remain.
  `hy`, `hT`: (in `jointKey_at`, `askLayers_tree`, `askLayers_call`) the tree's number is below
    2 ^ rK and below NT.
  `hc`: (in `askLayers_call`) the tree's call is q.
  All three are comparisons of the shape's public numbers.
  `h`, `hm`: (in `keysG_free`, `keysG_rest`) what kind of padding place it is.
  No hypothesis is made on the cells, the index or a trace, and none on the shape beyond these.

Users. Honest/K3/Law/KeysTie.lean imports this file.

Limits. The layers' calls alone. That the reader's cells are a trace's entries is not said here (at
the full size: Honest/K3/Law/WitOwnerFull.lean, Honest/K3/Law/MeetsNamed.lean). Nothing is said on
the extension of a key vector at a point.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.WitLaw
import Johnson.Desc.ProofFile.Honest.K3.WitOwner

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E)
open OnBytes.Ends (jointKey tauN t0N)

/-- The reading by which the row's elements are read back is the library's. -/
theorem inE_is_gl (x : E) : inE x = OnBytes.Model.Reading.gl.val x := rfl

/-- **Key number n of call q of the lookup on the calls of group g's layers**, in the library's
field: the library's `kvG` at the reader `ownG` of the sources. -/
def keysG (X : OnBytes.Model.Verify.Public) (C : Cells) (W : Weights) (g q n : ℕ) : Cb.Gl.E :=
  OnBytes.Ends.G.kvG X.layers g (ownG X C.cell W.entry (linkG X g)) q n

section
variable {W₀ Rc Xi Tr' : Type}

/-- **The row's key, read back, is the joint key vector of `keysG`.** -/
theorem askLayers_key (X : OnBytes.Model.Verify.Public) (cells : Tr' → Cells)
    (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) (g : ℕ)
    (t : Local W₀ Rc Xi Tr') (heard : List Fmt.Drawn) (theta : E) (i n : ℕ) :
    inE ((askOf (ownSources X cells weights pubH) (.layers g) t heard).key theta i n) =
      jointKey X.layers.y.fo (keysG X (cells t.trace) (weights t.w₀) g) (inE theta) n :=
  hidden_key _ theta i n

/-- The same over `tiedOwnSources`, the seated filling. -/
theorem askLayers_tied (X : OnBytes.Model.Verify.Public) (cells : Tr' → Cells)
    (weights : W₀ → Weights) (req : Xi → OnBytes.Model.Head.Covered × Array ℕ) (g : ℕ)
    (t : Local W₀ Rc Xi Tr') (heard : List Fmt.Drawn) (theta : E) (i n : ℕ) :
    inE ((askOf (tiedOwnSources X cells weights req) (.layers g) t heard).key theta i n) =
      jointKey X.layers.y.fo (keysG X (cells t.trace) (weights t.w₀) g) (inE theta) n :=
  hidden_key _ theta i n

end

/-- The joint key vector at place x of tree y. Conditional on y < 2 ^ rK, y < NT. -/
theorem jointKey_at {R : Type} [CommRing R] (h : OnBytes.Model.Forest.Shape) (kv : ℕ → ℕ → R)
    (θ : R) (x y : ℕ) (hy : y < 2 ^ h.rK) (hT : y < h.NT) :
    jointKey h kv θ (x * 2 ^ h.rK + y) =
      kv (h.callOf.getD y 0) ((y - h.first.getD (h.callOf.getD y 0) 0) * 2 ^ h.dT + x) +
        ((h.callOf.getD y 0 : ℕ) : R) * θ := by
  have e1 : (x * 2 ^ h.rK + y) % 2 ^ h.rK = y := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hy]
  have e2 : (x * 2 ^ h.rK + y) / 2 ^ h.rK = x := by
    rw [Nat.mul_comm, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hy, Nat.add_zero]
  unfold jointKey
  simp only [e1, e2, hT, if_true]

section
variable {W₀ Rc Xi Tr' : Type}

/-- The row's key at place x of tree y. Conditional on y < 2 ^ rK, y < NT. -/
theorem askLayers_tree (X : OnBytes.Model.Verify.Public) (cells : Tr' → Cells)
    (weights : W₀ → Weights) (req : Xi → OnBytes.Model.Head.Covered × Array ℕ) (g : ℕ)
    (t : Local W₀ Rc Xi Tr') (heard : List Fmt.Drawn) (theta : E) (i x y : ℕ)
    (hy : y < 2 ^ X.layers.y.fo.rK) (hT : y < X.layers.y.fo.NT) :
    inE ((askOf (tiedOwnSources X cells weights req) (.layers g) t heard).key theta i
        (x * 2 ^ X.layers.y.fo.rK + y)) =
      keysG X (cells t.trace) (weights t.w₀) g (X.layers.y.fo.callOf.getD y 0)
          ((y - X.layers.y.fo.first.getD (X.layers.y.fo.callOf.getD y 0) 0) *
            2 ^ X.layers.y.fo.dT + x) +
        ((X.layers.y.fo.callOf.getD y 0 : ℕ) : Cb.Gl.E) * inE theta := by
  rw [askLayers_tied, jointKey_at _ _ _ x y hy hT]

/-- **Key number n of call q stands in the row's structure at place n mod 2 ^ dT of the tree first q
+ n / 2 ^ dT, moved by q times the shift.** Conditional on: that tree's number is below 2 ^ rK and
below NT, and its call is q. -/
theorem askLayers_call (X : OnBytes.Model.Verify.Public) (cells : Tr' → Cells)
    (weights : W₀ → Weights) (req : Xi → OnBytes.Model.Head.Covered × Array ℕ) (g : ℕ)
    (t : Local W₀ Rc Xi Tr') (heard : List Fmt.Drawn) (theta : E) (i q n : ℕ)
    (hy : X.layers.y.fo.first.getD q 0 + n / 2 ^ X.layers.y.fo.dT < 2 ^ X.layers.y.fo.rK)
    (hT : X.layers.y.fo.first.getD q 0 + n / 2 ^ X.layers.y.fo.dT < X.layers.y.fo.NT)
    (hc : X.layers.y.fo.callOf.getD
      (X.layers.y.fo.first.getD q 0 + n / 2 ^ X.layers.y.fo.dT) 0 = q) :
    inE ((askOf (tiedOwnSources X cells weights req) (.layers g) t heard).key theta i
        (n % 2 ^ X.layers.y.fo.dT * 2 ^ X.layers.y.fo.rK +
          (X.layers.y.fo.first.getD q 0 + n / 2 ^ X.layers.y.fo.dT))) =
      keysG X (cells t.trace) (weights t.w₀) g q n + ((q : ℕ) : Cb.Gl.E) * inE theta := by
  rw [askLayers_tree X cells weights req g t heard theta i _ _ hy hT, hc, Nat.add_sub_cancel_left,
    Nat.div_add_mod']

end

/-- **At a column that no segment lists the key is the table's padding value.** -/
theorem keysG_free (X : OnBytes.Model.Verify.Public) (C : Cells) (W : Weights) (g q n : ℕ)
    (h : OnBytes.Ends.G.colG X.layers.y q
      (n / X.layers.y.T % 2 ^ (X.layers.y.calls.getD q default).lJ) = none) :
    keysG X C W g q n = ((tauN X.layers.y.fo q (t0N X.layers.y.fo q) : ℕ) : Cb.Gl.E) := by
  unfold keysG OnBytes.Ends.G.kvG OnBytes.Ends.G.kvOf
  simp only [h]

/-- **The same at a segment of routed experts on a layer that has none.** -/
theorem keysG_rest (X : OnBytes.Model.Verify.Public) (C : Cells) (W : Weights) (g q n : ℕ)
    (s : OnBytes.Model.Seg) (x : ℕ)
    (h : OnBytes.Ends.G.colG X.layers.y q
      (n / X.layers.y.T % 2 ^ (X.layers.y.calls.getD q default).lJ) = some (s, x))
    (hm : (s.moe && n / X.layers.y.T / 2 ^ (X.layers.y.calls.getD q default).lJ % 2 == 0) = true) :
    keysG X C W g q n = ((tauN X.layers.y.fo q (t0N X.layers.y.fo q) : ℕ) : Cb.Gl.E) := by
  unfold keysG OnBytes.Ends.G.kvG OnBytes.Ends.G.kvOf
  simp only [h, hm, if_true]

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.inE_is_gl
#print axioms ProofFile.Honest.K3.askLayers_key
#print axioms ProofFile.Honest.K3.askLayers_tied
#print axioms ProofFile.Honest.K3.jointKey_at
#print axioms ProofFile.Honest.K3.askLayers_tree
#print axioms ProofFile.Honest.K3.askLayers_call
#print axioms ProofFile.Honest.K3.keysG_free
#print axioms ProofFile.Honest.K3.keysG_rest
