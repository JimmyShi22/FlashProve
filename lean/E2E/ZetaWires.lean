-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ZetaWires.lean: how many leaves the hash trees of a protocol have, as a computable function of
the rounds' data.

Summary. The error term `zetaW` counts hash queries, and these counts need the number of leaves of
all trees that a prover sends. This file computes that number from a protocol's wiring (the
structure that says how its rounds are hashed), for the wiring of a whole file of three chains
(`OnBytes.Maker.wqWhole`: the key file's and the proof file's protocol) and for the link's
(`Johnson.RunOne.StrictW.wqW`). The rounds' data are arbitrary.

Main results.
  `lv_wqWhole`: for a whole file the number of leaves is the sum over its three chains; the front
    round, the joining round and the seam send no tree.
  `lv_wqW`: for the link it is the sum over its rounds; the round in front sends no tree.

Terms: E2E/HidingTerms.lean.

Limits. A count of leaves, not of hash queries. No security property is stated.

Definitions and helper lemmas.
  `lv s A W`: over the rounds of a wiring, 2 ^ d summed over the depths d of each round's trees, of
    both components; `lvR`: one round's share.
  `treesSum`, `leavesT`, `leavesR`: 2 ^ a summed over the shapes of the trees that a list of rounds'
    data sends.
  `sum_depths`: the sum of 2 ^ depth over a list of shapes is `treesSum` of the list.
  `lv_app`, `lv_wires`: two wirings in a row; the six parts of a file.
  `lv_wiresLo`, `lv_wiresSh`, `lv_wiresSL`: a chain of rounds has one tree for each of a round's
    shapes.


-/
import Johnson.Flat.Dec.FailsClosed
import Johnson.Flat.ArmSibAt
import Johnson.RunOne.StrictLinkW

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.ZetaAt
open TypedOracleCompiler.Iop TypedOracleCompiler.Joined OnBytes.Maker
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (CK View XO Dn)

section
variable {lam K : ℕ}

/-- The leaves of all trees of a wiring's rounds. -/
def lv : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ
  | [], _, _ => 0
  | _ :: s, (_, A), (w, W) =>
      (w.depth0.map fun d => 2 ^ d).sum + (w.depthJ.map fun d => 2 ^ d).sum + lv s A W

/-- Two wirings in a row. -/
theorem lv_app : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} (W : RoundsQueryLayout lam K s A)
    (V : RoundsQueryLayout lam K u B), lv (s ++ u) (RoundSplits.app A B) (WireSB.app W V) = lv s A W + lv u B V
  | [], _, _, _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, (_, _), _, (w, W), V => by
    show _ + _ + lv _ _ (WireSB.app W V) = _ + _ + lv _ _ W + lv _ _ V
    rw [lv_app W V]
    omega

end

section
variable {lam K : ℕ}

/-- The leaves of one round's trees. -/
def lvR {r : Round} {a : RAnn r} (w : WireRB lam K r a) : ℕ :=
  (w.depth0.map fun d => 2 ^ d).sum + (w.depthJ.map fun d => 2 ^ d).sum

/-- The six parts of a file. -/
theorem lv_wires {G : Compile.Joined.Chains} (V : Wires lam K G) :
    lv _ _ V.sh =
      lvR V.wF + (lv _ _ V.W₁ + (lvR V.wJ + (lv _ _ V.W₂ + (lvR V.w3 + lv _ _ V.W₃)))) := by
  show lvR V.wF + lv _ _ (WireSB.app V.W₁ V.shJ) = _
  rw [lv_app]
  show lvR V.wF + (lv _ _ V.W₁ + (lvR V.wJ + lv _ _ (WireSB.app V.W₂ V.sh₃))) = _
  rw [lv_app]
  rfl

end

/-- The leaves of the trees of the listed shapes. -/
def treesSum (ts : List Fmt.Shape) : ℕ := (ts.map fun s => 2 ^ s.a).sum

/-- The leaves of all trees that a file's chain of rounds sends. -/
def leavesT (ds : List RDT) : ℕ := (ds.map fun d => treesSum d.trees).sum

/-- The same for the link's rounds. -/
def leavesR (ds : List TypedOracleCompiler.Run.PQ.RD) : ℕ := (ds.map fun d => treesSum d.trees).sum

theorem sum_depths (ts : List Fmt.Shape) :
    ((ts.map (·.a)).map fun d => 2 ^ d).sum = treesSum ts := by
  unfold treesSum
  rw [List.map_map]
  rfl

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

theorem lv_wiresLo : ∀ ds : List RDT, lv _ _ (wiresLo C K chal ds) = leavesT ds
  | [] => rfl
  | d :: ds => by
    show (([] : List ℕ).map fun d => 2 ^ d).sum + ((d.trees.map (·.a)).map fun d => 2 ^ d).sum +
      lv _ _ (wiresLo C K chal ds) = treesSum d.trees + leavesT ds
    rw [lv_wiresLo ds, sum_depths]
    simp

theorem lv_wiresSh : ∀ ds : List RDT, lv _ _ (wiresSh C K chal ds) = leavesT ds
  | [] => rfl
  | d :: ds => by
    show ((d.trees.map (·.a)).map fun d => 2 ^ d).sum + (([] : List ℕ).map fun d => 2 ^ d).sum +
      lv _ _ (wiresSh C K chal ds) = treesSum d.trees + leavesT ds
    rw [lv_wiresSh ds, sum_depths]
    simp

theorem lv_wiresSL : ∀ ds : List TypedOracleCompiler.Run.PQ.RD,
    lv _ _ (TypedOracleCompiler.Run.PQ.wiresSL C K chal ds) = leavesR ds
  | [] => rfl
  | d :: ds => by
    show (([] : List ℕ).map fun d => 2 ^ d).sum + ((d.trees.map (·.a)).map fun d => 2 ^ d).sum +
      lv _ _ (TypedOracleCompiler.Run.PQ.wiresSL C K chal ds) = treesSum d.trees + leavesR ds
    rw [lv_wiresSL ds, sum_depths]
    simp

variable (D : WholeD) {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **The leaves of a whole file's wiring**: the front round, the joining round and the seam send no
tree. -/
theorem lv_wqWhole : lv _ _ (wqWhole C K chal D tF tJ t3 silent run).sh =
    leavesT D.ds₁ + (leavesT D.ds₂ + leavesT D.ds₃) := by
  show lv _ _ (wiresOf C K chal D tF tJ t3).sh = _
  rw [lv_wires]
  show (0 + 0) + (lv _ _ (wiresLo C K chal D.ds₁) + ((0 + 0) + (lv _ _ (wiresSh C K chal D.ds₂) +
    ((0 + 0) + lv _ _ (wiresLo C K chal D.ds₃))))) = _
  rw [lv_wiresLo, lv_wiresSh, lv_wiresLo]
  omega

variable (ds : List TypedOracleCompiler.Run.PQ.RD) (a : ℕ) (xs : List XO) {Y : Type}
  (dec : Y → View → Bool)

/-- The leaves of the link's wiring: the round in front sends no tree. -/
theorem lv_wqW : lv _ _ (Johnson.RunOne.StrictW.wqW C ds a xs dec K chal).sh = leavesR ds := by
  show 0 + 0 + lv _ _ (TypedOracleCompiler.Run.PQ.wiresSL C K chal ds) = _
  rw [lv_wiresSL]
  omega

end

end AtPublicFiles.ZetaAt

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.ZetaAt.lv_app
#print axioms AtPublicFiles.ZetaAt.lv_wqWhole
#print axioms AtPublicFiles.ZetaAt.lv_wqW
#print axioms AtPublicFiles.ZetaAt.lv_wires
#print axioms AtPublicFiles.ZetaAt.sum_depths
#print axioms AtPublicFiles.ZetaAt.lv_wiresLo
#print axioms AtPublicFiles.ZetaAt.lv_wiresSh
#print axioms AtPublicFiles.ZetaAt.lv_wiresSL
