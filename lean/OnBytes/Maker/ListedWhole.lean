-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ListedWhole.lean: at the description of a whole file (wholeDesc,
OnBytes/Maker/WholeLaws.lean; OnBytes/Maker/Whole.lean, OnBytes/Maker/Wire.lean): what the verifier
along lists (OnBytes/TypedOracleCompiler/Compile/Batch/ListedVerifier.lean) asks of its caller on the verifier's
side: the read leaves and the read positions of the stored table, as numbers, and the wiring in
pieces. Definitions, and one equation by rfl (wlOne_less).

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

A whole file's verifier reads what its three chains' draws ask for: the wants (wantsAll,
OnBytes/Maker/ReadsAt.lean): a tree's number over the whole file with a leaf, or a position of the
stored table. The description turns the wants into a set of typed positions. Here they stay numbers.
The trees are numbered round by round, from 0 at the first chain's first tree (treeAt:
OnBytes/Maker/TypingT.lean; D.t₁, D.t₂: OnBytes/Maker/Whole.lean). A local round's trees are the
slot's component's, a shared round's the shared component's (OnBytes/TypedOracleCompiler/Run/PlanQS.lean, wireS;
OnBytes/TypedOracleCompiler/Slice/Batch3Wire.lean, wireSh).

Main definitions.
  risingOf l: the members of l, each once, rising.
  rdChain: for a chain's written rounds, from the number of its first tree on: round by round and
    tree by tree the wanted leaves, rising; in the shared component's place for the second chain,
    in the slot's for the first and the third.
  rdWhole, rdEWhole: the read leaves of all rounds of the file (the front, the joining round and the
    seam have no tree), and the read positions of the stored table, rising.
  wlOne a: the stored table's wiring less its list of all positions.
  verifyWholeL: verifyBSL at these.

Limits. Definitions, and one equation by rfl. THAT rdWhole AND rdEWhole LIST EXACTLY THE POSITIONS
THAT THE DESCRIPTION READS (two premises of the equation between verifyBSL and verifyOneProtocol) IS NOT
SHOWN HERE: it is shown in OnBytes/Maker/ListedWholeLaws.lean (leavesOK_whole) and
OnBytes/Maker/ListedWholeExt.lean (rdEWhole_eq). Where openings stand in an argument string (own,
listed) is the caller's to say. risingOf strikes repeats before it sorts, at a cost that grows with
the square of the number of wants. Nothing on time or memory is a theorem. Nothing on soundness.
The program does not import this file.


-/
import OnBytes.Maker.Wire
import OnBytes.Maker.ReadsAt
import OnBytes.TypedOracleCompiler.Compile.Batch.ListedVerifier

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

/-- The members of l, each once, rising. -/
def risingOf (l : List ℕ) : List ℕ := l.dedup.mergeSort fun a b => decide (a ≤ b)

/-- The wants that ask for a leaf of a tree: the tree's number over the whole file, and the leaf. -/
def leafWants : List Want → List (ℕ × ℕ)
  | [] => []
  | .tree j x :: ws => (j, x) :: leafWants ws
  | .table _ _ :: ws => leafWants ws

/-- The wants that ask for a position of the stored table. -/
def placeWants : List Want → List ℕ
  | [] => []
  | .table _ x :: ws => x :: placeWants ws
  | .tree _ _ :: ws => placeWants ws

/-- A chain's written rounds, from tree number b on. -/
def rdChain (shared : Bool) (ws : List (ℕ × ℕ)) : ℕ → List RDT → Leaves
  | _, [] => []
  | b, d :: ds =>
    let ls := (List.range d.trees.length).map fun k =>
      risingOf ((ws.filter fun w => w.1 == b + k).map (·.2))
    (if shared then (ls, []) else ([], ls)) :: rdChain shared ws (b + d.trees.length) ds

/-- The stored table's wiring less its list of all positions. -/
def wlOne (a : ℕ) : WireELess (oneExternalString (2 ^ a) SgX) where
  which := fun _ => 0
  leaf := fun p => p.val
  depth := a
  build := fun f p => (f p).getD (0, [])
  dec := inferInstanceAs (DecidableEq (Fin (2 ^ a)))
  pr := true

/-- It is the stored table's wiring (weOne) less the list. -/
theorem wlOne_less (a : ℕ) : wlOne a = (weOne a).less := rfl

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD)
  {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- The read leaves of all rounds of the file. -/
def rdWhole (ρ : Rho (chainsOf C D tF tJ t3).sh) : Leaves :=
  let ws := leafWants (wantsAll C D tF tJ t3 ρ)
  ([], []) :: (rdChain false ws 0 D.ds₁ ++
    ([], []) :: (rdChain true ws D.t₁ D.ds₂ ++
      ([], []) :: rdChain false ws (D.t₁ + D.t₂) D.ds₃))

/-- The read positions of the stored table, rising. -/
def rdEWhole (ρ : Rho (chainsOf C D tF tJ t3).sh) : List (oneExternalString (2 ^ D.a) SgX).Pos :=
  (risingOf (placeWants (wantsAll C D tF tJ t3 ρ))).filterMap fun x =>
    if h : x < 2 ^ D.a then some (⟨x, h⟩ : Fin (2 ^ D.a)) else none

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool)

/-- **The verifier of a whole file along the lists.** own, listed: where openings stand in π. -/
def verifyWholeL (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) (own : Leaves)
    (listed : List (oneExternalString (2 ^ D.a) SgX).Pos) : TypedOracleComputation 256 (K + 1) L Bool :=
  verifyBSL sMT sFS t (wholeDesc C D tF tJ t3 silent run).batch
    (wiresOf C K chal D tF tJ t3).sh (wlOne D.a) (nOpenW D) (maxDepthW D) embS embP xin embE
    depthReq cms x π own listed (fun _ ρ _ => rdWhole C D tF tJ t3 ρ)
    (fun _ ρ => rdEWhole C D tF tJ t3 ρ)

end

end OnBytes.Maker
