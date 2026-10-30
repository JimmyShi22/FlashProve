-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PlanQS.lean: THE GENERIC PROTOCOL AND ITS WIRING, FROM ROUNDS' DATA WITH A LIST OF
TREES A ROUND.
After the library's Run/PlanQS.lean (rounds as skeletons, the view, the protocol's skeleton,
the wires, the ambient interface) and Run/PlanQWire.lean (depthOf, nOpen, maxDepth), declaration for
declaration.
  TURNED BY MATTER     roundS (Orc, Pos, Sym, dOrc), posAtS, colAtS, decSL, wireS, wire0S (its two
                       fields
                       has0 | hasJ are not here), depthOf, maxDepth
  THE SAME TEXT (they name RD or roundS)           SL, SOf, uL, drawnSL, passSL, rhoSL, rvSL,
                                                   viewSL, decOS, PSof,
                       wiresSL, wqS, LtS, nOpen
  LEFT TO THE LIBRARY s0, we0, Dn, pL, pB, dfltS, Twin.up | allLo | RS | PS, GPlain, GChal,
  chalGrind, grOf
  NOT SAID             the spellings and the typing (embPL, msgSL, nonceSL, leafSL, PDS, plainsSL,
                       placeSL, symSL,
                       TYS), the run functions and their ties (VPC … run_readers), Lo3, Lb, LbS, Wb

Terms: lean/GLOSSARY.md.

-/
import Run.PlanQS
import OnBytes.TypedOracleCompiler.Run.PlanQTypes
import OnBytes.TypedOracleCompiler.Tagged

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open _root_.Run.Twin (RS PS)

/-! ## Rounds as skeletons -/

@[reducible] def roundS (C : CK) (d : RD) : RS where
  Orc := (p : PosT d.trees) → SymT d.trees p
  Pos := PosT d.trees
  Sym := SymT d.trees
  rd := fun o p => o p
  Plain := GPlain ℕ d.entry.work (PlainOf d.items)
  Chal := GChal d.entry.work (C.Ch d.entry d.kind)
  dOrc := zeroT d.trees
  dPlain := GPlain.mk d.entry.work (PlainOf.dflt d.items) default
  finT := fun _ => inferInstance
  ne := inferInstance

@[reducible] def SL (C : CK) : List RD → List RS
  | [] => []
  | d :: ds => roundS C d :: SL C ds

abbrev SOf (C : CK) (ds : List RD) : List RS := s0 C :: SL C ds

/-- the shape behind the trivial round: in types alone -/
abbrev uL (C : CK) (ds : List RD) : Shape := Twin.up (SL C ds)

/-! ## The view -/

def drawnSL (C : CK) : (ds : List RD) → Rho (uL C ds) → List _root_.Fmt.Drawn
  | [], _ => []
  | d :: ds, (c, ρ) => C.dr d.entry d.kind (GChal.old (b := d.entry.work) c) :: drawnSL C ds ρ

def passSL (C : CK) : (ds : List RD) → Rho (uL C ds) → Bool
  | [], _ => true
  | d :: ds, (c, ρ) => GChal.pass (b := d.entry.work) c && passSL C ds ρ

def rhoSL (C : CK) : (ds : List RD) → Iop.Tr (uL C ds) → Rho (uL C ds)
  | [], _ => ()
  | _ :: ds, (_, c, τ) => (c, rhoSL C ds τ)

def rvSL (C : CK) : (ds : List RD) → Iop.Tr (uL C ds) → List RV
  | [], _ => []
  | d :: ds, (m, c, τ) =>
    ⟨PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
        C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)⟩ :: rvSL C ds τ

def posAtS (C : CK) : (ds : List RD) → Nat → Nat → Option (OPos (uL C ds))
  | [], _, _ => none
  | d :: ds, n, x =>
    if n < d.trees.length then (posAtT d.trees n x).map .inl
    else (posAtS C ds (n - d.trees.length) x).map .inr

def colAtS (C : CK) : (ds : List RD) → Iop.Tr (uL C ds) → Nat → Nat → Option (List UInt64)
  | [], _, _, _ => none
  | d :: ds, (m, _, τ), n, x =>
    if n < d.trees.length then (posAtT d.trees n x).map fun p => colT d.trees p (m.1 p)
    else colAtS C ds τ (n - d.trees.length) x

def viewSL (C : CK) (ds : List RD) (τ : Iop.Tr (uL C ds)) : View where
  rounds := rvSL C ds τ
  opened := (wanted ds (drawnSL C ds (rhoSL C ds τ))).filterMap fun nx =>
    (colAtS C ds τ nx.1 nx.2).map fun c => (nx.1, nx.2, c)

/-! ## The protocol's skeleton -/

instance decSL (C : CK) : (ds : List RD) → DecidableEq (OPos (uL C ds))
  | [] => inferInstanceAs (DecidableEq Empty)
  | d :: ds => by
      haveI := decSL C ds
      haveI := decPosT d.trees
      exact inferInstanceAs (DecidableEq (PosT d.trees ⊕ OPos (uL C ds)))

instance decOS (C : CK) (ds : List RD) : DecidableEq (OPos (Twin.up (SOf C ds))) :=
  inferInstanceAs (DecidableEq (Empty ⊕ OPos (uL C ds)))

/-- The skeleton of the protocol. -/
@[reducible] def PSof (C : CK) (ds : List RD) (dec : View → Bool) : PS Unit E0 where
  S := SOf C ds
  blinded := fun _ => true
  extReads := fun _ _ => ∅
  reads := fun _ ρ _ =>
    (((wanted ds (drawnSL C ds ρ.2)).filterMap fun nx =>
      (posAtS C ds nx.1 nx.2).map fun p => (Sum.inr p : OPos (Twin.up (SOf C ds))))).toFinset
  accept := fun _ _ τ => passSL C ds (rhoSL C ds τ.2.2) && dec (viewSL C ds τ.2.2)
  ann := Twin.allLo (SOf C ds)

/-! ## The wires -/

/-- the greatest depth of a round's trees -/
def depthOf (ts : List _root_.Fmt.Shape) : Nat := ts.foldl (fun a s => max a s.a) 0

/-- the verifier opens at most this many positions -/
def nOpen (ds : List RD) : Nat := (ds.map fun d => d.entry.poss * d.opens.length).sum

/-- the greatest depth of a tree -/
def maxDepth (ds : List RD) : Nat := ds.foldl (fun a d => max a (depthOf d.trees)) 0

/-- the wire of a round, with its test: ONE TREE FOR EACH OF THE ROUND's SHAPES -/
def wireS (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (d : RD) :
    WireRB 256 (K + 1) (roundS C d).up (roundS C d).lo where
  pt := ⟨finPosT d.trees, decPosT d.trees, fun f => f, fun _ _ => rfl, fun _ => rfl, zeroT d.trees⟩
  depth0 := []
  depthJ := d.trees.map (·.a)
  tree := treeT d.trees
  place := placeT d.trees
  posAt0 := fun _ _ => none
  posAtJ := posAtT d.trees
  chal := chalGrind (chal d.entry d.kind) d.entry.work
  prJ := true
  gr0 := none
  grJ := (grOf Dn (C.Ch d.entry d.kind) (PlainOf d.items) d.entry.work).map Tagged.ofGr

def wire0S (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    WireRB 256 (K + 1) (s0 C).up (s0 C).lo where
  pt := ⟨inferInstanceAs (Fintype Empty), inferInstanceAs (DecidableEq Empty), fun _ => (),
    fun _ p => p.elim, fun _ => rfl, fun p => p.elim⟩
  depth0 := []
  depthJ := []
  tree := fun p => p.elim
  place := fun p => p.elim
  posAt0 := fun _ _ => none
  posAtJ := fun _ _ => none
  chal := chalGrind (chal e0 .nothing) 0

def wiresSL (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    (ds : List RD) → RoundsQueryLayout 256 (K + 1) (uL C ds) (Twin.allLo (SL C ds))
  | [] => ()
  | d :: ds => (wireS C K chal d, wiresSL C K chal ds)

def wqS (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (ds : List RD) (dec : View → Bool) :
    ProtocolQueryLayout 256 (K + 1) (PSof C ds dec).up :=
  ⟨(wire0S C K chal, wiresSL C K chal ds), we0, decOS C ds, nOpen ds, maxDepth ds⟩

/-! ## The ambient interface -/

/-- The ambient interface: its Test is the protocol itself. (An interface of the LIBRARY's type: a
body is chosen beside it: Tagged.tagged, or strings.) -/
@[reducible] def LtS (C : CK) (ds : List RD) (dec : View → Bool) : _root_.Iop.BatchProtocol Unit Unit where
  wordLength := 0
  Symbol := Unit
  EncodingRandomness := Unit
  encodeIndex := fun _ _ _ => ()
  decodeIndex := fun _ => some ()
  offline := (PSof C ds dec).up.loc
  link := pL
  maxBatchSize := 1
  onlineBatch := BatchInteractiveOracleProof.ofProto pB
  honestOfflineProver := { Coin := Unit, ext := fun _ _ => (), strat := fun _ _ _ => dfltS () _,
                           Bad := ∅, Hid := fun _ _ => ∅ }
  honestLinkProver := { Coin := Unit, ext := fun _ => (fun _ => (), fun _ => ()), strat := fun _ _ _ => (),
                        Bad := ∅, Hid := fun _ _ => ∅ }
  honestOnlineBatchProver := { Coin0 := Unit, Coin := Unit, ext := fun _ _ => (), strat0 := fun _ _ => (),
                               strat := fun _ _ _ _ => (), Bad := ∅, Hid := fun _ _ => ∅, stop0 := fun _ => false }
  early := id
  late := none

end TypedOracleCompiler.Run.PQ
