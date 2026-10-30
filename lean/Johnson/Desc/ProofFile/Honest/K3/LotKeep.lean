-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/LotKeep.lean: the honest side of the lot of lookups at rows that
pass their tables on (`proverSideOfLookupInChainKeepingTablesAtOneOwner`, Honest/K3/RowKeep.lean), beside `rowLot` and `rowLotAt`
(Honest/K3/LotRow.lean, Honest/K3/LotFilled.lean). Definitions with code; no theorem.

Terms. Honest/K3/GLOSSARY.md. In this file: a row's own state is a value of `RowOwn`
(Honest/K3/KeptTypes.lean).

What is defined.
  `FillKeep`: the letters that are left, site by site: the row's two letters (`Keeps`) and the
    reader of the chain's input.
  `rowLotKeep A get set`: at each site the row that passes its tables on, seated. Beside `rowLot`'s
    argument it takes get and set: how the row's own state is read in what the chain's parts pass
    on, and how it is laid there. All sites share the one place in the chain's state: a row begins
    and ends at `rowOwn₀`, and the rows of a chain are played one behind the other.
  `rowLotKeepAt`: the same at letters that may read the public part.

Imported. Honest/K3/Lot.lean for the sites and the lot's name; Honest/K3/RowKeep.lean for the row.
The frame's files lie beneath them.

Users. Honest/K3/RowKeepFill.lean; Honest/K3/LotInstKeep.lean. Meant for a filling of the honest
prover whose state has a field of the type `RowOwn`: get reads that field and set lays it.

Limits. Letters: see Honest/K3/RowKeep.lean under "Limits". Nothing asks that get and set fit each
other. With a get that always gives `rowOwn₀` every move makes its tables from the start. That a
row begins at `rowOwn₀` in a run is not shown here: it wants the chain's first state to hold it and
every other part to leave the field alone. That the rows of a chain are played one behind the other,
so that one place in the chain's state serves all sites, is said above and not shown.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Lot
import Johnson.Desc.ProofFile.Honest.K3.RowKeep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3

variable {V W X : Type}

/-- **The letters that are left**, site by site. Here W is the chain's input. -/
structure FillKeep (W : Type) where
  /-- the stages' jobs with a kept state, and the maker of the store -/
  keeps : Site → Keeps
  /-- the small structure, of the chain's input -/
  wit : Site → W → Ask

/-- **The lot's honest side at rows that pass their tables on**: at each site the row, seated. -/
def rowLotKeep (A : FillKeep W) (get : X → RowOwn) (set : X → RowOwn → X) : HLot V W X :=
  lotBy fun s => (proverSideOfLookupInChainKeepingTablesAtOneOwner (A.keeps s) (A.wit s) get set s.at_).parts

/-- The same at letters that may read the public part. -/
def rowLotKeepAt (A : Pub → FillKeep W) (get : X → RowOwn) (set : X → RowOwn → X) : HLot V W X :=
  { name := lotName
    halves := fun Z G => (rowLotKeep (A Z) get set).halves Z G }

end ProofFile.Honest.K3
