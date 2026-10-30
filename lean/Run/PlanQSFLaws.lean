-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQSFLaws.lean: the wiring with whole paths meets the library's conditions on a wiring
wherever the wiring with pruned openings does. (Whole paths: each opened leaf has an authentication
path of its own. Pruned openings: the opened leaves of a tree share one set of sibling digests, as
in the files.)

A wiring is the data that say how deep the trees are, where a position stands among a tree's leaves,
and how hash output becomes challenges. The library's conditions on a wiring that may have tests of
work (Iop/BatchWire.lean: `WireRB.OKG`, `RoundsQueryLayout.OKG`, `ProtocolQueryLayout.OKG`) speak of places, depths,
positions, the distribution of the verifier message, and the records of the tests. (The records of
the tests: the data of a round's proof-of-work test: `GrW`; fields `gr0`, `grJ` of `WireRB`,
Iop/BatchWire.lean.) No clause names the flag that selects pruned openings. The wirings of
Run/PlanQSF.lean are those of Run/PlanQS.lean with that flag false.

1. What the file contains. The lemmas `wireSF_okg`, `wiresSLF_okg`, `depthSLF`, round by round.

2. What is checked when the file compiles. Nothing beyond the proofs.

3. Theorems.
   `wqSF_okg` (statement `Run.PQ.Spec.wqSF_okg`)
                        `(wqS C K chal ds dec).OKG → (wqSF C K chal ds dec).OKG`, for every choice C
                        of challenge types, number K of blocks, samplers, list of rounds and
                        decision.

4. What is not claimed. That `wqS` meets the conditions at a given choice C of challenge types: for
   that see Run/PlanQSLaws.lean (`wqS_okg`, under its hypotheses) and Run/PlanPull.lean (challenges
   as hash blocks). The conditions on the wiring of a whole interface are not in this file; for them
   see Run/BatchDoor.lean (`okgWb`).

Terms: lean/GLOSSARY.md.
-/
import Run.PlanQSF
import Run.PlanQSLaws

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch

theorem wireSF_okg (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (d : RD) (h : (wireS C K chal d).OKG) : (wireSF C K chal d).OKG :=
  { place_lt0 := h.place_lt0, place_ltJ := h.place_ltJ, posAt0_place := h.posAt0_place,
    posAtJ_place := h.posAtJ_place, place_posAt0 := h.place_posAt0, place_posAtJ := h.place_posAtJ
    no0 := h.no0, noJ := h.noJ, chal_unif := h.chal_unif, gr0_ok := h.gr0_ok, grJ_ok := h.grJ_ok }

theorem wiresSLF_okg (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    ∀ ds : List RD, RoundsQueryLayout.OKG (uL C ds) (Twin.allLo (SL C ds)) (wiresSL C K chal ds) →
      RoundsQueryLayout.OKG (uL C ds) (Twin.allLo (SL C ds)) (wiresSLF C K chal ds)
  | [], _ => trivial
  | d :: ds, h => ⟨wireSF_okg C K chal d h.1, wiresSLF_okg C K chal ds h.2⟩

theorem depthSLF (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (n : Nat) :
    ∀ ds : List RD, RoundsQueryLayout.DepthLe n (uL C ds) (Twin.allLo (SL C ds)) (wiresSL C K chal ds) →
      RoundsQueryLayout.DepthLe n (uL C ds) (Twin.allLo (SL C ds)) (wiresSLF C K chal ds)
  | [], _ => trivial
  | _ :: ds, h => ⟨h.1, depthSLF C K chal n ds h.2⟩

def Spec.wqSF_okg : Prop :=
  ∀ (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
      (ds : List RD) (dec : View → Bool),
    (wqS C K chal ds dec).OKG → (wqSF C K chal ds dec).OKG

theorem wqSF_okg : Spec.wqSF_okg := fun C K chal ds _ h =>
  { sh := ⟨h.sh.1, wiresSLF_okg C K chal ds h.sh.2⟩
    ext := h.ext
    opens := h.opens
    depth := ⟨h.depth.1, depthSLF C K chal _ ds h.depth.2⟩ }

end Run.PQ
