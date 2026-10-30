-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/JoinReader.lean: CONDITIONAL.

Not shown here. That the hypotheses hold anywhere: no example is known. That the public parameters
X hold the plans of the public numbers Q.P (hG; Johnson/Road/K4/C/BordersTails.lean's
plans_tails_at gives its form where X.G is what plansG returns and the lists are tailsOf's); that
the model has attention layers between the groups (h4); that an owner's group is a group (hog);
that the list of the lookup's link at K4's segment has at number mu the entry of the public
numbers' list (hM); that this entry is borrowed or begins at column 0 (hk). For cellsAre_reader:
these at every matrix, with hM as one equation of lists (hTl). Nothing on what a cell holds. By a
walk over the files' imports the closure holds seven modules under Johnson/RecCompile/ (Join, Wire,
Pass, CmsGlue, CmsBcs, Cms, Bcs); none under Johnson/Goal/ or Johnson/D/; under Johnson/RecCompile/
none of the names Honest…, Both…, PassH…. No property is claimed.

THE LOOKUP's READER OF A MATRIX AND K4's SMALL INPUT READ ONE CELL. The honest side of the kind
"lookup" reads cell (r, c) of matrix number mu of a link's list by atOwn
(Johnson/Desc/ProofFile/Honest/K3/WitOwner.lean), off the reader of the witness's cells; K4's parts
read it by k4Wit (Johnson/Desc/ProofFile/Honest/K4/Part.lean), off the same reader. Both go through
the owner's key: atOwn_is (Honest/K3/Law/OwnerKeyIs.lean) and k4Owner_key
(Honest/K4/Law/OwnerIs.lean).

  `gl_slice`        a word made of an element of the base field reads as that element.
  **`reader_is_ours`**   the title's sentence, at the reading Reading.gl.
  `weight_is_ours`  the like for an entry of the committed matrix of the weights: no premise.
  `at_getD`         a tool.
  **`cellsAre_reader`**   so the lookup's reader's matrices meet CellsAre
      (Johnson/Road/K4/C/Cells.lean) at K4's small input.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.OwnerKeyIs
import Johnson.Desc.ProofFile.Honest.K4.Law.OwnerIs
import Johnson.Road.K4.C.Cells

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Model (Reading)
open OnBytes.Desc.First.K4.Honest (K4Pub matsOf)
open OnBytes.Road.K4.C (CellsAre)

/-- A word made of an element of the base field reads as that element. -/
theorem gl_slice (x : Cb.Gl.F) :
    Reading.gl.val (OnBytes.ofF (OnBytes.Slice.ofF x)) = algebraMap Cb.Gl.F Cb.Gl.E x := by
  show OnBytes.Slice.readE (OnBytes.ofF (OnBytes.Slice.ofF x)) = _
  rw [OnBytes.Slice.readE_ofF, OnBytes.Slice.toF_ofF]

variable {W₀ Rc Xi Tr : Type}

/-- **The lookup's reader of a matrix and K4's small input read one cell.** CONDITIONAL: on every
hypothesis named. -/
theorem reader_is_ours (Q : K4Pub) (X : OnBytes.Model.Verify.Public) (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard) (i : Local W₀ Rc Xi Tr) (mu r c : Nat)
    (h4 : X.p4 = true)
    (hog : ((Q.P.tails.getD Q.g {}).mats.getD mu {}).kind = 1 →
      ((Q.P.tails.getD Q.g {}).mats.getD mu {}).aId / 256 - 1 < X.NGr)
    (hG : ∀ og, og < X.NGr → (X.G[og]?).map (·.tl.mats) = (Q.P.tails[og]?).map (·.mats))
    (hM : (K3.tlOf X Q.seg).mats[mu]? = some ((Q.P.tails.getD Q.g {}).mats.getD mu {}))
    (hk : ((Q.P.tails.getD Q.g {}).mats.getD mu {}).kind = 1 ∨
      ((Q.P.tails.getD Q.g {}).mats.getD mu {}).ttOff = 0) :
    K3.atOwn X (cells i.trace).cell Q.seg mu r c =
      Reading.gl.val (OnBytes.ofF ((k4Wit Q cells weights tokens look i).cell mu r c)) := by
  rw [K3.atOwn_is X _ Q.seg mu r c _ hM hk, ← k4Owner_key Q mu X h4 hog hG]
  exact (gl_slice _).symm

/-- The like for an entry of the committed matrix of the weights. -/
theorem weight_is_ours (Q : K4Pub) (cells : Tr → Cells) (weights : W₀ → Weights)
    (tokens : Xi → Array Nat) (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    (i : Local W₀ Rc Xi Tr) (r c : Nat) :
    algebraMap Cb.Gl.F Cb.Gl.E ((weights i.w₀).entry r c) =
      Reading.gl.val (OnBytes.ofF ((k4Wit Q cells weights tokens look i).w r c)) :=
  (gl_slice _).symm

/-- A member of an array, below its size. -/
theorem at_getD {α : Type} (ms : Array α) (d : α) {n : Nat} (h : n < ms.size) :
    ms[n]? = some (ms.getD n d) := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
  rfl

/-- **The lookup's reader's matrices meet CellsAre at K4's small input.** CONDITIONAL: on every
hypothesis named. hTl: the list of the lookup's link at K4's segment is the public numbers' list of
the group. -/
theorem cellsAre_reader (Q : K4Pub) (X : OnBytes.Model.Verify.Public) (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard) (i : Local W₀ Rc Xi Tr)
    (h4 : X.p4 = true)
    (hog : ∀ mu, ((Q.P.tails.getD Q.g {}).mats.getD mu {}).kind = 1 →
      ((Q.P.tails.getD Q.g {}).mats.getD mu {}).aId / 256 - 1 < X.NGr)
    (hG : ∀ og, og < X.NGr → (X.G[og]?).map (·.tl.mats) = (Q.P.tails[og]?).map (·.mats))
    (hTl : (K3.tlOf X Q.seg).mats = (Q.P.tails.getD Q.g {}).mats)
    (hk : ∀ mu, ((Q.P.tails.getD Q.g {}).mats.getD mu {}).kind = 1 ∨
      ((Q.P.tails.getD Q.g {}).mats.getD mu {}).ttOff = 0) :
    CellsAre Q (k4Wit Q cells weights tokens look i)
      (fun a r c => K3.atOwn X (cells i.trace).cell Q.seg a r c) := by
  intro mu _ r c hr _
  have hlt : mu < (Q.P.tails.getD Q.g {}).mats.size := by
    by_contra hn
    have e : (matsOf Q).getD mu (0, 0) = (0, 0) := by
      unfold matsOf
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
        rw [Array.size_map]
        omega)]
      rfl
    rw [e] at hr
    exact absurd hr (Nat.not_lt_zero _)
  refine reader_is_ours Q X cells weights tokens look i mu r c h4 (hog mu) hG ?_ (hk mu)
  rw [hTl]
  exact at_getD _ _ hlt

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.gl_slice
#print axioms ProofFile.Honest.K4.reader_is_ours
#print axioms ProofFile.Honest.K4.weight_is_ours
#print axioms ProofFile.Honest.K4.at_getD
#print axioms ProofFile.Honest.K4.cellsAre_reader
