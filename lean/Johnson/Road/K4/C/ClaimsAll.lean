-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/ClaimsAll.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the weight claims: THE WHOLE LIST OF THE
PANELS' WEIGHT CLAIMS RETURNS (weightClaims, OnBytes/Model/LayerPanels.lean, at the calls 0, 1, 2, 5
for the second walk): six claims for each layer of the group and four for each layer with routed
experts, each on a unit of the layout of the weights and with the sizes that the layout asks. At the
library's eight lines of calls the function walks two lists of segments' names; segment by segment
the claims return (ClaimsWalk.lean, ClaimsQK.lean) or there are none (the library's claimsA_not,
claimsT_other). Two definitions; statements and proofs. General in the sizes.

  `retCl_nil`, `retCl_names`   no claim; a walk over names, each with its number of claims.
  `pairsA`, `pairsT`           the names of the two walks, each with its number of claims.
  `namesA_eq`, `namesT_eq`     the verifier's two lists of names are these.
  `pairsA_ret`, `pairsT_ret`   each name returns its number of good claims.
  **`weightClaims_ret`**       the whole list.

Not shown here. That the hypotheses hold at any plan: no example is shown here. WHO HAS THE TWO
BUNDLES: ClaimRdOf.lean (claimRd_of, qkRd_of), AT THE BLANK STRUCTURE ALONE, where every challenge
and coordinate is 0; at a structure with sampled challenges no statement has them. There
weightClaims_ret has its one caller (ClaimsBOf.lean). AT A LAYOUT WHOSE EIGHT LINES OF CALLS ARE THE
LIBRARY's AND A LAYOUT OF THE WEIGHTS THAT wsLayOf RETURNS FOR A MODEL WITH ROUTED EXPERTS. ClaimRd
also asks: that the dense width is twice an expert's (f = 2 fe); switch p3 on; each routed layer's
number in the group; five sizes at least one. The embedding's claim is not here. Public data alone:
whether a claim IS THERE and how long its parts are; nothing on its elements.
No property is claimed.
-/
import Johnson.Road.K4.C.ClaimsQK
import Johnson.Road.FormsKeysPans

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (ClaimEnv callsAC)
open Inst.Model (Params)

/-- No claim. -/
theorem retCl_nil {lay : WsLay} {x : Option (List WsClaim)} (h : x = some []) : RetCl lay x 0 :=
  ⟨[], h, rfl, fun _ hc => by cases hc⟩

/-- A walk over names, each with its number of good claims: the lists are returned, and together
they hold the sum of the numbers, all good. -/
theorem retCl_names {lay : WsLay} {f : String → Option (List WsClaim)} :
    ∀ (l : List (String × ℕ)), (∀ p ∈ l, RetCl lay (f p.1) p.2) →
    ∃ a, (l.map (·.1)).mapM f = some a ∧ a.flatten.length = (l.map (·.2)).sum ∧
      ∀ cl ∈ a.flatten, GoodCl lay cl
  | [], _ => ⟨[], rfl, rfl, fun _ h => by cases h⟩
  | p :: l, h => by
    obtain ⟨x, h1, h2, h3⟩ := h p List.mem_cons_self
    obtain ⟨a, a1, a2, a3⟩ := retCl_names l fun b hb => h b (List.mem_cons_of_mem _ hb)
    refine ⟨x :: a, ?_, ?_, fun cl hcl => ?_⟩
    · rw [List.map_cons, List.mapM_cons, h1, a1]
      rfl
    · rw [List.flatten_cons, List.length_append, h2, a2, List.map_cons, List.sum_cons]
    · rw [List.flatten_cons, List.mem_append] at hcl
      rcases hcl with hc | hc
      · exact h3 cl hc
      · exact a3 cl hc

/-- The names of the first walk, each with its number of claims. -/
def pairsA (c : ClaimEnv) : List (String × ℕ) :=
  [("G", c.v.y.Lam), ("U", c.v.y.Lam), ("N1", 0), ("N1H", 0), ("N2", 0), ("N2H", 0),
   ("O", c.v.y.Lam), ("D", c.v.y.Lam), ("V", c.v.y.Lam), ("QK", 0), ("QKH", 0), ("XR", 0),
   ("LR", c.v.y.LamM), ("LT", 0), ("DD", 0)]

/-- The names of the second walk, each with its number of claims. -/
def pairsT (c : ClaimEnv) : List (String × ℕ) :=
  [("G", c.v.y.LamM), ("U", c.v.y.LamM), ("N1", 0), ("N1H", 0), ("N2", 0), ("N2H", 0), ("O", 0),
   ("D", c.v.y.LamM), ("V", 0), ("QK", c.v.y.Lam), ("QKH", 0), ("XR", 0), ("LR", 0), ("LT", 0),
   ("DD", 0), ("MR", 0), ("CG", 0)]

variable {c : ClaimEnv} {s : WsShape} {P : Params} {lk : ℕ}

/-- The verifier's list of names for the first walk. -/
theorem namesA_eq (hN : LinesAre c.v.y) :
    ((callsAC c.v.y).flatMap fun q => (c.v.y.calls.getD q default).segs.map (·.name)) =
      (pairsA c).map (·.1) := by
  have l0 : (c.v.y.calls.getD 0 default).segs.map (·.name) = ["G", "U"] := line_at hN 0
  have l1 : (c.v.y.calls.getD 1 default).segs.map (·.name) =
      ["N1", "N1H", "N2", "N2H", "O", "D", "V"] := line_at hN 1
  have l2 : (c.v.y.calls.getD 2 default).segs.map (·.name) =
      ["QK", "QKH", "XR", "LR", "LT", "DD"] := line_at hN 2
  rw [callsAC_of_lines hN]
  simp only [List.flatMap_cons, List.flatMap_nil, l0, l1, l2]
  rfl

/-- The verifier's list of names for the second walk. -/
theorem namesT_eq (hN : LinesAre c.v.y) :
    (([0, 1, 2, 5] : List ℕ).flatMap fun q => (c.v.y.calls.getD q default).segs.map (·.name)) =
      (pairsT c).map (·.1) := by
  have l0 : (c.v.y.calls.getD 0 default).segs.map (·.name) = ["G", "U"] := line_at hN 0
  have l1 : (c.v.y.calls.getD 1 default).segs.map (·.name) =
      ["N1", "N1H", "N2", "N2H", "O", "D", "V"] := line_at hN 1
  have l2 : (c.v.y.calls.getD 2 default).segs.map (·.name) =
      ["QK", "QKH", "XR", "LR", "LT", "DD"] := line_at hN 2
  have l5 : (c.v.y.calls.getD 5 default).segs.map (·.name) = ["MR", "CG"] := line_at hN 5
  simp only [List.flatMap_cons, List.flatMap_nil, l0, l1, l2, l5]
  rfl

/-- Each name of the first walk returns its number of good claims. -/
theorem pairsA_ret (R : ClaimRd c s P lk) : ∀ p ∈ pairsA c, RetCl c.wsLay (c.claimsA p.1) p.2 := by
  intro p hp
  unfold pairsA at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact claimsA_G R
  · exact claimsA_U R
  · exact retCl_nil (claimsA_not c _ rfl)
  · exact retCl_nil (claimsA_not c _ rfl)
  · exact retCl_nil (claimsA_not c _ rfl)
  · exact retCl_nil (claimsA_not c _ rfl)
  · exact claimsA_O R
  · exact claimsA_D R
  · exact claimsA_V R
  · exact retCl_nil (claimsA_not c _ rfl)
  · exact retCl_nil (claimsA_not c _ rfl)
  · exact retCl_nil (claimsA_not c _ rfl)
  · exact claimsA_LR R
  · exact retCl_nil (claimsA_not c _ rfl)
  · exact retCl_nil (claimsA_not c _ rfl)

/-- Each name of the second walk returns its number of good claims. -/
theorem pairsT_ret (R : ClaimRd c s P lk) (Q : QkRd c s) :
    ∀ p ∈ pairsT c, RetCl c.wsLay (c.claimsT p.1) p.2 := by
  intro p hp
  unfold pairsT at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact claimsT_G R
  · exact claimsT_U R
  · exact retCl_nil (claimsT_other c _ (by decide) (by rw [R.p3]; decide))
  · exact retCl_nil (claimsT_other c _ (by decide) (by rw [R.p3]; decide))
  · exact retCl_nil (claimsT_other c _ (by decide) (by rw [R.p3]; decide))
  · exact retCl_nil (claimsT_other c _ (by decide) (by rw [R.p3]; decide))
  · exact retCl_nil (claimsT_other c _ (by decide) (by rw [R.p3]; decide))
  · exact claimsT_D R
  · exact retCl_nil (claimsT_other c _ (by decide) (by rw [R.p3]; decide))
  · exact claimsT_QK R Q
  · exact retCl_nil (claimsT_other c _ (by decide) (by rw [R.p3]; decide))
  · exact retCl_nil (claimsT_other c _ (by decide) (by rw [R.p3]; decide))
  · exact retCl_nil (claimsT_other c _ (by decide) (by rw [R.p3]; decide))
  · exact retCl_nil (claimsT_other c _ (by decide) (by rw [R.p3]; decide))
  · exact retCl_nil (claimsT_other c _ (by decide) (by rw [R.p3]; decide))
  · exact retCl_nil (claimsT_other c _ (by decide) (by rw [R.p3]; decide))
  · exact retCl_nil (claimsT_other c _ (by decide) (by rw [R.p3]; decide))

/-- **THE WHOLE LIST OF THE PANELS' WEIGHT CLAIMS RETURNS**: six good claims for each layer of the
group and four for each layer with routed experts. CONDITIONAL: on the eight lines, R and Q. -/
theorem weightClaims_ret (hN : LinesAre c.v.y) (R : ClaimRd c s P lk) (Q : QkRd c s) :
    RetCl c.wsLay (c.weightClaims [0, 1, 2, 5]) (6 * c.v.y.Lam + 4 * c.v.y.LamM) := by
  obtain ⟨a, a1, a2, a3⟩ := retCl_names (pairsA c) (pairsA_ret R)
  obtain ⟨t, t1, t2, t3⟩ := retCl_names (pairsT c) (pairsT_ret R Q)
  rw [← namesA_eq hN] at a1
  rw [← namesT_eq hN] at t1
  refine ⟨a.flatten ++ t.flatten, ?_, ?_, fun cl hcl => ?_⟩
  · unfold ClaimEnv.weightClaims
    dsimp only
    rw [a1]
    show (do
      let t ← (([0, 1, 2, 5] : List ℕ).flatMap fun (q : ℕ) =>
        (c.v.y.calls.getD q (default : CallD)).segs.map fun (g : Seg) => g.name).mapM c.claimsT
      pure (a.flatten ++ t.flatten)) = _
    rw [t1]
    rfl
  · rw [List.length_append, a2, t2]
    unfold pairsA pairsT
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · rcases List.mem_append.mp hcl with hc | hc
    · exact a3 cl hc
    · exact t3 cl hc

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.retCl_nil
#print axioms OnBytes.Road.K4.C.retCl_names
#print axioms OnBytes.Road.K4.C.namesA_eq
#print axioms OnBytes.Road.K4.C.namesT_eq
#print axioms OnBytes.Road.K4.C.pairsA_ret
#print axioms OnBytes.Road.K4.C.pairsT_ret
#print axioms OnBytes.Road.K4.C.weightClaims_ret
