-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyBase.lean: THE LAST STAGE: the base case's part says yes on what bodyAll
shows there (lastOut, Johnson/Prover/Link/BodyAll.lean). One statement and its proof: base_yes_five
(Johnson/Prover/Link/BaseWhole.lean) at the state by index.

  map_mod_of_lt   positions that lie in the range are their own residues
  base_at      BaseFront · the stage has no row variable · base_yes_five's three public clauses ·
               the claim in front is true at μOf s P, read with one row variable · the tree's
               written column is lastCol s P · "BASE lambda" drew one element · every position
               that "BASE" drew lies in the tree's range, and in its declared round's
               ⟹ the base case's part says yes on lastOut's rounds, shown without digest, and its
               group, AND LEAVES THE RECORD WRITTEN OUT: the second message marked as spent, one
               list more on the tree, nothing passed on, no mask

Not shown here. That a record meets BaseFront. Nothing on soundness; nothing on what any value that
is sent discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BodyHelps

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.Prox VerifiableInference.Desc.K12
open H2K.Pub (sgOf)

theorem map_mod_of_lt (a : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, x < 2 ^ a) → l.map (· % 2 ^ a) = l
  | [], _ => rfl
  | x :: l, h => by
    show x % 2 ^ a :: l.map (· % 2 ^ a) = x :: l
    rw [Nat.mod_eq_of_lt (h x (List.mem_cons_self ..)),
      map_mod_of_lt a l fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- **The base case's part says yes on what bodyAll shows at the last stage.** -/
theorem base_at (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (d₁ d₂ : Fmt.DeclaredRound) (o : ℕ) (t : T12)
    (P : PS) (D : ℕ → Fmt.Drawn) (row : GroupRow) (L : GroupLayout) (c : IoppStage)
    (cl : BaseClaim) (m star a : ℕ) (lam : Fmt.M1.E)
    (hst : (sgOf cur).st = cur)
    (hF : BaseFront p j cur t row L c cl m star a) (hh : (sgOf cur).h = 0)
    (hgg : (sgOf cur).g = 0) (hp : (sgOf cur).C.l = 2 ^ ceilLog2 (sgOf cur).C.l)
    (hd : row.d.size = (sgOf cur).Z.l) (hfix : FixLaw row.c [zeroE])
    (hw : (Slf.idf (E := GE) (J := (sgOf cur).cIn.J)).Holds (stmGk (sgOf cur) 1 0 row)
      (μOf (sgOf cur) P))
    (hlam : (D o).elems = [lam]) (hx : ∀ x ∈ (D (o + 1)).poss, x < 2 ^ (sgOf cur).C.a)
    (hz : inRange [d₁, d₂] ((lastOut p j cur o t P (lastCol (sgOf cur) P) (rowOf t) D).rs.map
      noDigest) = true) :
    (guardedProximityTestParts.base p j cur [d₁, d₂]).decide t
      ((lastOut p j cur o t P (lastCol (sgOf cur) P) (rowOf t) D).rs.map noDigest)
      (lastOut p j cur o t P (lastCol (sgOf cur) P) (rowOf t) D).gs = .ok { t with
        st :=
          { t.st with oracles := t.st.oracles.modify star fun x => { x with spentAsMask := true } }
        book :=
          { t.book with trees := t.book.trees.modify a fun x => { x with lists := x.lists + 1 } }
        pass := .nothing, mask := none } := by
  have hr : rowOf t = row := rowOf_claim hF.pass
  have hF' : BaseFront p j (sgOf cur).st t row L c cl m star a := by rw [hst]; exact hF
  have hcl : ((stageAt p j cur).bind fun c => claimAt t.st.codes c (rowOf t)).getD
      ⟨#[], #[], (0, 0, 0)⟩ = cl := by
    rw [hr, hF.stage]
    show (claimAt t.st.codes c row).getD _ = cl
    rw [hF.claim]
    rfl
  have key := base_yes_five p j (sgOf cur) d₁ d₂ t row L c cl m star a
    (noDigest ⟨[.e (tauSW (sgOf cur).C (sgOf cur).Z cl.c cl.d P.sM (P.fM 0))], D o⟩)
    (noDigest ⟨(shownAll (sgOf cur).C (sgOf cur).Z lam (mainOf (sgOf cur) (μOf (sgOf cur) P))
      (P.tM 0) (maskOf (sgOf cur) (μOf (sgOf cur) P)) (P.tZ 0) P.sM P.sT (P.fM 0)
      (P.fT 0)).map .e, D (o + 1)⟩)
    (groupAt (sgOf cur).C.a (D (o + 1)).poss (lastCol (sgOf cur) P)) lam (μOf (sgOf cur) P) (P.tM 0)
    (P.tZ 0) P.sM P.sT (P.fM 0) (P.fT 0) hF' hh hgg hp hd hfix hw rfl hlam rfl
    (by
      unfold groupAt
      rw [List.map_map, map_mod_of_lt _ _ hx]
      exact List.map_id _)
    (fun y hy => (mem_groupAt _ _ _ y hy).2)
    (by
      have e := hz
      unfold lastOut at e
      rw [hcl, hlam] at e
      exact e)
  rw [hst] at key
  unfold lastOut
  rw [hcl, hlam]
  exact key

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.map_mod_of_lt
#print axioms Johnson.Prover.Link.base_at
