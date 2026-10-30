-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/Four/Exchange.lean: THE SMALLNESS TEST: THE FIRST FOUR CLAIMS OF ITS RUN OF
EQUATIONS, EXCHANGED FOR WHAT THE LOOKUP ON THE DIGITS PUTS OUT.

The run "K8.equations" (Johnson/Desc/First/TailClaims/Equations.lean) lays a list of claims. Its
first four are no equations of the smallness test: they are the end claims of the lookup on the
digits: one on the key vectors, three on the planes of the counts. The table of joints exchanges
them, at the batching's front, for that lookup's items "keys" and "planes". Two laws of other files
meet here, and this file joins them:
  the cut of a yes of the run at `eqKeys`, `eqCounts` and the rest (`eq_parts`, `eqTail_total`:
    Johnson/Desc/First/TailClaims/EquationsCover.lean, EquationsTotal.lean);
  the payer into the lookup's row out from the four claims (`k3Out_of_rows`,
    Johnson/Top/H/K3OutRows.lean).
Main names:
  `laid_four`: `eqKeys` and then `eqCounts`, from whatever list, lay FOUR claims: under their own
    yes alone.
  `first_four`: **a yes of the whole run**: `eqKeys` and then `eqCounts` said yes from the empty
    list; what they laid are FOUR claims, and these are the first four of the run's list; the ledger
    that the run hands on is the one behind `eqCounts`.
  `k3Out_of_equations`: **THE EXCHANGE**: from a yes of the whole run, and THE FIRST FOUR CLAIMS OF
    ITS LIST WORTH 0 in the world of a later ledger H, the lookup's row out `K3Out` (its rows, its
    planes, its keys), under the premises of `k3Out_of_rows` less its free list and the two
    routines' yes.
Statements and proofs; nothing on the lookup or on the run's text is proved anew.
Limits. Those of K3OutRows.lean and of Johnson/Top/H/EqPort/EqFour.lean: a tie without an error
term; nothing where the run refuses. PREMISES, PAID BY NOBODY HERE: that the four are worth 0 (the
batching's law gives it, but for its error) · `DigRows`: the four kinds of virtual rows that the
four claims read are the stated combinations of the cells μ₀ ∘ en · the lookup's own rows' claims
and their worth · `Later` from the ledger at which the lookup was heard to the run's, and from the
run's to H · the tests on public numbers (`FoNums.ok`, `TailOK`, `PieceOK`, the pieces apart, the
sizes). All of these together at a real run: tried by nobody. NO CASE IS SHOWN HERE AT WHICH THE RUN
SAYS YES: where it never does, `first_four` and the exchange hold idly.

-/
import Johnson.Top.H.K3OutRows
import Johnson.Desc.First.TailClaims.EquationsCover

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Four

open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp Finset
open _root_.Fo _root_.Fo.Eq
open VerifiableInference.OnPublicFiles VerifiableInference.Desc.First.TailClaims

/-- **The two routines lay four claims**, from whatever list: without a yes of the whole run. Were a
claim more or fewer laid by either text, this proof would fail. -/
theorem laid_four {front : ℕ} (tl tla tlb : HTailF2) (F G1 G2 : Fork) (c c1 c2 : Array Desc.Claim)
    (hJ : EqM.at (eqKeys tl) front F c = .ok ((tla, G1), c1))
    (hB : EqM.at (eqCounts tla) front G1 c1 = .ok ((tlb, G2), c2)) : c2.size = c.size + 4 := by
  obtain ⟨_, _, _, _, _, j4, _, _⟩ := eqKeys_cut tl tla F G1 c c1 hJ
  obtain ⟨_, _, _, _, _, k3, _, _⟩ := eqCounts_cut tla tlb G1 G2 c1 c2 hB
  rw [k3, j4]
  simp

/-- **A yes of the whole run, cut behind its first four claims.** -/
theorem first_four {front : ℕ} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Desc.Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) :
    ∃ (tla tlb : HTailF2) (G1 : Fork) (c1 c2 : Array Desc.Claim),
      EqM.at (eqKeys tl) front F #[] = .ok ((tla, G1), c1) ∧
      EqM.at (eqCounts tla) front G1 c1 = .ok ((tlb, F1), c2) ∧
      c2.size = 4 ∧ cls.take 4 = c2.toList := by
  obtain ⟨before, tla, tlb, s1, s2, arr, h8, h9, k9, hcl⟩ := Law.eq_parts h
  obtain ⟨_, _, _, _, _, _, new, e, _, _⟩ :=
    Law.eqTail_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ F before tlb tl' funs front s2
      (F1, arr) k9
  have eF : F1 = s2.1 := congrArg Prod.fst e
  have eA : arr = s2.2 ++ new.toArray := congrArg Prod.snd e
  have hJ : EqM.at (eqKeys tl) front F #[] = .ok ((tla, s1.1), s1.2) :=
    (at_ok _ _ _ _).2 h8
  have hB : EqM.at (eqCounts tla) front s1.1 s1.2 = .ok ((tlb, s2.1), s2.2) :=
    (at_ok _ _ _ _).2 h9
  have hsz : s2.2.size = 4 := by
    rw [laid_four tl tla tlb F s1.1 s2.1 #[] s1.2 s2.2 hJ hB]
    rfl
  refine ⟨tla, tlb, s1.1, s1.2, s2.2, hJ, eF ▸ hB, hsz, ?_⟩
  rw [← hcl, eA, Array.toList_append, List.take_left' (by simpa using hsz)]

section
variable {K : Type} [Field K] (ρ : Reading K) {J₀ : Type} {front : ℕ}

/-- **The exchange.** -/
theorem k3Out_of_equations (tl tl' : HTailF2) (funs : Array HFun) (F F1 : Fork)
    (cls : List Desc.Claim) (h : equations front tl funs F = .ok (tl', F1, cls))
    (g : Heard) (hg : tl.heard = some g) (hs : tl.f9 = g.shape) (jLK : ℕ)
    (F' : Fork) (h0 : _root_.Fo.Later F' F)
    (hok : FoNums.ok g.shape = true) (hT : TailOK tl) (hF : Sized F)
    (hfull : 2 ^ g.shape.cK = g.shape.NC) (h5 : 5 ≤ g.shape.kT + g.shape.cK)
    (hn : ∀ q < 2, (g.zk.getD q #[]).size = (tl.zOf q).call.n)
    (h63 : ∀ q < 2, (tl.zOf q).call.n ≤ 63)
    (hP : ∀ q < 2, ∀ p ∈ piecesL tl q, PieceOK tl q (tl.zOf q).call.n p)
    (hD : ∀ q < 2, (piecesL tl q).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off)
    (en : Ent3 → J₀) (mk : ℕ → J₀) (μ₀ : J₀ → K) (entry : ℕ → ℕ → ℕ → K)
    (H : Fork) (hH : _root_.Fo.Later F1 H)
    (hV : DigRows ρ tl g entry fun e => μ₀ (en e))
    (clO : List Desc.Claim)
    (hO : ∀ rs : Rounds K, HeardIs ρ g F' (endsOf g.shape 5 jLK rs) →
      clO.map (valC ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry)) =
        (endsOf g.shape 5 jLK rs).rows.map
          (rowRes fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)))
    (hzO : ∀ k ∈ clO, valC ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry) k = 0)
    (hz : ∀ k ∈ cls.take 4, valC ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry) k = 0) :
    K3Out g.shape 5 jLK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
      (forK K (digL5 K tl en mk jLK Unit) () (zext μ₀)) ρ g F' := by
  obtain ⟨tla, tlb, G1, c1, c2, hJ, hB, _, e4⟩ := first_four h
  exact k3Out_of_rows ρ tl tla tlb F G1 F1 #[] c1 c2 hJ hB g hg hs jLK F' h0 hok hT hF hfull h5 hn
    h63 hP hD en mk μ₀ entry H hH hV clO hO hzO (e4 ▸ hz)

end

end VerifiableInference.Desc.First.K8.Four

#print axioms VerifiableInference.Desc.First.K8.Four.laid_four
#print axioms VerifiableInference.Desc.First.K8.Four.first_four
#print axioms VerifiableInference.Desc.First.K8.Four.k3Out_of_equations
