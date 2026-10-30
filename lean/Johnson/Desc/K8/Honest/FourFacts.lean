-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/FourFacts.lean: THE SMALLNESS TEST: WHAT `vals4_zero`
(Johnson/Desc/K8/Honest/ValsZero.lean) ASKS BESIDE THE RUN's YES, GATHERED INTO ONE NAMED SENTENCE
ON WHAT IS FIXED IN FRONT OF THE BATCHING AND THE WITNESS's DATA, so that a caller at a state need
not name its letters. A definition and one lemma; none of the library's goals.

  `FourFacts u π q y`   A BUNDLE: at every data tl that what is fixed shows blanked, the snapshot v
                   and what the lookup heard g: TWELVE FACTS ON tl, g AND v, AND: there are letters
                   en, mk, μ₀, a number, a ledger F' that the snapshot's is later than, and one list
                   of rounds rs at which the heard structure stands and the lookup's two items hold,
                   with the three ties of the letters to the data's cells and mask row
  **`vals4_of_facts`**   the run's yes at tl and F · what is fixed shows tl blanked · the snapshot
                   v, with its sizes · F later than the snapshot's ledger · FourFacts ⊢ the term's
                   four values are 0
AGAINST `vals4_zero`'s OWN PREMISES TWO STAND IN ANOTHER FORM: the masks are asked at `four8 tl g`
(under the run's yes that is the list's first four) · THE LOOKUP's LEDGER IS ASKED TO BE EARLIER
THAN THE SNAPSHOT's, WHICH IS MORE THAN `vals4_zero` ASKS (it has it at the run's ledger): so no
walk through the gatherer is wanted for it.
Limits. `FourFacts` IS A PREMISE, AND A HEAVY ONE: THAT AN HONEST STATE MEETS IT IS NOT SAID HERE;
its three ties follow from named premises (`ties_of_rest`, TiesOfRest.lean). Its "at every tl with
that blanked form" asks no more than at one: Johnson/Desc/K8/Honest/FourFactsAt.lean.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.ValsZero
import Johnson.Top.H.Keep.RunsPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.First.K8.Honest
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp Finset
open _root_.Fo _root_.Fo.Eq
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First.TailClaims (equations)
open VerifiableInference.Desc.First.TailClaims.Law (blank eq_later)
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K9L (Pub9 Bound GE8 claimValue vals4 four8 four8_blank take_four)
open VerifiableInference.Desc.LinkJoin (ent4)
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.Desc.K4Values (refWorld winOf LaidAt InWin laid_of_run)

variable {α : Type}

/-- **The bundle**: what `vals4_zero` asks beside the run's yes and what a stand gives. -/
def FourFacts (u : HTailF2) (π : α → Option HTailF2 × Option (Array HFun))
    (q : α × Option Pub9) (y : Bound GE8) : Prop :=
  ∀ (tl : HTailF2) (v : Pub9) (g : Heard), (π q.1).1 = some (blank u tl) → q.2 = some v →
    tl.heard = some g →
    (∀ cl ∈ four8 tl g, ∀ x ∈ cl.form.slots.toList,
      InWin (winOf g.leaves) x.1 ∨ OnBytes.PscRun.Filled v.F x.1) ∧
    tl.f9 = g.shape ∧ FoNums.ok g.shape = true ∧ TailOK tl ∧
    2 ^ g.shape.cK = g.shape.NC ∧ 5 ≤ g.shape.kT + g.shape.cK ∧
    (∀ c < 2, (g.zk.getD c #[]).size = (tl.zOf c).call.n) ∧
    (∀ c < 2, (tl.zOf c).call.n ≤ 63) ∧
    (∀ c < 2, ∀ p ∈ piecesL tl c, PieceOK tl c (tl.zOf c).call.n p) ∧
    (∀ c < 2, (piecesL tl c).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off) ∧
    CoefOK (blank u tl) v.F ∧
    (∀ a ∈ allPieces tl, a.2.r0 + a.2.Rp ≤ (v.F.trees.getD a.2.tree {}).R) ∧
    ∃ (jLK : ℕ) (F' : Fork) (J₀ : Type) (en : Ent3 → J₀) (mk : ℕ → J₀) (μ₀ : J₀ → GE8)
      (rs : Rounds GE8), _root_.Fo.Later F' v.F ∧
      (∀ r < 32, ∀ i < tl.bzColumns, entUnit q y tl.ix.BZ r i = μ₀ (en (tl.ix.BZ, r, i))) ∧
      (∀ c < 2, ∀ p ∈ piecesL tl c, ∀ r < p.Rp, ∀ i < p.Cp,
        entUnit q y tl.ix.ZZ (p.r0 + r) (p.c0 + i) = μ₀ (en (tl.ix.ZZ, p.r0 + r, p.c0 + i))) ∧
      (∀ k ∈ four8 tl g, ∀ s ∈ k.form.slots.toList, y.mask s.1 = μ₀ (mk s.1)) ∧
      HeardIs Reading.gl g F' (endsOf g.shape 5 jLK rs) ∧
      K3Planes g.shape 5 jLK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)) rs ∧
      K3Keys g.shape 5 jLK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
        (forK GE8 (digL5 GE8 tl en mk jLK Unit) () (zext μ₀)) rs

/-- **The term's four values are 0, from the bundle.** -/
theorem vals4_of_facts (π : α → Option HTailF2 × Option (Array HFun)) (u : HTailF2)
    (q : α × Option Pub9) (y : Bound GE8) {front : ℕ} {tl tl' : HTailF2} {funs : Array HFun}
    {F F1 : Fork} {cls : List Desc.Claim} (he : equations front tl funs F = .ok (tl', F1, cls))
    {v : Pub9} (h1 : (π q.1).1 = some (blank u tl)) (h2 : q.2 = some v)
    (hsz : OnBytes.PscRun.Sized v.F) (hU : OnBytes.PscRun.Later v.F F)
    (hF : FourFacts u π q y) : ∀ x ∈ vals4 π (ent4 π) q y, x = 0 := by
  obtain ⟨g, Fa, hg, h4, -, -⟩ := take_four he
  obtain ⟨hslots, hs, hok, hT, hfull, h5, hn, h63, hP, hD, hC, hRw, jLK, F', J₀, en, mk, μ₀, rs,
    hF', hcb, hcz, hm, hI, hPl, hKy⟩ := hF tl v g h1 h2 hg
  exact vals4_zero π u q y he h1 h2 hg hsz hU hslots hs jLK F' (hF'.trans (OnPublicFiles.fo_of_psc hU))
    hok hT hfull h5 hn h63 hP hD hC hRw en mk μ₀ hcb hcz (fun k hk => hm k (h4 ▸ hk)) rs hI hPl hKy

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.vals4_of_facts
#print axioms VerifiableInference.Desc.First.K8.Honest.FourFacts
