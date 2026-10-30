-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/ValsZero.lean: THE SMALLNESS TEST: THE FOUR VALUES AT WHICH THE LIBRARY's
TERM `tmFour` (Johnson/Desc/First/Link/Law/LinkRestAtSort2.lean: `numbered n (vals4 pi8 (ent4 pi8) q
y)`) VALUES THE FIRST FOUR CLAIMS OF THE RUN "K8.equations" OFF WHAT IS FIXED IN FRONT OF THE
BATCHING's DRAW ARE ALL 0, WHERE THAT RUN SAYS YES, THE LOOKUP ON THE DIGITS STANDS AND ITS TWO
ITEMS "planes" AND "keys" HOLD. The last link behind Johnson/Desc/K8/Honest/FourZero.lean: from the
world H.worldOf … to the world that the snapshot's ledger names (`K4Values.refWorld`). NO STATE IS
NAMED. Lemmas; none of the library's goals.

  **`claim_refOf`**   a claim's value in the world that the ledger U names is its value at a later
                   ledger B, at the same entries, if each slot that its form names lies in a window
                   that is laid in B or is filled in U: the slots' half of the library's `claim_ref`
                   (Johnson/Desc/First/Batch/Law/K8Four.lean), with the entries a free letter
  **`vals4_zero`**   … → ∀ x ∈ vals4 π (ent4 π) q y, x = 0
Limits. AN IMPLICATION WITH MANY PREMISES, NONE PAID HERE: most of those of `four_zero_ent4` (see
that file's Limits), and three more on the snapshot's ledger: it has its sizes (hsz); the run's
ledger is later than it (hU); each slot that the four name lies in the window of the leaves'
sumcheck or is filled in it (hslots): the second half of the library's promise in front of the draw.
THE RUN's YES (he) IS A PREMISE: on the honest side it lies inside the yes of the batching's
gathering of claims. The ties of the letters en, mk, μ₀ to the data (hcb, hcz, hm4) follow from
named premises: `ties_of_rest` (TiesOfRest.lean).
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.FourZero
import Johnson.Desc.First.Batch.Law.K8FourZero

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
open VerifiableInference.Desc.ValueLater (value_on)

/-- **The slots' half, with the entries a free letter.** -/
theorem claim_refOf {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K) (cl : Desc.Claim)
    (U B : Fork) (wins : List (ℕ × ℕ)) (ent : ℕ → ℕ → ℕ → K) (y : Bound K)
    (hU : OnBytes.PscRun.Later U B) (hw : ∀ w ∈ wins, LaidAt B w)
    (hs : ∀ x ∈ cl.form.slots.toList, (∃ w ∈ wins, InWin w x.1) ∨ OnBytes.PscRun.Filled U x.1) :
    claimValue ρ (refWorld ρ U wins ent y) cl = valC ρ (B.worldOf ρ y.mask ent) cl := by
  have e1 : cl.form.value ρ (refWorld ρ U wins ent y) =
      cl.form.value ρ (B.worldOf ρ y.mask ent) := by
    refine value_on ρ cl.form _ _ (fun x hx => ?_) fun _ _ => rfl
    show (if ∃ w ∈ wins, InWin w x.1 then y.mask x.1
      else ρ.val (U.vp.getD x.1 zeroE) - ρ.val (U.mf.getD x.1 zeroE) * y.mask x.1) =
      ρ.val (B.vp.getD x.1 zeroE) - ρ.val (B.mf.getD x.1 zeroE) * y.mask x.1
    by_cases hin : ∃ w ∈ wins, InWin w x.1
    · rw [if_pos hin]
      obtain ⟨w, hw', hj⟩ := hin
      obtain ⟨h1, h2⟩ := hw w hw' x.1 hj
      rw [h1, h2, ρ.sub, ρ.zero, ρ.one]
      ring
    · rw [if_neg hin]
      obtain ⟨_, h1, h2⟩ := hU.keep x.1 ((hs x hx).resolve_left hin)
      rw [h1, h2]
  have e2 : Run2.value ρ (refWorld ρ U wins ent y) = Run2.value ρ (B.worldOf ρ y.mask ent) :=
    funext fun _ => rfl
  unfold claimValue valC
  rw [e1, e2]

variable {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) {J₀ : Type} {front : ℕ}

/-- **The term's four values are 0.** -/
theorem vals4_zero (u : HTailF2) (q : α × Option Pub9) (y : Bound GE8) {tl tl' : HTailF2}
    {funs : Array HFun} {F F1 : Fork} {cls : List Desc.Claim}
    (he : equations front tl funs F = .ok (tl', F1, cls)) {v : Pub9} {g : Heard}
    (h1 : (π q.1).1 = some (blank u tl)) (h2 : q.2 = some v) (hg : tl.heard = some g)
    (hsz : OnBytes.PscRun.Sized v.F) (hU : OnBytes.PscRun.Later v.F F)
    (hslots : ∀ cl ∈ four8 tl g, ∀ x ∈ cl.form.slots.toList,
      InWin (winOf g.leaves) x.1 ∨ OnBytes.PscRun.Filled v.F x.1)
    (hs : tl.f9 = g.shape) (jLK : ℕ) (F' : Fork) (h0 : _root_.Fo.Later F' F)
    (hok : FoNums.ok g.shape = true) (hT : TailOK tl)
    (hfull : 2 ^ g.shape.cK = g.shape.NC) (h5 : 5 ≤ g.shape.kT + g.shape.cK)
    (hn : ∀ c < 2, (g.zk.getD c #[]).size = (tl.zOf c).call.n)
    (h63 : ∀ c < 2, (tl.zOf c).call.n ≤ 63)
    (hP : ∀ c < 2, ∀ p ∈ piecesL tl c, PieceOK tl c (tl.zOf c).call.n p)
    (hD : ∀ c < 2, (piecesL tl c).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off)
    (T : CoefOK (blank u tl) v.F)
    (hRw : ∀ a ∈ allPieces tl, a.2.r0 + a.2.Rp ≤ (v.F.trees.getD a.2.tree {}).R)
    (en : Ent3 → J₀) (mk : ℕ → J₀) (μ₀ : J₀ → GE8)
    (hcb : ∀ r < 32, ∀ i < tl.bzColumns,
      entUnit q y tl.ix.BZ r i = μ₀ (en (tl.ix.BZ, r, i)))
    (hcz : ∀ c < 2, ∀ p ∈ piecesL tl c, ∀ r < p.Rp, ∀ i < p.Cp,
      entUnit q y tl.ix.ZZ (p.r0 + r) (p.c0 + i) = μ₀ (en (tl.ix.ZZ, p.r0 + r, p.c0 + i)))
    (hm4 : ∀ k ∈ cls.take 4, ∀ s ∈ k.form.slots.toList, y.mask s.1 = μ₀ (mk s.1))
    (rs : Rounds GE8) (hI : HeardIs Reading.gl g F' (endsOf g.shape 5 jLK rs))
    (hPl : K3Planes g.shape 5 jLK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)) rs)
    (hK : K3Keys g.shape 5 jLK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
      (forK GE8 (digL5 GE8 tl en mk jLK Unit) () (zext μ₀)) rs) :
    ∀ x ∈ vals4 π (ent4 π) q y, x = 0 := by
  obtain ⟨g', Fa, hg', h4, hrun, hF1⟩ := take_four he
  obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hg)
  have hsa : OnBytes.PscRun.Sized F := hU.sized hsz
  have hlaid : LaidAt F1 (winOf g'.leaves) :=
    laid_of_run ((OnBytes.PscRun.paid_later F g'.owedJoin).sized hsa) hrun
      (by rw [hF1]; exact OnBytes.PscRun.paid_later Fa g'.owedPlanes)
  have hvals : vals4 π (ent4 π) q y = (four8 tl g').map (claimValue Reading.gl
      (refWorld Reading.gl v.F [winOf g'.leaves] (ent4 π q y) y)) := by
    have hgb : (blank u tl).heard = some g' := hg
    simp only [vals4, h1, h2, hgb]
    rw [four8_blank]
  intro x hx
  rw [hvals] at hx
  obtain ⟨cl, hcl, rfl⟩ := List.mem_map.1 hx
  rw [claim_refOf Reading.gl cl v.F F1 [winOf g'.leaves] (ent4 π q y) y (hU.trans (eq_later he))
    (fun w hw => by
      rw [List.mem_singleton] at hw
      rw [hw]
      exact hlaid)
    fun z hz => (hslots cl hcl z hz).imp (fun h => ⟨_, List.mem_singleton.2 rfl, h⟩) id]
  exact four_zero_ent4 π u q y he h1 h2 hg hs jLK F' h0 hok hT hsa hfull h5 hn h63 hP hD T hRw en mk
    μ₀ hcb hcz hm4 F1 (_root_.Fo.Later.refl F1) rs hI hPl hK cl (h4 ▸ hcl)

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.claim_refOf
#print axioms VerifiableInference.Desc.First.K8.Honest.vals4_zero
