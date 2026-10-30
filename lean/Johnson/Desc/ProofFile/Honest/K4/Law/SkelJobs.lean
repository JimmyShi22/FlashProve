-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SkelJobs.lean: CONDITIONAL: on `LookSkel`, on three lengths,
and on own sampled values and tokens taken as equal.

What is here. CONGRUENCES: THREE OF THE SEVEN SUMMANDS' MAKERS OF THE FEED-FORWARD LAYERS' ROUNDS,
AND ONE OF THE TWO LONG LISTS OF SCALARS THAT GO EACH PLUS A MASK ENTRY (the row products; which
two: `k4MakersFit`, Honest/K4/Part.lean), at two lists of what the lookup in front has sampled: the
row products and their sumcheck over the tokens; the first gated product; the merge
(Johnson/Desc/K4/Honest/Norms.lean, Johnson/Desc/K4/Honest/Gated.lean,
Johnson/Desc/K4/Honest/Merge.lean). One definition, and nineteen statements with their proofs.

  `JobSkel`, `jobSkel_of`, `fitsAny_rel`   two jobs to which the public test on a job's shape
      (`k4JobFits`, Honest/K4/Part.lean) gives one answer, at every call.
  `len_one`   a small law: two lists of one member are as long.
  `rowForms_eq`, `rowMaps_rel`, `rowProducts_len`, `jobRows_skel`   the norms' rows.
  `gatedTabs_rel`, `levelJob_skel`, `jobGated_skel`   the first gated product.
  `claimEnvOf_rel`, `embClaim_rel`, `mergeClaimsAt_rel`, `jobMerge_skel`   the merge.
  `mergeSizes_rel`, `zipIdx_snd_rel`, `mergePairs_rel`, `mergeJob_fits_rel`, `mergeJob_skel`   its
      tools.

Debts and ends. `JobSkel` IS AN END: NO DEBT. In four files of its writers a statement names it, all
of this family of congruences: this one, Law/SkelGen.lean, Law/SkelTerms.lean and
Law/SkelStack.lean. In every statement but one it is the end; it is the hypothesis of `fitsAny_rel`,
here, which turns it into one answer of the public test on a job's shape; and, in the files of its
writers, `fitsAny_rel` is called in Law/MakersSkel.lean and Law/MakersAt.lean alone, each time with
one of these ends. Here it is had from its definition by `jobSkel_of`, from six comparisons of
Bools, numbers and lengths, and by `mergeJob_skel`; the four others that end in it here
(`levelJob_skel`, `jobRows_skel`, `jobGated_skel`, `jobMerge_skel`) go through one of the two. IT
COMPARES TWO JOBS BY ONE BOOL AT EVERY CALL. `LookSkel` IS A DEBT: see Law/LookSkel.lean: it is the
hypothesis S of eight statements here: `rowMaps_rel`, `rowProducts_len`, `jobRows_skel`,
`jobGated_skel`, `claimEnvOf_rel`, `embClaim_rel`, `mergeClaimsAt_rel`, `jobMerge_skel`. THREE
LENGTHS OF OWN SAMPLED VALUES ARE HYPOTHESES TOO: hrs (of rs) of `claimEnvOf_rel`; hrs, hZ (of ZE)
and hk (of tkh) of `embClaim_rel`, `mergeClaimsAt_rel` and `jobMerge_skel`: fields of `PtsFull`
(Law/MakersAt.lean) or of its first field `PtsSkel` (Law/SkelEnv.lean): debts: see there; in
Law/MakersSkel.lean each closes by rfl, at the zero challenges; Law/SkelGen.lean, which calls
`claimEnvOf_rel`, takes hrs as a hypothesis of its own laws and hands it on. The library's `EnvKeys`
is the hypothesis S of `rowForms_eq`, paid in `rowMaps_rel` from `envOf_rel`; its `ClaimSkel` and
`ClaimAlike` are ends here (`claimEnvOf_rel`; `embClaim_rel`, `mergeClaimsAt_rel`). `HasSame`
(Law/SkelReads.lean) and `EnvLook` (Law/SkelEnv.lean) are ends of sister files, had and spent inside
proofs here. THE TWO INPUTS w AND w₀ ARE FREE LETTERS, but for their tokens in the three statements
named under Not shown here.

Not shown here. NO MAKER IS SHOWN TO RETURN ANYWHERE: a statement on a maker compares two calls. THE
OWN SAMPLED VALUES THAT STAND IN A MAKER's JOB (PV, omV in `jobRows_skel`; rs in `jobGated_skel`)
AND THE TOKENS (`embClaim_rel`, `mergeClaimsAt_rel`, `jobMerge_skel`) ARE TAKEN AS EQUAL HERE: MORE
THAN THE SHAPE READS (of PV and rs the length, of omV nothing: Law/SkelGen.lean): in those files
these five serve two zero inputs alone; for a run against the zero input:
Law/SkelGen.lean. Nothing on what a table, a sum or an end value is worth.

Kin. For two values that may be missing, under two functions, the library's `optRel_map'`
(OnBytes/Flat/LinksFreeFork.lean) is called, here and in Law/SkelGen.lean, Law/SkelTerms.lean and
Law/SkelStack.lean. Law/SkelGen.lean has the five statements named above anew, with lengths in the
stead of equal values. `mergeJob_fits` (Law/SumMerge.lean) is the stronger law on the merge's cube:
its test is true whatever the claims, the matrix and the coefficients; from it `mergeJob_fits_rel`
and `mergeJob_skel` would follow at any two lists of claims, without h; it is not called: this file
does not build on that one. `colTab_size` and `rowTab_size` there are the two sizes that
`mergeSizes_rel` finds anew. `gatedTabs_size` (Law/SumLevels.lean) has, from one return, the number
of entries of the two tables that `gatedTabs_rel` compares. The short names len_one and rowForms_eq
are borne by other theorems of the library, on other things (len_one:
Johnson/Desc/First/K4/Returns/Kit.lean and three more; rowForms_eq:
Johnson/Desc/Kinds/Law/NormProof.lean, Johnson/Desc/Reads/NormRows.lean). No definition of the
library under the short name JobSkel was found.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SkelEnv
import Johnson.Desc.ProofFile.Honest.K4.Part
import Johnson.Desc.K4.Honest.Law.Cube
import Johnson.Desc.First.K4.Returns.Pub.Claims
import Johnson.Desc.First.K4.Returns.Pub.End
import OnBytes.Flat.LinksFreeFork

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E F zeroE)
open OnBytes.Model (Aff Forest.Heard WsClaim)
open OnBytes.Model.Layer (ClaimEnv downFrom callsTS)
open OnBytes.Flat (All2 OptRel ClaimAlike optRel_bind optRel_bind_same optRel_map')
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw (fits_sizes wayLen valuesAt_size)
open OnBytes.Desc.First.K4.RtPub

/-! ## Two jobs of one shape -/

/-- Two jobs to which the public test on a job's shape gives one answer, at every call. -/
def JobSkel (j j₀ : Job) : Prop := ∀ sh, k4JobFits sh j = k4JobFits sh j₀

/-- `JobSkel` from six comparisons: the cube's test, its number of variables, the lead's length,
whether the way has a length, dY, and the number of end values at every list of challenges. -/
theorem jobSkel_of {j j₀ : Job} (h1 : j.cube.fits = j₀.cube.fits) (h2 : j.cube.n = j₀.cube.n)
    (h3 : j.lead.length = j₀.lead.length)
    (h4 : (wayLen j.cube.way).isSome = (wayLen j₀.cube.way).isSome) (h5 : j.dY = j₀.dY)
    (h6 : ∀ rs, (j.ends rs).length = (j₀.ends rs).length) : JobSkel j j₀ := by
  intro sh
  unfold k4JobFits
  dsimp only
  rw [h1, h2, h3, h5]
  simp only [h6]
  cases hw : j.cube.way <;> cases hw₀ : j₀.cube.way
  · rfl
  · rw [hw, hw₀] at h4
    cases h4
  · rw [hw, hw₀] at h4
    cases h4
  · rfl

/-- Two lists of one member. Stated of variables, so that the two members are not compared. -/
theorem len_one {α : Type} (a b : α) : [a].length = [b].length := rfl

/-- Two jobs that may be missing, in `JobSkel`: the public test finds one answer. -/
theorem fitsAny_rel {x y : Option Job} (h : OptRel JobSkel x y)
    (sh : VerifiableInference.Desc.Part.MaskedSum.Call) :
    x.any (k4JobFits sh) = y.any (k4JobFits sh) :=
  any_rel h fun _ _ r => r sh

/-! ## The norms' rows -/

/-- The rows' forms are the same at two environments of the same keys. -/
theorem rowForms_eq {v v₀ : OnBytes.Model.Layer.Env} (S : EnvKeys v v₀) :
    rowForms v = rowForms v₀ := by
  unfold rowForms
  rw [S.y]
  simp only [digitsAt_eq S]

variable (Q : K4Pub) (w w₀ : K4In) {p p₀ : Pts}

/-- The rows' fields as tables on the tokens: as many tables, of the same sizes. -/
theorem rowMaps_rel (S : LookSkel p.fo p₀.fo) :
    OptRel (fun ms ms₀ : Array Tab => ms.map Array.size = ms₀.map Array.size) (rowMaps Q w p)
      (rowMaps Q w₀ p₀) := by
  unfold rowMaps
  refine optRel_bind (envOf_rel Q S) fun v v₀ hv => ?_
  rw [rowForms_eq hv.1.keys]
  refine optRel_bind_same fun fs => ?_
  refine optRel_bind (amapM_rel (R := HasSame)
    (fun t => readsAt_has Q w w₀ S (All2.refl (fun _ => ⟨rfl, rfl⟩) _)) _) fun Rs Rs₀ hR => ?_
  refine OptRel.mono (fun ms ms₀ h => Array.toList_inj.mp ?_)
    (amapM_rel (R := fun a a₀ : Array E => a.size = a₀.size) (fun f =>
      OptRel.mono (fun _ _ k => k.length)
        (amapM_all2_rel (S := HasSame) (R := fun _ _ : E => True)
          (fun R R₀ k => valAff_rel hv.1.keys.iU3 hv.1.keys.K3 k rfl _ _) hR)) fs)
  rw [Array.toList_map, Array.toList_map]
  exact All2.map_eq (fun _ _ r => r) h

/-- The row products: as many. -/
theorem rowProducts_len (S : LookSkel p.fo p₀.fo) :
    (rowProducts Q w p).length = (rowProducts Q w₀ p₀).length := by
  unfold rowProducts
  have r := rowMaps_rel Q w w₀ S
  revert r
  cases rowMaps Q w p <;> cases rowMaps Q w₀ p₀ <;> intro r
  · rfl
  · exact False.elim r
  · exact False.elim r
  · dsimp only
    rw [length_flatMap_every _ _ (fun _ => List.length_map ..),
      length_flatMap_every _ _ (fun _ => List.length_map ..)]

/-- The row products' sumcheck over the tokens, at equal PV and omV. -/
theorem jobRows_skel (S : LookSkel p.fo p₀.fo) (hPV : p.PV = p₀.PV) (hom : p.omV = p₀.omV) :
    OptRel JobSkel (jobRows Q w p) (jobRows Q w₀ p₀) := by
  unfold jobRows
  refine optRel_bind (rowMaps_rel Q w w₀ S) fun ms ms₀ hm => ?_
  dsimp only
  rw [hPV, hom]
  refine optRel_iteB (fits_sizes _ _ (by rfl) (by rfl) hm (by rfl) (by rfl))
    (optRel_pure (jobSkel_of (fits_sizes _ _ (by rfl) (by rfl) hm (by rfl) (by rfl)) (by rfl)
      (len_one _ _) (by rfl) (by rfl) fun rs => ?_))
    (by trivial)
  show (Cube.valuesAt _ rs).toList.length = (Cube.valuesAt _ rs).toList.length
  rw [Array.length_toList, Array.length_toList, valuesAt_size, valuesAt_size]
  have e := congrArg Array.size hm
  rw [Array.size_map, Array.size_map] at e
  exact e

/-! ## The first gated product -/

/-- The first gated product's two tables: made together, of the same sizes. -/
theorem gatedTabs_rel :
    OptRel (fun t t₀ : Tab × Tab => t.1.size = t₀.1.size ∧ t.2.size = t₀.2.size) (gatedTabs Q w)
      (gatedTabs Q w₀) := by
  unfold gatedTabs
  refine optRel_bind_same fun ts => optRel_bind_same fun tu => optRel_pure ⟨?_, ?_⟩
  · show (layerTab _ _ _ _ _ _ _ _).size = (layerTab _ _ _ _ _ _ _ _).size
    unfold layerTab
    rw [Array.size_ofFn, Array.size_ofFn]
  · show (layerTab _ _ _ _ _ _ _ _).size = (layerTab _ _ _ _ _ _ _ _).size
    unfold layerTab
    rw [Array.size_ofFn, Array.size_ofFn]

/-- A level's job at two points of one length and two pairs of tables of the same sizes. -/
theorem levelJob_skel (mu : Nat) (order : List Nat) {rho rho₀ : Array E} {t t₀ : Tab × Tab}
    (hr : rho.size = rho₀.size) (h1 : t.1.size = t₀.1.size) (h2 : t.2.size = t₀.2.size) :
    JobSkel (levelJob mu order rho t) (levelJob mu order rho₀ t₀) := by
  have hf : (levelJob mu order rho t).cube.fits = (levelJob mu order rho₀ t₀).cube.fits :=
    fits_sizes _ _ rfl rfl (by
      show #[t.1, t.2].map Array.size = #[t₀.1, t₀.2].map Array.size
      simp [h1, h2]) rfl (by
      show some rho.size = some rho₀.size
      rw [hr])
  refine jobSkel_of hf rfl rfl rfl rfl fun rs => ?_
  show (Cube.valuesAt _ rs).toList.length = (Cube.valuesAt _ rs).toList.length
  rw [Array.length_toList, Array.length_toList, valuesAt_size, valuesAt_size]
  rfl

/-- The first gated product's job, at equal rs. -/
theorem jobGated_skel (S : LookSkel p.fo p₀.fo) (hrs : p.rs = p₀.rs) :
    OptRel JobSkel (jobGated Q w p) (jobGated Q w₀ p₀) := by
  unfold jobGated
  refine optRel_map' (gatedTabs_rel Q w w₀) fun t t₀ h => levelJob_skel _ _ ?_ h.1 h.2
  rw [hrs, Array.size_append, Array.size_append, ztOf_skel Q S]

/-! ## The merge -/

/-- The claims' environment: there at both or at neither, of one skeleton. -/
theorem claimEnvOf_rel (S : LookSkel p.fo p₀.fo) (hrs : p.rs.size = p₀.rs.size) :
    OptRel ClaimSkel (claimEnvOf Q p) (claimEnvOf Q p₀) := by
  unfold claimEnvOf
  exact optRel_map' (envOf_rel Q S) fun v v₀ h => ⟨h.1.keys.y, h.1.g, rfl, hrs, h.1.zk⟩

/-- The embedding's claim, at equal tokens: there at both or at neither, and alike. -/
theorem embClaim_rel (S : LookSkel p.fo p₀.fo) (hrs : p.rs.size = p₀.rs.size)
    (hZ : p.ZE.size = p₀.ZE.size) (hk : p.tkh.size = p₀.tkh.size) (ht : w.tokv = w₀.tokv) :
    OptRel ClaimAlike (embClaim Q w p) (embClaim Q w₀ p₀) := by
  unfold embClaim
  refine optRel_ite (optRel_bind (claimEnvOf_rel Q S hrs) fun c c₀ k => ?_) trivial
  rw [ht]
  exact claimE_rel k hZ hk _ rfl rfl

/-- The merge's list of claims likewise, claim by claim. -/
theorem mergeClaimsAt_rel (S : LookSkel p.fo p₀.fo) (hrs : p.rs.size = p₀.rs.size)
    (hZ : p.ZE.size = p₀.ZE.size) (hk : p.tkh.size = p₀.tkh.size) (ht : w.tokv = w₀.tokv) :
    OptRel (All2 ClaimAlike) (mergeClaimsAt Q w p) (mergeClaimsAt Q w₀ p₀) := by
  unfold mergeClaimsAt panelClaims
  refine optRel_bind (S := All2 ClaimAlike)
    (optRel_bind (claimEnvOf_rel Q S hrs) fun c c₀ k =>
      optRel_bind_same fun TS => weightClaims_rel k TS)
    fun cp cp₀ hcp => ?_
  dsimp only
  exact optRel_ite
    (optRel_bind (S := All2 ClaimAlike)
      (optRel_map' (embClaim_rel Q w w₀ S hrs hZ hk ht) fun _ _ h => .cons h .nil)
      fun ce ce₀ hce => optRel_pure (hcp.append hce))
    (optRel_bind (S := All2 ClaimAlike) (OptRel.some .nil)
      fun ce ce₀ hce => optRel_pure (hcp.append hce))

/-- The merge's tables at two lists of as many claims: as many, of the same sizes. -/
theorem mergeSizes_rel (lay : OnBytes.Model.WsLay) (a a₀ : Nat → Nat → F) :
    ∀ (cls cls₀ : List WsClaim), cls.length = cls₀.length → ∀ acc acc₀ : Array Tab,
      acc.map Array.size = acc₀.map Array.size →
      (cls.foldl (fun t c => (t.push (colTab lay c)).push (rowTab lay a c)) acc).map Array.size =
        (cls₀.foldl (fun t c => (t.push (colTab lay c)).push (rowTab lay a₀ c)) acc₀).map Array.size
  | [], [], _, _, _, h => h
  | [], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _ => by simp at hl
  | c :: l, c₀ :: l₀, hl, acc, acc₀, h => by
    rw [List.foldl_cons, List.foldl_cons]
    refine mergeSizes_rel lay a a₀ l l₀ (Nat.succ.inj hl) _ _ ?_
    have e1 : (colTab lay c).size = (colTab lay c₀).size := by
      simp [colTab, Johnson.Desc.First.ForkMerge.Honest.onColumns]
    have e2 : (rowTab lay a c).size = (rowTab lay a₀ c₀).size := by
      unfold rowTab
      split <;> split <;> simp
    rw [Array.map_push, Array.map_push, Array.map_push, Array.map_push, h, e1, e2]

/-- Two lists of one length, numbered from k: a function of the numbers alone gives one list. -/
theorem zipIdx_snd_rel {α β γ : Type} (g : Nat → γ) :
    ∀ (l : List α) (l₀ : List β), l.length = l₀.length → ∀ k,
      (l.zipIdx k).map (fun x => g x.2) = (l₀.zipIdx k).map fun x => g x.2
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | _ :: l, _ :: l₀, hl, k => by
    rw [List.zipIdx_cons, List.zipIdx_cons, List.map_cons, List.map_cons,
      zipIdx_snd_rel g l l₀ (Nat.succ.inj hl) (k + 1)]

/-- The numbers of the merge's pairs of tables are the same at two lists of as many claims. -/
theorem mergePairs_rel {cls cls₀ : List WsClaim} (h : cls.length = cls₀.length)
    (rho rho₀ : Array E) :
    (cls.zipIdx.map fun x => (rho.getD x.2 zeroE, 2 * x.2, 2 * x.2 + 1)).map Prod.snd =
      (cls₀.zipIdx.map fun x => (rho₀.getD x.2 zeroE, 2 * x.2, 2 * x.2 + 1)).map Prod.snd := by
  rw [List.map_map, List.map_map]
  exact zipIdx_snd_rel (fun k => (2 * k, 2 * k + 1)) cls cls₀ h 0

/-- The merge's cube passes its test at both or at neither. -/
theorem mergeJob_fits_rel (lay : OnBytes.Model.WsLay) (a a₀ : Nat → Nat → F)
    {cls cls₀ : List WsClaim} (h : cls.length = cls₀.length) (rho rho₀ : Array E) :
    (mergeJobOf lay a cls rho).cube.fits = (mergeJobOf lay a₀ cls₀ rho₀).cube.fits := by
  unfold mergeJobOf
  dsimp only
  exact fits_sizes _ _ rfl rfl (mergeSizes_rel lay a a₀ cls cls₀ h #[] #[] rfl)
    (mergePairs_rel h rho rho₀) rfl

/-- The merge's job at two lists of as many claims. -/
theorem mergeJob_skel (lay : OnBytes.Model.WsLay) (a a₀ : Nat → Nat → F) {cls cls₀ : List WsClaim}
    (h : cls.length = cls₀.length) (rho rho₀ : Array E) :
    JobSkel (mergeJobOf lay a cls rho) (mergeJobOf lay a₀ cls₀ rho₀) := by
  intro sh
  unfold k4JobFits
  rw [mergeJob_fits_rel lay a a₀ h rho rho₀]
  simp [mergeJobOf]

/-- The merge's job, at equal tokens: both makers return or neither, and the jobs are in `JobSkel`.
-/
theorem jobMerge_skel (S : LookSkel p.fo p₀.fo) (hrs : p.rs.size = p₀.rs.size)
    (hZ : p.ZE.size = p₀.ZE.size) (hk : p.tkh.size = p₀.tkh.size) (ht : w.tokv = w₀.tokv) :
    OptRel JobSkel (jobMerge Q w p) (jobMerge Q w₀ p₀) := by
  unfold jobMerge
  exact optRel_map' (mergeClaimsAt_rel Q w w₀ S hrs hZ hk ht) fun _ _ h =>
    mergeJob_skel _ _ _ h.length _ _

end ProofFile.Honest.K4




#print axioms ProofFile.Honest.K4.JobSkel
#print axioms ProofFile.Honest.K4.jobSkel_of
#print axioms ProofFile.Honest.K4.len_one
#print axioms ProofFile.Honest.K4.fitsAny_rel
#print axioms ProofFile.Honest.K4.rowForms_eq
#print axioms ProofFile.Honest.K4.rowMaps_rel
#print axioms ProofFile.Honest.K4.rowProducts_len
#print axioms ProofFile.Honest.K4.jobRows_skel
#print axioms ProofFile.Honest.K4.gatedTabs_rel
#print axioms ProofFile.Honest.K4.levelJob_skel
#print axioms ProofFile.Honest.K4.jobGated_skel
#print axioms ProofFile.Honest.K4.claimEnvOf_rel
#print axioms ProofFile.Honest.K4.embClaim_rel
#print axioms ProofFile.Honest.K4.mergeClaimsAt_rel
#print axioms ProofFile.Honest.K4.mergeSizes_rel
#print axioms ProofFile.Honest.K4.zipIdx_snd_rel
#print axioms ProofFile.Honest.K4.mergePairs_rel
#print axioms ProofFile.Honest.K4.mergeJob_fits_rel
#print axioms ProofFile.Honest.K4.mergeJob_skel
#print axioms ProofFile.Honest.K4.jobMerge_skel
