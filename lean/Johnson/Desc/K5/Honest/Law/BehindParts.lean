-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/BehindParts.lean: CONDITIONAL: the three premises on public tests that
the library's law "the promise behind the block of an attention segment's own rounds follows from
the promise in front" (`k5_t2`, Johnson/Desc/First/Att/K05T2.lean) takes beside `K5Fill`, AT ONE
STATE: the tests tied to the items that stay open ride over the lay (keptForms); the tests tied to
the three items that the block makes hold behind the lay (madeForms); the two extra tests that the
block is let to make hold behind the lay (madeMore).

Why this file. The library has all three as sentences over every state that meets the promise in
front (`keptForms_at`, `madeForms_at`, `planesIn_plus`, `madeMore_plus`,
Johnson/Desc/First/Att/Door/Law/), each under premises over every such state. At the table's own
filling these premises do not follow from the promise alone; they follow at a state at which
further facts are known. So the same proofs are laid here at one state, with the facts as
premises. `planesIn_at` and `made_at` follow the library's proofs line by line; `kept_at` also pays
that law's two premises on the reader, `madeMore_at` that law's two on the tests behind the lay.

Main names:
  `kept_at`: keptForms at one state. It spends: what is held as received from the lookup, and that
    its kept rows name no entry.
  `planesIn_at`: the test tied to the lookup's run "planes" holds behind the lay. It spends: what
    the lookup leaves (`K3LeftOutIs`), and the library's test on what it has left and the ledger
    (`FillBare.leftAtB`).
  `made_at`: madeForms at one state, from the runs' returns and `planesIn_at`'s conclusion.
  `madeMore_at`: madeMore at one state, at the list of extra tests
    `(moreOver9 M0).strike leavesName`.

Limits. All are conditional; none of the premises is shown to be met here. All four also take hpub,
which the docstrings do not name: the filling's tests with code are `pubAll D base`.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.Door.Law.KeptFormsAt
import Johnson.Desc.First.Att.Door.Law.MadeFormsAt
import Johnson.Desc.First.Att.Door.Law.MadeMorePlus
import Johnson.Desc.First.Att.Door.Law.MadeBehind
import Johnson.Desc.First.Att.Door.Law.K5LeftFitsF

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open Cb Cb.LdLkp OnBytes OnBytes.Model
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K9 (Readers readerOf statesOfLink readersOfLink LinkHoles)
open VerifiableInference.Desc.First.Att.P (behind hear Heard K5Place K3LeftOutIs RunsReturn GeoFits
  U3There parCOf runsN geoOf readersOfO fork_front guardC)
open H2K5.Door

section
variable {Pp W : Type} (D : PubData) (base : Pub → Pp × S → Bool) (Mg : Meaning Pp W)
  (hpub : Mg.pub = pubAll D base) {π : Pp} {s : S} {att : AttOwn} {own : Params.AttentionRounds}
  {rs : List Fmt.RoundView} {hd : Heard} {G : Fork}
include hpub

/-- **The tests tied to the items that stay open ride over the lay, at one state.** Conditional:
hO: beside the index's, one tied test is met at the border: that of the run "objects" (a test on
the table's lists); hrO, hObj, hGst: that run's two readers (facts on the verifier's own link); e,
hh, hz: the open segment, the hearing's return, the sized ledger; hlk, hbr: what is held as
received from the lookup, and that its kept rows name no entry. -/
theorem kept_at (links : List ModelPart) (pl : VerifiableInference.Desc.Place) (O : List Item) (m : ℕ)
    (hO : ∀ i ∈ O, (rowOf links pl).ins.contains i = false → i ≠ .pinI → ∀ q ∈ tiesOf i,
      q = .formsInT m 2 "objects")
    (hrO : D.runs m 2 "objects" = [(1, "objects"), (1, "guests")])
    (hObj : ∀ (t : S) (F : Fork) (g₁ : Forest.Heard), t.fork? = some F → t.lookHeard? = some g₁ →
      (∀ f ∈ g₁.rows.toList, f.ents = #[]) →
      (D.Rd m).forms 1 "objects" t = some { forms := g₁.rows.toList, late := [] })
    (hGst : ∀ (t : S) (F : Fork), t.fork? = some F →
      (D.Rd m).forms 1 "guests" t = some { forms := [], late := [] })
    (e : s.here = .att att) (hh : hear own (att.F, rs, 0) = some (hd, G, [], 0))
    (hz : OnBytes.Model.Road.Sized att.F) {g₁ : Forest.Heard} (hlk : s.lookHeard? = some g₁)
    (hbr : ∀ f ∈ g₁.rows.toList, f.ents = #[]) :
    ∀ i ∈ O, (rowOf links pl).ins.contains i = false → i ≠ .pinI → ∀ q ∈ tiesOf i,
      Mg.pub q (π, s) = true → Mg.pub q (π, behind s att hd G) = true := by
  intro i hi h1 h2 q hq hv
  obtain rfl := hO i hi h1 h2 q hq
  have hlk' : (behind s att hd G).lookHeard? = some g₁ := by
    unfold S.lookHeard? at hlk ⊢
    rw [e] at hlk
    exact hlk
  rw [hpub, pubAll_formsInT] at hv ⊢
  refine List.all_eq_true.2 fun p hp => ?_
  have hv' := List.all_eq_true.1 hv p hp
  rw [hrO] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · refine Att.P.formsInT_kept (D.Rd m) (D.N.sent m 0) 1 "objects" e hh hz
      ((hObj _ G _ rfl hlk' hbr).trans (hObj s att.F _ (fork_front e) hlk hbr).symm)
      (fun R hR x hx => ?_) hv'
    obtain rfl := Option.some.inj ((hObj s att.F _ (fork_front e) hlk hbr).symm.trans hR)
    cases hx
  · refine Att.P.formsInT_kept (D.Rd m) (D.N.sent m 0) 1 "guests" e hh hz
      ((hGst _ G rfl).trans (hGst s att.F (fork_front e)).symm) (fun R hR x hx => ?_) hv'
    obtain rfl := Option.some.inj ((hGst s att.F (fork_front e)).symm.trans hR)
    cases hx

/-- **The test tied to the lookup's run "planes" holds behind the lay, at one state.**
Conditional: hrP, hRd, hcl, hL, hsame: the run and its reader at the verifier's own link; hh, hz:
the hearing's return, the sized ledger; hin: the claims' reading behind the lay returns; U: three
facts on the state in front; hLf: what the lookup leaves; e: the open segment; hleft: the library's
test on what the lookup has left and the ledger in front; hPl, hPos, hn, hlm: tests and
comparisons on public numbers. -/
theorem planesIn_at {Cl St₀ J₀ : Type} [DecidableEq J₀] (claim : Aff → Cl) (m : ℕ)
    (a : Attention.Plan) (hrP : D.runs m 2 "planes" = [(1, "planes")]) (H : LinkHoles)
    (Lk : Link S Claim) (hRd : D.Rd m = readersOfLink H Lk) {same : S → S → Bool}
    (claimC : Aff → Claim)
    (hcl : ∀ f, (claimC f).form = f ∧ (claimC f).runs.isEmpty = true ∧
      (claimC f).eqFirst.isNone = true) (lm : ℕ) {nm : String}
    (hL : ((statesOfLink Lk 1).find? fun c => c.1 == "planes") = some (guardC same
      (nm, K3.planesRun (K3.seatCalls claimC) lm (readersOfO a))))
    (hsame : ∀ s t : S, t.out = s.out → same s t = true)
    (e : s.here = .att att) (hh : hear own (att.F, rs, 0) = some (hd, G, [], 0))
    (hz : OnBytes.Model.Road.Sized att.F) {i : Att.P.Runs.In} {K : ℕ}
    (hin : Att.P.inOf (Att.P.seatCO (parCOf a)) (parCOf a) (behind s att hd G) = some (i, K))
    (U : U3There (D.N.sent m 0) s att (parCOf a)) {fs : Forest.Shape} {lm' first : ℕ}
    {io : Fo.Pl → Option J₀} {Qf : Fork → Prop} {x0 : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀)}
    {gL : Forest.Heard}
    (hLf : K3LeftOutIs (K3.seatCalls claim).fork (K3.seatCalls claim).heard fs lm' first io Qf x0
      gL s)
    (hleft : FillBare.leftAtB gL att.F = true)
    (hPl : Look.planesOk fs (parCOf a).geo.lmb = true) (hPos : K5Law.PosG (geoOf a.S))
    (hn : fs.NC * 2 ^ (fs.kT + 5 - (parCOf a).geo.lmb) ≤
      (a.seam.tl.mats.getD (a.S.cf.NAs + 2) {}).k *
        ((a.seam.tl.mats.getD (a.S.cf.NAs + 2) {}).m / 2 ^ a.S.cf.lmb))
    (hlm : lm = (parCOf a).geo.lmb) :
    Mg.pub (.formsInT m 2 "planes") (π, behind s att hd G) = true := by
  obtain ⟨_, F', _, _, _, Lf, e1, e2, _⟩ := hLf
  have hshape : gL.shape = fs := Lf.shape
  obtain rfl : F' = att.F :=
    Option.some.inj ((show s.fork? = some F' from e2).symm.trans (fork_front e))
  have hlk : att.lookHeard = some gL := by
    have e1' : s.lookHeard? = some gL := e1
    rw [Att.P.lookHeard_front e] at e1'
    exact e1'
  obtain ⟨eg, _, hK, _, _, lk, _, _, _, ht⟩ := Att.P.inOf_behind hin
  obtain ⟨_, bl⟩ := Att.P.hear_below hh hz
  have lt : _root_.Fo.Later att.F G := by
    obtain ⟨_, _, _, _, _, _, st⟩ := Att.P.hear_said hh hz
    exact ⟨bl.1, bl.ns, fun j hj => by
      obtain ⟨a₁, b₁, d₁⟩ := st j _ _ ⟨hj, rfl, rfl⟩
      exact ⟨a₁, b₁, d₁⟩⟩
  have hW : (parCOf a).nW ≤ K := by
    obtain ⟨T, hT, _, hw⟩ := U.tree
    rw [bl.trees, hT] at hK
    obtain rfl : T.K = K := Option.some.inj hK
    exact hw
  rw [← eg] at ht
  rw [hpub, pubAll_formsInT, hrP]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [hRd]
  refine Att.P.formsInT_planes_left H Lk _ claimC hcl a lm hh hz hin U hlk hL hsame
    (by rw [Att.P.unpaid_below bl]; exact unpaid_planes_of_left Lf.padLeft)
    (leftAtB_later lt bl hleft) (by rw [hshape, hlm]; exact hPl) (fun r hr => ?_)
  have R := Att.P.readers_ret_plan (n := fs.NC * 2 ^ (fs.kT + 5 - (parCOf a).geo.lmb)) hin hr
    (K5Law.len_in ht) hW (S := a.S) (tl := a.seam.tl) eg ht (eg ▸ hPos) hn
  rw [hshape, hlm]
  exact R

/-- **The tests tied to the three items that the block makes hold behind the lay, at one state.**
Conditional: hr3, hrJ, hRds: the runs and their readers at the verifier's own link; hh, hz; Rt: the
four runs return; gf: a test on public numbers; U; hplanes: `planesIn_at`'s conclusion. -/
theorem made_at (m : ℕ) (A : Attention.Plan)
    (hr3 : D.runs m 3 "own" = [(2, "first"), (2, "keys"), (2, "second")])
    (hrJ : D.runs m 2 "join" = [(2, "join")])
    (hRds : ∀ (name : String) (s : S) (R : K9.Read), (name == "K8.equations") = false →
      readerOf (fun _ => runsN A) 2 name s = some R → (D.Rd m).forms 2 name s = some R)
    (hh : hear own (att.F, rs, 0) = some (hd, G, [], 0)) (hz : OnBytes.Model.Road.Sized att.F)
    (Rt : RunsReturn A s att hd G) (gf : GeoFits (parCOf A).geo own)
    (U : U3There (D.N.sent m 0) s att (parCOf A))
    (hplanes : Mg.pub (.formsInT m 2 "planes") (π, behind s att hd G) = true) :
    ∀ q ∈ [Pub.formsInT m 3 "own", Pub.formsInT m 2 "planes", Pub.formsInT m 2 "join"],
      Mg.pub q (π, behind s att hd G) = true := by
  intro q hq
  obtain ⟨i, K, l₁, l₂, j, kf, gL, yj, hin, h1, h2, hk, hg, hcE, hcF, hun, hj⟩ := Rt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · have h := Att.P.formsInT_own_behind (fun _ => runsN A) A rfl (D.N.sent m 0) hh hz hin h1 h2 hk
      gf U
    rw [hpub, pubAll_formsInT, hr3]
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨formsInT_mono _ 2 "first" _ (fun R => hRds "first" _ R (by decide))
        (h "first" (by simp)),
      formsInT_mono _ 2 "keys" _ (fun R => hRds "keys" _ R (by decide)) (h "keys" (by simp)),
      formsInT_mono _ 2 "second" _ (fun R => hRds "second" _ R (by decide))
        (h "second" (by simp))⟩
  · exact hplanes
  · have h := Att.P.formsInT_join_behind (fun _ => runsN A) A rfl (D.N.sent m 0) hh hz hin h1 hk gf
      U hg hcE hcF hun hj
    rw [hpub, pubAll_formsInT, hrJ]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    exact formsInT_mono _ 2 "join" _ (fun R => hRds "join" _ R (by decide)) h

/-- **The two extra tests that the block is let to make hold behind the lay, at one state.**
Conditional: hmore: the filling's list of extra tests; Ix, h0, hatt, hA: facts on the table's lists
and the composed data; hPm: what the two items say beside their tests, asked at every state: the
conclusion's second half is this premise; e, hh; hsz: the ledger's test in front; gf; hl: the open
link's number; hreads: the test on the array of the tables in front. -/
theorem madeMore_at (M0 : More) (hmore : Mg.more = (moreOver9 M0).strike leavesName)
    (links : List ModelPart) {pl pl' : VerifiableInference.Desc.Place} {m : ℕ}
    (Ix : K5Place links m pl pl')
    (h0 : (M0.rows links pl).makes = []) (hatt : D.d5.isAtt m = true) {A : Attention.Plan}
    (hA : D.d5.W.A[m / 2]? = some A)
    (hPm : ∀ a : Pp × S, Mg.pubP (.more (some m) "K5.okAt") a ∧
      Mg.pubP (.more (some m) "K5.plain") a)
    (e : s.here = .att att) (hh : hear own (att.F, rs, 0) = some (hd, G, [], 0))
    (hsz : s.fork?.any K3.sizedB = true) (gf : GeoFits (geoOf A.S) own) (hl : att.L.link = m)
    {ownL : List (ℕ × ℕ)} (hreads : readsThereB D.d5.W ownL s = true) :
    ∀ x ∈ (Mg.more.rows links pl).makes, Mg.pub (moreItem x) (π, behind s att hd G) = true ∧
      Mg.pubP (moreItem x) (π, behind s att hd G) := by
  intro x hx
  rw [hmore, k5_makes_9 Ix M0 h0] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · refine ⟨?_, (hPm _).1⟩
    show Mg.pub (.more (some m) "K5.okAt") _ = true
    rw [hpub, pubAll_more_okAt D base m hatt, hA]
    exact ok_made_behind e hh hsz gf
  · refine ⟨?_, (hPm _).2⟩
    show Mg.pub (.more (some m) "K5.plain") _ = true
    rw [hpub, pubAll_more_plain D base m hatt, hA]
    exact plain_made_behind D.d5.W ownL e (by rw [hl]; exact hA) hh hsz hreads

end

end H2K5.Honest

#print axioms H2K5.Honest.kept_at
#print axioms H2K5.Honest.planesIn_at
#print axioms H2K5.Honest.made_at
#print axioms H2K5.Honest.madeMore_at
