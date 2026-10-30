-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/ClaimsAtRecord.lean: the claims that the output head's block returns in its run
"policy" are the four forms of the row's letters.

What is shown. Steps: they speak of the kind's written block `kind`
(Johnson/Desc/Kinds/HeadKind.lean) and of `runsBy` (Johnson/Desc/Kinds/HeadFrame.lean).
  `letters_of_run`: a yes of a run of claims made by `runsBy`: all the kind's letters are there at
    the state; the run's forms are found under its name; the claims are these forms, one by one.
  `policy_claims`: **at a state that lies so, a yes of the block's run "policy" returns the four
    forms of the row's letters**, each under the letter that turns a form into a claim. By
    `forms_at` (Reads/FormsAtRecord.lean).
  `lies_of_three`: a lemma on the way: `Lies` behind three yeses: the kind's own decision on its
    rounds; the block of a commitment with the reads' quiet step behind it; a run of the kind's
    claims at the state that this leaves. By `core_of_kind` (Reads/HeardSizes.lean).

Limits. `lies_of_three` speaks of no run of the seated description: there the claims are run later
than at the state behind the quiet step: see Reads/RowAtSeat.lean. Its premises on a state (cols;
the sizes of the lookup's two points on the planes; the ledger in front of the head's own rounds is
well laid) are shown by nothing here. No state of a run is shown. Nothing on soundness.


-/
import Johnson.Desc.Reads.HeardSizes
import Johnson.Desc.Reads.FormsAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtSeat

open OnBytes.Model.Head (Covered Tables)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K8 (ReadsQuiet.head ReadsQuiet.bind_ok ReadsQuiet.named_ok)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law

/-- **What a yes of a run of claims says.** -/
theorem letters_of_run {T Cl : Type} {names : List String}
    {runs : Given → Behind → Places → List (String × List Form)}
    {keys : Given → Behind → Places → List Form} {toCl : Form → Cl} {p : Par} {L : Head.Seat T}
    {c : String × (ℕ → T → Except String (List Cl × T))}
    (hc : c ∈ runsBy names runs keys toCl p L) {n : ℕ} {s : T} {y : List Cl × T}
    (h : c.2 n s = .ok y) :
    ∃ g b x fs, lettersAt p L s = .ok (g, b, x) ∧ (runs g b x).lookup c.1 = some fs ∧
      y.1 = fs.map toCl := by
  unfold runsBy at hc
  obtain ⟨name, -, rfl⟩ := List.mem_map.1 hc
  dsimp only at h
  obtain ⟨⟨g, b, x⟩, h1, h⟩ := ReadsQuiet.bind_ok h
  obtain ⟨fs, h2, h⟩ := ReadsQuiet.bind_ok h
  exact ⟨g, b, x, fs, h1, ReadsQuiet.named_ok h2, (congrArg Prod.fst (Except.ok.inj h)).symm⟩

/-- **The block's run "policy" returns the four forms of the row's letters.** -/
theorem policy_claims {Cl : Type} (cl : Form → Cl) (Z : Fill) (link piece : ℕ) {s : S}
    {o : HeadOwn} {cov : Covered} {x : OnBytes.Model.Head.Heard} {t : Tables} {g : Given}
    {bh : Behind} {pl : Places} (Q : Lies Z s o cov x t g bh pl)
    {c : String × (ℕ → S → Except String (List Cl × S))}
    (hc : c ∈ (kind cl (seatAt Z.h Z.iU3) link piece (parOf Z.h Z.work)).claims)
    (hname : c.1 = "policy") {n : ℕ} {y : List Cl × S} (h : c.2 n s = .ok y) :
    y.1 = (Z.letters.letters.forms () s).map cl := by
  have hc' : c ∈ runsBy ["norm", "policy", "logits"] (fun _ _ _ => claims)
      (fun g _ _ => g.calls.map fun c => keyVector key c.1 c.2) cl (parOf Z.h Z.work)
      (seatAt Z.h Z.iU3) := hc
  obtain ⟨g', b', x', fs, h1, h2, h3⟩ := letters_of_run hc' h
  rw [Q.letters] at h1
  obtain ⟨rfl, rfl, rfl⟩ : g = g' ∧ bh = b' ∧ pl = x' := by
    have e := Except.ok.inj h1
    exact ⟨congrArg Prod.fst e, congrArg (fun w => w.2.1) e, congrArg (fun w => w.2.2) e⟩
  rw [hname] at h2
  have e0 : (letI := g; letI := bh; letI := pl; Head.claims).lookup "policy" =
      some (letI := g; letI := pl; Head.policy) := rfl
  have e2 : fs = (letI := g; letI := pl; Head.policy) := Option.some.inj (h2.symm.trans e0)
  rw [h3, e2, forms_at Z Q]

/-- **Lies, behind three yeses.** -/
theorem lies_of_three {Cl : Type} (cl : Form → Cl) (Z : Fill)
    (hZ : Z.tab = planTab Z.h Z.hp.tl.mats) (place : VerifiableInference.Desc.Place)
    (link4 piece4 : ℕ) {s0 s2 s4 : S} {rs4 : List Fmt.RoundView}
    {gs4 : List (List (ℕ × List UInt64))}
    (h4 : (kind cl (seatAt Z.h Z.iU3) link4 piece4 (parOf Z.h Z.work)).decide s0 rs4 gs4 = .ok s2)
    (hWL : WellLaid ((seatAt Z.h Z.iU3).ledger s0))
    (hJ0 : (Z.L.calls.getD 0 default).lJ =
      (letI := sizesOf Z.h; lJ (OnBytes.Model.Head.keyFloor Z.h) (callKeys 0)))
    (hlsJ0 : Z.h.ls ≤ (Z.L.calls.getD 0 default).lJ)
    (P : VerifiableInference.Desc.K1.Par) (link moment : ℕ) (arrays : Option (List ℕ))
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h5 : (VerifiableInference.Desc.K8.ReadsQuiet.behind
      (VerifiableInference.Desc.K1.commitAtS P link moment arrays)
      (ReadsQuiet.head ⟨place, Z.h, Z.L, Z.hp⟩)).decide s2 rs gs = .ok s4)
    {c : String × (ℕ → S → Except String (List Cl × S))}
    (hc : c ∈ (kind cl (seatAt Z.h Z.iU3) link4 piece4 (parOf Z.h Z.work)).claims)
    {n : ℕ} {y : List Cl × S} (hrun : c.2 n s4 = .ok y)
    (hcols : ∀ o, s4.here = .head o → ∃ tr, o.F.trees[Z.iU3]? = some tr ∧ tr.K = Z.cols)
    (hzb : ∀ o x, s2.here = .head o → o.x = some x →
      x.g1.zb0.size = x.g1.shape.kT + x.g1.shape.cK + 5 ∧
      x.g1.zb1.size = x.g1.shape.kT + x.g1.shape.cK + 5) :
    Z.AtClose s4 := by
  have hc' : c ∈ runsBy ["norm", "policy", "logits"] (fun _ _ _ => claims)
      (fun g _ _ => g.calls.map fun c => keyVector key c.1 c.2) cl (parOf Z.h Z.work)
      (seatAt Z.h Z.iU3) := hc
  obtain ⟨g, bh, pl, fs, hl, -, -⟩ := letters_of_run hc' hrun
  have h4' : decideBy (fun _ => rounds) (fun _ => Head.hear) (fun _ _ => forTheMerge)
      (parOf Z.h Z.work) (seatAt Z.h Z.iU3) s0 rs4 = .ok s2 := h4
  obtain ⟨o, cov, x, t, Q⟩ := core_of_kind Z hZ place h4' hWL hJ0 hlsJ0 P link moment arrays h5
    hcols hzb
  exact ⟨o, cov, x, t, g, bh, pl, Q.lies hl⟩

end VerifiableInference.Reads.AtSeat

#print axioms VerifiableInference.Reads.AtSeat.letters_of_run
#print axioms VerifiableInference.Reads.AtSeat.policy_claims
#print axioms VerifiableInference.Reads.AtSeat.lies_of_three
