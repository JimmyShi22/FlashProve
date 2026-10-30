-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/BehindMade.lean: THREE OF THE PUBLIC TESTS' GROUNDS THAT THE SUB-PROTOCOL
"the output head's own rounds" (K6) MAKES, BEHIND A YES OF THE STRICT READING OF ITS BARE BLOCK:
lookIn 24 8; the table's test on the forms at the head's four runs; that test at the lookup's run on
the planes. AT A STATE, AT NO OPENED LEAVES (the sub-protocol's decision reads none); general in the
composed meaning's data. EVERY THEOREM IS CONDITIONAL.

  `below_of_yes`     the strict reading of a block says yes where the block does and every word of
                     the rounds is below the prime
  `made_lookIn_at`   lookIn 24 8
  `behind_facts`     three facts on the state behind a yes of the bare block
  `made_forms_at`    the test on the forms at each of the four runs
  `made_planes_at`   the test on the forms at the run on the planes

WHY IT IS TYPED, AND HOW. The library has the three at a piece of the proof of soundness
(`made_lookIn`, Johnson/Desc/Kinds/Law/K6LookInMade.lean; `made_forms`, Law/K6FormsMade.lean; the
planes' arm of `pubBehind_four`, Law/K6PubBehindFour.lean). These statements take a piece (`Seated`)
and its yes: the honest side has a block's yes and no piece. THE THREE PROOFS HERE ARE THE LIBRARY's
OWN TEXTS, LESS THE PIECE: cut off these files by a program, with "the piece's yes" turned into "the
strict reading of the bare block says yes". Two more things have turned: the library's two premises
`planB Wp = true` and `K6Left` are here the one premise `K6On`; and in `made_lookIn_at` its six
premises on public parameters are the one test with code `k6PubC`, read out by `k6Pub_says`. What
lies beneath is called as it lies: `lookIn_below` (Law/K6Makes.lean); `four_behind`,
`noTables_below` (Law/HeadRidesSays.lean); `four_answer`, `letters_behind` (Law/SilentAnswers.lean);
`k6_formsInT` (Law/K6FormsInT.lean); `planes_formsInT_behind` (Law/PlanesFormsInT.lean);
`readers_silent_planes` (Law/PlanesCell.lean); `left_says` (Law/K6LeftSays.lean); `k6Pub_says`
(Law/K6PubNumbers.lean); `canonical_of_below` (Law/K6RecordPaid.lean); `blockOf_trees`
(Law/KeepsTrees.lean); `blockOf_owed` (Law/KeepsOwed.lean).

Relatives. Of `below_of_yes`: the other direction (`below_yes`, Johnson/Desc/Sound/PieceYes.lean).
Of `behind_facts`: `below_ledgers` (Law/PlanesArm.lean). A search over the library's statements for
one that ends in one of the three main conclusions from a block's yes found none: a search, not a
proof that there is none. That is said of the conclusions at the composed data's own readers. At
readers that are letters the library has two of the three from where the strict reading of the bare
sub-protocol accepts: `planes_formsInT_behind`, `lookIn_below`: they are called.

WHAT GOES IN AS IT COMES OUT, AND WHAT IS MADE. Three premises of `made_forms_at` and of
`made_planes_at` speak of the state BEHIND (haK, hMask, hEnt), and hMask and hEnt are clauses of the
very test that is concluded: an entry of a form is to pass `entInT`; a slot wants the mask row's
seat. What the two theorems make is that the reader answers, and that each form names only entries
of row 0 below the width and filled slots. Honest/Law/BehindFour.lean makes hMask and hEnt, from two
tests with code. The other premises stand in the statements alone; what is left of them at the
gathering is listed in that file's head.

Limits. These tests are totalities: they say that a later test of the verifier's will find what it
looks for. No yes is shown, and no state at which the premises hold together. Modules under
lean/Johnson/Goal/ are among what this file imports: it imports no module of that folder by name and
calls nothing that is declared there: they lie beneath the library's files that it calls. Nothing on
any property.

-/
import Johnson.Desc.K6.Honest.Law.BehindKept
import Johnson.Desc.Kinds.Law.K6LookInMade
import Johnson.Desc.Kinds.Law.K6PubNumbers
import Johnson.Desc.Kinds.Law.K6PubBehindFour

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Honest
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S Pub pubAll)
open OnBytes
open OnBytes.Model (Ent)
open VerifiableInference.Desc (Link)
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Desc.Kinds.Head.Law.AtTable

/-- The strict reading of a block says yes where the block does and every word of the rounds is
below the prime. At no opened leaves. -/
theorem below_of_yes {Cl : Type} (b : Block S Cl) {s s' : S} {rs : List Fmt.RoundView}
    (hcan : viewWordsBelowPrime ⟨rs, []⟩ = true) (hd : b.decide s rs [] = .ok s') :
    (Sound.below b).decide s rs [] = .ok s' := by
  show (if viewWordsBelowPrime ⟨rs, (([] : List (List (Nat × List UInt64))).flatMap id).map
                  fun c => (0, c.1, c.2)⟩ then b.decide s rs [] else .error "a word is not below the prime") = _
  have e : (([] : List (List (Nat × List UInt64))).flatMap id).map
      (fun c => ((0 : Nat), c.1, c.2)) = [] := rfl
  rw [e, if_pos hcan]
  exact hd

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : Sound.MgData Xi P Tok rows cols nR Wp) (base : Pub → P × S → Bool) (z : P) {s s' : S}
  {rs : List Fmt.RoundView} {b6 : Block S Unit} (h6 : blockOf Wp 24 = some b6)
  (hd : (Sound.below b6).decide s rs [] = .ok s')

include h6 hd

/-- **lookIn 24 8 is made.** The library's proof at a piece (`made_lookIn`,
Johnson/Desc/Kinds/Law/K6LookInMade.lean), less the piece. CONDITIONAL. -/
theorem made_lookIn_at (hOn : K6On Wp s)
    (left : VerifiableInference.OnPublicFiles.k3LeftItemAt Wp 24 s)
    (hrows : First.Tape.RowsOwed.noneWaits s.rowsOwed = true)
    (hlk : (∃ L, s.link? = some L ∧ L.link = 24 ∧ L.arrayOf = D.sent.arrayOf.getD 24 #[]) ∧
      (s.tl?.bind (·.heard)).isNone = true)
    (hpubC : Law.k6PubC Wp = true) :
    pubAll D.pubD base (.lookIn 24 8) (z, s') = true := by
  obtain ⟨_, hsort8, _, _, _, p8, sh8, hp8, hsh8, hnum⟩ := Law.k6Pub_says Wp hpubC
  obtain ⟨p3, hp3, L3⟩ := left
  obtain ⟨h3, F, g, hs3, hF, hg, Y, _⟩ := Law.left_says p3 s L3
  obtain ⟨n1, n2, n3⟩ := hnum p3 h3 hp3 hs3
  obtain ⟨x8, hx8, rfl⟩ := Option.map_eq_some_iff.1 hp8
  have hl8 : x8.link = 24 := VerifiableInference.OnPublicFiles.lookAt_link hx8
  have K := Law.lookIn_below Wp 24 b6 h6 s s' rs [] hd hOn g hg
    (by rw [Y.zx]; exact n3) _ sh8 hsh8 rfl (D.sent.arrayOf.getD 24 #[]) F hF
    (by rw [Y.next]; exact n1) (by rw [Y.ns]; exact n2) Y.free hlk.2 hrows (by
      obtain ⟨L, e1, e2, e3⟩ := hlk.1
      rw [e1]
      show (L.link == x8.link && L.arrayOf == D.sent.arrayOf.getD 24 #[]) = true
      rw [e2, e3, hl8]
      simp)
  rw [First.pubAll_lookIn D.pubD base 24 8 true hsort8]
  show First.Look.lookInC (First.Look.K3Data.of Wp D.sent) 24 true s' = true
  rw [First.Look.lookInC_is]
  unfold First.Look.k3LookInAt
  rw [hp8]
  exact K

omit hd in
/-- Three facts on the state behind a yes of the bare block. -/
theorem behind_facts (hd' : b6.decide s rs [] = .ok s') :
    ∃ F1, s'.fork? = some F1 ∧ s'.lookHeard? = s.lookHeard? ∧ K9.mergeOf s' = K9.mergeOf s := by
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp h6
  obtain ⟨o, F1, X, Q, ho, _, e, _, hG⟩ := forks_blockAt _ i _ 24 hd'
  refine ⟨F1, hG, ?_, ?_⟩
  · rw [e]
    unfold First.S.lookHeard?
    rw [ho]
  · rw [e]
    unfold K9.mergeOf
    rw [ho]

/-- **The table's test on the forms accepts at each of the head's four runs, behind a yes.** The
library's proof at a piece (`made_forms`, Johnson/Desc/Kinds/Law/K6FormsMade.lean), less the piece.
CONDITIONAL. -/
theorem made_forms_at (hOn : K6On Wp s) (hA : K6After Wp s') (piece6 : ℕ) (Lk : Link S Claim)
    (small : S → Option K9.Read)
    (KS : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) 24 piece6 (K9.statesOfLink Lk) 3)
    (KB : K6Back Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) 24 piece6 (K9.statesOfLink Lk) 3)
    (readers : D.Rd 24 = K9.readersOfLink ⟨small, k6Silent (p8K6 Wp 24) (K9.statesOfLink Lk)⟩ Lk)
    (Z1 : noTablesB s = true) (hwo : K9.mergeOf s = none)
    (left : VerifiableInference.OnPublicFiles.k3LeftItemAt Wp 24 s)
    (tree : ∃ G tr, s.fork? = some G ∧ G.trees[readsOf Wp]? = some tr ∧ tr.R = 1 ∧
      tr.K = Wp.H.nU.getD 2 0)
    (hnU : Wp.H.nU.getD 2 0 ≠ 0) (hB : tabsPlanB Wp.hS Wp.HLy Wp.H = true)
    (hRB : readsPlanB Wp.hS Wp.H = true)
    (hcov : ∃ cov, s'.covered Wp.hS.T Wp.hS.V = .ok cov) (h4 : 5 ≤ Wp.hS.lmbH)
    (hpub : ∀ p3 h3, First.Look.placeAt Wp 24 false = some p3 → p3.shape = some h3 →
      h3.NC = 6 ∧ h3.calls.size = 6 ∧ Wp.hS.lmbH ≤ h3.kT + 5 ∧
        Wp.hS.ls ≤ (Wp.HLy.calls.getD 0 default).lJ ∧
        Wp.hS.ls ≤ ((h3.calls[0]?).map (·.n)).getD 0)
    (aK : K9.Part) (haK : K9.segAt? s' = some aK)
    (hMask : (K9.maskSeat (D.N.sent 24 0) aK).isSome = true)
    (hEnt : ∀ x : Ent, x.tree = readsOf Wp → x.row = 0 → x.idx < Wp.H.nU.getD 2 0 →
      K9.entInT (D.N.sent 24 0) aK x = true)
    (name : String) (hn : K6Name name) :
    K9.formsInT (D.Rd 24) (D.N.sent 24 0) 3 name s' = true := by
  obtain ⟨p3, hp3, L3⟩ := left
  obtain ⟨h3, F, g, hs3, hF, hg, Y, _⟩ := left_says p3 s L3
  obtain ⟨q1, q2, q3, q4, q5⟩ := hpub p3 h3 hp3 hs3
  obtain ⟨G0, tr, hG0, htr0, hR1, hK⟩ := tree
  obtain rfl : G0 = F := Option.some.inj (hG0.symm.trans hF)
  obtain ⟨hcan, hd'⟩ := Law.canonical_of_below b6 s s' rs [] hd
  obtain ⟨F1, hF1, hlk, hmg⟩ := behind_facts h6 hd'
  have et := blockOf_trees Wp 24 b6 h6 s s' rs [] hd'
  have eo := blockOf_owed Wp 24 b6 h6 s s' rs [] hd'
  rw [hF, hF1] at et eo
  have et' : F1.trees = G0.trees := et
  have eo' : F1.owed = G0.owed := eo
  have htr1 : F1.trees[readsOf Wp]? = some tr := by
    rw [et']
    exact htr0
  have hgb : s'.lookHeard? = some g := hlk.trans hg
  have one : ∀ gk, s.lookHeard? = some gk → gk = g := fun gk hgk =>
    Option.some.inj (hgk.symm.trans hg)
  have hKne : tr.K ≠ 0 := by
    rw [hK]
    exact hnU
  have hwide : (p8K6 Wp 24).hp.nU.getD 2 0 ≤ tr.K := by
    rw [hK]
    exact Nat.le_refl _
  have Z2 : readsWideB (readsOf Wp) ((p8K6 Wp 24).hp.nU.getD 2 0) s = true := by
    unfold readsWideB
    rw [hF]
    show (match G0.trees[readsOf Wp]? with
      | some tr => Decidable.decide ((p8K6 Wp 24).hp.nU.getD 2 0 ≤ tr.K)
      | none => false) = true
    rw [htr0]
    exact decide_eq_true hwide
  have hzj : ∀ gk, s.lookHeard? = some gk →
      Wp.hS.ls ≤ (OnBytes.Model.Head.zjOf (p8K6 Wp 24).L gk 0).size := by
    intro gk hgk
    rw [one gk hgk]
    have z0 := Y.zkLen 0 (by rw [q1]; decide)
    show Wp.hS.ls ≤ ((g.zk.getD 0 #[]).extract 0 (Wp.HLy.calls.getD 0 default).lJ).size
    rw [Array.size_extract, z0]
    omega
  have h5 : ∀ gk, s.lookHeard? = some gk → Wp.hS.lmbH ≤ gk.shape.kT + 5 := by
    intro gk hgk
    rw [one gk hgk, Y.shape]
    exact q3
  have hun : K3.unpaid F1 g.owedJoin = true := by
    have := Y.join
    unfold K3.unpaid at this ⊢
    rw [eo']
    exact this
  obtain ⟨f1, f2, _, _⟩ := four_behind Wp 24 b6 h6 s s' rs [] hd hOn (p8K6 Wp 24) Z1 Z2 24
    piece6 3 Lk KS small
  obtain ⟨R, hR⟩ := four_answer Wp 24 b6 h6 s s' rs [] hd hOn (p8K6 Wp 24) rfl hB hRB hcov
    hzj h4 h5 F1 tr hF1 htr1 hKne hwide hR1 piece6 3 (K9.statesOfLink Lk) KS KB g hgb hun Y.cEnd
    (by rw [Y.shape]; exact q2) (by rw [Y.e]; exact q1) name hn
  have hFree : K9.mergeOf s' = none := hmg.trans hwo
  have hRow : ∀ e v, withTables (p8K6 Wp 24) s' = some e →
      lettersAt (parOf Wp.hS (workOf Wp)) (seatAt Wp.hS (readsOf Wp)) e = .ok v →
      (letI := v.1
       letI := v.2.1
       EntriesRow0 (readsOf Wp) tr.K v.2.2.final v.2.2.head) := by
    obtain ⟨i, hu, hbb⟩ := Option.map_eq_some_iff.mp h6
    have hr : readsOf Wp = i := by
      unfold readsOf
      rw [hu]
      rfl
    subst hr
    subst hbb
    obtain ⟨e0, v0, he0, hv0, _, _, _, _, _, hRow0, _⟩ := letters_behind Wp 24 hd' hOn.1 hcan
      hOn.2.1 (p8K6 Wp 24) rfl hB hRB hcov hOn.2.2.1 hzj h4 h5 F1 tr hF1 htr1 hKne hwide
    intro e v he hv
    obtain rfl : e0 = e := Option.some.inj (he0.symm.trans he)
    obtain rfl : v0 = v := Except.ok.inj (hv0.symm.trans hv)
    exact hRow0
  rw [readers]
  exact k6_formsInT Wp (p8K6 Wp 24) 24 piece6 3 (K9.statesOfLink Lk) KS _ (D.N.sent 24 0) s' aK
    haK f1 hOn.2.1 f2 hA.2.1 hA.2.2.1
    (fun gk hgk => by rw [Option.some.inj (hgk.symm.trans hgb)]; exact Y.cEnd) tr.K hRow
    (by rw [hK]; exact hEnt) hMask hFree name hn R hR


/-- **The table's test on the forms accepts at the lookup's run on the planes, behind a yes.** The
library's proof at a piece (inside `pubBehind_four`, Johnson/Desc/Kinds/Law/K6PubBehindFour.lean),
less the piece. CONDITIONAL. -/
theorem made_planes_at (hOn : K6On Wp s) (Lk : Link S Claim) (small : S → Option K9.Read)
    (runs2 : PlanesStates (readsOf Wp) Wp.hS.lmbH (K9.statesOfLink Lk) 2)
    (back2 : PlanesBack (readsOf Wp) Wp.hS.lmbH (K9.statesOfLink Lk) 2)
    (readers : D.Rd 24 = K9.readersOfLink ⟨small, k6Silent (p8K6 Wp 24) (K9.statesOfLink Lk)⟩ Lk)
    (R : AtFold.K6Reached s) (left : VerifiableInference.OnPublicFiles.k3LeftItemAt Wp 24 s)
    (tree : ∃ G tr, s.fork? = some G ∧ G.trees[readsOf Wp]? = some tr ∧ tr.R = 1 ∧
      tr.K = Wp.H.nU.getD 2 0)
    (c3 : Wp.H.nU.getD 2 0 ≠ 0) (hB : tabsPlanB Wp.hS Wp.HLy Wp.H = true)
    (hRB : readsPlanB Wp.hS Wp.H = true)
    (hc : ∃ cov, s'.covered Wp.hS.T Wp.hS.V = .ok cov) (c4 : 5 ≤ Wp.hS.lmbH)
    (c5 : ∀ p3 h3, First.Look.placeAt Wp 24 false = some p3 → p3.shape = some h3 →
      h3.NC = 6 ∧ h3.calls.size = 6 ∧ Wp.hS.lmbH ≤ h3.kT + 5 ∧
        Wp.hS.ls ≤ (Wp.HLy.calls.getD 0 default).lJ ∧
        Wp.hS.ls ≤ ((h3.calls[0]?).map (·.n)).getD 0)
    (planeCols : ∀ p3 h3, First.Look.placeAt Wp 24 false = some p3 → p3.shape = some h3 →
      h3.NC * 2 ^ (h3.kT + 5 - Wp.hS.lmbH) ≤ (Wp.H.tl.mats.getD (Wp.hS.NHf + 1 + 1) {}).k *
        ((Wp.H.tl.mats.getD (Wp.hS.NHf + 1 + 1) {}).m / 2 ^ Wp.hS.lmbH))
    (hLv : ∀ Fs gk, s.fork? = some Fs → s.lookHeard? = some gk →
      LeavesReady gk Fs ∧ OnBytes.PscRun.Filled Fs gk.sBit ∧
        ∀ x ∈ gk.leaves.start.slots.toList, OnBytes.PscRun.Filled Fs x.1)
    (aK : K9.Part) (haK : K9.segAt? s' = some aK)
    (hMask : (K9.maskSeat (D.N.sent 24 0) aK).isSome = true)
    (hEnt : ∀ x : Ent, x.tree = readsOf Wp → x.row = 0 → x.idx < Wp.H.nU.getD 2 0 →
      K9.entInT (D.N.sent 24 0) aK x = true) :
    K9.formsInT (D.Rd 24) (D.N.sent 24 0) 2 "planes" s' = true := by
  obtain ⟨p3, hp3, L3⟩ := left
  obtain ⟨h3, F, g, hs3, hF, hg, Y, hlv⟩ := left_says p3 s L3
  obtain ⟨q1, _, q3, q4, q5⟩ := c5 p3 h3 hp3 hs3
  obtain ⟨G0, tr, hG0, htr0, hR1, hK⟩ := tree
  obtain rfl : G0 = F := Option.some.inj (hG0.symm.trans hF)
  obtain ⟨_, hd'⟩ := canonical_of_below b6 s s' rs [] hd
  have et := blockOf_trees Wp 24 b6 h6 s s' rs [] hd'
  rw [hF, seg_fork haK] at et
  have et' : aK.F.trees = G0.trees := et
  obtain ⟨o', ho', ht'⟩ := (noTablesB_iff s').1
    (noTables_below Wp 24 b6 h6 s s' rs [] hd R.noTab)
  obtain ⟨v1, v2, v3⟩ := hLv G0 g hF hg
  obtain ⟨_, _, _, hmg⟩ := behind_facts h6 hd'
  have hFree : K9.mergeOf s' = none := hmg.trans R.wo
  rw [readers]
  exact planes_formsInT_behind Wp 24 b6 h6 s s' rs [] hd
    hOn (p8K6 Wp 24) rfl hB hRB hc aK haK tr
    (by rw [et']; exact htr0) (by rw [hK]; exact c3) (by rw [hK]; exact Nat.le_refl _) hR1 2
    (K9.statesOfLink Lk) runs2 back2 _ (D.N.sent 24 0)
    (readers_silent_planes (readsOf Wp) Wp.hS.lmbH 2 Lk runs2 (p8K6 Wp 24) small s' o' ho' ht')
    G0 hF g hg v1
    (by
      have z0 := Y.zkLen 0 (by rw [q1]; decide)
      show Wp.hS.ls ≤ ((g.zk.getD 0 #[]).extract 0 (Wp.HLy.calls.getD 0 default).lJ).size
      rw [Array.size_extract, z0]
      omega)
    (by
      unfold First.Look.planesOk
      rw [Y.shape, decide_eq_true c4, decide_eq_true q3]
      rfl)
    (by
      show g.shape.NC * 2 ^ (g.shape.kT + 5 - Wp.hS.lmbH) ≤ _
      rw [Y.shape]
      exact planeCols p3 h3 hp3 hs3)
    hlv v3 v2 (by rw [hK]; exact hEnt) hMask hFree

end

end VerifiableInference.Desc.Kinds.Head.Honest

#print axioms VerifiableInference.Desc.Kinds.Head.Honest.below_of_yes
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.made_lookIn_at
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.behind_facts
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.made_forms_at
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.made_planes_at
